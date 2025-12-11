section "Semantics of the target AST"

theory TargetSemantics
  imports TargetAST Main "Word_Lib.Word_64"
begin

(*64 bits = 8 bytes. require even length of stack for
amd64 calling convention*)
datatype word_or_ret = Word "64 word" | RetAddr nat

record target_state = instructions :: asm
  pc :: nat
  regs :: "reg \<Rightarrow> 64 word option"
  stack :: "word_or_ret list"
  memory :: "64 word \<Rightarrow> 64 word option option"
  input :: "char list"
  out :: "string"

fun ts_inc :: "target_state \<Rightarrow> target_state" where
  "ts_inc ts = ts \<lparr>pc := Suc (pc ts)\<rparr>"

fun ts_write_reg :: "target_state \<Rightarrow> reg \<Rightarrow> 64 word option \<Rightarrow> target_state" where
  "ts_write_reg ts rg val = ts \<lparr>regs := (regs ts)(rg := val)\<rparr>"

fun ts_write_regs :: "target_state \<Rightarrow> (reg \<times> 64 word option) list \<Rightarrow> target_state" where
  "ts_write_regs ts [] = ts"
| "ts_write_regs ts ((rg, val) # xs) = ts_write_reg (ts_write_regs ts xs) rg val"

fun ts_wri :: "target_state \<Rightarrow> reg \<Rightarrow> 64 word option \<Rightarrow> target_state" where
  "ts_wri ts rg val = ts \<lparr>pc := Suc (pc ts), regs := (regs ts)(rg := val)\<rparr>"

datatype t_state_or_halt = State target_state | Halt "64 word" string

(*assume 0 \<le> pc ts < size ts*)
fun fetch_instr :: "target_state \<Rightarrow> inst" where
  "fetch_instr ts = (instructions ts) ! (pc ts)"

text "Memory addresses can only be written to when it is storing a
value of \\texttt{Some None}, meaning that it is available vbut not yet
initialised."

definition can_write_to_mem_addr :: "target_state \<Rightarrow> 64 word \<Rightarrow> bool" where
  "can_write_to_mem_addr ts addr \<equiv> (memory ts) addr = Some None"

fun char_to_64word :: "char \<Rightarrow> 64 word" where
  "char_to_64word c = word_of_int (of_char c)"

definition eof_const :: "64 word" where "eof_const = 0xFFFFFFFF"

fun read_char_as_64word :: "string \<Rightarrow> 64 word \<times> string" where
  "read_char_as_64word [] = (eof_const, [])"
| "read_char_as_64word (x # xs) = (char_to_64word x, xs)"

inductive tl_step :: "t_state_or_halt \<Rightarrow> t_state_or_halt \<Rightarrow> bool" where
  const: "fetch_instr s = Const r w
    \<Longrightarrow> tl_step (State s) (State (ts_wri s r (Some w)))"
| mov: "\<lbrakk>
          fetch_instr s = Mov src dst;
          regs s src = Some val
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (ts_wri s dst (Some val)))"
| add: "\<lbrakk>
          fetch_instr s = Add src dst;
          regs s src = Some vs;
          regs s dst = Some vd
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (ts_wri s dst (Some (vs + vd))))"
| sub: "\<lbrakk>
          fetch_instr s = Sub src dst;
          regs s src = Some vs;
          regs s dst = Some vd
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (ts_wri s dst (Some (vd - vs))))"
| comment: "fetch_instr s = Comment _ \<Longrightarrow> tl_step (State s) (State s)" (*no-op*)
| call: "fetch_instr s = Call n
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := n, stack := RetAddr (Suc (pc s)) # (stack s)\<rparr>))"
| ret: "\<lbrakk>
          fetch_instr s = Ret;
          stack s = (RetAddr n) # xs
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := n, stack := xs\<rparr>))"
| exit: "\<lbrakk>
          fetch_instr s = Exit;
          (regs s) RDI = Some exit_code;
          even (length (stack s))
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (Halt exit_code (out s))"
| jmp: "\<lbrakk>fetch_instr s = Jump Always n\<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := n\<rparr>))"
| jmp_eq: "\<lbrakk>
          fetch_instr s = Jump (Equal r1 r2) n;
          (regs s) r1 = Some v1;
          (regs s) r2 = Some v2;
          v1 = v2
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := n\<rparr>))"
| jmp_less: "\<lbrakk>
          fetch_instr s = Jump (Less r1 r2) n;
          (regs s) r1 = Some v1;
          (regs s) r2 = Some v2;
          v1 < v2
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := n\<rparr>))"
| divq: "\<lbrakk>
          fetch_instr s = Div r;
          (regs s) r = Some dv;
          (regs s) RDX = Some 0; (regs s)
          RAX = Some a;
          dv \<noteq> 0
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (
          ts_inc (ts_write_regs s [(RAX, Some (a div dv)), (RDX, Some (a mod dv))])
        ))"
| push: "\<lbrakk>
          fetch_instr s = Push rg;
          (regs s) rg = Some vl
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := Suc (pc s), stack := Word vl # (stack s)\<rparr>))"
| pop: "\<lbrakk>
          fetch_instr s = Pop rg;
          stack s = vl # stk
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := Suc (pc s)\<rparr>))"
| load: "\<lbrakk>
        fetch_instr s = Load dst ra ofs;
        (regs s) ra = Some addr;
        (memory s) (addr + ucast ofs) = Some vo
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (ts_wri s dst vo))"
| store: "\<lbrakk>
          fetch_instr s = Store src ra ofs;
          (regs s) src = Some vl;
          (regs s) ra = Some addr
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>
          memory := (memory s)(
            (addr + ucast ofs) := Some ((regs s) src)
          )
        \<rparr>))"
| add_rsp: "\<lbrakk>
          fetch_instr s = Add_RSP (length xs);
          stack s = xs @ ys
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (s \<lparr>pc := Suc (pc s), stack := ys\<rparr>))"
| load_rsp: "\<lbrakk>
          fetch_instr s = Load_RSP dst ofs;
          ofs < length (stack s);
          (stack s) ! ofs = Word wd
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State (ts_wri s dst (Some wd)))"
| get_char: "\<lbrakk>
          fetch_instr s = Get_Char;
          read_char_as_64word (input s) = (ch, rest);
          even (length (stack s))
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State ((ts_inc
          (ts_write_regs s [
            (RDX, None), (RDI, None),
            (RAX, Some ch)
          ])
        ) \<lparr>input := rest\<rparr>))"
| put_char: "\<lbrakk>
          fetch_instr s = Put_Char;
          (regs s) RDI = Some (of_char n);
          (of_char n :: int) < 256;
          even (length (stack s))
        \<rbrakk>
    \<Longrightarrow> tl_step (State s) (State ((
          ts_inc (ts_write_regs s [
            (RDX, None),
            (RAX, None),
            (RDI, None)
          ])
        ) \<lparr>out := (out s) @ [n]\<rparr>))"

end