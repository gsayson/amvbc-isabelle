theory TargetAST
    imports Main "Word_Lib.Word_64"
begin

datatype reg = RAX | RDI | RBX | RBP | RDX | R12 | R13 | R14 | R15

datatype cond = Always | Less reg reg | Equal reg reg

(*Const reg \<longrightarrow> 64-bit; Load reg reg and Store reg reg take 4-bit addr offsets*)
datatype inst = Const reg "64 word" | Mov reg reg | Add reg reg | Sub reg reg | Div reg |
    Jump cond nat | Call nat | Ret | Pop reg | Push reg | Add_RSP nat |
    Load_RSP reg nat | Load reg reg "4 word" | Store reg reg "4 word" | Get_Char | Put_Char |
    Exit | Comment string

type_synonym asm = "inst list"

end