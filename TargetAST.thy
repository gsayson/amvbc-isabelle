theory TargetAST
    imports Main
begin

datatype reg = RAX | RDI | RBX | RBP | RDX | R12 | R13 | R14 | R15

datatype cond = Always | Less reg reg | Equal reg reg

(*Const reg \<longrightarrow> 64-bit; Load reg reg and Store reg reg take 4-bit addr offsets*)
datatype inst = Const reg | Mov reg reg | Add reg reg | Sub reg reg | Div reg |
    Jump cond nat | Call nat | Ret | Pop reg | Push reg | Add_RSP nat |
    Load_RSP reg nat | Load reg reg | Store reg reg | GetChar | PutChar |
    Exit | Comment string

end