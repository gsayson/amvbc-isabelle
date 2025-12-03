theory SourceAST
  imports Main
begin

type_synonym vname = nat

type_synonym fname = nat

datatype v = Pair v v | Num nat

datatype op = Add | Sub | Div | Cons | Head | Tail | Read | Write

datatype test = Less | Equal (*p1 > p2 \<Longleftrightarrow> p2 < p1*)

datatype exp =
  Const nat |
  Var vname |
  Op op "exp list" |
  Let vname exp exp |
  Call fname "exp list" |
  If test "exp list" exp exp

datatype dec = Defun fname "vname list" exp

datatype prog = Program "dec list" exp

end