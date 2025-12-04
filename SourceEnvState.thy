theory SourceEnvState
  imports SourceAST Main
begin

type_synonym env = "vname \<Rightarrow> v option"

record state =
  input :: "char list"
  "output" :: string
  funs :: "dec list"
  clock :: nat

datatype error_type = Crash

datatype 'a result = Res 'a | Err error_type

abbreviation empty_env where "empty_env \<equiv> (\<lambda>x. None)"

(* helper function for env making from previous env *)
fun make_env :: "vname list \<Rightarrow> v list \<Rightarrow> env \<Rightarrow> env" where
  "make_env [] [] e = e" |
  "make_env (x # xs) (y # ys) e = make_env xs ys (e(x := Some y))" |
  "make_env [] _ _ = undefined" | "make_env _ [] _ = undefined"

fun lookup_function :: "fname \<Rightarrow> dec list \<Rightarrow> dec option" where
  "lookup_function _ [] = None" |
  "lookup_function name (Defun f v e # fs) = (if f = name then (Some (Defun f v e)) else
  lookup_function name fs)"

fun env_and_body :: "fname \<Rightarrow> v list \<Rightarrow> state \<Rightarrow> (env \<times> exp) option" where
  "env_and_body name args st = (case (lookup_function name (funs st)) of
  None \<Rightarrow> None | Some (Defun f params e) \<Rightarrow> Some (make_env params args empty_env, e))"

end