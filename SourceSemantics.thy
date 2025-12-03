theory SourceSemantics
  imports SourceAST Main SourceEnvState
begin

fun eval_op :: "op \<Rightarrow> v list \<Rightarrow> state \<Rightarrow> v result \<times> state" where
"eval_op Cons [x, y] s = (Res (Pair x y), s)" |
"eval_op Head [Pair x y] s = (Res x, s)" |
"eval_op Tail [Pair x y] s = (Res y, s)" |
"eval_op Div [Num n1, Num n2] s = (if n2 \<noteq> 0 then (Res (Num (n1 div n2)), s)
else (Err Crash, s))" |
"eval_op _ _ s = (Err Crash, s)"


inductive big_step_exp :: "env \<times> exp list \<times> state \<Rightarrow> v list \<times> state \<Rightarrow> bool" ("_ \<Rightarrow> _" 50) and
  app :: "fname \<Rightarrow> v list \<Rightarrow> state \<Rightarrow> v \<times> state \<Rightarrow> bool" where
"(env, [Const n], s) \<Rightarrow> ([Num n], s)" |
"env n = Some v \<Longrightarrow> (env, [Var n], s) \<Rightarrow> ([v], s)" |
"\<lbrakk>env_and_body fname vs s1 = Some (env, body); (env, [body], s1) \<Rightarrow> ([v], s2)\<rbrakk>
\<Longrightarrow> app fname vs s1 (v, s2)" | 
"\<lbrakk>(env, xs, s1) \<Rightarrow> (vs, s2); app fname vs s2 (v, s3)\<rbrakk> \<Longrightarrow> (env, [Call fname xs], s1) \<Rightarrow> ([v], s3)" |
"\<lbrakk>(env, xs, s1) \<Rightarrow> (vs, s2); eval_op f vs s2 = (Res v, s3)\<rbrakk> \<Longrightarrow> (env, [Op f xs], s1) \<Rightarrow> ([v], s3)"


end