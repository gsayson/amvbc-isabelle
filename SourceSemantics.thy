theory SourceSemantics
  imports SourceAST Main SourceEnvState
begin

fun take_branch :: "test \<Rightarrow> v list \<Rightarrow> source_state \<Rightarrow> (bool result \<times> source_state)" where
  "take_branch Equal [Num m, Num n] s = (Res (m = n), s)"
| "take_branch Less [Num m, Num n] s = (Res (m < n), s)"
| "take_branch _ _ s = (Err Crash, s)"

fun (sequential) eval_op :: "op \<Rightarrow> v list \<Rightarrow> source_state \<Rightarrow> v result \<times> source_state" where
  "eval_op Cons [x, y] s = (Res (Pair x y), s)"
| "eval_op Head [Pair x y] s = (Res x, s)"
| "eval_op Tail [Pair x y] s = (Res y, s)"
| "eval_op Write [Num n] s = (
    if n < 256 then (Res (Num 0), s \<lparr>out := (out s) @ [char_of n]\<rparr>)
    else (Err Crash, s)
  )"
| "eval_op Read [] s = (
    case (input s) of
      [] \<Rightarrow> (Res (Num (2^32 - 1)), s)
    | x # xs::string \<Rightarrow> (Res (Num (of_char x)), s \<lparr>input := xs\<rparr>)
  )"
| "eval_op Add [Num n1, Num n2] s = (Res (Num (n1 + n2)), s)"
| "eval_op Sub [Num n1, Num n2] s = (Res (Num (n1 - n2)), s)"
| "eval_op Div [Num n1, Num n2] s = (
    if n2 \<noteq> 0 then (Res (Num (n1 div n2)), s)
    else (Err Crash, s)
  )"
| "eval_op _ _ s = (Err Crash, s)"

inductive sl_big_step :: "env \<times> exp list \<times> source_state \<Rightarrow> v list \<times> source_state \<Rightarrow> bool"
  ("_ \<Down> _" 50) and app :: "fname \<Rightarrow> v list \<Rightarrow> source_state \<Rightarrow> v \<times> source_state \<Rightarrow> bool" where
  empty_rule: "(env, [], s) \<Down> ([], s)"
| const: "(env, [Const n], s) \<Down> ([Num n], s)"
| var: "env n = Some v
    \<Longrightarrow> (env, [Var n], s) \<Down> ([v], s)"
| app_rule: "\<lbrakk>env_and_body fname vs s1 = Some (env, body); (env, [body], s1) \<Down> ([v], s2)\<rbrakk>
    \<Longrightarrow> app fname vs s1 (v, s2)"
| call: "\<lbrakk>(env, xs, s1) \<Down> (vs, s2); app fname vs s2 (v, s3)\<rbrakk>
    \<Longrightarrow> (env, [Call fname xs], s1) \<Down> ([v], s3)"
| op: "\<lbrakk>(env, xs, s1) \<Down> (vs, s2); eval_op f vs s2 = (Res v, s3)\<rbrakk>
    \<Longrightarrow> (env, [Op f xs], s1) \<Down> ([v], s3)"
| let_rule: "\<lbrakk>
    (env, [x], s1) \<Down> ([v1], s2);
    (env(n := Some v1), [y], s2) \<Down> ([v2], s3)
  \<rbrakk>
    \<Longrightarrow> (env, [Let n x y], s2) \<Down> ([v2], s3)"
| if_rule: "\<lbrakk>
    (env, xs, s1) \<Down> (vs, s2);
    take_branch test vs s2 = (Res b, s2);
    (env, [if b then y else z], s2) \<Down> ([v], s3)
  \<rbrakk>
    \<Longrightarrow> (env, [If test xs y z], s1) \<Down> ([v], s3)"


end