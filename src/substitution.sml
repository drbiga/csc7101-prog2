type Substitution = string * int -> Term;

fun empty x = Var x;
val empty : Substitution = fn x => Var x;

fun value S (Var v) = S v
    | value S (Fun (f, args)) = Fun (f, map (value S) args);

fun comp (S, R) v = value S (R v);

fun S v = if v = ("X",0) then t2 else if v = ("Z",0) then t3 else Var v
fun R v = if v = ("X",0) then t1 else if v = ("Y",0) then Var("Z",0) else Var v

fun upd (v, t) S = comp (fn w => if w = v then t else Var w, S)

(upd (("Z",0), t3) R)

(comp (S,R))

(*
val empty : Substitution
val value : Substitution -> Term -> Term
val comp : Substitution * Substitution -> Substitution
val upd : (string * int) * Term -> Substitution -> Substitution
*)
