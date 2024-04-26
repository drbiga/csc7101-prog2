datatype term = Variable of string | Constant of string | Compound of string * term list;

exception UnificationFailure;

fun unify (t1, t2, subst) =
    let
        fun applySubst (Variable v) = 
            (case List.lookup (fn (x, _) => x = v) subst of
                NONE => Variable v
              | SOME t => applySubst t)
          | applySubst (Compound (s, ts)) = 
            Compound (s, map applySubst ts)
          | applySubst t = t;

        fun unifyHelper (t1, t2) =
            case (applySubst t1, applySubst t2) of
                (Variable v1, Variable v2) =>
                    if v1 = v2 then subst
                    else (v1, Variable v2) :: subst
              | (Variable v, t) =>
                    if occursCheck v t then raise UnificationFailure
                    else (v, t) :: subst
              | (t, Variable v) =>
                    if occursCheck v t then raise UnificationFailure
                    else (v, t) :: subst
              | (Constant c1, Constant c2) =>
                    if c1 = c2 then subst
                    else raise UnificationFailure
              | (Compound (s1, ts1), Compound (s2, ts2)) =>
                    if s1 <> s2 then raise UnificationFailure
                    else unifyList (ts1, ts2, subst)
              | _ => raise UnificationFailure

        and unifyList ([], [], subst) = subst
          | unifyList (t1 :: ts1, t2 :: ts2, subst) =
            let
                val subst' = unifyHelper (t1, t2)
            in
                unifyList (ts1, ts2, subst')
            end
          | unifyList _ = raise UnificationFailure

        and occursCheck v t =
            let
                fun occurs (Variable v') =
                    if v = v' then true
                    else (case List.lookup (fn (x, _) => x = v') subst of
                              NONE => false
                            | SOME t' => occurs t')
                  | occurs (Compound (_, ts)) = exists occurs ts
                  | occurs _ = false
            in
                occurs t
            end
    in
        unifyHelper (t1, t2)
    end;

(* Example usage *)
val subst = unify (Compound ("f", [Variable "X", Constant "a"]), Compound ("f", [Constant "b", Variable "Y"]), []);
