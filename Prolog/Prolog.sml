(* Substitutions *)
type Substitution = string * int -> Term

fun empty x = Var x

(* ================================================================================= *)
(* ================================================================================= *)
(* ================================================================================= *)
(* Prolog Notes Substitutions video *)

(* Understanding what a Substitution is *)
(* fun S v =
  if v = ("X", 0) then Fun("a", [])
  else if v = ("Y", 0) then Fun("f", [Fun("b", [])])
  else Var v *)

(* Applying a substitution based on the type of the variable? *)

(* We need to apply different types of substitutions based on whether the variable *)
(* is a Var or a Fun. We can use pattern matching to implement this behavior *)
fun value S (Var v)         = S v
  | value S (Fun (f, args)) = Fun (f, map (value S) args)

(* ================================================================================= *)
(* How to construct substitutions? *)
(* - Have a compose function *)

fun comp (S, R) v = value S (R v)

(* Update function *)
(* Assign a new variable binding to an existing substitution *)
fun upd (v, t) S = comp (fn w => if w = v then t else Var w, S)

fun upd (v, t) S w = if w = v then t else S w

fun
  top S (Var v) = S v
  | top S (x) = x


(* ================================================================================= *)
(* ================================================================================= *)
(* ================================================================================= *)
(* PROLOG NOTES UNIFICATION *)
(* Unification *)
exception non_unifiable_exception and occurs_check_exception and length_exception;

fun
  pairup (nil, nil)       = nil
  | pairup (a::b, c::d)     = (a, c) :: pairup(b, d)
  | pairup (_)              = raise length_exception

fun
  occurs v (Var w) = (v = w)
  | occurs v (Fun (w, args)) = List.exists (occurs v) args

fun unify' ((t1, t2), S) =
  let
    val t1' = top S t1;
    val t2' = top S t2;
  in
    case (t1', t2') of
      (Var v, Var w) => if v = w then S else upd(v, t2') S
      | (Var v, _) => if occurs v t2 then raise occurs_check_exception else upd(v, t2') S
      | (_, Var w) => if occurs w t1 then raise occurs_check_exception else upd(w, t1') S
      | (Fun (f1, fargs1), Fun (f2, fargs2)) =>
          if f1 = f2 then foldr unify' S (pairup (fargs1, fargs2))
          else raise non_unifiable_exception
  end

fun unify (t1, t2) =
    unify' ((t1, t2), empty)
    handle
      length_exception => raise non_unifiable_exception  
      | occors => raise non_unifiable_exception


(* ================================================================================= *)
(* ================================================================================= *)
(* ================================================================================= *)

(* Solver *)

exception unsolvable_exception

fun rename l (Var (x, _)) = Var (x, l)
  | rename l (Fun (f, args)) = Fun (f, map (rename l) args)

fun incl (Var (x, l)) = rename (l+1) (Var (x, l))

fun print_goal (goal: Term) =
  let
    fun
      print_term (Var (id, level)) = print (id ^ Int.toString(level))
      | print_term (Fun (p, args)) =
          if length args > 0 then (print p; print "("; print_list args; print ")")
          else (print p)
    and
      print_list (nil) = ()
      | print_list (head :: tail) = (print_term head; print_list tail)
  in
    print_term (goal)
  end

fun
  term_lists_are_equal (nil, nil) = true
  | term_lists_are_equal (h1 :: t1, h2 :: t2) = terms_are_equal (h1, h2) andalso term_lists_are_equal (t1, t2)
and
  terms_are_equal (Var (x, level_x), Var (y, level_y)) =
    if x = y andalso level_x = level_y then true
    else false
  | terms_are_equal (Fun (p, args_p), Fun (q, args_q)) =
    if p = q andalso term_lists_are_equal (args_p, args_q) then true
    else false
  | terms_are_equal (Var _, Fun _) = false
  | terms_are_equal (Fun _, Var _) = false

fun
  extract_variables (nil) = nil
  | extract_variables (goal :: goals) =
    case goal of
      Var (x, l) => x :: extract_variables (goals)
      | Fun (p, args) => extract_variables (goals)

fun extract_single_variable (Var (x, l)) = x
  | extract_single_variable (Fun (p, args)) = extract_single_variable (List.hd args)

exception subject_not_found_exception

fun extract_single_subject (Var (x, l)) = raise subject_not_found_exception
  | extract_single_subject (Fun (p, args)) = case (List.hd args) of Fun (p', args) => p' | _ => ""

fun Solve (goals: Term list, db: HornClause list) =
  let
    fun solve (nil, _, _, S) = S
      | solve (_, nil, _, _) = raise unsolvable_exception
      | solve (_, Headless _ :: _, _, _) = empty (* this can never happen *)
      | solve (goal :: goals, Headed (h, args) :: rules, level, S) =
        let
          val h' = rename (level + 1) h
          val S' = unify' ((goal, h), S)
            handle non_unifiable_exception => (OutLine ("Unification exception"); solve (goal :: goals, rules, level, S))
        in
          case goal of
            Var (x, l) => (
              OutLine (
                "Found viable substitution: " ^ PrintTerm (top S' (Var (x, l)))
              );
              S'
            )
            | Fun (p, args) => (
                S'
            )
        end
      
      (* val h' = rename level h
	    val S' = unify (goal, h) handle 
	      if unification succeeds
            t' = map (rename l) t
	    apply S' to t', goals
	    solve tail and rest of goals
	    else try next rule in db
	    else ... *)
     
  in
    solve (goals, db, 1, empty)
      handle unsolvable_exception => (OutLine ("false"); empty)
  end

(* Printing *)

fun OutQuery (goals: Term list, db: HornClause list) =
  let
    val S = Solve (goals, db)
    val bindings = map (value S) goals
    val value_bindings = map extract_single_subject bindings
    val variables = map extract_single_variable goals
    val pairs = pairup (variables, value_bindings)
    fun print_pairs (nil) = ()
      | print_pairs ((v, b) :: rest) = (OutLine (v ^ " = " ^ (b)); print_pairs (rest))
  in
    (* OutLine(foldr op^  "" (map PrintTerm bindings)) *)
    (* (
      OutLine(foldr op^ "" (value_bindings));
      OutLine (foldr op^ "" (variables))
    ) *)
    print_pairs (pairs)
    (* OutLine((PrintTerm (List.hd args)) ^ " = " ^ (PrintTerm (extract_single_subject (value S' goal)))); *)
    (*
       collect variables from goals
       reverse list of variable
       remove duplicates
       look up values of variable in S
       pass list of (variable, value) pairs to OutSol
    *)
  end


fun Prolog (x as (Headed (Var _, _))) =
    OutLine ("Illegal clause:  " ^ PrintClause x)
  | Prolog (x as (Headless (Var _ :: _))) =
    OutLine ("Illegal clause:  " ^ PrintClause x)
  | Prolog (Headed (Fun ("init", nil),nil)) = InitDB ()
  | Prolog (x as (Headed _)) = Assert x
  | Prolog (x as Headless y) =
    (OutLine ("query:  " ^ PrintClause x);
     (* OutLine ("query not yet implemented") *)
     OutQuery (y, !db)
    )

fun t () = (
  Prolog (parse "init.");
  Prolog (parse "p(a, b).");
  Prolog (parse "p(X, Y)?")
)

(* 
  Creating a substitution: val R = comp (empty, fn (x, l) => if x = "X" then Fun ("a", []) else Var (x, l))
  Creating a composed substitution: val Q = comp (R, fn (x, l) => if x = "Y" then Fun ("b", []) else Var (x, l))
  Applying a substitution to a pair string * int: R ("X", 1)
  Applying a substitution to a Term defined by a pair string * int: value R (Var ("X", 1))
  Applying every substitution defined so far: value Q (Fun ("p", [Var ("X", 1), Var ("Y", 1)]))
  Defining a complex term: val t = Fun ("a", [Var ("X", 1)]);
  Applying top to a substitution of a term will
    only apply the top-level substitution, even if the substituion is composed of others: top R t
  Applying all the substitutions defined on a substitution function: value R t;
 *)

(* ================================================================================= *)
(* ================================================================================= *)
(* ================================================================================= *)
