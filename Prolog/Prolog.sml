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


(* Update function *)
(* Assign a new variable binding to an existing substitution *)

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

fun print_var  (x, l) = "Var(" ^ x ^ ", " ^ Int.toString(l) ^ ")"

fun
  occurs v (Var w) = (
    (* OutLine ("Checking occurs " ^ print_var v ^ " in " ^ print_var w); *)
    (v = w)
  )
  | occurs v (Fun (w, args)) = (
    (* OutLine ("Calling occurs recursively"); *)
    foldr (fn (x, acc) => x orelse acc) false (map (occurs v) args)
  )

fun unify' ((goal_term, rule_term), S) =
  let
    val goal_term' = top S goal_term;
    val rule_term' = top S rule_term;
  in
    case (goal_term', rule_term') of
      (Var goal_var, Var rule_var) => if goal_var = rule_var then S else upd(goal_var, rule_term') S
      | (Var goal_var, _) => if occurs goal_var rule_term then raise occurs_check_exception else upd(goal_var, rule_term') S
      | (_, Var rule_var) => if occurs rule_var goal_term then raise occurs_check_exception else upd(rule_var, goal_term') S
      | (Fun (f1, fargs1), Fun (f2, fargs2)) =>
          if f1 = f2 then foldr unify' S (pairup (fargs1, fargs2))
          else raise non_unifiable_exception
  end

fun unify (goal_term, rule_term) =
    unify' ((goal_term, rule_term), empty)
    handle
      length_exception => raise non_unifiable_exception  
      | occurs_check_exception => raise non_unifiable_exception


(* ================================================================================= *)
(* ================================================================================= *)
(* ================================================================================= *)

(* Solver *)

exception unsolvable_exception

fun rename l (Var (x, _)) = Var (x, l)
  | rename l (Fun (f, args)) = Fun (f, map (rename l) args)


fun Solve (goals: Term list, db: HornClause list) =
  let
    fun solve (nil, _, _, S) = S
      | solve (_, nil, _, _) = raise unsolvable_exception
      | solve (_, Headless _ :: _, _, _) = empty (* this can never happen *)
      | solve (goal :: goals, Headed (h, args) :: rules, level, S) =
        let
          val _ = (
            (* OutLine ("-----------------------------------------------------------------------------------");
            OutLine ("Goals: " ^ PrintTerm goal ^ foldr (fn (x, acc) => acc ^ ", " ^ x) "" (map PrintTerm goals));
            OutLine ("Rules: " ^ PrintClause (Headed(h, args)) ^ foldr (fn (x, acc) => acc ^ ", " ^ x) "" (map PrintClause rules));
            OutLine ("Unifying " ^ PrintTerm goal ^ " with " ^ PrintTerm h);
            OutLine ("-----------------------------------------------------------------------------------") *)
          )
          val h' = rename (level + 1) h
          val S' = unify' ((goal, h'), S)
            (* handle non_unifiable_exception => (OutLine ("Unification exception"); solve (goal :: goals, rules, level, S)) *)
            handle non_unifiable_exception => solve (goal :: goals, rules, level, S)
          (* val S' = unify (goal, h')
            handle non_unifiable_exception => (OutLine ("Unification exception"); solve (goal :: goals, rules, level, S)) *)
          (* val  *)
          val args_level = map (rename (level + 1)) args
          val goals_level = map (rename (level + 1)) goals
        in
          (
            (* Check if there isn't already some *)
            (* if not occurs (top S' goal) args solve (map (value S') (goals @ args), db, level, S') *)
            (* OutLine("Substitution performed:" ^ PrintTerm goal ^ " " ^ PrintTerm (value S' goal)); *)
            solve (map (value S') (args_level @ goals_level), db, level+1, S')
              handle unsolvable_exception => (OutLine ("Backtracking should be here"); S')
            (* if false
              then solve (goal :: goals, rules, level, S)
              else solve (map (value S') (args_level @ goals), db, level+1, S')
                    handle unsolvable_exception => (OutLine ("Backtracking should be here"); S') *)
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

fun build_string (nil) = ""
 | build_string (string :: string_list) = if length string_list > 0 then string ^ ", " ^ build_string (string_list) else string


fun OutQuery (goals: Term list, db: HornClause list) =
  let
    val S = Solve (goals, db)
    val bindings = map (value S) goals
    val bindings = map (value S) bindings
    val term_pairs = pairup (goals, bindings)

    fun
      print_list_bindings (nil, nil) = ()
      | print_list_bindings (var :: vars, vall :: vals) = (
        print_pair(var, vall);
        print_list_bindings(vars, vals)
      )
    and print_pair (v, b) =
      case (v, b) of
        (Var x, Var y) => if x = y
          then OutLine ("Equal Vars: " ^ (print_var x) ^ "=" ^ (print_var y))
          else OutLine ("Different Vars: " ^ (print_var x) ^ "!=" ^ (print_var y))
        | (Var (x, l), Fun (a, [])) => OutLine(x ^ " = " ^ a)
        | (Fun (p, argsp), Fun (q, argsq)) => print_list_bindings (argsp, argsq)
        | _ => (OutLine ("print pair error: " ^ build_string (map PrintTerm [v, b])); ())
    and print_pairs (nil) = ()
      | print_pairs ((v, b) :: rest) = (print_pair (v, b); print_pairs (rest))
  in
    (
      OutLine ("solution:");
      (* OutLine (build_string (map PrintTerm goals)); *)
      (* OutLine (build_string (map PrintTerm bindings)); *)
      print_pairs (term_pairs)
    )
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
  OutLine ("===================================================================================");
  Prolog (parse "init.");
  Prolog (parse "p(a).");
  Prolog (parse "p(X)?");
  OutLine ("===================================================================================");
  Prolog (parse "init.");
  Prolog (parse "q(a, b).");
  Prolog (parse "q(X, Y)?");
  OutLine ("===================================================================================");
  Prolog (parse "init.");
  Prolog (parse "parent(matheus, walter).");
  Prolog (parse "son(X, Y) :- parent(Y, X).");
  Prolog (parse "son(walter, X)?")
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
