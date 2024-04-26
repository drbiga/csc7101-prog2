(*
    ALGORITHM for the solver
    for g in goals
        for r in rules
            h = rename head of r
            S = unify g and h
            if unify fails go to next rule
            t = rename tail of r
            t' = apply S to t
            apply S to remaining goals
            recursively call solver for t' and remaining goals and full db
            if recursive call fails, backtrack
*)