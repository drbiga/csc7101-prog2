fun fac(n) =
    if n = 0 then 1
    else n * fac(n-1);

datatype Color = 
    RED
    | GREEN
    | BLUE;

fun colorToInt RED = 0
    | colorToInt GREEN = 1
    | colorToInt BLUE = 2;


datatype Tree =
    Leaf of int
    | Node of Tree * Tree;

fun max(i, j) = if i > j then i else j;
(* fun 'a max(i: 'a, j: 'a) = if i > j then i else j; *)

fun height (Leaf _) = 0
    | height (Node (l, r)) = 
        1 + max(height l, height r );

(* height (Node(Leaf 1, Node(Leaf 2, Leaf 3))); *)

(* max(1, 2); *)
(* max(2.3, 3.2); *)

fun id x = x;

datatype 'a Tree = 
    Leaf of 'a
    | Node of 'a Tree * 'a Tree;

fun height (Leaf _) = 0
    | height (Node (l, r)) = 
        1 + max(height l, height r );


datatype 'a Tree = 
    Empty
    | Node of 'a * 'a Tree * 'a Tree;


fun insert(x, Empty) = Node(x, Empty, Empty)
    | insert(x, Node(v, l, r)) =
        if x < v then Node(v, insert(x, l), r)
        else if x > v then Node(v, l, insert(x, r))
        else Node(v, l, r) (* Value already exists *)

fun search(x, Empty) = false
    | search(x, Node(v, l, r)) =
        if x < v then search(x, l)
        else if x > v then search(x, r)
        else true;


val tree = insert(5, insert(3, insert(2, insert(10, insert(9, Empty)))));
search(5, tree);


fun add5(x) =
    let
        fun add(x, y) = x + y;
    in
        add(x, 5)
    end;

(* add5(5); *)


(* fun TopLevel() = (
    print "PROLOG> ";
    case TextIO.inputLine TextIO.stdIn of
        NONE => ()
        | SOME "\n" => TopLevel()
        | SOME inp =>
            let
                val code = "predicate(term)."
            in
                if code = (Headed (Fun ("end_of_file", []), []))
                then ()
                else (
                    print code;
                    (* Prolog code; *)
                    TopLevel()
                )
            end
); *)

(* TopLevel(); *)

datatype MyType =
    IntVar of int
    | IdIntVar of string * int;

fun
    print_mytype (x as IntVar y) = print (Int.toString(y)) |
    print_mytype (IdIntVar (id, y)) = print (id ^ Int.toString(y)) 

fun print_list (l: MyType list) =
    let
        fun
            print_list' (nil, _) = ()
            | print_list' (h :: t, merge) = (print_mytype h; print merge; print_list t)
    in
        print_list' (l, ", ")
    end

fun main () = print_list ([IntVar 0, IntVar 1])
