datatype 'a Tree =
    Empty
    | Node of 'a * 'a Tree * 'a Tree;

fun insert(x, Empty) = Node(x, Empty, Empty)
    | insert(x, Node(v, l, r)) =
        if x < v then Node(v, insert(x, l), r)
        else if x > v then Node(v, l, insert(x, r))
        else Node(v, l, r);

fun print_tree(Empty) = ""
    | print_tree(Node(v, l, r)) =
        print_tree(l) ^ " " ^ Int.toString(v) ^ " " ^ print_tree(r);

(* datatype Command =
    Empty
    | Insert
    | Print;

fun processCommand (command, Empty) =
        if command = "insert\n" then (print "insert\n"; ())
        else if command = "print\n" then (print "print\n"; ())
        else (print "invalid command\n"; ())
    | processCommand(command, Insert) =
        (print "insert"; ())
    | processCommand(command, Print) =
        (print "print"; ()) *)

fun readInput() =
    (print ">>> ";
     TextIO.inputLine TextIO.stdIn)

(* fun main() =
    let
        fun loop() =
                let
                    val userInput = readInput()
                in
                    case userInput of
                        SOME input =>
                            if input = "exit\n" then ()
                            else (print ("Reading " ^ input ^ "\n"); processCommand input ; loop())
                        | NONE => loop()
                end
    in
        loop()
    end *)

(* val _ = main() *)

val value = ref 0

fun counter(command) =
    let
        fun increment() =
            (value := !value + 1;
            ())
        
        fun decrement() =
            (value := !value - 1;
            ())

        fun processCommand(command) =
            if command = "increment\n" then increment()
            else if command = "decrement\n" then decrement()
            else ()
        
        val _ = processCommand(command)
    in
        (print(Int.toString(!value) ^ "\n"); ())
    end

fun main() =
    let
        fun loop() =
                let
                    val userInput = readInput()
                in
                    case userInput of
                        SOME input =>
                            if input = "exit\n" then ()
                            else (print ("Reading " ^ input); counter(input) ; loop())
                        | NONE => loop()
                end
    in
        loop()
    end

val _ = main()


