(* fragments.sml
 *
 * COPYRIGHT (c) 2018 The Fellowship of SML/NJ (https://smlnj.org)
 * All rights reserved.
 *
 * !!! THIS FILE WAS GENERATED; DO NOT EDIT !!!
 *)

structure Fragments =
  struct

    val pickleUtil = "\
          \(*---------- begin pickle-util.in ----------*)\n\
          \    type instream = @PICKLER@.instream\n\
          \    type outstream = @PICKLER@.outstream\n\
          \  (* write an option *)\n\
          \    fun writeOption wrFn (outS, NONE) = @PICKLER@.writeTag8(outS, 0w0)\n\
          \      | writeOption wrFn (outS, SOME obj) = (\n\
          \          @PICKLER@.writeTag8(outS, 0w1);\n\
          \          wrFn(outS, obj))\n\
          \  (* read an option *)\n\
          \    fun readOption rdFn inS = (case @PICKLER@.readTag8 inS\n\
          \           of 0w0 => NONE\n\
          \            | 0w1 => let val obj = rdFn in SOME obj end\n\
          \            | _ => raise ASDL.DecodeError\n\
          \          (* end case *))\n\
          \  (* write a list of values as a sequence *)\n\
          \    fun writeSeq wrFn (outS, xs) = let\n\
          \          fun write [] = ()\n\
          \            | write (x::xr) = (wrFn(outS, x); write xr)\n\
          \          in\n\
          \            @PICKLER@.writeUInt(outS, Word.fromInt(length xs));\n\
          \            write xs\n\
          \          end\n\
          \  (* read a sequence into a sequence of values *)\n\
          \    fun readSeq rdFn inS = let\n\
          \          val len = @PICKLER@.readUInt inS\n\
          \          fun read (0w0, xs) = reverse (xs, [])\n\
          \            | read (n, xs) = let\n\
          \                val x = rdFn inS\n\
          \                in\n\
          \                  read (n-0w1, x::xs)\n\
          \                end\n\
          \          and reverse ([], xs) = xs\n\
          \            | reverse (x::xr, xs) = reverse (xr, x::xs)\n\
          \          in\n\
          \            read (len, [])\n\
          \          end\n\
          \(*---------- end pickle-util.in ----------*)\n\
          \"

    val sexpUtil = "\
          \(*---------- begin sexp-util.in ----------*)\n\
          \    structure SExpPkl = @PICKLER@\n\
          \    type instream = SExpPkl.instream\n\
          \    type outstream = SExpPkl.outstream\n\
          \    val writeSExp = SExpPkl.writeSExp\n\
          \    val writeOption = SExpPkl.writeOption\n\
          \    val readOption = SExpPkl.readOption\n\
          \    val writeSeq = SExpPkl.writeSeq\n\
          \    val readSeq = SExpPkl.readSeq\n\
          \    val writeEnum = SExpPkl.writeEnum\n\
          \    val space = SExpPkl.space\n\
          \(*---------- end sexp-util.in ----------*)\n\
          \"

    val streams = "\
          \(*---------- begin streams.in ----------*)\n\
          \    type instream = @PICKLER@.instream\n\
          \    type outstream = @PICKLER@.outstream\n\
          \(*---------- end streams.in ----------*)\n\
          \"

  end
