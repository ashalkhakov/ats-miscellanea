(* driver program *)

staload "libc/sys/SATS/types.sats"
staload STDIO = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "shared/disj.sats"
staload "shared/types.sats"
staload "shared/tas.sats"
staload "frontend/absyn.sats"
staload "frontend/parse.sats"
staload "frontend/trans.sats"
staload "backend/eval.sats"

(* ****** ****** *)

dynload "frontend/parse.dats"

(* ****** ****** *)

#define VERSION "0.0.1"

typedef state_t (G:env) = @(env_t G, ctx_t G)
typedef state_t = [G:env] state_t G

(* ****** ****** *)

// stlc [--help | --version | <filename>]
fun usage (cmd: string): void = () where {
  val () = printf ("%s [--help | --version | <filename>]\n", @(cmd));
  val () = print "if no command is given, starts in interactive mode\n"
}

// two modes of operation:
// - batch compile an input file (that is, typecheck and eval)
// - interactive (parse-typecheck-eval loop)

// in one case, we want to read the entire file (EOF is normal EOF)
// in another case, we want to read input file line by line

// parse, typecheck, interpret file stream
// the plan is to use this function in both repl and batch compilation
// FIXME: it doesn't propagate contexts properly
// i suppose we need a function to merge two contexts ...
fun interp_env {G:env} {m,n:nat}
  (sbf: &strbuf (m, n), st: state_t G)
  : Error_vt @([t:ty] val_t t, state_t) = let
  val exp0 = parse_from_strbuf sbf
in
  case+ exp0 of
  | InsLeft_vt _ => (fold@ exp0; exp0)
  | ~InsRight_vt exp0 => let
    val () = print "parsed AST: "
    val () = print exp0
    val () = print_newline ()
    val () = print "typechecking...\n"
    val exp1 = tycheck (exp0, st.1)
  in
    case+ exp1 of
    | InsLeft_vt _ => (fold@ exp1; exp1)
    | ~InsRight_vt @(t, exp1) => let
//      val () = print "type: "
//      val () = print_ty t
      val () = print "\nexp1: "
      val () = print (show_exp exp1)
      val () = print_newline ()
    in
      InsRight_vt @(eval (st.0, exp1), st)
    end
  end
end

// report interpretation error
fun interp_error (cmd: string, err: string): void =
  prerrf ("%s: ERROR %s\n", @(cmd, err));

(* ****** ****** *)
(* file operations missing from the prelude *)

// file size using posix
// throws exceptions
fun filesize1_exn {m:file_mode} (f: &FILE m): lint = let
  val curpos = $STDIO.ftell1_exn f
  val _ = $STDIO.fseek1_exn (f, lint_of_int 0, SEEK_END)
  val size = $STDIO.ftell1_exn f
  val _ = $STDIO.fseek1_exn (f, curpos, SEEK_SET)
in size end

// read a (text) file into a string buffer
// partial, throws exceptions on out of memory or file IO failure
// two errors of logical kind where fixed because of the typechecker:
// - buffer size is file size + 1 (for 0 terminator at the end of file,
//   moreover, buffer must not be 0 for malloc)
// - check file size
// but the first run revealed a strange error: the routine was trying
// to read more bytes than there are in file! (I discovered this with
// a glimpse at libc/CATS/stdio.cats) oops, somebody called
// fread with buffer size instead of file size :)
fun file_read_strbuf_exn {m:file_mode}
  (pf: file_mode_lte (m, r) | iop: &FILE m)
  : [l:agz] [n,m:nat] (free_ngc_v (n, l), strbuf_v (n, m, l) | ptr l) = let
  val filesz = let
    val x = (int1_of_int (int_of_lint (filesize1_exn iop)))
    val () = assert_errmsg_bool1 (x >= 0, "file size less than zero")
  in size1_of_int1 x end
  val bufsz = filesz + 1
  val (pf_mem, pf_buf | p_mem) = malloc_ngc bufsz
  // fread expects initialized buffer, why?
  prval pf_buf = bytes_v_of_b0ytes_v pf_buf
  val _ = $STDIO.fread_byte_exn (pf | !p_mem, filesz, iop)
  val () = bytes_strbuf_trans (pf_buf | p_mem, filesz)
in
  (pf_mem, pf_buf | p_mem)
end

(* ****** ****** *)

// parse, typecheck and interpret file
fun filename_interp (cmd: string, name: string): void = let
  val (pfopt | p_ifp) = $STDIO.fopen_err (name, file_mode_r)
in
  if p_ifp <> null then let
    prval Some_v (pf) = pfopt
    val (pf_ngc, pf_strbuf | p_strbuf) =
      file_read_strbuf_exn (file_mode_lte_r_r | !p_ifp)
    val res = interp_env (!p_strbuf, @(env_empty (), ctx_empty ()))
    val () = free_ngc (pf_ngc, bytes_v_of_strbuf_v pf_strbuf | p_strbuf)
    val () = $STDIO.fclose1_exn (pf | p_ifp)
  in
    case+ res of
    | ~InsLeft_vt err => begin
      interp_error (cmd, err); exit {void} (1)
    end
    | ~InsRight_vt @(v, _) => begin
      printf ("%s: SUCCESS: ", @(cmd));
      print v; print_newline ()
    end
  end else let
    prval None_v () = pfopt
    val () = prerrf ("%s: can't open [%s]\n", @(cmd, name))
  in
    exit (1)
  end
end

(* ****** ****** *)

// parse-typecheck-evaluate-print loop
fun reploop (cmd: string): void = let
  #define BUFSZ 1024
  #define BUFSZ1 (BUFSZ+1)
  var !p_buf with pf_buf = @[byte][BUFSZ1]()
  stadef l_buf = p_buf
  // the loop itself
  fun loop {G:env} {t:ty} (
      pf_buf: !b0ytes BUFSZ1 @ l_buf
    | cmd: string, p_buf: ptr l_buf, iop: &FILE r, st: state_t G)
    : state_t = let
    val () = print "> " // poor man's command prompt
    val (pf1 | p1) =
      $STDIO.fgets_err (file_mode_lte_r_r, pf_buf | p_buf, BUFSZ, iop)
  in
    if :(pf_buf: b0ytes BUFSZ1 @ l_buf) =>
      p1 <> null then let
      prval $STDIO.fgets_v_succ (pf1) = pf1
      val res = interp_env (!p_buf, st)
      prval () = pf_buf := bytes_v_of_strbuf_v pf1
    in
      case+ res of
      | ~InsLeft_vt err => (interp_error (cmd, err); st)
      | ~InsRight_vt @(v, st) => loop (pf_buf | cmd, p_buf, iop, st)
    end else let
      prval $STDIO.fgets_v_fail (pf1) = pf1; prval () = pf_buf := pf1
    in
      st // no more bytes
    end
  end
  val (pf_stdin | p_stdin) = stdin_get ()
  val () = print "The Glorious Simply-Typed Lambda Calculus Interpretation System\n"
  val () = printf ("Version %s\n", @(VERSION))
  val () = print "Copyright (C) 2010 Artyom Shalkhakov\n"
  val _ = loop (pf_buf | cmd, p_buf, !p_stdin, @(env_empty (), ctx_empty ()))
  val () = stdin_view_set (pf_stdin | (*none*))
in
  // empty
end

(* ****** ****** *)

implement main {n} (argc, argv) = let
  val () = assert_errmsg (argc >= 1, "argc < 1!")
  val cmd = argv.[0]
in
  if argc >= 2 then
    case+ argv.[1] of
    | "--help" => begin
      usage cmd; exit (1)
    end
    | "--version" => begin
      printf ("STLC %s\n", @(VERSION)); exit (1)
    end
    | _ => filename_interp (cmd, argv.[1])
  else reploop cmd
end