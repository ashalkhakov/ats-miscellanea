(* parsing *)
staload "frontend/absyn.sats"
staload "shared/disj.sats"

fun parse_from_strbuf {m,n:nat}
  (p_strbuf: &strbuf (m, n)): Error_vt EXP0

