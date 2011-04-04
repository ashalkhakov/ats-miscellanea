staload "SATS/regexp.sats"

absviewtype DFA

fun dfa_make (r: RE): DFA
fun dfa_free (x: DFA):<> void

fun print_dfa (x: !DFA): void
overload print with print_dfa
