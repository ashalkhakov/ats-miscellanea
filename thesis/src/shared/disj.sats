(* a disjunction data type *)
(* it really has to go to the prelude *)

dataviewtype disj_viewt0ype_viewt0ype_int_viewtype
  (l:viewt@ype, r:viewt@ype, int) =
  | InsLeft_vt (l, r, 0) of l
  | InsRight_vt (l, r, 1) of r

stadef disj_vt = disj_viewt0ype_viewt0ype_int_viewtype
viewtypedef Disj_vt (l:viewt@ype, r:viewt@ype) = [b:int] disj_vt (l, r, b)

// this is ought to be elsewhere
viewtypedef Error_vt (r:viewt@ype) = Disj_vt (string, r)
