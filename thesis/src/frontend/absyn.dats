staload "parcomb/posloc.sats"

staload "frontend/absyn.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

implement print_ty0 (t) = case+ t.ty0_node of
  | TY0int () => print "int"
  | TY0fun (t1, t2) => begin
      print "fun("; print_ty0 t1; print ", "; print_ty0 t2; print ")"
    end

implement show_ty0 (t) = case+ t.ty0_node of
  | TY0int () => "int"
  | TY0fun (t1, t2) => "fun(" + (show_ty0 t1 + (", " + (show_ty0 t2 + ")")))

implement ty0_int (loc) =
  '{ ty0_loc= loc, ty0_node= TY0int }

implement ty0_fun (loc, f, x) =
  '{ ty0_loc = loc, ty0_node= TY0fun (f, x) }

(* ****** ****** *)

implement print_exp0 (e) = case+ e.exp0_node of
  | EXP0var name => (print "var("; print name; print ")")
  | EXP0lam (name, t, b) => begin
      print "lam("; print name; print ": "; print_ty0 t;
      print " . "; print_exp0 b; print ")"
    end
  | EXP0app (e1, e2) => begin
      print "app("; print_exp0 e1; print ", "; print_exp0 e2; print ")"
    end

implement show_exp0 (e) = case+ e.exp0_node of
  | EXP0var name => "var(" + (name + ")")
  | EXP0lam (name, t, b) => "lam(" + (name + ": " + (show_ty0 t + (" . " + (show_exp0 b + ")"))))
  | EXP0app (e1, e2) => "app(" + (show_exp0 e1 + (", " + (show_exp0 e2 + ")")))

implement exp0_var (loc, name) =
  '{ exp0_loc= loc, exp0_node= EXP0var name }

implement exp0_lam (loc, x, t, b) =
  '{ exp0_loc= loc, exp0_node= EXP0lam (x, t, b) }

implement exp0_app (loc, f, x) =
  '{ exp0_loc= loc, exp0_node= EXP0app (f, x) }
