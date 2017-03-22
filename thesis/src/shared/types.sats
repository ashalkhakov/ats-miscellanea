#include "shared/types.hats"

// base types
datasort tyb = integer | boolean
datasort ty = tybool | int | ->> of (ty, ty)
datasort env = nil | :: of (ty, env)

// see the rules for |-0
dataprop VAR (G:env, ty, int) =
  | {t:ty} VARone (t :: G, t, 0)
  | {t1,t2:ty} {n:nat} VARshi (t2 :: G, t1, n+1) of VAR (G, t1, n)
