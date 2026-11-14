/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: AllowedSubtileIncidence]

/-!
# AllowedSubtileIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Allowed incidence is the symmetric relation on periodic labeled-subtile
indices generated, for every common translate $(m,n)$, by the following
eighteen edge orbits from the manuscript's fixed $A$--$F$ ledger:
$$
\begin{gathered}
 A B,\ A B_{0,1},\ A B_{1,1},\ A C,\ A C_{1,1},\ A D,\
 A E_{0,1},\ A F,\\
 B C,\ B D_{-1,-1},\ B D,\ B E,\ B F_{0,-1},\\
 C D_{-1,0},\ C E_{-1,0},\ C F,\ D E,\ D F_{1,0}.
\end{gathered}
$$
Here every displayed subscript is added to the common translate $(m,n)$.
This is a purely combinatorial relation defined from the paper's face/edge
ledger; in particular it is not defined by asking whether the interpreted
tiles happen to intersect.
-/
inductive AllowedSubtileIncidence :
    PeriodicSubtileIndex → PeriodicSubtileIndex → Prop where
-- BODY
  | AB (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.B, m, n⟩
  | AB01 (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.B, m, n + 1⟩
  | AB11 (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.B, m + 1, n + 1⟩
  | AC (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.C, m, n⟩
  | AC11 (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.C, m + 1, n + 1⟩
  | AD (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.D, m, n⟩
  | AE01 (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.E, m, n + 1⟩
  | AF (m n : Int) : AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.F, m, n⟩
  | BC (m n : Int) : AllowedSubtileIncidence ⟨.B, m, n⟩ ⟨.C, m, n⟩
  | BDm1m1 (m n : Int) : AllowedSubtileIncidence ⟨.B, m, n⟩ ⟨.D, m - 1, n - 1⟩
  | BD (m n : Int) : AllowedSubtileIncidence ⟨.B, m, n⟩ ⟨.D, m, n⟩
  | BE (m n : Int) : AllowedSubtileIncidence ⟨.B, m, n⟩ ⟨.E, m, n⟩
  | BF0m1 (m n : Int) : AllowedSubtileIncidence ⟨.B, m, n⟩ ⟨.F, m, n - 1⟩
  | CDm10 (m n : Int) : AllowedSubtileIncidence ⟨.C, m, n⟩ ⟨.D, m - 1, n⟩
  | CEm10 (m n : Int) : AllowedSubtileIncidence ⟨.C, m, n⟩ ⟨.E, m - 1, n⟩
  | CF (m n : Int) : AllowedSubtileIncidence ⟨.C, m, n⟩ ⟨.F, m, n⟩
  | DE (m n : Int) : AllowedSubtileIncidence ⟨.D, m, n⟩ ⟨.E, m, n⟩
  | DF10 (m n : Int) : AllowedSubtileIncidence ⟨.D, m, n⟩ ⟨.F, m + 1, n⟩
  | symm {a b} : AllowedSubtileIncidence a b → AllowedSubtileIncidence b a

end ApollonianSuperharmonic

end
