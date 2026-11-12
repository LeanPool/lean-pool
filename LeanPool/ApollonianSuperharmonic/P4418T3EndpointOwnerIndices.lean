/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow

-- [TABLET NODE: P4418T3EndpointOwnerIndices]

/-!
# P4418T3EndpointOwnerIndices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a selected contact row in an ordered-general layout, the ordered pair
of third-owner indices is the following table. The order is a naming
convention only, not an orientation of a previously supplied path.
$$
\begin{array}{c|cc}
\text{row}&g_0&g_1\\\hline
L_1^+&C_{0,0}&D_{-1,-1}\\
L_2^+&E_{0,0}&F_{0,-1}\\
L_3^+&E_{0,0}&F_{1,0}\\
L_1^-&C_{1,1}&D_{0,0}\\
L_2^-&E_{0,1}&F_{0,0}\\
L_3^-&E_{-1,0}&F_{0,0}\\
S_1^+&B_{0,0}&E_{-1,0}\\
S_2^+&B_{0,0}&C_{1,0}\\
S_3^+&A_{0,-1}&D_{0,0}\\
S_4^+&B_{1,1}&E_{0,1}\\
S_5^+&B_{0,1}&C_{1,1}\\
S_6^+&A_{-1,-1}&D_{-1,0}\\
S_1^-&A_{0,0}&F_{1,0}\\
S_2^-&A_{0,0}&D_{-1,0}\\
S_3^-&B_{0,1}&C_{0,0}\\
S_4^-&A_{-1,-1}&F_{0,-1}\\
S_5^-&A_{0,-1}&D_{-1,-1}\\
S_6^-&B_{1,1}&C_{1,0}\\
\end{array}
$$
Here $X_{m,n}$ is the original periodic occurrence with label $X$ and
translation $mu+nv$, not its precursor-deleted replacement.
-/
def P4418T3EndpointOwnerIndices
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) : PeriodicSubtileIndex ×
        PeriodicSubtileIndex :=
-- BODY
  match row with
  | .positiveL1 _ _ => (⟨.C, 0, 0⟩, ⟨.D, -1, -1⟩)
  | .positiveL2 _ _ => (⟨.E, 0, 0⟩, ⟨.F, 0, -1⟩)
  | .positiveL3 _ _ => (⟨.E, 0, 0⟩, ⟨.F, 1, 0⟩)
  | .reflectedL1 _ _ => (⟨.C, 1, 1⟩, ⟨.D, 0, 0⟩)
  | .reflectedL2 _ _ => (⟨.E, 0, 1⟩, ⟨.F, 0, 0⟩)
  | .reflectedL3 _ _ => (⟨.E, -1, 0⟩, ⟨.F, 0, 0⟩)
  | .positiveS1 _ => (⟨.B, 0, 0⟩, ⟨.E, -1, 0⟩)
  | .positiveS2 _ => (⟨.B, 0, 0⟩, ⟨.C, 1, 0⟩)
  | .positiveS3 _ => (⟨.A, 0, -1⟩, ⟨.D, 0, 0⟩)
  | .positiveS4 _ => (⟨.B, 1, 1⟩, ⟨.E, 0, 1⟩)
  | .positiveS5 _ => (⟨.B, 0, 1⟩, ⟨.C, 1, 1⟩)
  | .positiveS6 _ => (⟨.A, -1, -1⟩, ⟨.D, -1, 0⟩)
  | .reflectedS1 _ => (⟨.A, 0, 0⟩, ⟨.F, 1, 0⟩)
  | .reflectedS2 _ => (⟨.A, 0, 0⟩, ⟨.D, -1, 0⟩)
  | .reflectedS3 _ => (⟨.B, 0, 1⟩, ⟨.C, 0, 0⟩)
  | .reflectedS4 _ => (⟨.A, -1, -1⟩, ⟨.F, 0, -1⟩)
  | .reflectedS5 _ => (⟨.A, 0, -1⟩, ⟨.D, -1, -1⟩)
  | .reflectedS6 _ => (⟨.B, 1, 1⟩, ⟨.C, 1, 0⟩)

end ApollonianSuperharmonic

end
