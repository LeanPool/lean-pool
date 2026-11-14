/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowParameters

-- [TABLET NODE: P3996T1SRowTable]

/-!
# P3996T1SRowTable

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a configuration $q,\mathrm{cfg}$ and layout certificate with periods
$u,v$, the numerical row table is undefined in the six $L$ constructors.
In each $S$ constructor it has the following
`P3996T1SRowParameters` entry.  Put
$r=\mathrm{cfg.firstPredecessor}$, $t=\mathrm{cfg.secondPredecessor}$,
$\alpha=v^r_{02}$, $\beta=v^r_{30}$, $\gamma=v^t_{01}$ and $I=\sqrt{-1}$.
Slots in this table are zero-based.  The columns are the child slot and
sign, the source sign, the child and parent indices, the exterior flag,
the predecessor, parent slot and rotation, and the three shifts $b,d,a$.
$$
\begin{array}{c|cc|c|cc|c|ccc|ccc}
 &l&\epsilon&f&X&Y&\mathrm{ext}&p&m&s&b&d&a\\ \hline
S_1^+&0&+&-&A_{-1,-1}&C_{0,0}&1&r&1&0&-u-v&\alpha&-u\\
S_2^+&0&+&+&A_{0,-1}&E_{0,0}&1&r&2&3&-v&I^3\beta&u\\
S_3^+&1&+&-&C_{1,0}&E_{0,0}&1&t&0&0&u&\gamma&-v\\
S_4^+&0&+&-&A_{0,0}&C_{1,1}&0&r&1&0&0&\alpha&v\\
S_5^+&0&+&+&A_{0,0}&E_{0,1}&0&r&2&3&0&I^3\beta&u+v\\
S_6^+&1&+&-&C_{0,0}&E_{-1,0}&0&t&0&0&0&\gamma&-u-v\\
S_1^-&0&-&+&B_{1,1}&D_{0,0}&1&r&1&2&u+v&I^2\alpha&u\\
S_2^-&0&-&-&B_{0,1}&F_{0,0}&1&r&2&1&v&I\beta&-u\\
S_3^-&1&-&+&D_{-1,0}&F_{0,0}&1&t&0&2&-u&I^2\gamma&v\\
S_4^-&0&-&+&B_{0,0}&D_{-1,-1}&0&r&1&2&0&I^2\alpha&-v\\
S_5^-&0&-&-&B_{0,0}&F_{0,-1}&0&r&2&1&0&I\beta&-u-v\\
S_6^-&1&-&+&D_{0,0}&F_{1,0}&0&t&0&2&0&I^2\gamma&u+v
\end{array}
$$
-/
noncomputable def P3996T1SRowTable
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    {a b : PeriodicSubtileIndex}
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) :
    Option P3996T1SRowParameters :=
-- BODY
  match row with
  | .positiveL1 _ _ => none
  | .positiveL2 _ _ => none
  | .positiveL3 _ _ => none
  | .reflectedL1 _ _ => none
  | .reflectedL2 _ _ => none
  | .reflectedL3 _ _ => none
  | .positiveS1 _ => some {
      childSlot := 0, childSign := true, sourceSign := false
      childIndex := ⟨.A, -1, -1⟩, parentIndex := ⟨.C, 0, 0⟩
      childIsExterior := true, predecessor := cfg.firstPredecessor
      parentSlot := 1, rotation := 0
      childShift := -cert.u - cert.v
      rightShift := BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)
      oldShift := -cert.u }
  | .positiveS2 _ => some {
      childSlot := 0, childSign := true, sourceSign := true
      childIndex := ⟨.A, 0, -1⟩, parentIndex := ⟨.E, 0, 0⟩
      childIsExterior := true, predecessor := cfg.firstPredecessor
      parentSlot := 2, rotation := 3
      childShift := -cert.v
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * BandVectors.1 (cfg.firstPredecessor 3)
          (cfg.firstPredecessor 0)
      oldShift := cert.u }
  | .positiveS3 _ => some {
      childSlot := 1, childSign := true, sourceSign := false
      childIndex := ⟨.C, 1, 0⟩, parentIndex := ⟨.E, 0, 0⟩
      childIsExterior := true, predecessor := cfg.secondPredecessor
      parentSlot := 0, rotation := 0
      childShift := cert.u
      rightShift := BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)
      oldShift := -cert.v }
  | .positiveS4 _ => some {
      childSlot := 0, childSign := true, sourceSign := false
      childIndex := ⟨.A, 0, 0⟩, parentIndex := ⟨.C, 1, 1⟩
      childIsExterior := false, predecessor := cfg.firstPredecessor
      parentSlot := 1, rotation := 0
      childShift := 0
      rightShift := BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)
      oldShift := cert.v }
  | .positiveS5 _ => some {
      childSlot := 0, childSign := true, sourceSign := true
      childIndex := ⟨.A, 0, 0⟩, parentIndex := ⟨.E, 0, 1⟩
      childIsExterior := false, predecessor := cfg.firstPredecessor
      parentSlot := 2, rotation := 3
      childShift := 0
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * BandVectors.1 (cfg.firstPredecessor 3)
          (cfg.firstPredecessor 0)
      oldShift := cert.u + cert.v }
  | .positiveS6 _ => some {
      childSlot := 1, childSign := true, sourceSign := false
      childIndex := ⟨.C, 0, 0⟩, parentIndex := ⟨.E, -1, 0⟩
      childIsExterior := false, predecessor := cfg.secondPredecessor
      parentSlot := 0, rotation := 0
      childShift := 0
      rightShift := BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)
      oldShift := -cert.u - cert.v }
  | .reflectedS1 _ => some {
      childSlot := 0, childSign := false, sourceSign := true
      childIndex := ⟨.B, 1, 1⟩, parentIndex := ⟨.D, 0, 0⟩
      childIsExterior := true, predecessor := cfg.firstPredecessor
      parentSlot := 1, rotation := 2
      childShift := cert.u + cert.v
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * BandVectors.1 (cfg.firstPredecessor 0)
          (cfg.firstPredecessor 2)
      oldShift := cert.u }
  | .reflectedS2 _ => some {
      childSlot := 0, childSign := false, sourceSign := false
      childIndex := ⟨.B, 0, 1⟩, parentIndex := ⟨.F, 0, 0⟩
      childIsExterior := true, predecessor := cfg.firstPredecessor
      parentSlot := 2, rotation := 1
      childShift := cert.v
      rightShift := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor 3)
          (cfg.firstPredecessor 0)
      oldShift := -cert.u }
  | .reflectedS3 _ => some {
      childSlot := 1, childSign := false, sourceSign := true
      childIndex := ⟨.D, -1, 0⟩, parentIndex := ⟨.F, 0, 0⟩
      childIsExterior := true, predecessor := cfg.secondPredecessor
      parentSlot := 0, rotation := 2
      childShift := -cert.u
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * BandVectors.1 (cfg.secondPredecessor 0)
          (cfg.secondPredecessor 1)
      oldShift := cert.v }
  | .reflectedS4 _ => some {
      childSlot := 0, childSign := false, sourceSign := true
      childIndex := ⟨.B, 0, 0⟩, parentIndex := ⟨.D, -1, -1⟩
      childIsExterior := false, predecessor := cfg.firstPredecessor
      parentSlot := 1, rotation := 2
      childShift := 0
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * BandVectors.1 (cfg.firstPredecessor 0)
          (cfg.firstPredecessor 2)
      oldShift := -cert.v }
  | .reflectedS5 _ => some {
      childSlot := 0, childSign := false, sourceSign := false
      childIndex := ⟨.B, 0, 0⟩, parentIndex := ⟨.F, 0, -1⟩
      childIsExterior := false, predecessor := cfg.firstPredecessor
      parentSlot := 2, rotation := 1
      childShift := 0
      rightShift := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor 3)
          (cfg.firstPredecessor 0)
      oldShift := -cert.u - cert.v }
  | .reflectedS6 _ => some {
      childSlot := 1, childSign := false, sourceSign := true
      childIndex := ⟨.D, 0, 0⟩, parentIndex := ⟨.F, 1, 0⟩
      childIsExterior := false, predecessor := cfg.secondPredecessor
      parentSlot := 0, rotation := 2
      childShift := 0
      rightShift := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * BandVectors.1 (cfg.secondPredecessor 0)
          (cfg.secondPredecessor 1)
      oldShift := cert.u + cert.v }

end ApollonianSuperharmonic

end
