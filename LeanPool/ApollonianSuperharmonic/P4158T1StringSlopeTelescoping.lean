/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ZippedChainInvariant

public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector

-- [TABLET NODE: P4158T1StringSlopeTelescoping]

/-!
# P4158T1StringSlopeTelescoping

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4158T1StringSlopeTelescoping
    (C : BandCircle) (hlarge : 1 < C.1.1.1)
    (orientation : Bool) (base R S : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : OdometerStringRespect C orientation base R S tiles hs)
    (hr : OdometerStringRespect C orientation base S R reverseTiles reverseHs)
    (hendpoint : PartialOdometer)
    (hh : hs.head? = some hendpoint) (hh' : reverseHs.getLast? = some hendpoint)
    (U V : ProtoTile) (g k : PartialOdometer)
    (hU : (U, g) ∈ tiles.zip hs) (hV : (V, k) ∈ reverseTiles.zip reverseHs) :
    ∃ s t : Real × Real,
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      t.1 - s.1 = CircleMatrix C 0 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 0 1 * ((TileCentroid V).2 - (TileCentroid U).2) ∧
      t.2 - s.2 = CircleMatrix C 1 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 1 1 * ((TileCentroid V).2 - (TileCentroid U).2) := by
-- BODY
  have slopeDefined : ∀ (c : CircleCoordinates) (T : ProtoTile) (f : PartialOdometer),
      TileOdometer c T f → 1 < c.1 → ∃ p : Real × Real, PartialOdometerSlope f = some p := by
    intro c T f ho hc
    induction ho with
    | line w z hw hdom => omega
    | unit z w T f hT hdom htrans => omega
    | @decompose qd hqd S T hs f hT hsub hcells hfoot hcentroid hdom
        hvalue hcompat hslope ih =>
      have facts := ProperBandCurvatureStructure qd hqd
      have hp : ∃ i : Fin 3, 0 < (qd i.succ).1 := by
        by_cases h0 : 0 < (qd (0 : Fin 3).succ).1
        · exact ⟨0, h0⟩
        by_cases h1 : 0 < (qd (1 : Fin 3).succ).1
        · exact ⟨1, h1⟩
        have n0 := facts.2.1 (0 : Fin 3)
        have n1 := facts.2.1 (1 : Fin 3)
        have z0 : (qd (0 : Fin 3).succ).1 = 0 := by omega
        have z1 : (qd (1 : Fin 3).succ).1 = 0 := by omega
        exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
      obtain ⟨i, hi⟩ := hp
      obtain hz | ⟨p, pi, hp, hpi, hpr, hpi'⟩ := hslope i false
      · omega
      · exact ⟨p, hp⟩
  obtain ⟨s, hsg⟩ := slopeDefined C.1.1 U g (List.forall₂_zip hf.2.1 hU) hlarge
  obtain ⟨t, htk⟩ := slopeDefined C.1.1 V k (List.forall₂_zip hr.2.1 hV) hlarge
  let slopeVec := fun f : PartialOdometer =>
    let p := (PartialOdometerSlope f).getD (0, 0)
    ![p.1, p.2]
  let centroidVec := fun T : ProtoTile => ![(TileCentroid T).1, (TileCentroid T).2]
  let invariant := fun X : ProtoTile × PartialOdometer =>
    slopeVec X.2 - Matrix.mulVec (CircleMatrix C) (centroidVec X.1)
  let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
  have invStep : ∀ A B : ProtoTile × PartialOdometer,
      LeftLatticeAdjacent C A.1 B.1 A.2 B.2 → invRel A B := by
    intro A B hadj
    obtain ⟨_, _, p, p', hp, hp', hcase⟩ := hadj
    obtain hunit | ⟨q, j, e, hq, hq0, hcent, hpRe, hpIm⟩ := hcase
    · omega
    have hin := CircleMatrixIncomingVector C q hq.1 hq0 j
    let sign : Real := if e = true then 1 else -1
    have hc0 : (TileCentroid B.1).1 - (TileCentroid A.1).1 =
        sign * ((BandVectors.1 (q j.succ) (q 0)).re : Real) := by
      have hh := congrArg Prod.fst hcent
      change _ = (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).re : Real) at hh
      exact hh
    have hc1 : (TileCentroid B.1).2 - (TileCentroid A.1).2 =
        sign * ((BandVectors.1 (q j.succ) (q 0)).im : Real) := by
      have hh := congrArg Prod.snd hcent
      change _ = (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).im : Real) at hh
      exact hh
    have hcentVec : centroidVec B.1 - centroidVec A.1 =
        sign • ![((BandVectors.1 (q j.succ) (q 0)).re : Real),
          ((BandVectors.1 (q j.succ) (q 0)).im : Real)] := by
      ext n
      fin_cases n
      · simpa [centroidVec, sign, smul_eq_mul] using hc0
      · simpa [centroidVec, sign, smul_eq_mul] using hc1
    have hslopeVec : slopeVec B.2 - slopeVec A.2 =
        sign • ![((BandVectors.2 (q j.succ) (q 0)).re : Real),
          ((BandVectors.2 (q j.succ) (q 0)).im : Real)] := by
      ext n
      fin_cases n <;> simp [slopeVec, hp, hp', hpRe, hpIm, sign]
    have hmain : Matrix.mulVec (CircleMatrix C) (centroidVec B.1 - centroidVec A.1) =
        slopeVec B.2 - slopeVec A.2 := by
      rw [hcentVec, Matrix.mulVec_smul, hin, hslopeVec]
    change invariant A = invariant B
    dsimp [invariant]
    ext n
    fin_cases n
    · have heq := congrFun hmain 0
      simp [slopeVec, centroidVec, hp, hp', Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] at heq ⊢
      linear_combination heq
    · have heq := congrFun hmain 1
      simp [slopeVec, centroidVec, hp, hp', Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] at heq ⊢
      linear_combination heq
  have hInvUV := zippedChainInvariant invariant tiles reverseTiles hs reverseHs R hendpoint
    hf.1.2.1 hh hr.1.2.2.1 hh' (List.Forall₂.length_eq hr.2.1)
    (hf.2.2.imp invStep) (hr.2.2.imp invStep) U V g k hU hV
  refine ⟨s, t, hsg, htk, ?_, ?_⟩
  · have heq := congrFun hInvUV 0
    change slopeVec g 0 - (CircleMatrix C).mulVec (centroidVec U) 0 =
      slopeVec k 0 - (CircleMatrix C).mulVec (centroidVec V) 0 at heq
    simp [slopeVec, centroidVec, hsg, htk, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at heq
    linear_combination -heq
  · have heq := congrFun hInvUV 1
    change slopeVec g 1 - (CircleMatrix C).mulVec (centroidVec U) 1 =
      slopeVec k 1 - (CircleMatrix C).mulVec (centroidVec V) 1 at heq
    simp [slopeVec, centroidVec, hsg, htk, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at heq
    linear_combination -heq

end ApollonianSuperharmonic

end
