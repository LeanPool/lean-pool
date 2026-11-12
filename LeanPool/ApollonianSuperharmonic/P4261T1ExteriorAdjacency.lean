/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.P4261T1ExteriorIndices
public import LeanPool.ApollonianSuperharmonic.P3045T1RightBoundaryDisplacementAlgebra
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4261T1ExteriorAdjacency]

/-!
# P4261T1ExteriorAdjacency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExteriorAdjacencyGeometry

private theorem displacement :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (a :
            PeriodicSubtileIndex), (a ∈ P4261T1ExteriorIndices) → (
        let slot : Fin 3 × Bool := match a.label with
            | .A => (0, true) | .B => (0, false)
            | .C => (1, true) | .D => (1, false)
            | .E => (2, true) | .F => (2, false)
          let i := slot.1
          let ε : GaussianInt := if slot.2 then 1 else -1
          let I : GaussianInt := ⟨0, 1⟩
          ∃ s : Fin 4,
            ε * ((1 - I) * BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) +
                2 * ((a.first : GaussianInt) * BandVectors.1 (q 0) (q 1) +
                  (a.second : GaussianInt) * BandVectors.1 (q 0) (q 2)) =
              I ^ s.val * (BandVectors.1 (q i.succ) (q 0) +
                BandVectors.1 (q 0) (q i.succ)) ∧
            ε * ((1 + I) * BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))) +
                2 * ((a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
                  (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2)) =
              (-I) ^ s.val * (BandVectors.2 (q i.succ) (q 0) +
                BandVectors.2 (q 0) (q i.succ)))) ) := by
  classical
  intro q hq a ha
  as_aux_lemma =>
    have sums :
        (-BandVectors.1 (q 0) (q 1) - BandVectors.1 (q 0) (q 2) =
          BandVectors.1 (q 0) (q 3)) ∧
        (-BandVectors.2 (q 0) (q 1) - BandVectors.2 (q 0) (q 2) =
          BandVectors.2 (q 0) (q 3)) := by
      as_aux_lemma =>
        obtain ⟨vs, as, v1, a1, flip⟩ := VectorRecursionLaws q hq.1
        have l2 := VectorRecursionLaws _ (SemiProperQuadruple.rotate hq.1)
        have l3 := VectorRecursionLaws _
          (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1))
        have v2 : BandVectors.1 (q 2) (q 0) = BandVectors.1 (q 2) (q 1) -
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 2) := by
          simpa using l2.2.2.1
        have a2 : BandVectors.2 (q 2) (q 0) = BandVectors.2 (q 2) (q 1) +
            (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 3) (q 2) := by
          simpa using l2.2.2.2.1
        have v3 : BandVectors.1 (q 3) (q 0) = BandVectors.1 (q 3) (q 2) -
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3) := by
          simpa using l3.2.2.1
        have a3 : BandVectors.2 (q 3) (q 0) = BandVectors.2 (q 3) (q 2) +
            (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 1) (q 3) := by
          simpa using l3.2.2.2.1
        have f0 := flip hq 0
        have f1 := flip hq 1
        have f2 := flip hq 2
        simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl] at f0
        simp only [show (1 : Fin 3).succ = (2 : Fin 4) from rfl] at f1
        simp only [show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at f2
        constructor
        · apply eq_of_sub_eq_zero
          rw [f0.1, f1.1, f2.1, v1, v2, v3]
          calc
            _ = (-(⟨0, 1⟩ : GaussianInt) + (⟨0, 1⟩ : GaussianInt) ^ 2) *
                (BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
                  BandVectors.1 (q 2) (q 1)) := by ring
            _ = 0 := by rw [vs, mul_zero]
        · apply eq_of_sub_eq_zero
          rw [f0.2, f1.2, f2.2, a1, a2, a3]
          calc
            _ = ((⟨0, 1⟩ : GaussianInt) + (⟨0, 1⟩ : GaussianInt) ^ 2) *
                (BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
                  BandVectors.2 (q 2) (q 1)) := by ring
            _ = 0 := by rw [as, mul_zero]
    have I2 : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by decide +kernel
    have I3 : (⟨0, 1⟩ : GaussianInt) ^ 3 = -(⟨0, 1⟩ : GaussianInt) := by
      rw [pow_succ, I2, neg_one_mul]
    have nI3 : (-(⟨0, 1⟩ : GaussianInt)) ^ 3 = (⟨0, 1⟩ : GaussianInt) := by
      rw [neg_pow, I3]
      norm_num
    have nI2 : (-(⟨0, 1⟩ : GaussianInt)) ^ 2 = -1 := by
      rw [neg_sq, I2]
    obtain ⟨v00, v01, v02, v03, a00, a01, a02, a03, _⟩ :=
      P3045T1RightBoundaryDisplacementAlgebra q hq 0 1 2 (Or.inl ⟨rfl, rfl, rfl⟩)
    obtain ⟨v10, v11, v12, v13, a10, a11, a12, a13, _⟩ :=
      P3045T1RightBoundaryDisplacementAlgebra q hq 1 2 0
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    obtain ⟨v20, v21, v22, v23, a20, a21, a22, a23, _⟩ :=
      P3045T1RightBoundaryDisplacementAlgebra q hq 2 0 1
        (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at v00 v01 v02 v03 a00 a01 a02 a03
    simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at v10 v11 v12 v13 a10 a11 a12 a13
    simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at v20 v21 v22 v23 a20 a21 a22 a23
    simp only [P4261T1ExteriorIndices, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only
    all_goals simp only [show ((0 : Fin 3) + 2).succ = (3 : Fin 4) from rfl,
      show ((0 : Fin 3) + 1).succ = (2 : Fin 4) from rfl,
      show ((1 : Fin 3) + 2).succ = (1 : Fin 4) from rfl,
      show ((1 : Fin 3) + 1).succ = (3 : Fin 4) from rfl,
      show ((2 : Fin 3) + 2).succ = (2 : Fin 4) from rfl,
      show ((2 : Fin 3) + 1).succ = (1 : Fin 4) from rfl,
      show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
    · refine ⟨3, ?_, ?_⟩
      · convert v00 using 1 <;> norm_num [I3, ← sums.1]; ring
      · convert a00 using 1 <;> norm_num [nI3, ← sums.2]; ring
    · refine ⟨0, ?_, ?_⟩
      · convert v23 using 1 <;> norm_num; ring
      · convert a23 using 1 <;> norm_num; ring
    · refine ⟨3, ?_, ?_⟩
      · convert v10 using 1 <;> norm_num [I3]
      · convert a10 using 1 <;> norm_num [nI3]
    · refine ⟨0, ?_, ?_⟩
      · convert v03 using 1 <;> norm_num [← sums.1]; ring
      · convert a03 using 1 <;> norm_num [← sums.2]; ring
    · refine ⟨3, ?_, ?_⟩
      · convert v20 using 1 <;> norm_num [I3]
      · convert a20 using 1 <;> norm_num [nI3]
    · refine ⟨0, ?_, ?_⟩
      · convert v13 using 1 <;> norm_num; ring
      · convert a13 using 1 <;> norm_num; ring
    · refine ⟨1, ?_, ?_⟩
      · convert v02 using 1 <;> norm_num [← sums.1]; ring
      · convert a02 using 1 <;> norm_num [← sums.2]; ring
    · refine ⟨2, ?_, ?_⟩
      · convert v21 using 1 <;> norm_num [I2]; ring
      · convert a21 using 1 <;> norm_num [nI2]; ring
    · refine ⟨1, ?_, ?_⟩
      · convert v12 using 1 <;> norm_num; ring
      · convert a12 using 1 <;> norm_num; ring
    · refine ⟨2, ?_, ?_⟩
      · convert v01 using 1 <;> norm_num [I2, ← sums.1]; ring
      · convert a01 using 1 <;> norm_num [nI2, ← sums.2]; ring
    · refine ⟨1, ?_, ?_⟩
      · convert v22 using 1 <;> norm_num; ring
      · convert a22 using 1 <;> norm_num; ring
    · refine ⟨2, ?_, ?_⟩
      · convert v11 using 1 <;> norm_num [I2]; ring
      · convert a11 using 1 <;> norm_num [nI2]; ring

private theorem ht :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (a : PeriodicSubtileIndex),
        let slot : Fin 3 × Bool := match a.label with
          | .A => (0, true) | .B => (0, false)
          | .C => (1, true) | .D => (1, false)
          | .E => (2, true) | .F => (2, false)
        let i := slot.1
        let pos := slot.2
        let dV := (a.first : GaussianInt) * BandVectors.1 (q 0) (q 1) +
          (a.second : GaussianInt) * BandVectors.1 (q 0) (q 2)
        SubtileOccurrenceInterpretation cert.P cert.u cert.v a = TileTranslation (cert.P i pos)
            dV ) := by
  classical
  intro q cfg C₀ T₀ cert a slot i pos dV
  dsimp only [SubtileOccurrenceInterpretation, i, pos, slot, dV]
  rw [cert.period_u, cert.period_v]
  cases a.label <;> rfl

end ExteriorAdjacencyGeometry

theorem P4261T1ExteriorAdjacency
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer) (hroot : TileOdometer C₀.1.1 T₀ h₀)
    (C : BandCircle) (T : ProtoTile) (h : PartialOdometer)
    (a : PeriodicSubtileIndex) (ha : a ∈ P4261T1ExteriorIndices)
    (placed : P4261T1PlacedOdometer cert h₀ C T h a) :
    SubtileLatticeAdjacent C₀ C T₀ T h₀ h := by
-- BODY
  let slot : Fin 3 × Bool := match a.label with
    | .A => (0, true) | .B => (0, false)
    | .C => (1, true) | .D => (1, false)
    | .E => (2, true) | .F => (2, false)
  let i := slot.1
  let pos := slot.2
  let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let b := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
  let dV := (a.first : GaussianInt) * BandVectors.1 (q 0) (q 1) +
    (a.second : GaussianInt) * BandVectors.1 (q 0) (q 2)
  let dA := (a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
    (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2)
  -- Convert the twelve period indices using the three cyclic displacement calculations.
  have displacement (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
      (a : PeriodicSubtileIndex) (ha : a ∈ P4261T1ExteriorIndices) :=
          ExteriorAdjacencyGeometry.displacement q hq a ha
  obtain ⟨s, hV, hA⟩ := displacement q cfg.proper a ha
  change (if pos then (1 : GaussianInt) else -1) *
    ((1 - (⟨0, 1⟩ : GaussianInt)) * w) + 2 * dV =
      (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ)) at hV
  change (if pos then (1 : GaussianInt) else -1) *
    ((1 + (⟨0, 1⟩ : GaussianInt)) * b) + 2 * dA =
      (-(⟨0, 1⟩ : GaussianInt)) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)) at hA
  have parent : q i.succ = C.1.1 := placed.circle.symm
  refine ⟨hroot, placed.odometer, placed.rootSlope, placed.slope,
    placed.root_slope, placed.function_slope, q, i, s,
    cfg.proper, cert.child_eq, parent, ?_, ?_, ?_⟩
  · have ht : SubtileOccurrenceInterpretation cert.P cert.u cert.v a =
        TileTranslation (cert.P i pos) dV := ExteriorAdjacencyGeometry.ht q cfg C₀ T₀ cert a
    have hc := placed.centroid
    rw [ht, (TileTranslationFormulas (cert.P i pos) dV).2.2.2.2.1] at hc
    have ho := (cert.outer_occurrence i pos).2.2
    change TileCentroid (cert.P i pos) - TileCentroid T₀ =
      (if pos = true then (1 : Real) else -1) •
        ((1 / 2 : Real) • (GaussianRealPoint w -
          (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) at ho
    have hvx := congrArg (fun z : GaussianInt => (z.re : Real)) hV
    have hvy := congrArg (fun z : GaussianInt => (z.im : Real)) hV
    have hcx := congrArg Prod.fst hc
    have hcy := congrArg Prod.snd hc
    have hox := congrArg Prod.fst ho
    have hoy := congrArg Prod.snd ho
    apply Prod.ext
    all_goals
      cases hp : pos <;>
        simp [hp, GaussianRealPoint] at hvx hvy hcx hcy hox hoy ⊢ <;>
        linarith only [hvx, hvy, hcx, hcy, hox, hoy]
  · have ho := placed.slope_offset
    change placed.slope - placed.rootSlope =
      (if pos then (1 : Real) else -1) • P4250T1SlopeOffset b +
        GaussianRealPoint dA at ho
    have hox := congrArg Prod.fst ho
    have hax := congrArg (fun z : GaussianInt => (z.re : Real)) hA
    cases hp : pos <;>
      simp [hp, GaussianRealPoint, P4250T1SlopeOffset] at hox hax ⊢ <;>
      linarith only [hox, hax]
  · have ho := placed.slope_offset
    change placed.slope - placed.rootSlope =
      (if pos then (1 : Real) else -1) • P4250T1SlopeOffset b +
        GaussianRealPoint dA at ho
    have hoy := congrArg Prod.snd ho
    have hay := congrArg (fun z : GaussianInt => (z.im : Real)) hA
    cases hp : pos <;>
      simp [hp, GaussianRealPoint, P4250T1SlopeOffset] at hoy hay ⊢ <;>
      linarith only [hoy, hay]

end ApollonianSuperharmonic

end
