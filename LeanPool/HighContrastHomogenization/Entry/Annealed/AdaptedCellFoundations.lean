/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Contrast
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Setup.NormalizedFluctuation
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import LeanPool.HighContrastHomogenization.Entry.Source.Subdivision
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain

/-!
# High-contrast homogenization: Entry.Annealed.AdaptedCellFoundations

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability on the adapted cell and the aligned subdivision

Integrability of the coarse block on an adapted cell, and the combinatorics of the aligned triadic
subdivision the annealed estimates are carried out over. The module establishes law integrability
of every entry of an actual adapted coarse block and full positive definiteness of the adapted
annealed means, then describes the finite aligned subdivision of a parent adapted cell into its
triadic descendants, their centers, disjointness and common relative volume. It serves the
parent-child recurrence `p.fixed.geometry.parent.child.recurrence`.
-/

section
/-!
## Finite positive adapted expectations

The actual law integrability uses arbitrary finite moments, with an auxiliary
bounded window. No original-window containment or fixed-Q source threshold is needed
for ordinary support lemmas. Source-facing consumers retain the source lower scale.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean annealedBlock
  blockMatEntry_annealedBlock blockPosDef_annealedBlock isSymmetricBlockMat_coarseBlockMatrix)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry

noncomputable section

/-- Every entry of an actual adapted coarse block is law integrable. -/
theorem hasIntegrableCoarseBlock_adapted (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) (y : Vec d) :
    HasIntegrableCoarseBlock P (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) := by
  exact (Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar m hm j y 1 le_rfl).integrable_entry le_rfl

/-- Full positive definiteness of the actual adapted annealed means, at every
integer generation, from the standing stationary dagger law. -/
theorem adaptedMean_posDef (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    (toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) j)).PosDef := by
  let : NeZero d := ⟨by omega⟩
  have hint := hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar m hm j 0
  have hpos := blockPosDef_annealedBlock hint (fun a =>
    blockPosDef_coarseBlock_adapted (explicitRoundedGrid jStar m)
      (isUnit_roundedGrid hjStar hm) j 0 a)
  have hp := posDef_toFullBlockMat
    (isSymmetricBlockMat_annealedBlock P _) hpos
  simpa [adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell,
    HighContrast.centeredCube] using hp

end

end HCPolySupport.HighContrast.Annealed
end

section
/-!
## Finite aligned subdivisions

These are the actual triadic descendants used at `p.fixed.geometry.parent.child.recurrence`. The
integer
translation assertion retains the lower alignment threshold jStar ≤ j.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Set

noncomputable section

/-- An aligned center belongs to its parent precisely on the finite integer box. -/
theorem alignedCenter_mem_iff (d : ℕ) (j : ℤ) (h : ℕ) (w : Fin d → ℤ)
    (b : ℕ) (hb : 3 ^ h = 2 * b + 1) :
    standardCellCenter j w ∈ centeredCube d (j + h) ↔
      ∀ i, -(b : ℤ) ≤ w i ∧ w i ≤ (b : ℤ) := by
  have hpow : (3 : ℝ) ^ (j + (h : ℤ)) = (2 * (b : ℝ) + 1) * (3 : ℝ) ^ j := by
    have hbR : (3 : ℝ) ^ h = 2 * (b : ℝ) + 1 := by exact_mod_cast hb
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, hbR, mul_comm]
  rw [Recurrence.mem_centeredCube_iff]
  simp only [standardCellCenter]
  rw [hpow]
  have hpos : 0 < (3 : ℝ) ^ j := by positivity
  constructor
  · intro hw i
    obtain ⟨hl, hu⟩ := hw i
    have hlR : -(b : ℝ) - 1 < (w i : ℝ) := by
      have h : (3 : ℝ) ^ j * (-(b : ℝ) - 1) < (3 : ℝ) ^ j * (w i : ℝ) := by
        calc (3 : ℝ) ^ j * (-(b : ℝ) - 1)
            < -((1 : ℝ) / 2) * ((2 * (b : ℝ) + 1) * (3 : ℝ) ^ j) := by
              linarith only [hpos]
          _ < (3 : ℝ) ^ j * (w i : ℝ) := hl
      exact lt_of_mul_lt_mul_left h hpos.le
    have huR : (w i : ℝ) < (b : ℝ) + 1 := by
      have h : (3 : ℝ) ^ j * (w i : ℝ) < (3 : ℝ) ^ j * ((b : ℝ) + 1) := by
        calc (3 : ℝ) ^ j * (w i : ℝ)
            < (1 / 2 : ℝ) * ((2 * (b : ℝ) + 1) * (3 : ℝ) ^ j) := hu
          _ < (3 : ℝ) ^ j * ((b : ℝ) + 1) := by
              linarith only [hpos]
      exact lt_of_mul_lt_mul_left h hpos.le
    have hlZ : -(b : ℤ) - 1 < w i := by exact_mod_cast hlR
    have huZ : w i < (b : ℤ) + 1 := by exact_mod_cast huR
    omega
  · intro hw i
    have hl : -(b : ℝ) ≤ (w i : ℝ) := by exact_mod_cast (hw i).1
    have hu : (w i : ℝ) ≤ (b : ℝ) := by exact_mod_cast (hw i).2
    constructor
    · have h : (3 : ℝ) ^ j * (-(b : ℝ) - 1 / 2) < (3 : ℝ) ^ j * (w i : ℝ) :=
        mul_lt_mul_of_pos_left (by linarith only [hl]) hpos
      calc -((1 : ℝ) / 2) * ((2 * (b : ℝ) + 1) * (3 : ℝ) ^ j)
          = (3 : ℝ) ^ j * (-(b : ℝ) - 1 / 2) := by ring
        _ < (3 : ℝ) ^ j * (w i : ℝ) := h
    · have h : (3 : ℝ) ^ j * (w i : ℝ) < (3 : ℝ) ^ j * ((b : ℝ) + 1 / 2) :=
        mul_lt_mul_of_pos_left (by linarith only [hu]) hpos
      calc (3 : ℝ) ^ j * (w i : ℝ)
          < (3 : ℝ) ^ j * ((b : ℝ) + 1 / 2) := h
        _ = (1 / 2 : ℝ) * ((2 * (b : ℝ) + 1) * (3 : ℝ) ^ j) := by ring

/-- Every nonnegative gap gives exactly 3^(d*h) centers, including the singleton h=0. -/
theorem alignedCenterSet_finite_card (d : ℕ) (j : ℤ) (h : ℕ) :
    {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}.Finite ∧
    {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}.ncard =
      3 ^ (d * h) := by
  obtain ⟨b, hb⟩ : Odd ((3 : ℕ) ^ h) := Odd.pow (by decide)
  let F : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(b : ℤ)) b
  have hset : {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)} =
      (F : Set (Fin d → ℤ)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, F, Fintype.mem_piFinset, Finset.mem_Icc]
    exact alignedCenter_mem_iff d j h w b hb
  rw [hset]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  have hcard : (Finset.Icc (-(b : ℤ)) (b : ℤ)).card = 3 ^ h := by
    rw [Int.card_Icc, hb]
    omega
  simp [F, Fintype.card_piFinset, hcard, ← pow_mul, Nat.mul_comm]

/-- Each actual rounded-grid center is an integer translation at admissible scales. -/
theorem adaptedCellCenter_eq_intTranslation {d : ℕ} (jStar : ℕ) (m : Mat d)
    {j : ℤ} (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ) :
    ∃ z : Fin d → ℤ, adaptedCellCenter (explicitRoundedGrid jStar m) j w =
      HCPolySupport.Source.AKL.intTranslation z := by
  obtain ⟨z, hz⟩ := explicitRoundedGrid_mulVec_intCast jStar m hj w
  exact ⟨z, by simpa [adaptedCellCenter, matVecMul_eq_mulVec,
    HCPolySupport.Source.AKL.intTranslation] using! hz⟩

/-- Standard cells at a fixed finer generation form the full finite parent partition. -/
theorem aligned_standard_partition {d : ℕ} (j : ℤ) (h : ℕ) :
    let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
    (∀ w ∈ s, standardCell d j w ⊆ centeredCube d (j + h)) ∧
      s.PairwiseDisjoint (standardCell d j) ∧
      volume (centeredCube d (j + h) \ ⋃ w ∈ s, standardCell d j w) = 0 := by
  intro s
  have hsub : ∀ w ∈ s, standardCell d j w ⊆ centeredCube d (j + h) := by
    intro w hw
    change standardCellCenter j w ∈ centeredCube d (j + h) at hw
    rw [centeredCube_eq_standardCell] at hw ⊢
    exact standardCell_subset_of_mem (by omega) (Recurrence.standardCellCenter_mem_standardCell
      j w) hw
  refine ⟨hsub, fun w _ v _ hne => standardCell_disjoint_of_ne j hne, ?_⟩
  apply measure_mono_null (t := gridFaces d j) _ (volume_gridFaces j)
  intro x hx
  by_contra hface
  obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hface
  have hsw : standardCell d j w ⊆ centeredCube d (j + h) := by
    rw [centeredCube_eq_standardCell] at hx ⊢
    exact standardCell_subset_of_mem (by omega) hw hx.1
  exact hx.2 (mem_iUnion₂.mpr ⟨w, hsw (Recurrence.standardCellCenter_mem_standardCell j w), hw⟩)

/-- The invertible affine image preserves the aligned partition and its null boundaries. -/
theorem aligned_adapted_partition {d : ℕ} (q : Mat d) (hq : IsUnit q) (j : ℤ) (h : ℕ) :
    let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
    (∀ w ∈ s, adaptedCellAtCenter q j w ⊆ adaptedCell q (j + h)) ∧
      s.PairwiseDisjoint (adaptedCellAtCenter q j) ∧
      volume (adaptedCell q (j + h) \ ⋃ w ∈ s, adaptedCellAtCenter q j w) = 0 := by
  intro s
  obtain ⟨hsub, hdisj, _⟩ := aligned_standard_partition (d := d) j h
  have hinj : Function.Injective (matVecMul q) := by
    simpa only [matVecMul_eq_mulVec] using! Matrix.mulVec_injective_iff_isUnit.mpr hq
  refine ⟨fun w hw => ?_, ?_, ?_⟩
  · rw [adaptedCellAtCenter_eq_affine_standardCell]
    exact Set.image_mono (hsub w hw)
  · intro w hw v hv hne
    change Disjoint (adaptedCellAtCenter q j w) (adaptedCellAtCenter q j v)
    rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
    exact (Set.disjoint_image_iff hinj).2 (hdisj hw hv hne)
  · apply measure_mono_null (t := matVecMul q '' ⋃ k : ℤ, gridFaces d k) _
      (volume_image_iUnion_gridFaces q)
    rintro x ⟨⟨u, hu, rfl⟩, hx⟩
    by_cases hface : u ∈ gridFaces d j
    · exact ⟨u, mem_iUnion.mpr ⟨j, hface⟩, rfl⟩
    · obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hface
      have hsw : standardCell d j w ⊆ centeredCube d (j + h) := by
        rw [centeredCube_eq_standardCell] at hu ⊢
        exact standardCell_subset_of_mem (by omega) hw hu
      apply False.elim
      apply hx
      refine mem_iUnion₂.mpr ⟨w, hsw (Recurrence.standardCellCenter_mem_standardCell j w), ?_⟩
      rw [adaptedCellAtCenter_eq_affine_standardCell]
      exact ⟨u, hw, rfl⟩

/-- Each child has the same relative volume 3^(-d*h) in the full adapted parent. -/
theorem aligned_adapted_volume_ratio {d : ℕ} (q : Mat d) (hq : IsUnit q)
    (j : ℤ) (h : ℕ) (w : Fin d → ℤ) :
    (volume (adaptedCellAtCenter q j w)).toReal / (volume (adaptedCell q (j + h))).toReal =
      ((3 : ℝ) ^ (d * h))⁻¹ := by
  have hparent : adaptedCell q (j + h) = adaptedCellTranslate q (j + h) 0 := by
    simp [adaptedCellTranslate]
  have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
  have habs : |q.det| ≠ 0 := abs_ne_zero.mpr hdet
  have h3 : (3 : ℝ) ^ j ≠ 0 := by positivity
  rw [hparent, volume_adaptedCellAtCenter, volume_adaptedCellTranslate]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity : 0 ≤ (3 : ℝ) ^ j),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (3 : ℝ) ^ (j + (h : ℤ)))]
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, mul_pow, ← pow_mul]
  rw [Nat.mul_comm h d]
  field_simp

end

end HCPolySupport.HighContrast.Annealed
end
