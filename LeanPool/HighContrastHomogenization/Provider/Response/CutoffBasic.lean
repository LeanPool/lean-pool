/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffCubeAverage

/-!
# High-contrast homogenization: Provider.Response.CutoffBasic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted pre-Young cutoff

The cutoff is the normalized canonical product cutoff on the centered reference
cube, pulled forward by the positive-definite grid matrix.  Its chosen inner
cube has at least half the parent volume, so normalization preserves the pointwise
upper bound two.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Set MeasureTheory

/-- The smooth mean-one cutoff on the adapted cell. -/
@[expose]
noncomputable def adaptedPreYoungCutoff {d : ℕ} [NeZero d]
    (q : Mat d) (_hq : q.PosDef) (t : ℤ) : Vec d → ℝ :=
  let Q : TriadicCube d := originCube d t
  let ρ₁ : ℝ := 1 - 1 / (2 * (d : ℝ))
  let ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ))
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂
  let A : ℝ := cubeAverage Q η
  fun x => A⁻¹ * η (matVecMul q⁻¹ x)

/-- Defining equation for the adapted cutoff. -/
@[simp] theorem adaptedPreYoungCutoff_apply {d : ℕ} [NeZero d]
    (q : Mat d) (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    adaptedPreYoungCutoff q hq t x =
      (cubeAverage (originCube d t)
        (QuantitativeCubeCutoff.canonicalFun (originCube d t)
          (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))))⁻¹ *
        QuantitativeCubeCutoff.canonicalFun (originCube d t)
          (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))
          (matVecMul q⁻¹ x) := by
  rfl

/-- The unnormalized cutoff has average at least one half. -/
theorem half_le_adaptedPreYoungCutoff_rawAverage {d : ℕ} [NeZero d]
    (t : ℤ) :
    (1 / 2 : ℝ) ≤
      cubeAverage (originCube d t)
        (QuantitativeCubeCutoff.canonicalFun (originCube d t)
          (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))) := by
  obtain ⟨hρ₁, hρ₁₂, hρ₂⟩ := cutoffRadii_spec d
  have hinner := innerRatio_pow_le_cubeAverage_canonicalFun (originCube d t)
    hρ₁ hρ₁₂ (lt_trans hρ₁₂ hρ₂)
  exact (half_le_innerRatio_pow d).trans hinner

/-- The normalizing average is positive. -/
theorem adaptedPreYoungCutoff_rawAverage_pos {d : ℕ} [NeZero d]
    (t : ℤ) :
    0 < cubeAverage (originCube d t)
      (QuantitativeCubeCutoff.canonicalFun (originCube d t)
        (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))) :=
  lt_of_lt_of_le (by norm_num) (half_le_adaptedPreYoungCutoff_rawAverage t)

/-- Normalization enlarges the canonical cutoff by at most two. -/
theorem adaptedPreYoungCutoff_inv_rawAverage_le_two {d : ℕ} [NeZero d]
    (t : ℤ) :
    (cubeAverage (originCube d t)
      (QuantitativeCubeCutoff.canonicalFun (originCube d t)
        (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))))⁻¹ ≤ 2 := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hA := half_le_adaptedPreYoungCutoff_rawAverage (d := d) t
  have hinv := one_div_le_one_div_of_le hhalf hA
  simpa only [one_div, inv_inv] using hinv

/-- Pulling the adapted cutoff back by its grid matrix recovers the normalized
reference cutoff exactly. -/
theorem adaptedPreYoungCutoff_pullback_apply {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (y : Vec d) :
    adaptedPreYoungCutoff q hq t (matVecMul q y) =
      (cubeAverage (originCube d t)
        (QuantitativeCubeCutoff.canonicalFun (originCube d t)
          (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))))⁻¹ *
        QuantitativeCubeCutoff.canonicalFun (originCube d t)
          (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ))) y := by
  rw [adaptedPreYoungCutoff_apply]
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hcancel : matVecMul q⁻¹ (matVecMul q y) = y := by
    change Matrix.mulVec q⁻¹ (Matrix.mulVec q y) = y
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hcancel]

/-- The adapted cutoff is nonnegative. -/
theorem adaptedPreYoungCutoff_nonneg {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    0 ≤ adaptedPreYoungCutoff q hq t x := by
  rw [adaptedPreYoungCutoff_apply]
  exact mul_nonneg
    (inv_nonneg.mpr (adaptedPreYoungCutoff_rawAverage_pos t).le)
    (QuantitativeCubeCutoff.canonicalFun_nonneg _ _ _ _)

/-- The normalized adapted cutoff is bounded above by two. -/
theorem adaptedPreYoungCutoff_le_two {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    adaptedPreYoungCutoff q hq t x ≤ 2 := by
  rw [adaptedPreYoungCutoff_apply]
  let A : ℝ := cubeAverage (originCube d t)
    (QuantitativeCubeCutoff.canonicalFun (originCube d t)
      (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ))))
  have hA_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr (by
    simpa [A] using (adaptedPreYoungCutoff_rawAverage_pos (d := d) t).le)
  have hη_le := QuantitativeCubeCutoff.canonicalFun_le_one (originCube d t)
    (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ))) (matVecMul q⁻¹ x)
  have hmul : A⁻¹ *
      QuantitativeCubeCutoff.canonicalFun (originCube d t)
        (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ))) (matVecMul q⁻¹ x) ≤
      A⁻¹ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hη_le hA_nonneg
  exact hmul.trans (by
    simpa [A] using adaptedPreYoungCutoff_inv_rawAverage_le_two (d := d) t)

/-- The adapted cutoff is smooth. -/
theorem adaptedPreYoungCutoff_smooth {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (adaptedPreYoungCutoff q hq t) := by
  obtain ⟨hρ₁, hρ₁₂, _hρ₂⟩ := cutoffRadii_spec d
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun (originCube d t)
    (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))
  let A : ℝ := cubeAverage (originCube d t) η
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using QuantitativeCubeCutoff.canonicalFun_smooth
      (originCube d t) hρ₁ hρ₁₂
  have hnormalized : ContDiff ℝ (⊤ : ℕ∞) (fun y => A⁻¹ * η y) := by
    simpa only [smul_eq_mul] using hη.const_smul A⁻¹
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q⁻¹) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q⁻¹)).contDiff
  simpa only [adaptedPreYoungCutoff, η, A, Function.comp_def] using
    hnormalized.comp hlinear

/-- The adapted cutoff has compact support. -/
theorem adaptedPreYoungCutoff_hasCompactSupport {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    HasCompactSupport (adaptedPreYoungCutoff q hq t) := by
  obtain ⟨hρ₁, hρ₁₂, hρ₂⟩ := cutoffRadii_spec d
  let Q : TriadicCube d := originCube d t
  let ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ))
  let K : Set (Vec d) := matVecMul q '' scaledClosedCubeSet Q ρ₂
  have hρ₂_nonneg : 0 ≤ ρ₂ := (lt_trans hρ₁ hρ₁₂).le
  have hKcompact : IsCompact K := by
    exact (isCompact_scaledClosedCubeSet Q hρ₂_nonneg).image
      (Matrix.mulVecLin q).continuous_of_finiteDimensional
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro x hx
  let y : Vec d := matVecMul q⁻¹ x
  have hηy : QuantitativeCubeCutoff.canonicalFun Q
      (1 - 1 / (2 * (d : ℝ))) ρ₂ y ≠ 0 := by
    intro hzero
    apply hx
    rw [adaptedPreYoungCutoff_apply]
    change _ * QuantitativeCubeCutoff.canonicalFun Q
      (1 - 1 / (2 * (d : ℝ))) ρ₂ y = 0
    rw [hzero, mul_zero]
  have hyclosed : y ∈ scaledClosedCubeSet Q ρ₂ :=
    QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
      hρ₁ hρ₁₂ (subset_closure hηy)
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hxy : matVecMul q y = x := by
    dsimp [y]
    change Matrix.mulVec q (Matrix.mulVec q⁻¹ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact ⟨y, hyclosed, hxy⟩

/-- The compact support lies inside the open adapted cell. -/
theorem adaptedPreYoungCutoff_tsupport_subset {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    tsupport (adaptedPreYoungCutoff q hq t) ⊆ adaptedCell q t := by
  obtain ⟨hρ₁, hρ₁₂, hρ₂⟩ := cutoffRadii_spec d
  let Q : TriadicCube d := originCube d t
  let ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ))
  let K : Set (Vec d) := matVecMul q '' scaledClosedCubeSet Q ρ₂
  have hρ₂_nonneg : 0 ≤ ρ₂ := (lt_trans hρ₁ hρ₁₂).le
  have hKcompact : IsCompact K := by
    exact (isCompact_scaledClosedCubeSet Q hρ₂_nonneg).image
      (Matrix.mulVecLin q).continuous_of_finiteDimensional
  have hsupp : Function.support (adaptedPreYoungCutoff q hq t) ⊆ K := by
    intro x hx
    let y : Vec d := matVecMul q⁻¹ x
    have hηy : QuantitativeCubeCutoff.canonicalFun Q
        (1 - 1 / (2 * (d : ℝ))) ρ₂ y ≠ 0 := by
      intro hzero
      apply hx
      rw [adaptedPreYoungCutoff_apply]
      change _ * QuantitativeCubeCutoff.canonicalFun Q
        (1 - 1 / (2 * (d : ℝ))) ρ₂ y = 0
      rw [hzero, mul_zero]
    have hyclosed : y ∈ scaledClosedCubeSet Q ρ₂ :=
      QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
        hρ₁ hρ₁₂ (subset_closure hηy)
    have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
    have hxy : matVecMul q y = x := by
      dsimp [y]
      change Matrix.mulVec q (Matrix.mulVec q⁻¹ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact ⟨y, hyclosed, hxy⟩
  have htsupport : tsupport (adaptedPreYoungCutoff q hq t) ⊆ K := by
    exact closure_minimal hsupp hKcompact.isClosed
  refine htsupport.trans ?_
  rintro x ⟨y, hy, rfl⟩
  rw [adaptedCell]
  exact ⟨y, by
    exact scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q hρ₂_nonneg hρ₂ hy, rfl⟩

/-- The reference-cube average of the normalized pullback is one. -/
theorem cubeAverage_adaptedPreYoungCutoff_pullback_eq_one {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    cubeAverage (originCube d t)
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) = 1 := by
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun (originCube d t)
    (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))
  let A : ℝ := cubeAverage (originCube d t) η
  have hApos : 0 < A := by
    simpa [A, η] using adaptedPreYoungCutoff_rawAverage_pos (d := d) t
  have hpull : (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) =
      fun y => A⁻¹ * η y := by
    funext y
    simpa [A, η] using adaptedPreYoungCutoff_pullback_apply hq t y
  rw [hpull]
  unfold cubeAverage
  rw [integral_const_mul]
  calc
    (cubeVolume (originCube d t))⁻¹ *
        (A⁻¹ * ∫ x in cubeSet (originCube d t), η x ∂volume) =
      A⁻¹ * ((cubeVolume (originCube d t))⁻¹ *
        ∫ x in cubeSet (originCube d t), η x ∂volume) := by ring
    _ = A⁻¹ * A := by rfl
    _ = 1 := inv_mul_cancel₀ hApos.ne.symm

end

end Response
end HighContrast
end HCPolySupport
