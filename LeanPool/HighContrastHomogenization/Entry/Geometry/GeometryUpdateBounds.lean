/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.GeometryUpdate
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Entry.Geometry.PositiveSqrtCongruence
public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveMetric
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Matrix.ZPow

/-!
# High-contrast homogenization: Entry.Geometry.GeometryUpdateBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Bounds for the geometry update

For positive definite `m` and `mStar`, the update `geometryUpdate ε m mStar` is again
positive definite.  On the branch where `m` and `mStar` are not projectively equal, its
normalized form is the real CFC power `matPow θ (normalizedMat m mStar)` with
`θ = min (ε / projectiveDistance m mStar) 1 ∈ (0, 1]`, and
`projectiveDistance m (geometryUpdate ε m mStar) = min ε (projectiveDistance m mStar)`,
so the update advances the projective class of `m` by exactly the requested step, capped
at the distance to `mStar`.  The spectral thresholds `specBound` and `specMin`, and their
ratio, of a positive CFC power are the corresponding scalar powers of the originals.
These are the update-side estimates that do not require the projective-distance separation
theorem of `HCPoly.Entry.Geometry.ProjectiveMetric`; they serve `l.projective.step` and the
step advance of the finite run in `p.global.selection`.
-/

open HCPolySupport.HighContrast (matPow matSqrt specBound specBound_nonneg)
namespace HCPolySupport.HighContrast.Geometry

open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem cfc_sqrt_inv {m : Mat d} (hm : m.PosDef) :
    (CFC.sqrt m)⁻¹ = CFC.sqrt m⁻¹ := by
  rw [eq_comm,
    CFC.sqrt_eq_iff _ _ hm.inv.posSemidef.nonneg
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg m)).inv.nonneg,
    ← sq, Matrix.inv_pow', CFC.sq_sqrt m]

private theorem matSqrt_inv_mul_matSqrt {m : Mat d} (hm : m.PosDef) :
    matSqrt m⁻¹ * matSqrt m = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef, matSqrt_eq_cfc_sqrt hm.posSemidef,
    ← cfc_sqrt_inv hm]
  exact Matrix.nonsing_inv_mul (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt hm).isUnit)

private theorem matSqrt_mul_matSqrt_inv {m : Mat d} (hm : m.PosDef) :
    matSqrt m * matSqrt m⁻¹ = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef, matSqrt_eq_cfc_sqrt hm.posSemidef,
    ← cfc_sqrt_inv hm]
  exact Matrix.mul_nonsing_inv (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt hm).isUnit)

/-- A positive matrix has positive real CFC powers for every real exponent. -/
theorem matPow_posDef {M : Mat d} (hM : M.PosDef) (θ : ℝ) :
    (matPow θ M).PosDef := by
  dsimp [matPow]
  rw [← CFC.rpow_eq_cfc_real (a := M) (y := θ)]
  exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.rpow M θ hM.isStrictlyPositive)

/-- Positive CFC powers raise the upper spectral threshold to the same scalar power. -/
theorem specBound_matPow {M : Mat d} [NeZero d] (hM : M.PosDef)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    specBound (matPow θ M) = specBound M ^ θ := by
  rw [← posDef_l2_opNorm_eq_specBound (matPow_posDef hM θ)]
  dsimp [matPow]
  exact posDef_l2_opNorm_cfc_rpow_eq_specBound_rpow hM hθ

/-- Positive CFC powers raise the lower spectral threshold to the same scalar power. -/
theorem specMin_matPow {M : Mat d} [NeZero d] (hM : M.PosDef)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    specMin (matPow θ M) = specMin M ^ θ := by
  have hpow := matPow_posDef hM θ
  have hnorm : ‖(matPow θ M)⁻¹‖ = (specMin (matPow θ M))⁻¹ :=
    posDef_inv_l2_opNorm_eq_specMin_inv hpow
  have hnorm' : ‖(matPow θ M)⁻¹‖ = (specMin M ^ θ)⁻¹ := by
    dsimp [matPow]
    exact posDef_inv_l2_opNorm_cfc_rpow_eq_specMin_rpow_inv hM hθ
  exact inv_injective (hnorm.symm.trans hnorm')

/-- The spectral spread of a positive CFC power is the scalar power of the original spread. -/
theorem specSpread_matPow {M : Mat d} [NeZero d] (hM : M.PosDef)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    specBound (matPow θ M) / specMin (matPow θ M) =
      (specBound M / specMin M) ^ θ := by
  rw [specBound_matPow hM hθ, specMin_matPow hM hθ,
    Real.div_rpow (specBound_nonneg M) (specMin_pos hM).le θ]

/-- In the projectively equal branch, the geometry update returns `mStar`. -/
theorem geometryUpdate_of_projectiveEq {m mStar : Mat d}
    (h : ProjectiveEq m mStar) (ε : ℝ) : geometryUpdate ε m mStar = mStar := by
  simp [geometryUpdate, h]

/-- Away from the projectively equal branch, the projective distance is strictly positive. -/
theorem projectiveDistance_pos_of_not_projectiveEq {m mStar : Mat d} [NeZero d]
    (hm : m.PosDef) (hStar : mStar.PosDef) (hne : ¬ ProjectiveEq m mStar) :
    0 < projectiveDistance m mStar := by
  have hnonneg := projectiveDistance_nonneg hm hStar
  by_contra hnot
  have hle : projectiveDistance m mStar ≤ 0 := le_of_not_gt hnot
  have hzero : projectiveDistance m mStar = 0 := le_antisymm hle hnonneg
  exact hne ((projectiveDistance_eq_zero_iff hm hStar).1 hzero)

/-- On the nonequal branch and for positive step size, the printed update exponent lies in
`(0, 1]`. -/
theorem geometryUpdate_exponent_mem_Ioc {m mStar : Mat d} [NeZero d]
    (hm : m.PosDef) (hStar : mStar.PosDef) (hne : ¬ ProjectiveEq m mStar)
    {ε : ℝ} (hε : 0 < ε) :
    min (ε / projectiveDistance m mStar) 1 ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact lt_min (div_pos hε (projectiveDistance_pos_of_not_projectiveEq hm hStar hne))
      zero_lt_one
  · exact min_le_right _ _

/-- On the nonequal branch, normalizing the update cancels the endpoint square roots and leaves
the powered relative matrix. -/
theorem normalizedMat_geometryUpdate_of_not_projectiveEq {m mStar : Mat d}
    (hm : m.PosDef) (hne : ¬ ProjectiveEq m mStar) (ε : ℝ) :
    normalizedMat m (geometryUpdate ε m mStar) =
      matPow (min (ε / projectiveDistance m mStar) 1) (normalizedMat m mStar) := by
  rw [geometryUpdate, ite_eq_right hne, normalizedMat, matSqrt_eq_cfc_sqrt hm.posSemidef]
  let θ := min (ε / projectiveDistance m mStar) 1
  let P := matPow θ (normalizedMat m mStar)
  change matSqrt m⁻¹ * (CFC.sqrt m * P * CFC.sqrt m) * matSqrt m⁻¹ = P
  calc
    matSqrt m⁻¹ * (CFC.sqrt m * P * CFC.sqrt m) * matSqrt m⁻¹ =
        (matSqrt m⁻¹ * CFC.sqrt m) * P * (CFC.sqrt m * matSqrt m⁻¹) := by
      noncomm_ring
    _ = P := by
      rw [show matSqrt m⁻¹ * CFC.sqrt m = 1 by
          rw [← matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_inv_mul_matSqrt hm],
        show CFC.sqrt m * matSqrt m⁻¹ = 1 by
          rw [← matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_mul_matSqrt_inv hm]]
      simp

/-- The geometry update is positive definite for positive endpoints and every real step. -/
theorem geometryUpdate_posDef {m mStar : Mat d}
    (hm : m.PosDef) (hStar : mStar.PosDef) (ε : ℝ) :
    (geometryUpdate ε m mStar).PosDef := by
  by_cases h : ProjectiveEq m mStar
  · rw [geometryUpdate_of_projectiveEq h ε]
    exact hStar
  · rw [geometryUpdate, ite_eq_right h]
    have hsqrt : (CFC.sqrt m).PosDef := posDef_sqrt hm
    have hsqrt_trans : Matrix.transpose (CFC.sqrt m) = CFC.sqrt m := transpose_sqrt hm
    have hinj : Function.Injective (CFC.sqrt m).vecMul :=
      Matrix.vecMul_injective_iff_isUnit.mpr hsqrt.isUnit
    have hpow :
        (matPow (min (ε / projectiveDistance m mStar) 1)
          (normalizedMat m mStar)).PosDef :=
      matPow_posDef (normalizedMat_posDef hm hStar) _
    have hconj :
        (CFC.sqrt m *
            matPow (min (ε / projectiveDistance m mStar) 1) (normalizedMat m mStar) *
          Matrix.conjTranspose (CFC.sqrt m)).PosDef :=
      hpow.mul_mul_conjTranspose_same (B := CFC.sqrt m) hinj
    rw [matSqrt_eq_cfc_sqrt hm.posSemidef]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hsqrt_trans] using hconj

private theorem specSpread_pos {M : Mat d} [NeZero d] (hM : M.PosDef) :
    0 < specBound M / specMin M := by
  have hmin_pos := specMin_pos hM
  obtain ⟨i, j, hmin, hbound, hle⟩ := spectral_extrema_attained hM
  have hbound_pos : 0 < specBound M := by
    rw [hbound]
    exact (hM.eigenvalues_pos i).trans_le (by
      simpa [hmin] using (hle j).1)
  exact div_pos hbound_pos hmin_pos

/-- The positive-step geometry update moves by the smaller of the requested step and the
endpoint projective distance. -/
theorem projectiveDistance_geometryUpdate_eq_min {m mStar : Mat d} [NeZero d]
    (hm : m.PosDef) (hStar : mStar.PosDef) {ε : ℝ} (hε : 0 < ε) :
    projectiveDistance m (geometryUpdate ε m mStar) =
      min ε (projectiveDistance m mStar) := by
  by_cases hEq : ProjectiveEq m mStar
  · rw [geometryUpdate_of_projectiveEq hEq ε]
    rw [(projectiveDistance_eq_zero_iff hm hStar).2 hEq]
    exact (min_eq_right hε.le).symm
  · let δ := projectiveDistance m mStar
    let θ := min (ε / δ) 1
    have hδ_pos : 0 < δ := by
      simpa [δ] using projectiveDistance_pos_of_not_projectiveEq hm hStar hEq
    have hθ_nonneg : 0 ≤ θ := by
      exact (geometryUpdate_exponent_mem_Ioc hm hStar hEq hε).1.le
    have hdist_eq :
        projectiveDistance m (geometryUpdate ε m mStar) = θ * δ := by
      have hN : (normalizedMat m mStar).PosDef := normalizedMat_posDef hm hStar
      rw [projectiveDistance, normalizedMat_geometryUpdate_of_not_projectiveEq hm hEq ε,
        specSpread_matPow hN hθ_nonneg]
      have hspread_pos : 0 < specBound (normalizedMat m mStar) /
          specMin (normalizedMat m mStar) :=
        specSpread_pos hN
      rw [Real.log_rpow hspread_pos θ]
      rw [show δ = projectiveDistance m mStar by rfl, projectiveDistance]
      ring
    have hθ_mul :
        θ * δ = min ε δ := by
      by_cases hεδ : ε / δ ≤ 1
      · have hε_le_delta : ε ≤ δ := by
          simpa using (div_le_iff₀ hδ_pos).1 hεδ
        rw [show θ = ε / δ by exact min_eq_left hεδ, min_eq_left hε_le_delta,
          div_mul_cancel₀ ε hδ_pos.ne']
      · have hone_le : 1 ≤ ε / δ := le_of_lt (lt_of_not_ge hεδ)
        have hdelta_le_ε : δ ≤ ε := by
          simpa using (le_div_iff₀ hδ_pos).1 hone_le
        rw [show θ = 1 by exact min_eq_right hone_le, min_eq_right hdelta_le_ε]
        ring
    rw [hdist_eq]
    exact hθ_mul

/-- A positive geometry update stays within the prescribed projective distance step. -/
theorem projectiveDistance_geometryUpdate_le {m mStar : Mat d} [NeZero d]
    (hm : m.PosDef) (hStar : mStar.PosDef) {ε : ℝ} (hε : 0 < ε) :
    projectiveDistance m (geometryUpdate ε m mStar) ≤ ε := by
  rw [projectiveDistance_geometryUpdate_eq_min hm hStar hε]
  exact min_le_left _ _

end

end HCPolySupport.HighContrast.Geometry
