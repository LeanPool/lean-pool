/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleClass
public import LeanPool.HighContrastHomogenization.Analytic.SkewGauge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedWeakSolutionPullback

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.LiouvilleGaugeInvariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar and constant-skew invariance of the Liouville class

Positive coefficient scaling changes the local symmetric energy by a fixed
factor.  Constant skew shifts leave that energy unchanged; their weak pairing
vanishes locally on the exhaustion cubes and hence globally.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

private theorem sEnergyOn_smul_coefficient
    (b : CoeffField d) (U : Set (Vec d)) (F : Vec d → Vec d)
    {c : ℝ} (hc : 0 ≤ c) :
    sEnergyOn (fun x ↦ c • b x) U F =
      ENNReal.ofReal c * sEnergyOn b U F := by
  unfold sEnergyOn
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [symmPart_smul, smul_matVecMul, vecDot_smul_right,
    ENNReal.ofReal_mul hc]

private theorem h1sNormSqOn_smul_coefficient_le
    (b : CoeffField d) (U : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) {c : ℝ} (hc : 0 ≤ c) :
    h1sNormSqOn (fun x ↦ c • b x) U u Du ≤
      max 1 (ENNReal.ofReal c) * h1sNormSqOn b U u Du := by
  rw [h1sNormSqOn, h1sNormSqOn, sEnergyOn_smul_coefficient b U Du hc]
  rw [mul_add]
  apply add_le_add
  · exact le_mul_of_one_le_left bot_le (le_max_left _ _)
  · exact mul_le_mul_left (le_max_right _ _) _

private theorem memH1sLoc_smul_coefficient
    {b : CoeffField d} {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    {c : ℝ} (hc : 0 ≤ c) (hv : MemH1sLoc b v Dv) :
    MemH1sLoc (fun x ↦ c • b x) v Dv := by
  refine ⟨hv.1, ?_⟩
  intro R hR
  obtain ⟨hweak, w, hw, htend⟩ := hv.2 R hR
  refine ⟨hweak, w, hw, ?_⟩
  let K : ℝ≥0∞ := max 1 (ENNReal.ofReal c)
  apply tendsto_zero_of_le_of_tendsto_zero
    (g := fun n ↦ K * h1sNormSqOn b (euclideanBall d R)
      (fun x ↦ w n x - v x) (fun x ↦ smoothGrad (w n) x - Dv x))
  · intro n
    exact h1sNormSqOn_smul_coefficient_le b _ _ _ hc
  · have hKtop : K ≠ ⊤ := max_ne_top (by norm_num) ENNReal.ofReal_ne_top
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul htend (Or.inr hKtop))

/-- Positive scalar multiplication of a coefficient leaves its full
Liouville class unchanged. -/
theorem memLiouvilleClass_smul_coefficient_iff
    {b : CoeffField d} {theta : ℝ} {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    {c : ℝ} (hc : 0 < c) :
    MemLiouvilleClass (fun x ↦ c • b x) theta v Dv ↔
      MemLiouvilleClass b theta v Dv := by
  constructor
  · intro h
    have hlocal := memH1sLoc_smul_coefficient (b := fun x ↦ c • b x)
      (inv_nonneg.mpr hc.le) h.1
    have hfield : (fun x ↦ c⁻¹ • (c • b x)) = b := by
      funext x
      simp [hc.ne']
    rw [hfield] at hlocal
    exact ⟨hlocal,
      (isWeakSolutionOn_smul_coefficient_iff b Dv hc.ne').mp h.2.1,
      h.2.2⟩
  · intro h
    exact ⟨memH1sLoc_smul_coefficient hc.le h.1,
      (isWeakSolutionOn_smul_coefficient_iff b Dv hc.ne').mpr h.2.1,
      h.2.2⟩

private theorem memH1sLoc_add_constSkew_iff
    (b : CoeffField d) (k : Mat d) (hk : IsSkewMat k)
    (v : Vec d → ℝ) (Dv : Vec d → Vec d) :
    MemH1sLoc (fun x ↦ b x + k) v Dv ↔ MemH1sLoc b v Dv := by
  constructor
  · rintro ⟨hmeas, hlocal⟩
    refine ⟨hmeas, fun R hR ↦ ?_⟩
    obtain ⟨hweak, w, hw, htend⟩ := hlocal R hR
    refine ⟨hweak, w, hw, ?_⟩
    simpa only [h1sNormSqOn_add_constSkew b (euclideanBall d R)
      _ _ k hk] using htend
  · rintro ⟨hmeas, hlocal⟩
    refine ⟨hmeas, fun R hR ↦ ?_⟩
    obtain ⟨hweak, w, hw, htend⟩ := hlocal R hR
    refine ⟨hweak, w, hw, ?_⟩
    simpa only [h1sNormSqOn_add_constSkew b (euclideanBall d R)
      _ _ k hk] using htend

private theorem memScalarL2_openCubeSet_of_growth
    [NeZero d]
    {theta : ℝ} {v : Vec d → ℝ}
    (hvmeas : AEStronglyMeasurable v volume)
    (hgrowth : Tendsto
      (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v) atTop (nhds 0))
    (q : ℕ) : MemScalarL2 (localGradientCube d q) v := by
  let Q := originCube d (q : ℤ)
  have hnorm := memLp_normalizedCubeMeasure_of_liouvilleGrowth
    hvmeas hgrowth q
  have hscaled := hnorm.smul_measure
    (c := ENNReal.ofReal (cubeVolume Q)) ENNReal.ofReal_ne_top
  have hcancel : ENNReal.ofReal (cubeVolume Q) *
      ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    field_simp [(cubeVolume_pos Q).ne']
    exact ENNReal.ofReal_one
  simpa only [localGradientCube, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, smul_smul,
    hcancel, one_smul, MemScalarL2, Q] using hscaled

private theorem hasWeakGradientOn_localGradientCube_of_memH1sLoc
    [NeZero d]
    {b : CoeffField d} {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemH1sLoc b v Dv) (q : ℕ) :
    HasWeakGradientOn (localGradientCube d q) v Dv := by
  obtain ⟨R, hR, hsub⟩ :=
    exists_pos_euclideanBall_superset_openCubeSet (originCube d (q : ℤ))
  have hweak := (hv.2 R hR).1
  exact hweak.restrict (by
    simpa only [localGradientCube] using
      (isOpen_openCubeSet (originCube d (q : ℤ)))) (by
        simpa only [localGradientCube] using hsub)

private theorem isWeakSolutionOn_univ_add_constSkew_iff
    [NeZero d]
    {b : CoeffField d} {theta : ℝ}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hlocal : MemH1sLoc b v Dv)
    (hgrowth : Tendsto
      (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v) atTop (nhds 0))
    (k : Mat d) (hk : IsSkewMat k) :
    IsWeakSolutionOn (fun x ↦ b x + k) Set.univ Dv ↔
      IsWeakSolutionOn b Set.univ Dv := by
  have hlocalEq : ∀ q : ℕ,
      IsWeakSolutionOn (fun x ↦ b x + k) (localGradientCube d q) Dv ↔
        IsWeakSolutionOn b (localGradientCube d q) Dv := by
    intro q
    have hvL2 := memScalarL2_openCubeSet_of_growth hlocal.1.1 hgrowth q
    have hDL2 := memVectorL2_grad_openCubeSet_of_memH1sLoc
      hb hlocal (originCube d (q : ℤ))
    have hweak := hasWeakGradientOn_localGradientCube_of_memH1sLoc hlocal q
    exact isWeakSolutionOn_add_constSkew_iff
      (by simpa only [localGradientCube] using
        (isOpen_openCubeSet (originCube d (q : ℤ))))
      b hvL2 (fun i ↦ hDL2.eval i) hweak k hk
  constructor
  · intro h
    apply isWeakSolutionOn_univ_of_localGradientCube
    intro q
    exact (hlocalEq q).mp (h.mono (subset_univ _))
  · intro h
    apply isWeakSolutionOn_univ_of_localGradientCube
    intro q
    exact (hlocalEq q).mpr (h.mono (subset_univ _))

/-- Adding a constant skew matrix leaves the full Liouville class unchanged. -/
theorem memLiouvilleClass_add_constSkew_iff
    [NeZero d]
    {b : CoeffField d} {theta : ℝ}
    (hb : IsAELocallyUniformlyElliptic b)
    (k : Mat d) (hk : IsSkewMat k)
    (v : Vec d → ℝ) (Dv : Vec d → Vec d) :
    MemLiouvilleClass (fun x ↦ b x + k) theta v Dv ↔
      MemLiouvilleClass b theta v Dv := by
  constructor
  · intro h
    have hlocal := (memH1sLoc_add_constSkew_iff b k hk v Dv).mp h.1
    exact ⟨hlocal,
      (isWeakSolutionOn_univ_add_constSkew_iff hb hlocal h.2.2 k hk).mp
        h.2.1,
      h.2.2⟩
  · intro h
    exact ⟨(memH1sLoc_add_constSkew_iff b k hk v Dv).mpr h.1,
      (isWeakSolutionOn_univ_add_constSkew_iff hb h.1 h.2.2 k hk).mpr
        h.2.1,
      h.2.2⟩

end

end Root
end HighContrast
end HCPolySupport
