/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.CenteredEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffQuadraticReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseCutoffBoundReduction
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseToAnnealedAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakIntegrandDomination
public import LeanPool.HighContrastHomogenization.Support.Besov.Basic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bound
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Definitions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.QuantitativeCutoff

/-!
# High-contrast homogenization: Entry.Response.Cutoff.ResponseCutoffExistence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Existence of the Response Cutoff

HC bridge III, Step 6 of the cutoff estimate `e.response.cutoff.estimate` (`AK.HC` Lemma A.1 and
`(3.45)`-`(3.54)`): a response cutoff `φ` is a function supported in the adapted cell, taking
values in `[0, 2]`, of volume average one, and satisfying first- and second-derivative bounds at
the scale `3^t` in the grid's coordinates. This file proves that such a cutoff exists, building
it from the canonical product cube cutoff pushed forward along the grid map and normalized by its
own cell average, and records the elementary estimates the construction needs: a Bernoulli-type
bound, smoothness and continuity of the associated linear maps, and the norm bound on the second
iterated derivative of a scaled function.
-/

section
/-!
## HC bridge III: the cutoff kernel of Step 6 (AK.HC Lemma A.1 and (3.45)-(3.54))

This file contains four statements, each re-typing the same estimates onto the
carriers `respTauMinus`/`respEJMinus`/`respLsMinus`/`respWMinus`/`IsResponseCutoff`/... of
`ResponseBlockObjects.lean`.  No definition of `ResponseBlockObjects.lean` is changed; the
definition
below (`cutoffPairingOnCellAux`) is local to this file.  The first is the only
statement carried on the CoarseGraining reference geometry `Book.Ch02.cubeDomain Q`; the second
transports
it to the adapted cell `U_t` (`ScaleAverageSeminorm.lean`), the third is the variational
calculation, and the fourth combines them into the payload `RespCutoffBound` used at
`ResponseCutoffEstimate.lean`.  Paper: `p.response.transfer`, Step 6.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The reference-cube cutoff bound.  AK.HC Lemma A.1 / (A.4) on the reference cube domain
`cubeDomain Q`.

AK.HC Lemma A.1 / (A.4) -- the cutoff product-term weak-norm bound on the reference cube -- is
stated with the same signature as
`HCPoly/Provider/Response/DivCurlWeakNormTerm.lean`.  Each name in the
signature was checked
in the pinned CoarseGraining rev `8ec687c`:

* `Book.Ch02.cubeDomain` `Book/Ch02/MultiscaleEllipticity.lean`;
* `Book.Ch02.CoeffOn` `Book/Ch02/Setup.lean`;
* `cubeBesovNegativeVectorPartialSeminorm` `Deterministic/WeakNormInterfaces/Definitions.lean`;
* `cubeBesovScaleWeight` `Besov/Basic.lean`;
* `scalarCutoffGradientField`
  `Deterministic/CoarseCaccioppoli/EnergyBridge/QuantitativeCutoff/Basic.lean`;
* `cutoffProductTermOnCube`
  `Book/Ch05/Theorems/Section53/JUpperBoundWeakNorms/EnergyDensities.lean`;
* `cutoffProductScaledWeakNormCoeff`
  `Book/Ch05/Theorems/Section53/JUpperBoundWeakNorms/Basic.lean`;
* `canonicalMaximizerGradientDefectOnCube` / `canonicalMaximizerFluxDefectOnCube`
  `Book/Ch05/Theorems/Section53/JUpperBoundWeakNorms/CanonicalFields.lean`.

NO SIGNATURE DRIFT was found: all eight are argument-for-argument what the old declaration used,
and the Mathlib spelling `ContDiff ℝ (⊤ : ℕ∞)` is still the one the pinned CG package itself uses
(`.../JUpperBoundWeakNorms/Product/Bound.lean`).  The old proof discharges this from
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
(`.../JUpperBoundWeakNorms/Product/Bridge.lean`), which is present in the pinned rev. -/

omit [NeZero d] in
private theorem cutoff_inv_cancel {q : Mat d} (hq : IsUnit q) (y : Vec d) :
    matVecMul q⁻¹ (matVecMul q y) = y := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  rw [Geometry.matVecMul_eq_mulVec, Geometry.matVecMul_eq_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul q hdet, Matrix.one_mulVec]

omit [NeZero d] in
private theorem cutoff_continuous_apply (q : Mat d) :
    Continuous fun x : Vec d => matVecMul q x :=
  Continuous.matrix_mulVec continuous_const continuous_id

private theorem cutoff_bernoulli_bound (d : ℕ) [NeZero d] :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (d : ℝ))) ^ d := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hA : (-2 : ℝ) ≤ -(1 / (2 * (d : ℝ))) := by
    have : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith only [hd1]
    linarith only [this]
  have h := one_add_mul_le_pow hA d
  have hlhs : (1 : ℝ) + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) = 1 / 2 := by
    have hdne : (d : ℝ) ≠ 0 := by linarith only [hd1]
    field_simp
    norm_num
  have hrhs : (1 : ℝ) + -(1 / (2 * (d : ℝ))) = 1 - 1 / (2 * (d : ℝ)) := by ring
  rw [hlhs, hrhs] at h
  exact h

omit [NeZero d] in
private theorem cutoff_contDiff_matVecMul (M : Mat d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => matVecMul M x := by
  have h : (fun x : Vec d => matVecMul M x)
      = fun x : Vec d => (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) x := by
    funext x
    simp [Geometry.matVecMul_eq_mulVec]
  rw [h]
  exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).contDiff

omit [NeZero d] in
private theorem cutoff_contDiff_smul_comp (M : Mat d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => c • f (matVecMul M x) :=
  (hf.comp (cutoff_contDiff_matVecMul M)).const_smul c

omit [NeZero d] in
private theorem cutoff_norm_iteratedFDeriv_two_smul (c : ℝ) (f : Vec d → ℝ)
    (hf : ContDiff ℝ (2 : ℕ) f) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (fun y : Vec d => c • f y) x‖ = |c| * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hfun : (fun y : Vec d => c • f y) = c • f := rfl
  rw [hfun, iteratedFDeriv_const_smul_apply hf.contDiffAt, norm_smul, Real.norm_eq_abs]

omit [NeZero d] in
private theorem cutoff_half_le_volumeAverage {q : Mat d} [NeZero d] (hq : IsUnit q) (t : ℤ)
    (f : Vec d → ℝ) (hcont : Continuous f) (hnonneg : ∀ x, 0 ≤ f x) (hle : ∀ x, f x ≤ 1)
    (hone : ∀ y : Vec d, ‖y‖ ≤ (1 - 1 / (2 * (d : ℝ))) * ((1 / 2 : ℝ) * (3 : ℝ) ^ t) →
      f (matVecMul q y) = 1) :
    (1 / 2 : ℝ) ≤ volumeAverage (HighContrast.adaptedCell q t) f := by
  classical
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hd1]
  have hdet : q.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
  have hdetpos : 0 < |q.det| := abs_pos.mpr hdet
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  set ρ : ℝ := 1 - 1 / (2 * (d : ℝ)) with hρdef
  have hinv2 : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith only [hd1]
  have hρpos : 0 < ρ := by rw [hρdef]; linarith only [hinv2]
  set r : ℝ := ρ * ((1 / 2 : ℝ) * (3 : ℝ) ^ t) with hrdef
  have hrnonneg : (0 : ℝ) ≤ r := by rw [hrdef]; positivity
  clear_value ρ r
  have hUmeas : MeasurableSet (HighContrast.adaptedCell q t) := by
    rw [← adaptedCellTranslate_zero q t]
    exact (Geometry.isOpen_adaptedCellTranslate hq t 0).measurableSet
  have hvolU : (volume (HighContrast.adaptedCell q t)).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d :=
    Geometry.volume_adaptedCell_toReal q t
  have hvolUlt : volume (HighContrast.adaptedCell q t) < ∞ := by
    rw [Geometry.volume_adaptedCell]
    finiteness
  have hfint : IntegrableOn f (HighContrast.adaptedCell q t) := by
    refine IntegrableOn.of_bound hvolUlt hcont.aestronglyMeasurable.restrict 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact hle x
  set V : Set (Vec d) := matVecMul q '' Metric.closedBall (0 : Vec d) r with hVdef
  have hVcompact : IsCompact V :=
    (ProperSpace.isCompact_closedBall (0 : Vec d) r).image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hVmeas : MeasurableSet V := hVcompact.isClosed.measurableSet
  have hVsub : V ⊆ HighContrast.adaptedCell q t := by
    rintro x ⟨y, hy, hxy⟩
    refine ⟨y, ?_, hxy⟩
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have hyi : |y i| ≤ r := by
      have := norm_le_pi_norm y i
      rw [Real.norm_eq_abs] at this
      linarith only [hy, this]
    have hrlt : r < (1 / 2 : ℝ) * (3 : ℝ) ^ t := by
      rw [hrdef, hρdef]
      have hpos : 0 < 1 / (2 * (d : ℝ)) := by positivity
      have hlt : 1 - 1 / (2 * (d : ℝ)) < 1 := by linarith only [hpos]
      calc (1 - 1 / (2 * (d : ℝ))) * ((1 / 2 : ℝ) * (3 : ℝ) ^ t)
          < 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ t) :=
            mul_lt_mul_of_pos_right hlt (mul_pos (by norm_num) h3pos)
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ t := one_mul _
    have habs := abs_lt.mp (lt_of_le_of_lt hyi hrlt)
    exact ⟨by linarith only [habs.1], habs.2⟩
  have hfV : ∀ x ∈ V, f x = 1 := by
    rintro x ⟨y, hy, hxy⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [← hxy]
    exact hone y hy
  have hintV : ∫ x in V, f x = (volume V).toReal := by
    have h1 : ∫ x in V, f x = ∫ _ in V, (1 : ℝ) := setIntegral_congr_fun hVmeas hfV
    rw [h1, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hVvol : (volume V).toReal = |q.det| * (2 * r) ^ d := by
    have h : V = (fun v : Vec d => (0 : Vec d) + matVecMul q v) ''
        Metric.closedBall (0 : Vec d) r := by
      rw [hVdef]; ext x; simp
    rw [h, Transport.volume_image_affine, Real.volume_pi_closedBall _ hrnonneg, Fintype.card_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (pow_nonneg (by linarith only [hrnonneg]) d)]
  have hmono : ∫ x in V, f x ≤ ∫ x in HighContrast.adaptedCell q t, f x := by
    refine setIntegral_mono_set hfint ?_ ?_
    · filter_upwards with x using hnonneg x
    · exact LE.le.eventuallyLE hVsub
  have hkey : 2 * r = (3 : ℝ) ^ t * ρ := by rw [hrdef]; ring
  have hTS : (1 / 2 : ℝ) * ((3 : ℝ) ^ t) ^ d ≤ (2 * r) ^ d := by
    rw [hkey, mul_pow]
    have hb : (1 / 2 : ℝ) ≤ ρ ^ d := by rw [hρdef]; exact cutoff_bernoulli_bound d
    have h3d : (0 : ℝ) < ((3 : ℝ) ^ t) ^ d := by positivity
    calc (1 / 2 : ℝ) * ((3 : ℝ) ^ t) ^ d
        ≤ ρ ^ d * ((3 : ℝ) ^ t) ^ d := mul_le_mul_of_nonneg_right hb h3d.le
      _ = ((3 : ℝ) ^ t) ^ d * ρ ^ d := by ring
  have hPS : (0 : ℝ) < |q.det| * ((3 : ℝ) ^ t) ^ d := by positivity
  have hJ : |q.det| * ((1 / 2 : ℝ) * ((3 : ℝ) ^ t) ^ d) ≤
      ∫ x in HighContrast.adaptedCell q t, f x := by
    have h1 : |q.det| * ((1 / 2 : ℝ) * ((3 : ℝ) ^ t) ^ d) ≤ |q.det| * (2 * r) ^ d :=
      mul_le_mul_of_nonneg_left hTS (abs_nonneg _)
    rw [← hVvol, ← hintV] at h1
    exact h1.trans hmono
  have hAeq : volumeAverage (HighContrast.adaptedCell q t) f
      = ((volume (HighContrast.adaptedCell q t)).toReal)⁻¹ *
        ∫ x in HighContrast.adaptedCell q t, f x := rfl
  rw [hAeq, hvolU]
  calc (1 / 2 : ℝ)
      = (|q.det| * ((3 : ℝ) ^ t) ^ d)⁻¹ * (|q.det| * ((1 / 2 : ℝ) * ((3 : ℝ) ^ t) ^ d)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hPS.le)

private theorem cutoff_reference_cube_geometry (Q0 : TriadicCube d) (t : ℤ)
    (ρ₁ ρ₂ : ℝ) (hρ₁pos : 0 < ρ₁) (hρ₂lt : ρ₂ < 1)
    (hcenter : ∀ i, cubeCenter Q0 i = 0)
    (hradius : cubeRadius Q0 = (1 / 2 : ℝ) * (3 : ℝ) ^ t) :
    scaledClosedCubeSet Q0 ρ₂ ⊆ HighContrast.centeredCube d t ∧
      scaledClosedCubeSet Q0 ρ₁ = Metric.closedBall (0 : Vec d) (ρ₁ * cubeRadius Q0) := by
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hsub2 : scaledClosedCubeSet Q0 ρ₂ ⊆ HighContrast.centeredCube d t := by
    intro y hy
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    have h := hy i
    rw [hcenter i, sub_zero, hradius] at h
    have hlt : ρ₂ * ((1 / 2 : ℝ) * (3 : ℝ) ^ t) < (1 / 2 : ℝ) * (3 : ℝ) ^ t := by
      calc ρ₂ * ((1 / 2 : ℝ) * (3 : ℝ) ^ t)
          < 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ t) :=
            mul_lt_mul_of_pos_right hρ₂lt (mul_pos (by norm_num) h3pos)
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ t := one_mul _
    have habs := abs_lt.mp (lt_of_le_of_lt h hlt)
    exact ⟨by linarith only [habs.1], habs.2⟩
  have hball : scaledClosedCubeSet Q0 ρ₁ = Metric.closedBall (0 : Vec d) (ρ₁ * cubeRadius Q0) := by
    ext y
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (mul_nonneg hρ₁pos.le (cubeRadius_nonneg Q0))]
    constructor
    · intro hy i
      have := hy i
      rw [hcenter i, sub_zero] at this
      rwa [Real.norm_eq_abs]
    · intro hy i
      have := hy i
      rw [Real.norm_eq_abs] at this
      rw [hcenter i, sub_zero]
      exact this
  exact ⟨hsub2, hball⟩

/-- The cutoff class `IsResponseCutoff` (`ResponseBlockObjects.lean`) is nonempty on every
invertible
grid.

A pullback Lipschitz constant `3^(-t)` carrying no dimensional factor is too small: a point of a
cube of side `3^t` is at sup-distance at most `3^t/2` from the complement, so such a cutoff is at
most `1/2` everywhere and cannot have mean one.  The constant `32 * d ^ 2 * 3 ^ (-t)` repairs this,
and a PIECEWISE-LINEAR witness attains it.

The class also carries the four conjuncts that the reference-cube cutoff bound consumes --
`ContDiff R (top : N-infty) phi`,
`HasCompactSupport phi`, `tsupport phi subseteq adaptedCell q t` and the second-derivative bound
`1024 * d ^ 4 * Theta ^ 2 * 3 ^ (-2 * t)`, with the universal profile factor `Theta` (see the
docstring of `IsResponseCutoff`) -- and the witness is built here as a genuinely smooth one.

The witness is the adapted avatar of the construction in
`HCPoly/Provider/Response/CutoffBasic.lean`, `adaptedPreYoungCutoff`, assembled from the
same two objects of the pinned CoarseGraining package: the canonical product cube cutoff
`QuantitativeCubeCutoff.canonicalFun Q rho1 rho2`
(`HCPolySupport/Sobolev/Foundations/QuantitativeCutoff.lean`) built on
`smoothTransitionProfile` (`.../Cutoff/Profile.lean`), taken on the reference cube
`Q = originCube d t` at `rho1 = 1 - 1/(2d)`, `rho2 = 1 - 1/(4d)`, normalized by its own cell
average `A` and pushed forward by `q`.

The five constants come out exactly as in the earlier construction.  The collar is
`(rho2 - rho1) * cubeRadius Q = 3^t / (8 d)`, so
`canonicalFun_gradient_bound` gives `‖D phi_0‖ <= 16 d^2 Theta 3^(-t)` and
`canonicalFun_hessian_bound` gives `‖D^2 phi_0‖ <= 512 d^4 Theta^2 3^(-2t)`; the normalization
costs a factor `A⁻¹ <= 2`, since `phi_0 = 1` on the inner cube of relative radius `rho1` and
`(1 - 1/(2d))^d >= 1/2` by Bernoulli (`cutoff_bernoulli_bound`), which also bounds the cutoff by
`2`.
Doubling the two bounds gives precisely the class constants `32 d^2 Theta 3^(-t)` and
`1024 d^4 Theta^2 3^(-2t)`.  Compact support and `tsupport phi subseteq adaptedCell q t` come
from `rho2 < 1`. -/
theorem exists_isResponseCutoff {q : Mat d} (hq : IsUnit q) (t : ℤ) :
    ∃ φ : Vec d → ℝ, IsResponseCutoff q t φ := by
  classical
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hd1]
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hdet : q.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
  have hdetpos : 0 < |q.det| := abs_pos.mpr hdet
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-t) := by positivity
  -- the reference cube and the two relative radii
  set Q0 : TriadicCube d := originCube d t with hQ0
  have hcenter : ∀ i, cubeCenter Q0 i = 0 := by
    intro i; simp [hQ0, cubeCenter, originCube]
  have hradius : cubeRadius Q0 = (1 / 2 : ℝ) * (3 : ℝ) ^ t := by
    simp [hQ0, cubeRadius, cubeScaleFactor, originCube]
  clear_value Q0
  set ρ₁ : ℝ := 1 - 1 / (2 * (d : ℝ)) with hρ₁def
  set ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ)) with hρ₂def
  have hinv2 : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith only [hd1]
  have hinv4 : 1 / (4 * (d : ℝ)) < 1 / (2 * (d : ℝ)) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith only [hd1]
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁def]; linarith only [hinv2]
  have hρ₁₂ : ρ₁ < ρ₂ := by rw [hρ₁def, hρ₂def]; linarith only [hinv4]
  have hρ₂lt : ρ₂ < 1 := by
    rw [hρ₂def]
    have : 0 < 1 / (4 * (d : ℝ)) := by positivity
    linarith only [this]
  have hρ₂nonneg : (0 : ℝ) ≤ ρ₂ := le_of_lt (lt_trans hρ₁pos hρ₁₂)
  have hdiff : ρ₂ - ρ₁ = 1 / (4 * (d : ℝ)) := by
    rw [hρ₁def, hρ₂def]; field_simp; ring
  have hcollar : (ρ₂ - ρ₁) * cubeRadius Q0 = (3 : ℝ) ^ t / (8 * (d : ℝ)) := by
    rw [hdiff, hradius]; field_simp; ring
  have htwodiv : 2 / ((ρ₂ - ρ₁) * cubeRadius Q0) = 16 * (d : ℝ) * (3 : ℝ) ^ (-t) := by
    rw [hcollar, zpow_neg]
    field_simp
    ring
  clear_value ρ₁ ρ₂
  -- the smooth cutoff on the reference cube
  set ψ : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q0 ρ₁ ρ₂ with hψdef
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    QuantitativeCubeCutoff.canonicalFun_smooth Q0 hρ₁pos hρ₁₂
  have hψdiff : Differentiable ℝ ψ := hψsmooth.differentiable (by simp)
  have hψ2 : ContDiff ℝ (2 : ℕ) ψ := hψsmooth.of_le (by norm_cast)
  have hψnonneg : ∀ x, 0 ≤ ψ x := QuantitativeCubeCutoff.canonicalFun_nonneg Q0 ρ₁ ρ₂
  have hψle : ∀ x, ψ x ≤ 1 := QuantitativeCubeCutoff.canonicalFun_le_one Q0 ρ₁ ρ₂
  have hψone : ∀ x ∈ scaledClosedCubeSet Q0 ρ₁, ψ x = 1 := fun x hx =>
    QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner hρ₁pos hρ₁₂ hx
  have hψsupp : Function.support ψ ⊆ scaledOpenCubeSet Q0 ρ₂ :=
    QuantitativeCubeCutoff.canonicalFun_support_subset hρ₁pos hρ₁₂
  have hΘ : responseCutoffProfileConst
      = max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound) := rfl
  have hΘpos : (0 : ℝ) < responseCutoffProfileConst := responseCutoffProfileConst_pos
  have hDΘ : smoothTransitionProfile.derivBound ≤ responseCutoffProfileConst := by
    rw [hΘ]; exact le_max_of_le_right (le_max_left _ _)
  have hψgrad : ∀ x, ‖fderiv ℝ ψ x‖ ≤
      16 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by
    intro x
    have h := QuantitativeCubeCutoff.canonicalFun_gradient_bound Q0 hρ₁pos hρ₁₂ x
    rw [htwodiv] at h
    calc ‖fderiv ℝ ψ x‖
        ≤ (d : ℝ) * smoothTransitionProfile.derivBound * (16 * (d : ℝ) * (3 : ℝ) ^ (-t)) := h
      _ = (16 * (d : ℝ) ^ 2 * (3 : ℝ) ^ (-t)) * smoothTransitionProfile.derivBound := by ring
      _ ≤ (16 * (d : ℝ) ^ 2 * (3 : ℝ) ^ (-t)) * responseCutoffProfileConst :=
          mul_le_mul_of_nonneg_left hDΘ (by positivity)
      _ = 16 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by ring
  have hsq : ((3 : ℝ) ^ (-t)) ^ 2 = (3 : ℝ) ^ (-2 * t) := by
    rw [pow_two, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hψhess : ∀ x, ‖iteratedFDeriv ℝ 2 ψ x‖ ≤
      512 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t) := by
    intro x
    have h := QuantitativeCubeCutoff.canonicalFun_hessian_bound Q0 hρ₁pos hρ₁₂ x
    rw [htwodiv, ← hΘ] at h
    calc ‖iteratedFDeriv ℝ 2 ψ x‖
        ≤ 2 * (d : ℝ) ^ 2 *
            (responseCutoffProfileConst * (16 * (d : ℝ) * (3 : ℝ) ^ (-t))) ^ 2 := h
      _ = 512 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (((3 : ℝ) ^ (-t)) ^ 2) := by ring
      _ = 512 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t) := by
          rw [hsq]
  clear_value ψ
  -- geometry of the reference cube
  obtain ⟨hsub2, hball⟩ :=
    cutoff_reference_cube_geometry Q0 t ρ₁ ρ₂ hρ₁pos hρ₂lt hcenter hradius
  -- the pushforward cutoff, its support and its normalizing average
  set η : Vec d → ℝ := fun x => ψ (matVecMul q⁻¹ x) with hηdef
  have hηapp : ∀ x : Vec d, η x = ψ (matVecMul q⁻¹ x) := fun x => by rw [hηdef]
  have hηpull : ∀ y : Vec d, η (matVecMul q y) = ψ y := by
    intro y; rw [hηapp, cutoff_inv_cancel hq]
  have hηnonneg : ∀ x, 0 ≤ η x := fun x => by rw [hηapp]; exact hψnonneg _
  have hηle : ∀ x, η x ≤ 1 := fun x => by rw [hηapp]; exact hψle _
  have hηcont : Continuous η := by
    rw [hηdef]; exact hψsmooth.continuous.comp (cutoff_continuous_apply q⁻¹)
  have hKcompact : IsCompact (matVecMul q '' scaledClosedCubeSet Q0 ρ₂) :=
    (isCompact_scaledClosedCubeSet Q0 hρ₂nonneg).image (cutoff_continuous_apply q)
  have hsuppK : ∀ x : Vec d, η x ≠ 0 → x ∈ matVecMul q '' scaledClosedCubeSet Q0 ρ₂ := by
    intro x hx
    rw [hηapp] at hx
    have h2 := hψsupp hx
    exact ⟨matVecMul q⁻¹ x, fun i => le_of_lt (h2 i), matVecMul_matVecMul_inv_cancel hq x⟩
  have hηzero : ∀ x : Vec d, x ∉ HighContrast.adaptedCell q t → η x = 0 := by
    intro x hx
    by_contra hcon
    obtain ⟨y, hy, hxy⟩ := hsuppK x hcon
    exact hx ⟨y, hsub2 hy, hxy⟩
  clear_value η
  have hAge : (1 / 2 : ℝ) ≤ volumeAverage (HighContrast.adaptedCell q t) η := by
    refine cutoff_half_le_volumeAverage hq t η hηcont hηnonneg hηle ?_
    intro y hy
    rw [hηpull y]
    refine hψone y ?_
    rw [hball, Metric.mem_closedBall, dist_zero_right, hρ₁def, hradius]
    exact hy
  set A : ℝ := volumeAverage (HighContrast.adaptedCell q t) η with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith only [hAge]
  have hAinvpos : 0 < A⁻¹ := inv_pos.mpr hApos
  have hAinv : A⁻¹ ≤ 2 := by
    have h1 : A⁻¹ * A = 1 := inv_mul_cancel₀ hApos.ne'
    have hAgeA : (1 / 2 : ℝ) ≤ A := by rw [hAdef]; exact hAge
    have h3 : A⁻¹ * A ≤ 2 * A := by rw [h1]; linarith only [hAgeA]
    exact le_of_mul_le_mul_right h3 hApos
  clear_value A
  have hsuppmul : Function.support (fun x : Vec d => A⁻¹ * η x) ⊆
      matVecMul q '' scaledClosedCubeSet Q0 ρ₂ := by
    intro x hx
    rw [Function.mem_support] at hx
    refine hsuppK x ?_
    intro h0
    exact hx (by rw [h0, mul_zero])
  refine ⟨fun x => A⁻¹ * η x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg hAinvpos.le (hηnonneg x)
  · intro x
    have hmm := mul_le_mul hAinv (hηle x) (hηnonneg x) (by norm_num : (0 : ℝ) ≤ 2)
    simpa using hmm
  · intro x hx
    simp only
    rw [hηzero x hx, mul_zero]
  · have h1 : volumeAverage (HighContrast.adaptedCell q t) (fun x => A⁻¹ * η x) = A⁻¹ * A := by
      rw [hAdef]
      unfold volumeAverage
      rw [integral_const_mul]
      ring
    rw [h1, inv_mul_cancel₀ hApos.ne']
  · have hfun : (fun y : Vec d => A⁻¹ * η (matVecMul q y)) = fun y : Vec d => A⁻¹ * ψ y :=
      funext fun y => by rw [hηpull y]
    rw [hfun]
    apply lipschitzWith_of_nnnorm_fderiv_le (hψdiff.const_mul A⁻¹)
    intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _
        (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2) hΘpos.le)
          h3npos.le)]
    rw [fderiv_const_mul (hψdiff x) A⁻¹, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hAinvpos.le]
    calc A⁻¹ * ‖fderiv ℝ ψ x‖
        ≤ 2 * (16 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) :=
          mul_le_mul hAinv (hψgrad x) (norm_nonneg _) (by norm_num)
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by ring
  · have hfun : (fun x : Vec d => A⁻¹ * η x)
        = fun x : Vec d => A⁻¹ • ψ (matVecMul q⁻¹ x) :=
      funext fun x => by rw [hηapp x, smul_eq_mul]
    rw [hfun]
    exact cutoff_contDiff_smul_comp q⁻¹ hψsmooth A⁻¹
  · exact HasCompactSupport.of_support_subset_isCompact hKcompact hsuppmul
  · refine (closure_minimal hsuppmul hKcompact.isClosed).trans ?_
    rintro x ⟨y, hy, hxy⟩
    exact ⟨y, hsub2 hy, hxy⟩
  · intro x
    have hfun : (fun y : Vec d => A⁻¹ * η (matVecMul q y)) = fun y : Vec d => A⁻¹ • ψ y :=
      funext fun y => by rw [hηpull y, smul_eq_mul]
    rw [hfun]
    have heq := cutoff_norm_iteratedFDeriv_two_smul A⁻¹ ψ hψ2 x
    rw [abs_of_nonneg hAinvpos.le] at heq
    refine le_trans (le_of_eq heq) ?_
    calc A⁻¹ * ‖iteratedFDeriv ℝ 2 ψ x‖
        ≤ 2 * (512 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t)) :=
          mul_le_mul hAinv (hψhess x) (norm_nonneg _) (by norm_num)
      _ = 1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t) := by ring

/-! ### Reduction helpers for the transport.

Four reductions that are independent of the analytic transport:

* the degenerate branch: if the grid is singular the adapted cell is Lebesgue-null, so every
  `volumeAverage` on it -- in particular `cutoffPairingOnCellAux` -- is the junk value `0`;
* `respWeakEnergy` is always nonnegative (an `sSup` of a set of nonnegative reals, with the two
  Mathlib junk branches `Real.sSup_empty` and `Real.sSup_of_not_bddAbove` handled);
* the `sSup` step: a maximizer family is a member of `respWeakEnergySet`, so -- using the
  boundedness `bddAbove_respWeakEnergySet_respWMinus` / `...respWPlus` of
  `HCPoly/Entry/Response/Core/ScalarMaximizerExistence.lean`, which needs `IsUnit (respGrid jStar
  F)` -- its own weak
  energy is at most `W^±`.

Together they reduce the transport to the PATHWISE analytic estimate. -/

/-! ## Transport of the reference-cube cutoff bound to the adapted cell `U_t`.

This is the composition of
`ofReal_partialSeminorm_metricPullback_fst_le_separate` /
`…_snd_le_separate` (`HCPoly/Provider/Response/AdaptedWeakProduct.lean`
and) with the reference-cube cutoff product-term weak-norm bound above and
`explicitRoundedGrid_metricFrobenius_product_le` (`AdaptedWeakProduct.lean`).  In the present
vocabulary the first two are `partialSeminorm_pullback_fst_le` / `…_snd_le` and the third is
`explicitRoundedGrid_metricFrobenius_product_le`, all three stated in
`HCPoly/Entry/Response/Kernel/ScaleAverageSeminorm.lean`. -/

/-! ### The three ingredients of `integrable_besovSeminorm_sq_respCell`.

`integrable_besovSeminorm_sq_respCell` below is proved from
three named private lemmas by the reduction (`Integrable = AEStronglyMeasurable ∧
HasFiniteIntegral`, the finite integral by domination).  Two of the three are analytic; the third,
`hc3_aestronglyMeasurable_besovSeminorm_sq`, is a statement-level gap recorded in
its own docstring. -/

end

end HCPolySupport.HighContrast.Multiscale
end
