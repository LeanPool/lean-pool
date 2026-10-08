/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangleCore
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalAssembly
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Analytic.CoefficientLocality
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangle

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `ExactRootBallTriangle`, proved

Exactly one analytic hypothesis stands between this module and a
hypothesis-free statement: the weighted-energy triangle inequality on the
exact-root
pullback ball, for the two fields the large-scale C¹ slope approximation terminal compares.  This
module
discharges it.

`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangleCore`
supplies Minkowski for
`‖s^{1/2} ·‖_{L_underlined²(U)}` on an arbitrary measurable set of finite volume, for two
**square-integrable** fields and an **almost everywhere** elliptic coefficient.
Three obligations remain, and this module proves them for the exact instance.

1. *The coefficient.*  `bRef = affineCoefficient q _ ⇑(normalizedCenteredCoeff
   a abar hS).1` is exactly the representative of the `affinePullbackCoeffSpace q _
   (normalizedCenteredCoeff a abar hS)`
   (`affinePullbackCoeffSpace_ae`), whose `CoeffSpace` membership *is* the
   almost-everywhere ellipticity, and whose representative is strongly
   measurable because it is the coercion of an `AEEqFun`.
2. *The solution's pullback gradient.*  `MemH1a` on a bounded set gives
   `IntegrableOn (vecNormSq ∘ Du)` (`integrableOn_vecNormSq_grad_of_memH1a_class`
   — the ellipsoid is bounded), hence `MemVectorL2 (ellipsoid abar R) Du`; the
   invertible pullback carries it to `matImage q⁻¹ (ellipsoid abar R) =
   closedNormBall d R`, and composing with the constant matrix `q` is a
   continuous linear map.
3. *The affine-plus-corrector field.*  The global gradient representative of a
   `NormalizedLocalH1Carrier` is square-integrable on every exhaustion cube
   (`memLp_globalGradientRepresentative`), and the closed ball sits inside one
   of them (`closedNormBall_subset_outerCube`); the constant slope `e` is
   square-integrable because the ball has finite volume.

No hypothesis on `R` is needed: `R ≤ 0` is covered because the two measure
facts used are the finiteness of the ball's volume — true for every `R` — and
the null case, which `weightedGradNorm_of_volume_eq_zero` closes with no
ellipticity at all.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Square integrability of the two fields -/

/-- The gradient slot of an `H¹_a(U)` pair on a bounded `U` has an honest
vector-valued `L²` realization.  The `H¹_{a,0}` analogue is (`memVectorL2_grad_of_memH1a0`); this
is the same argument with the bounded-`U`
integrability lemma of the wider class. -/
theorem memVectorL2_grad_of_memH1a {U : Set (Vec d)} {b : CoeffField d}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hUb : Bornology.IsBounded U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b U u Du) :
    MemVectorL2 U Du := by
  have hsq : IntegrableOn (fun x ↦ vecNormSq (Du x)) U volume :=
    integrableOn_vecNormSq_grad_of_memH1a_class hlam hell hUb hu
  have hcoord : ∀ i, MemScalarL2 U fun x ↦ Du x i := by
    intro i
    apply (memLp_two_iff_integrable_sq (hu.1.2 i)).2
    refine hsq.mono' ((hu.1.2 i).pow 2) ?_
    filter_upwards with x
    have hi : 0 ≤ Du x i ^ 2 := sq_nonneg _
    have hvec : 0 ≤ vecNormSq (Du x) := vecNormSq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hi, abs_of_nonneg hvec] using
      sq_apply_le_vecNormSq (Du x) i
  simpa [MemVectorL2, volumeMeasureOn] using
    (MemLp.of_eval hcoord : MemLp Du 2 (volumeMeasureOn U))

/-- Square integrability of a vector field is carried by an invertible linear
pullback.  Scalar version as `memL2On_affinePullback`; the proof is the
same, the codomain playing no role. -/
theorem memVectorL2_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 (matImage L⁻¹ U) fun y ↦ f (matVecMul L y) := by
  have hfmap : MemLp f 2
      (Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U))) := by
    rw [map_restrict_volume_affinePullback hL hU]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hfmap.comp_of_map (continuous_matVecMul L).aemeasurable

/-- A constant matrix acts on square-integrable fields. -/
theorem memVectorL2_matVecMul {U : Set (Vec d)} (L : Mat d)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U fun y ↦ matVecMul L (f y) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  exact T.comp_memLp' hf

/-! ## The two measure facts on the closed ball, at an arbitrary radius -/

/-- The closed pullback ball is measurable: it is a sublevel set of the
continuous `vecNormSq`. -/
theorem measurableSet_closedNormBall (d : ℕ) (R : ℝ) :
    MeasurableSet (closedNormBall d R) :=
  (isClosed_le continuous_vecNormSq continuous_const).measurableSet

private theorem closedNormBall_subset_abs_succ (d : ℕ) (R : ℝ) :
    closedNormBall d R ⊆ closedNormBall d (|R| + 1) := by
  intro y hy
  have hy' : vecNormSq y ≤ R ^ 2 := hy
  have habs : |R| ≤ |R| + 1 := by linarith only [zero_le_one (α := ℝ)]
  have hsq : R ^ 2 ≤ (|R| + 1) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg R) habs 2
    rwa [sq_abs] at h
  exact le_trans hy' hsq

/-- The closed pullback ball has finite volume at **every** real radius. -/
theorem volume_closedNormBall_ne_top' (R : ℝ) :
    volume (closedNormBall d R) ≠ ⊤ := by
  have hpos : (0 : ℝ) < |R| + 1 := by linarith only [abs_nonneg R]
  exact ne_top_of_le_ne_top (volume_closedNormBall_ne_top hpos)
    (measure_mono (closedNormBall_subset_abs_succ d R))

/-- The closed pullback ball at an arbitrary radius sits inside one member of
the centered cube exhaustion. -/
theorem exists_closedNormBall_subset_localGradientCube (d : ℕ) (R : ℝ) :
    ∃ n : ℕ, closedNormBall d R ⊆ localGradientCube d n := by
  have hpos : (0 : ℝ) < |R| + 1 := by linarith only [abs_nonneg R]
  have hfour : (0 : ℝ) < 2 * (2 * (|R| + 1)) := by linarith only [hpos]
  have hone : (1 : ℝ) ≤ 2 * (2 * (|R| + 1)) := by linarith only [abs_nonneg R]
  have hG0 : 0 ≤ outerTriadicGeneration (2 * (2 * (|R| + 1))) hfour :=
    outerTriadicGeneration_nonneg_of_one_le hfour hone
  refine ⟨(outerTriadicGeneration (2 * (2 * (|R| + 1))) hfour).toNat, ?_⟩
  have hcast :
      (((outerTriadicGeneration (2 * (2 * (|R| + 1))) hfour).toNat : ℕ) : ℤ) =
        outerTriadicGeneration (2 * (2 * (|R| + 1))) hfour :=
    Int.toNat_of_nonneg hG0
  have hcube := closedNormBall_subset_outerCube (d := d) hpos
  rw [localGradientCube, hcast]
  exact (closedNormBall_subset_abs_succ d R).trans hcube

/-! ## Obligation 2: the solution's exact-root pullback gradient -/

/-- The exact-root pullback of an `H¹_a(E_R)` gradient is square-integrable on
the closed pullback ball. -/
theorem memVectorL2_pullbackGrad_closedNormBall [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) (a : CoeffSpace d) (R : ℝ)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a (⇑a.1 : CoeffField d) (ellipsoid abar R) u Du) :
    MemVectorL2 (closedNormBall d R)
      fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) := by
  obtain ⟨lam, Lam, c, hlam, -, hell, hac⟩ :=
    a.2.exists_ae_isEllipticMatrix_ae_eq_restrict (isBounded_ellipsoid hS R)
  have hDu : MemVectorL2 (ellipsoid abar R) Du :=
    memVectorL2_grad_of_memH1a (Lam := Lam) hlam hell (isBounded_ellipsoid hS R)
      ((memH1a_congr_coeff hac u Du).mp hu)
  have hqdet : IsUnit (Selection.normalizedRoot (symmPart abar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (normalizedRoot_posDef_of_posDef hS).isUnit
  have hpull := memVectorL2_affinePullback hqdet (measurableSet_ellipsoid abar R) hDu
  rw [matImage_normalizedRoot_inv_ellipsoid_eq_closedNormBall hS R] at hpull
  exact memVectorL2_matVecMul _ hpull

/-! ## Obligation 3: the affine-plus-corrector field -/

/-- An affine slope plus the global gradient representative of a normalized
local `H¹` carrier is square-integrable on the closed pullback ball. -/
theorem memVectorL2_affineCorrector_closedNormBall
    (z : NormalizedLocalH1Carrier d) (e : Vec d) (R : ℝ) :
    MemVectorL2 (closedNormBall d R)
      fun y ↦ e + z.globalGradientRepresentative y := by
  obtain ⟨n, hn⟩ := exists_closedNormBall_subset_localGradientCube d R
  have hz : MemVectorL2 (closedNormBall d R) z.globalGradientRepresentative :=
    MemLp.mono_measure (Measure.restrict_mono hn le_rfl)
      (z.memLp_globalGradientRepresentative n)
  have hfin : IsFiniteMeasure (volume.restrict (closedNormBall d R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top (volume_closedNormBall_ne_top' R)
  exact (memLp_const e).add hz

/-! ## The residue, discharged -/

/-- **The weighted-energy triangle inequality on the exact-root pullback
ball**, for exactly the two fields the large-scale C¹ slope approximation terminal compares.  This
is the sole
hypothesis of `exactRootGaugeTerminal_onReconciled_of_ballTriangle`. -/
theorem exactRootBallTriangle (d : ℕ) [NeZero d] : ExactRootBallTriangle d := by
  intro abar hS a R u Du hu aId Phi hPhi e
  have hqdet : IsUnit (Selection.normalizedRoot (symmPart abar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (normalizedRoot_posDef_of_posDef hS).isUnit
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    (affinePullbackCoeffSpace (Selection.normalizedRoot (symmPart abar)) hqdet
      (normalizedCenteredCoeff a abar hS)).2.exists_ae_isEllipticMatrix_restrict
      (measurableSet_closedNormBall d R) (isBounded_closedNormBall d R)
  exact weightedGradNorm_sub_le_add_of_aeElliptic
    (measurableSet_closedNormBall d R) (volume_closedNormBall_ne_top' R) hlam hle
    (MeasureTheory.AEEqFun.stronglyMeasurable _)
    (affinePullbackCoeffSpace_ae _ hqdet _) hell
    (memVectorL2_pullbackGrad_closedNormBall hS a R hu)
    (memVectorL2_affineCorrector_closedNormBall (Phi e) e R)

end

end CorrectorComposition
end HighContrast
end HCPolySupport
