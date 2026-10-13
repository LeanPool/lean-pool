/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ResponseCommonDomination
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.HalfScaleExponentBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar

/-!
# CombineBadEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The observation-scale bad-event estimate

## The two source displays

With `delta_1 = 10^9 E^2 gamma`, this module proves, at the observation
scale `m` and for every cutoff `L < m`,

* `P[B_m] <= C(d) delta_1^2`, and
* `E[J(cu_{m-1}, p, q; a_L) 1_{B_m}] <= C(d) delta_1^2`,

where `B_m` is the complement of the good event `e.goodevent.combine`, read at
the halved discount and exponent `q = 2` (see below).

## Route

The heart of the argument -- the observation-scale fourth-moment transport of
the preceding-error clause, i.e. the weighted-depth split at scale `L`, the
coarse descendant averages controlled by the generalized `Gamma_{1/4}` triangle
inequality, the finite-maximum cost `C(1 + log N)^4`, and the geometrically
summable fine tail -- is already proved as
`observationScaleFiniteCover_sq_isBigOWith_gammaQuarter`, which transports the
lower clause from the cutoff cube at discount `1/16` to the observation cube at
discount `1/8` with a dimension-only constant.  This module

* collapses the resulting two-term amplitude to the single scale `C(d) E^2 gamma`
  using the regime fact `gamma <= E^{-10}` (the rare amplitude
  `exp(-2 E^{-3} gamma^{-1})` is dominated by `E^2 gamma`; see
  `exp_neg_sq_le_of_regime`);
* converts that `Gamma_{1/4}` control into the fourth moment
  `E[mathcal E_{1/8, infinity, 2}(cu_m; a_L, sigmabar_L)^4] <= C(d) (E^2 gamma)^2`;
* concludes both displays by Markov's inequality and the a.e. directional
  domination `J <= mathcal E^2` of `ResponseCommonDomination.lean`.

## The good event carried here

`observationScaleBadEvent` is the complement of `e.goodevent.combine` at the
*printed* discount `s = 1/4` and *printed* exponent `q = 1`, written in the
Section 3 inverse convention on the proved measurable observables:

`B_m = {sigmabar_L^{-1} Lambda_{1/4,1}(cu_m; a_L) <= 2 and
        sigmabar_L lambda_{1/4,1}^{-1}(cu_m; a_L) <= 2}^c`.

`mem_observationScaleBadEvent_iff` certifies that this is, at every sample
point, the complement of the printed three-clause event
`{sigmabar_L / 2 <= lambda_{1/4,1} <= Lambda_{1/4,1} <= 2 sigmabar_L}`: the
middle clause is a theorem (`lambdaSq_le_LambdaSq_oneCube`), and the outer two
transpose because the lower multiscale ellipticity of the actual cutoff is
strictly positive (`Ch02.lambdaSq_finite_pos`), so Lean's `0⁻¹ = 0` convention
cannot separate the two readings.

The half-discount comparison used to reach the `q = 2` envelope is sharp --
constant `1` -- because the two geometric weight families literally coincide:
`geometricWeight s q n = (1 - 3^{-s q}) 3^{-s q n}` depends on `(s, q)` only
through `s q`.  It is therefore Jensen's inequality for the geometric
probability weights, whose Jensen half is already inside CoarseGraining.

## References

* ABK26, Step 4 of `p.combine.under.S`, and the good event
  `e.goodevent.combine`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## Elementary arithmetic -/

/-- The halved discount `t = s / 2 = 1/8` is positive.  It is public so that
consumers can spell the same observables as `observationScaleBadEvent`. -/
theorem eighth_pos : (0 : ℝ) < 1 / 8 := by norm_num

/-- `exp (-x) <= 2 / x ^ 2` for positive `x`. -/
private theorem exp_neg_le_two_div_sq {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 2 / x ^ 2 := by
  have hquad : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx.le
  have hsq : 0 < x ^ 2 := by positivity
  have hlow : x ^ 2 / 2 ≤ Real.exp x := by nlinarith
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [hneg, inv_le_iff_one_le_mul₀ hexp, div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith

/-- **The regime collapse.**  Under the induction regime `gamma <= E^{-10}` the
squared rare amplitude of the lower clause is dominated by `E ^ 2 * gamma`, so
the two-term observation-scale amplitude collapses to the single scale `delta_1
= 10 ^ 9 * E ^ 2 * gamma`. -/
private theorem exp_neg_sq_le_of_regime {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma : 0 < gamma) (hregime : gamma ≤ (E⁻¹) ^ 10) :
    Real.exp (-(E⁻¹ ^ 3 * gamma⁻¹)) ^ 2 ≤ E ^ 2 * gamma := by
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hEinv : 0 < E⁻¹ := inv_pos.mpr hEpos
  have hx : 0 < E⁻¹ ^ 3 * gamma⁻¹ := by positivity
  set x : ℝ := E⁻¹ ^ 3 * gamma⁻¹ with hxdef
  have hsq : Real.exp (-x) ^ 2 = Real.exp (-(2 * x)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htwo : 0 < 2 * x := by linarith
  have hbound : Real.exp (-(2 * x)) ≤ 2 / (2 * x) ^ 2 := exp_neg_le_two_div_sq htwo
  have hxval : (2 * x) ^ 2 = 4 * (E⁻¹ ^ 6 * (gamma⁻¹) ^ 2) := by
    rw [hxdef]
    ring
  have hgammaInv : 0 < gamma⁻¹ := inv_pos.mpr hgamma
  have hEsix : E⁻¹ ^ 6 = (E ^ 6)⁻¹ := by
    rw [inv_pow]
  have hEten : (E⁻¹) ^ 10 = (E ^ 10)⁻¹ := by
    rw [inv_pow]
  have hquot : 2 / (2 * x) ^ 2 = E ^ 6 * gamma ^ 2 / 2 := by
    rw [hxval, hEsix]
    field_simp
    norm_num
  have hgammaLe : gamma ≤ (E ^ 10)⁻¹ := by
    rw [← hEten]
    exact hregime
  have hE10 : 0 < E ^ 10 := by positivity
  have hgammaE : E ^ 10 * gamma ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hgammaLe hE10.le
    rwa [mul_inv_cancel₀ hE10.ne'] at this
  have hE6le : E ^ 6 * gamma ^ 2 / 2 ≤ E ^ 2 * gamma := by
    have hE4 : (1 : ℝ) ≤ E ^ 4 := one_le_pow₀ hE
    have hfactor : E ^ 6 * gamma ^ 2 = (E ^ 10 * gamma) * gamma / E ^ 4 := by
      field_simp
    have hstep : (E ^ 10 * gamma) * gamma / E ^ 4 ≤ gamma := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < E ^ 4)]
      nlinarith [hgamma.le]
    have hgammaLeTwo : E ^ 6 * gamma ^ 2 ≤ gamma := by
      rw [hfactor]; exact hstep
    have hEtwo : (1 : ℝ) ≤ E ^ 2 := one_le_pow₀ hE
    nlinarith [hgamma.le]
  calc
    Real.exp (-x) ^ 2 = Real.exp (-(2 * x)) := hsq
    _ ≤ 2 / (2 * x) ^ 2 := hbound
    _ = E ^ 6 * gamma ^ 2 / 2 := hquot
    _ ≤ E ^ 2 * gamma := hE6le

/-- The quadratic ellipticity gate: below the threshold `1/5` the right-hand
side of the upper half of `l.mathcal.E.to.Lambdas` stays below `2`.  The exact
positive root of `1 + 2 X ^ 2 + sqrt 2 * X = 2` is `(sqrt 10 - sqrt 2) / 4 > 1 /
5`. -/
private theorem one_add_two_mul_sq_add_mul_le_two {X r : ℝ} (hX0 : 0 ≤ X)
    (hX : X < 1 / 5) (hr : r ≤ 3 / 2) :
    1 + 2 * X ^ 2 + r * X ≤ 2 := by
  nlinarith

/-- `sqrt 2 <= 3 / 2`. -/
private theorem sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2 : ℝ) ^ 2) by
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- The printed discount `s = 1/4` is positive. -/
theorem quarter_pos : (0 : ℝ) < 1 / 4 := by norm_num

/-! ## The `q = 1` to `q = 2` half-discount comparison

`Lambda_{s,1} <= Lambda_{s/2,2}` and `lambda_{s,1}^{-1} <= lambda_{s/2,2}^{-1}`,

is already proved as `ErrorComparison.LambdaSq_finite_one_le_half_two` and
`ErrorComparison.lambdaSq_finite_one_inv_le_half_two`
(`Provider/ErrorComparison/HalfScaleExponentBridge.lean`); it is consumed here,
not re-derived. -/

/-- The literal ordering `lambda_{s,q} <= Lambda_{s,q}` through the one-cube
quantities, as in the printed good event's middle clause. -/
private theorem lambdaSq_le_LambdaSq_oneCube [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    Ch02.lambdaSq Q s (.finite q) a ≤ Ch02.LambdaSq Q s (.finite q) a :=
  (Ch02.lambdaSq_le_oneCube Q a hs (by simpa using hq)).trans
    ((Ch02.oneCube_sigmaStarInv_le_b Q a).trans
      (Ch02.oneCube_b_le_LambdaSq Q a hs (by simpa using hq)))

/-- The two Section 3 clauses and the printed three clauses of
`e.goodevent.combine` define the same event. -/
private theorem ellipticity_clauses_iff {sigma lam Lam : ℝ} (hsigma : 0 < sigma)
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    (sigma⁻¹ * Lam ≤ 2 ∧ sigma * lam⁻¹ ≤ 2) ↔
      (sigma / 2 ≤ lam ∧ lam ≤ Lam ∧ Lam ≤ 2 * sigma) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [inv_mul_le_iff₀ hsigma] at h1
    rw [mul_inv_le_iff₀ hlam] at h2
    exact ⟨by linarith, hle, by linarith⟩
  · rintro ⟨h1, -, h3⟩
    rw [inv_mul_le_iff₀ hsigma, mul_inv_le_iff₀ hlam]
    exact ⟨by linarith, by linarith⟩

/-! ## The observation-scale bad event -/

/-- The admissible exponent `q = 1`, at which `e.goodevent.combine` is printed. -/
def exponentOne : CoarseEllipticityExponent :=
  CoarseEllipticityExponent.finite ⟨1, le_refl 1⟩

/-- The compatible triadic family of the genuine cutoff agrees, modulo Chapter 2
almost-everywhere equality on every cube, with CoarseGraining's dependent
family attached to the same ambient field. -/
private theorem cutoffFamily_aeeq (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu L omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)) :=
  fun _ => Filter.EventuallyEq.rfl

/-- The upper multiscale ellipticity observable at cube scale `m` and
coefficient-cutoff scale `L`, evaluated on the genuine cutoff family. -/
private theorem cutoffUpperEllipticity_eq_LambdaSq (M : ABKModel d) (m L : ℤ) {s : ℝ}
    (hs : 0 < s) (q : CoarseEllipticityExponent) {q' : Ch02.MultiscaleExponent}
    (hq : q.1 = q') (omega : Cutoff.CutoffSample d) :
    Observable.cutoffUpperEllipticity M m L s hs q omega =
      Ch02.LambdaSq (originCube d m) s q'
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  subst hq
  rw [Observable.cutoffUpperEllipticity_eq_literal]
  change Ch04.LambdaSqCoeffField (originCube d m) s q.1
      (Cutoff.coefficientCutoff M.nu L omega) = _
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)]
  exact (Ch02.LambdaSq_eq_ofAEEq (cutoffFamily_aeeq M L omega)
    (originCube d m) s q.1).symm

/-- The inverse lower multiscale ellipticity observable at cube scale `m` and
coefficient-cutoff scale `L`, evaluated on the genuine cutoff family. -/
private theorem cutoffLowerEllipticityInv_eq_lambdaSq_inv (M : ABKModel d) (m L : ℤ)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    {q' : Ch02.MultiscaleExponent} (hq : q.1 = q')
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInv M m L s hs q omega =
      (Ch02.lambdaSq (originCube d m) s q'
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  subst hq
  rw [Observable.cutoffLowerEllipticityInv_eq_literal]
  change (Ch04.lambdaSqCoeffField (originCube d m) s q.1
      (Cutoff.coefficientCutoff M.nu L omega))⁻¹ = _
  rw [Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)]
  exact congrArg Inv.inv
    (Ch02.lambdaSq_eq_ofAEEq (cutoffFamily_aeeq M L omega)
      (originCube d m) s q.1).symm

/-- **The observation-scale bad event** `B_m` of Step 4: the complement of the
good event `e.goodevent.combine` at the printed discount `s = 1/4` and printed
exponent `q = 1`, on the genuine cutoff family and in the Section 3 inverse
convention.

`mem_observationScaleBadEvent_iff` certifies that this is exactly the complement
of the printed three-clause event
`{sigmabar_L / 2 <= lambda_{1/4,1} <= Lambda_{1/4,1} <= 2 sigmabar_L}`. -/
def observationScaleBadEvent (M : ABKModel d) (L m : ℤ) :
    Set (Cutoff.CutoffSample d) :=
  {omega |
    ¬ ((Annealed.sigmaBar M L : ℝ)⁻¹ *
            Observable.cutoffUpperEllipticity M m L (1 / 4) quarter_pos exponentOne
              omega ≤ 2 ∧
          (Annealed.sigmaBar M L : ℝ) *
            Observable.cutoffLowerEllipticityInv M m L (1 / 4) quarter_pos exponentOne
              omega ≤ 2)}

/-- The observation-scale bad event is measurable: both multiscale ellipticity
observables are genuinely measurable. -/
theorem measurableSet_observationScaleBadEvent (M : ABKModel d) (L m : ℤ) :
    MeasurableSet (observationScaleBadEvent M L m) := by
  have hupper : MeasurableSet
      {omega : Cutoff.CutoffSample d |
        (Annealed.sigmaBar M L : ℝ)⁻¹ *
          Observable.cutoffUpperEllipticity M m L (1 / 4) quarter_pos exponentOne
            omega ≤ 2} :=
    measurableSet_le
      (measurable_const.mul
        (Observable.measurable_cutoffUpperEllipticity M m L (1 / 4) quarter_pos
          exponentOne))
      measurable_const
  have hlower : MeasurableSet
      {omega : Cutoff.CutoffSample d |
        (Annealed.sigmaBar M L : ℝ) *
          Observable.cutoffLowerEllipticityInv M m L (1 / 4) quarter_pos exponentOne
            omega ≤ 2} :=
    measurableSet_le
      (measurable_const.mul
        (Observable.measurable_cutoffLowerEllipticityInv M m L (1 / 4) quarter_pos
          exponentOne))
      measurable_const
  exact (hupper.inter hlower).compl

/-- **Faithfulness certificate.**  The measurable carrier
`observationScaleBadEvent` is exactly the complement of the literal printed
good event `e.goodevent.combine` at `s = 1/4`, `q = 1`, evaluated on the
genuine cutoff family.  The two readings agree at every sample point because
the lower multiscale ellipticity of the actual cutoff is strictly positive. -/
theorem mem_observationScaleBadEvent_iff [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    omega ∈ observationScaleBadEvent M L m ↔
      ¬ ((Annealed.sigmaBar M L : ℝ) / 2 ≤
            Ch02.lambdaSq (originCube d m) (1 / 4) (.finite 1)
              (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) ∧
          Ch02.lambdaSq (originCube d m) (1 / 4) (.finite 1)
              (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) ≤
            Ch02.LambdaSq (originCube d m) (1 / 4) (.finite 1)
              (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) ∧
          Ch02.LambdaSq (originCube d m) (1 / 4) (.finite 1)
              (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) ≤
            2 * (Annealed.sigmaBar M L : ℝ)) := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
  have hlam : 0 < Ch02.lambdaSq (originCube d m) (1 / 4) (.finite 1)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) :=
    Ch02.lambdaSq_finite_pos (originCube d m)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) quarter_pos
      (le_refl 1)
  have hle := lambdaSq_le_LambdaSq_oneCube (originCube d m)
    (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) quarter_pos
    (le_refl (1 : ℝ))
  change ¬ (_ ∧ _) ↔ _
  rw [cutoffUpperEllipticity_eq_LambdaSq M m L quarter_pos exponentOne
      (q' := Ch02.MultiscaleExponent.finite 1) rfl,
    cutoffLowerEllipticityInv_eq_lambdaSq_inv M m L quarter_pos exponentOne
      (q' := Ch02.MultiscaleExponent.finite 1) rfl]
  exact not_congr (ellipticity_clauses_iff hsigma hlam hle)

/-- **The bad-event inclusion.**  Almost surely, the
observation-scale bad event is contained in the threshold event
`{mathcal E_{1/8, infinity, 2}(cu_m; a_L, sigmabar_L) >= 1/5}`.

This is the upper half of `l.mathcal.E.to.Lambdas` at `q = 2` together with the
quadratic ellipticity gate; the threshold `1/5` is legitimate because the exact
positive root is `(sqrt 10 - sqrt 2) / 4 > 1/5`. -/
theorem ae_error_ge_of_mem_observationScaleBadEvent [NeZero d] (M : ABKModel d)
    (L m : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ observationScaleBadEvent M L m →
        (1 / 5 : ℝ) ≤ Observable.cutoffHomogenizationErrorRepresentative M L m
          eighth_pos (Annealed.sigmaBar M L) omega := by
  filter_upwards [Observable.cutoffHomogenizationErrorRaw_ae_eq_representative M L m
    eighth_pos (Annealed.sigmaBar M L)] with omega hraw
  intro hbad
  by_contra hlt
  push Not at hlt
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
  have hX0 : 0 ≤ Observable.cutoffHomogenizationErrorRepresentative M L m
      eighth_pos (Annealed.sigmaBar M L) omega :=
    Observable.cutoffHomogenizationErrorRepresentative_nonneg M L m eighth_pos
      (Annealed.sigmaBar M L) omega
  have hcomp : Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L) =
      scalarMatrix (d := d) ((Annealed.sigmaBar M L : ℝ)) := rfl
  have hErr : Ch02.HomogenizationErrorOnCube (originCube d m) (1 / 8) .infinity
        (.finite 2) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (scalarMatrix (d := d) ((Annealed.sigmaBar M L : ℝ))) =
      Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
        (Annealed.sigmaBar M L) omega := by
    rw [← hcomp, ← Observable.cutoffHomogenizationErrorRaw_characterization M L m
      (1 / 8) (Annealed.sigmaBar M L) omega]
    exact hraw
  have hmax :=
    ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
      (originCube d m) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      eighth_pos hsigma
  rw [hErr] at hmax
  have hgate := one_add_two_mul_sq_add_mul_le_two hX0 hlt sqrt_two_le
  have hboth := (max_le_iff).1 (hmax.trans hgate)
  have hhalf : (1 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
  have hcmpU : Ch02.LambdaSq (originCube d m) (1 / 4) (.finite 1)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) ≤
      Ch02.LambdaSq (originCube d m) (1 / 8) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) := by
    have h := ErrorComparison.LambdaSq_finite_one_le_half_two (originCube d m)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) quarter_pos
    rwa [hhalf] at h
  have hcmpL : (Ch02.lambdaSq (originCube d m) (1 / 4) (.finite 1)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤
      (Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ := by
    have h := ErrorComparison.lambdaSq_finite_one_inv_le_half_two (originCube d m)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) quarter_pos
    rwa [hhalf] at h
  refine hbad ⟨?_, ?_⟩
  · rw [cutoffUpperEllipticity_eq_LambdaSq M m L quarter_pos exponentOne
      (q' := Ch02.MultiscaleExponent.finite 1) rfl]
    exact le_trans (mul_le_mul_of_nonneg_left hcmpU (inv_nonneg.mpr hsigma.le))
      hboth.1
  · rw [cutoffLowerEllipticityInv_eq_lambdaSq_inv M m L quarter_pos exponentOne
      (q' := Ch02.MultiscaleExponent.finite 1) rfl]
    exact le_trans (mul_le_mul_of_nonneg_left hcmpL hsigma.le) hboth.2

/-! ## The observation-scale fourth moment -/

/-- The dimension-free moment constant of the second-moment extraction from
`Gamma_{1/4}` control. -/
noncomputable def badEventMomentConst : ℝ :=
  (gammaMomentConst (1 / 4) * (2 : ℝ) ^ ((1 / 4 : ℝ)⁻¹)) ^ 2

private theorem badEventMomentConst_nonneg : 0 ≤ badEventMomentConst := by
  unfold badEventMomentConst
  positivity

/-- Second-moment extraction from `Gamma_{1/4}` upper-tail control. -/
private theorem integrable_sq_and_integral_sq_le_of_isBigOWith
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Y : Omega → ℝ} {K : ℝ} (hK : 0 < K)
    (hYnonneg : ∀ omega, 0 ≤ Y omega) (hYm : Measurable Y)
    (hY : IsBigOWith mu (gammaSigma (1 / 4)) Y K) :
    Integrable (fun omega => Y omega * Y omega) mu ∧
      ∫ omega, Y omega * Y omega ∂mu ≤ badEventMomentConst * K ^ 2 := by
  have hpow : ∀ z : ℝ, z ^ (2 : ℝ) = z * z := by
    intro z
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two]
  have hint := integral_rpow_le_of_isBigOWith_gammaSigma (μ := mu) (Y := Y) (K := K)
    (σ := 1 / 4) (p := 2) (by norm_num) hK (by norm_num) hYnonneg hYm.aemeasurable hY
  have hintegrable := integrable_rpow_of_isBigOWith_gammaSigma (μ := mu) (Y := Y)
    (K := K) (σ := 1 / 4) (p := 2) (by norm_num) hK (by norm_num) hYnonneg
    hYm.aemeasurable hY
  refine ⟨by simpa only [hpow] using hintegrable, ?_⟩
  have hint' : ∫ omega, Y omega * Y omega ∂mu ≤
      gammaMomentConst (1 / 4) * (2 : ℝ) ^ ((1 / 4 : ℝ)⁻¹) * K *
        (gammaMomentConst (1 / 4) * (2 : ℝ) ^ ((1 / 4 : ℝ)⁻¹) * K) := by
    simpa only [hpow] using hint
  refine hint'.trans_eq ?_
  unfold badEventMomentConst
  ring

/-- The observation-scale fourth moment of Step 4, at the observation cube `n`
and the cutoff scale `L`, from `Gamma_{1/4}` control of the squared error at
scale `theta`. -/
private theorem fourthMoment_of_cover [NeZero d] {M : ABKModel d} {L n : ℤ}
    {theta : ℝ} (hthetaPos : 0 < theta)
    (hcov : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (fun omega =>
        Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
          (Annealed.sigmaBar M L) omega ^ 2) theta) :
    Integrable (fun omega =>
        Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
            (Annealed.sigmaBar M L) omega ^ 2 *
          Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
            (Annealed.sigmaBar M L) omega ^ 2)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ omega,
          Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
              (Annealed.sigmaBar M L) omega ^ 2 *
            Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
              (Annealed.sigmaBar M L) omega ^ 2
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        badEventMomentConst * theta ^ 2 :=
  integrable_sq_and_integral_sq_le_of_isBigOWith hthetaPos (fun _ => sq_nonneg _)
    ((Observable.measurable_cutoffHomogenizationErrorRepresentative M L n eighth_pos
      (Annealed.sigmaBar M L)).pow_const 2) hcov

/-! ## Pure-real cores of the probabilistic steps

Each of these keeps the heavy measurable carriers out of the arithmetic
tactics; they are applied to the observation-scale error by `exact`. -/

/-- The Markov threshold: on the bad event the fourth power of the error is at
least `5 ^ (-4)`. -/
private theorem inv_pow_four_le_of_fifth_le {X : ℝ} (h0 : 0 ≤ X) (h5 : 1 / 5 ≤ X) :
    (1 / 625 : ℝ) ≤ X ^ 2 * X ^ 2 := by
  have hsq : (1 / 25 : ℝ) ≤ X ^ 2 := by nlinarith
  nlinarith

/-- The pointwise majorization on the bad event: the response at the smaller
cube is dominated by the two fourth powers.  This replaces the printed
Cauchy--Schwarz step and produces the same amplitude. -/
private theorem response_le_of_bad_event {J X Y : ℝ} (hJ : J ≤ X ^ 2)
    (h0 : 0 ≤ Y) (h5 : 1 / 5 ≤ Y) :
    J ≤ 25 / 2 * (X ^ 2 * X ^ 2 + Y ^ 2 * Y ^ 2) := by
  have hy : (1 : ℝ) ≤ 25 * Y ^ 2 := by nlinarith
  have hx0 : 0 ≤ X ^ 2 := sq_nonneg X
  have hy0 : 0 ≤ Y ^ 2 := sq_nonneg Y
  nlinarith [sq_nonneg (X ^ 2 - Y ^ 2)]

/-- Markov's inequality, rearranged. -/
private theorem le_mul_of_inv_mul_le {a b : ℝ} (h : (1 / 625 : ℝ) * a ≤ b) :
    a ≤ 625 * b := by linarith

/-- The two-cube budget of the response step. -/
private theorem half_sum_le_of_le {a b c : ℝ} (ha : a ≤ c) (hb : b ≤ c) :
    25 / 2 * (a + b) ≤ 25 * c := by linarith

/-- The collapse of the two-term observation-scale amplitude. -/
private theorem amp_collapse_le {c u v : ℝ} (hc : 0 ≤ c) (h : v ≤ u) :
    c * (256 * u + 65536 * v) ≤ c * 65792 * u := by nlinarith

/-- The final constant budget: every amplitude produced below is at most
`Cbad * delta_1 ^ 2` with `delta_1 = 10 ^ 9 * E ^ 2 * gamma`. -/
private theorem badEvent_budget_le {b c u K : ℝ} (hb : 0 ≤ b)
    (hK : K * 65792 ^ 2 ≤ 10 ^ 18) :
    K * (b * (c * 65792 * u) ^ 2) ≤ max 1 (b * c ^ 2) * (10 ^ 9 * u) ^ 2 := by
  have hbcu : 0 ≤ b * c ^ 2 * u ^ 2 :=
    mul_nonneg (mul_nonneg hb (sq_nonneg c)) (sq_nonneg u)
  have hmax : b * c ^ 2 ≤ max 1 (b * c ^ 2) := le_max_right _ _
  calc
    K * (b * (c * 65792 * u) ^ 2) = (K * 65792 ^ 2) * (b * c ^ 2 * u ^ 2) := by ring
    _ ≤ 10 ^ 18 * (b * c ^ 2 * u ^ 2) := mul_le_mul_of_nonneg_right hK hbcu
    _ ≤ 10 ^ 18 * (max 1 (b * c ^ 2) * u ^ 2) := by nlinarith [sq_nonneg u]
    _ = max 1 (b * c ^ 2) * (10 ^ 9 * u) ^ 2 := by ring

/-! ## Step 4 -/

/-- With `delta_1 = 10 ^ 9 * E ^ 2 * gamma`, uniformly over the separation
`L <= m - 2` (which the frozen corridor `L <= m - Chom |log epsilon|`
implies with roughly thirty scales of slack):

* the observation-scale bad event has probability at most `C(d) delta_1 ^ 2`;
* its response contribution
  `E[J(cu_{m-1}, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L) 1_{B_m}]`
  is at most `C(d) delta_1 ^ 2`, in every unit direction.

Both constants depend only on `d`.  Finite-range concentration is not used.

This is a Provider endpoint and carries no source-node status by itself. -/
theorem exists_relativeCutoff_observationScale_badEvent_bound (d : ℕ) :
    ∃ Chom Cbad : ℝ, 64 ≤ Chom ∧ 1 ≤ Cbad ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ L : ℤ, L ≤ m - 2 →
              let delta1 : ℝ := 10 ^ 9 * (E : ℝ) ^ 2 * M.gamma
              (Cutoff.cutoffSampleLaw M).toMeasure.real
                    (observationScaleBadEvent M L m) ≤ Cbad * delta1 ^ 2 ∧
                ∀ e : Vec d, Ch02.vecNorm e = 1 →
                  ∫ omega in observationScaleBadEvent M L m,
                      Observable.cutoffResponseJ M (m - 1) L e omega
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
                    Cbad * delta1 ^ 2 := by
  obtain ⟨Cobs, hCobs1, hCobs⟩ := observationScaleFiniteCover_sq_isBigOWith_gammaQuarter d
  refine ⟨64, max 1 (badEventMomentConst * Cobs ^ 2), le_refl _, le_max_left _ _, ?_⟩
  intro M m E _hEfloor hregime hLower epsilon hepsilon hgate L hsep delta1
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hd1 : delta1 = 10 ^ 9 * (E : ℝ) ^ 2 * M.gamma := rfl
  -- Standing parameter facts.
  have hEpos : (0 : ℝ) < (E : ℝ) := zero_lt_one.trans_le E.property
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hepsilonPos : 0 < epsilon := hepsilon.1
  have hepsilonHalf : epsilon ≤ 1 / 2 := hepsilon.2
  -- The source range places both observation cubes above the cutoff.
  have hLm1 : L ≤ m - 1 := by omega
  have hLm2 : L ≤ m - 1 - 1 := by omega
  -- The legal window of the lower clause.
  have hEinvOne : (E : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hEpos).2 E.property
  have hEinvNonneg : 0 ≤ (E : ℝ)⁻¹ := inv_nonneg.mpr hEpos.le
  have hEinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ 1 := by nlinarith
  have hgamma128 : M.gamma ≤ 1 / 128 := by
    calc
      M.gamma ≤ (64 : ℝ)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon := hgate
      _ ≤ (64 : ℝ)⁻¹ * 1 * (1 / 2) := by gcongr
      _ = 1 / 128 := by norm_num
  have hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    ⟨by linarith, by norm_num⟩
  -- The regime collapse of the two-term observation-scale amplitude.
  have hCobsPos : (0 : ℝ) < Cobs := lt_of_lt_of_le zero_lt_one hCobs1
  have hthetaPos : (0 : ℝ) < Cobs * 65792 * ((E : ℝ) ^ 2 * M.gamma) := by positivity
  have hamp : Cobs *
        (((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma) ^ 2 +
          (((1 / 16 : ℝ)⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2) ≤
      Cobs * 65792 * ((E : ℝ) ^ 2 * M.gamma) := by
    have hsqrt : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hgammaPos.le
    have hA : ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma) ^ 2 =
        256 * ((E : ℝ) ^ 2 * M.gamma) := by
      calc
        ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma) ^ 2 =
            (E : ℝ) ^ 2 * ((1 / 16 : ℝ)⁻¹) ^ 2 * Real.sqrt M.gamma ^ 2 := by ring
        _ = (E : ℝ) ^ 2 * 256 * M.gamma := by rw [hsqrt]; norm_num
        _ = 256 * ((E : ℝ) ^ 2 * M.gamma) := by ring
    have hB : (((1 / 16 : ℝ)⁻¹) ^ 2 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2 =
        65536 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 2 := by
      rw [mul_pow]
      norm_num
    have hBle : Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 2 ≤
        (E : ℝ) ^ 2 * M.gamma :=
      exp_neg_sq_le_of_regime E.property hgammaPos hregime
    rw [hA, hB]
    exact amp_collapse_le hCobsPos.le hBle
  -- The observation-scale fourth moments at the two cubes.
  have hcovm := hCobs M m E hLower hwindow L hLm1
  have hcovm1 := hCobs M (m - 1) E (fun k hk => hLower k (by omega)) hwindow L hLm2
  obtain ⟨hintm, hmomm⟩ :=
    fourthMoment_of_cover (n := m) hthetaPos (IsBigOWith.mono_scale hcovm hamp)
  obtain ⟨hintm1, hmomm1⟩ :=
    fourthMoment_of_cover (n := m - 1) hthetaPos (IsBigOWith.mono_scale hcovm1 hamp)
  have hbadInc := ae_error_ge_of_mem_observationScaleBadEvent M L m
  refine ⟨?_, ?_⟩
  · -- Markov's inequality at the threshold `1/5`.
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (f := fun omega =>
        Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
            (Annealed.sigmaBar M L) omega ^ 2 *
          Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
            (Annealed.sigmaBar M L) omega ^ 2)
      (Filter.Eventually.of_forall fun _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) hintm (1 / 625)
    have hsub : (Cutoff.cutoffSampleLaw M).toMeasure.real
          (observationScaleBadEvent M L m) ≤
        (Cutoff.cutoffSampleLaw M).toMeasure.real
          {omega |
            (1 / 625 : ℝ) ≤
              Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                  (Annealed.sigmaBar M L) omega ^ 2 *
                Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                  (Annealed.sigmaBar M L) omega ^ 2} := by
      refine Ch04.measureReal_mono_ae ?_
      filter_upwards [hbadInc] with omega homega
      intro hmem
      exact inv_pow_four_le_of_fifth_le
        (Observable.cutoffHomogenizationErrorRepresentative_nonneg M L m eighth_pos
          (Annealed.sigmaBar M L) omega) (homega hmem)
    calc
      (Cutoff.cutoffSampleLaw M).toMeasure.real (observationScaleBadEvent M L m) ≤
          625 * ∫ omega,
            Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                (Annealed.sigmaBar M L) omega ^ 2 *
              Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                (Annealed.sigmaBar M L) omega ^ 2
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
        hsub.trans (le_mul_of_inv_mul_le hMarkov)
      _ ≤ 625 * (badEventMomentConst *
            (Cobs * 65792 * ((E : ℝ) ^ 2 * M.gamma)) ^ 2) :=
        mul_le_mul_of_nonneg_left hmomm (by norm_num)
      _ ≤ max 1 (badEventMomentConst * Cobs ^ 2) *
            (10 ^ 9 * ((E : ℝ) ^ 2 * M.gamma)) ^ 2 :=
        badEvent_budget_le badEventMomentConst_nonneg (by norm_num)
      _ = max 1 (badEventMomentConst * Cobs ^ 2) * delta1 ^ 2 := by
        rw [hd1]; ring
  · -- The response contribution, by the a.e. directional domination.
    intro e he
    have hB := measurableSet_observationScaleBadEvent M L m
    have hJdom :=
      ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq M (m - 1) L
        eighth_pos
    have hJnn := Observable.ae_forall_cutoffResponseJ_nonneg M (m - 1) L
    have hGint : Integrable (fun omega =>
        25 / 2 *
          (Observable.cutoffHomogenizationErrorRepresentative M L (m - 1) eighth_pos
                (Annealed.sigmaBar M L) omega ^ 2 *
              Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                eighth_pos (Annealed.sigmaBar M L) omega ^ 2 +
            Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                (Annealed.sigmaBar M L) omega ^ 2 *
              Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                (Annealed.sigmaBar M L) omega ^ 2))
        (Cutoff.cutoffSampleLaw M).toMeasure := (hintm1.add hintm).const_mul _
    have hnonneg : 0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
        fun omega => (observationScaleBadEvent M L m).indicator
          (fun omega => Observable.cutoffResponseJ M (m - 1) L e omega) omega := by
      filter_upwards [hJnn] with omega homega
      exact Set.indicator_nonneg (fun _ _ => homega e) omega
    have hle : (fun omega => (observationScaleBadEvent M L m).indicator
          (fun omega => Observable.cutoffResponseJ M (m - 1) L e omega) omega) ≤ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
        fun omega =>
          25 / 2 *
            (Observable.cutoffHomogenizationErrorRepresentative M L (m - 1) eighth_pos
                  (Annealed.sigmaBar M L) omega ^ 2 *
                Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                  eighth_pos (Annealed.sigmaBar M L) omega ^ 2 +
              Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                  (Annealed.sigmaBar M L) omega ^ 2 *
                Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                  (Annealed.sigmaBar M L) omega ^ 2) := by
      filter_upwards [hJdom, hbadInc] with omega hdom hinc
      by_cases hmem : omega ∈ observationScaleBadEvent M L m
      · rw [Set.indicator_of_mem hmem]
        exact response_le_of_bad_event (hdom e he)
          (Observable.cutoffHomogenizationErrorRepresentative_nonneg M L m eighth_pos
            (Annealed.sigmaBar M L) omega) (hinc hmem)
      · rw [Set.indicator_of_notMem hmem]
        exact mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    calc
      ∫ omega in observationScaleBadEvent M L m,
            Observable.cutoffResponseJ M (m - 1) L e omega
            ∂(Cutoff.cutoffSampleLaw M).toMeasure =
          ∫ omega, (observationScaleBadEvent M L m).indicator
              (fun omega => Observable.cutoffResponseJ M (m - 1) L e omega) omega
              ∂(Cutoff.cutoffSampleLaw M).toMeasure := (integral_indicator hB).symm
      _ ≤ ∫ omega,
            25 / 2 *
              (Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                    eighth_pos (Annealed.sigmaBar M L) omega ^ 2 *
                  Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                    eighth_pos (Annealed.sigmaBar M L) omega ^ 2 +
                Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                    (Annealed.sigmaBar M L) omega ^ 2 *
                  Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                    (Annealed.sigmaBar M L) omega ^ 2)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
        integral_mono_of_nonneg hnonneg hGint hle
      _ = 25 / 2 *
            ((∫ omega,
                Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                    eighth_pos (Annealed.sigmaBar M L) omega ^ 2 *
                  Observable.cutoffHomogenizationErrorRepresentative M L (m - 1)
                    eighth_pos (Annealed.sigmaBar M L) omega ^ 2
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
              ∫ omega,
                Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                    (Annealed.sigmaBar M L) omega ^ 2 *
                  Observable.cutoffHomogenizationErrorRepresentative M L m eighth_pos
                    (Annealed.sigmaBar M L) omega ^ 2
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
        rw [integral_const_mul, integral_add hintm1 hintm]
      _ ≤ 25 * (badEventMomentConst *
            (Cobs * 65792 * ((E : ℝ) ^ 2 * M.gamma)) ^ 2) :=
        half_sum_le_of_le hmomm1 hmomm
      _ ≤ max 1 (badEventMomentConst * Cobs ^ 2) *
            (10 ^ 9 * ((E : ℝ) ^ 2 * M.gamma)) ^ 2 :=
        badEvent_budget_le badEventMomentConst_nonneg (by norm_num)
      _ = max 1 (badEventMomentConst * Cobs ^ 2) * delta1 ^ 2 := by
        rw [hd1]; ring

end

end Algsuperdiff.Section3.Provider.Homogenization
