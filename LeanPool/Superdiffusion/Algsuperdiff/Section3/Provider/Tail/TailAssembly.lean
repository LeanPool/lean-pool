/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# TailAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `p.tail.bounds` from `p.cg.ellipticity.bounds`

This module formalizes the conditional derivation of Proposition
`p.tail.bounds` (statement) from Proposition `p.cg.ellipticity.bounds`
(statement) through Lemma `l.mathcal.E.to.Lambdas`, printed:

> `l.mathcal.E.to.Lambdas` asserts
> `E_{s,inf,2}(cu_m; a_m, sig_{m-1})^2
>  <= 2 sig_{m-1}^{-1} Lambda_{s,2}(cu_m;a_m)
>  + 2 sig_{m-1} lambda_{s,2}^{-1}(cu_m;a_m)`
> and therefore `e.cg.ellip.lower` and `e.cg.ellip.upper` imply
> `E^2 <= C s (2s-g)^{-1} + O_{Gamma_1}(C s g (2s-g)^{-3})
>  + O_{Gamma_{(1-sig)/3}}(exp(-C^{-1}E^{-2}g^{-1}))`.
> Taking square roots, and specializing to `sig = 1/4` and `s >= 4g`, we get
> `e.tail.bounds`.

The provider `tail_bounds_of_coarse_ellipticity_bounds` takes the exact
`p.cg.ellipticity.bounds` proposition as an explicit analytic A input and
returns the exact `p.tail.bounds` proposition.  The proved frozen export
`Algsuperdiff/Frozen/Section3/TailBounds.lean` is by the application

```
exact Algsuperdiff.Section3.Provider.Tail.tail_bounds_of_coarse_ellipticity_bounds d
  (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d)
```

The dependency `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is
proved, and the frozen tail module uses this application directly.  This
conditional provider still does not by itself confer graph status.  A probe
checks exact type compatibility against the two blocks; no other node is used.

## The four steps, and what each costs

1. **`l.mathcal.E.to.Lambdas` on the Section 3 carriers**
   (`sq_cutoffHomogenizationError_le`).  The proved one-cube inequality
   `ErrorComparison.half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity`
   is stated on a *single* `Ch02.TriadicCoeffFamily`; the Section 3 error
   observable and the Section 3 ellipticity observables are attached to two
   *different* families of the same ambient cutoff field.  They agree modulo
   `Ch02.TriadicCoeffFamily.A (`coefficientCutoffFamily_aeeq`), and
   CoarseGraining's `HomogenizationErrorOnCube_eq_ofA, `LambdaSq_eq_ofA,
   `lambdaSq_eq_ofA transport the inequality.  All three observables are
   measurable representatives, so the conclusion is **almost everywhere**; this
   is what `Provider.Tail.isTwoTermBigOWith_of_ae_le` exists to bridge.

   ** (normalization).**  Every leg here is normalized at `sigmaBar M (m-1)`:
   the error at comparator scale `m-1`, the upper leg by `sigmaBar M (m-1)⁻¹`,
   the lower leg by `sigmaBar M (m-1)`.  This is forced, because
   `l.mathcal.E.to.Lambdas` is an identity in one scalar.

2. **The merge of the two rare lanes.**  `e.cg.ellip.lower` contributes a
   `Gamma_{(1-sigma)/2}` lane and `e.cg.ellip.upper` a `Gamma_{(1-sigma)/3}`
   lane, both at the same scale `exp(-C^{-1}E^{-2}g^{-1})`; the printed `E^2`
   display has only one.  At `sigma = 1/4` the exponents are `3/8` and `1/4`;
   the first is downgraded to `1/4` by class antitonicity and the two are merged
   by `isBigOWith_gammaSigma_add_of_nonneg` at the explicit constant
   `mergeConstant_quarter = 81`, giving the factor `324`.

3. **The square root** (`isDeterministicShiftTwoTermOneSidedOrlicz_of_sq_le` of
   `TailSqrt.lean`), which turns `Gamma_1` into `Gamma_2` and `Gamma_{1/4}` into
   `Gamma_{1/2}`.

4. The output constant is chosen after the input constant as

   `Ctail = exp(4 Ccg) + 646 Ccg + 2 Ccg^2 + 2`,

   and the four places it is spent are isolated as `tailAmplitudeGate_det`,
   `tailAmplitudeGate_middle`, `tailAmplitudeGate_heavy`, and `tailWindowGate`:

   * `exp(4 Ccg) <= Ctail` opens `e.percolation.admissibility` at `sigma = 1/4`
     from `e.percolation.admissibility.tails`;
   * `2 Ccg^2 <= Ctail` turns the printed floor `4 gamma <= s` into the
     parameter-dependent floor `gamma/2 + exp(-Ccg^{-1}E^{-2}gamma^{-1}) <= s`
     (`tailWindowGate`);
   * `646 Ccg <= Ctail` pays the halved rate and the merge factor `324`
     (`tailAmplitudeGate_heavy`), using `E^{-2} gamma^{-1} >= E^3 >= Ctail`,
     which is exactly the interaction of the two gates of
     `e.percolation.admissibility.tails`;
   * `4 Ccg <= Ctail^2` and `2 Ccg <= Ctail^2` pay the deterministic and
     `Gamma_2` lanes.

   ** (respected, and independently reconfirmed).**  The deterministic and
   middle gates below are proved under `gamma <= s` alone; the printed `4 gamma
   <= s` is spent **only** in `tailWindowGate`.

## Main results

* `exponentTwo` --- the admissible exponent `q = 2`.
* `coefficientCutoffFamily_aeeq`, `cutoffUpperEllipticityLiteral_eq`,
  `cutoffLowerEllipticityInvLiteral_eq` --- the carrier bridge.
* `sq_cutoffHomogenizationError_le` --- `l.mathcal.E.to.Lambdas` at `q = 2` on
  the Section 3 observables.
* `pow_five_le_inv_of_le_rpow`, `cube_le_rate` --- the admissibility window in
  polynomial form.
* `tail_bounds_of_coarse_ellipticity_bounds` --- the conditional coarse-to-tail
  provider.

## References

* ABK26, `p.tail.bounds`; `p.cg.ellipticity.bounds`; the derivation.
* ABK26, `l.mathcal.E.to.Lambdas`.
-/

namespace Algsuperdiff.Section3.Provider.Tail

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Probability

noncomputable section

variable {d : ℕ}

/-- The admissible exponent `q = 2`, at which `l.mathcal.E.to.Lambdas` is
available. -/
def exponentTwo : CoarseEllipticityExponent :=
  CoarseEllipticityExponent.finite ⟨2, by norm_num⟩

private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The compatible triadic family of the genuine cutoff agrees, modulo Chapter 2
almost-everywhere equality on every cube, with CoarseGraining's dependent
family attached to the same ambient field. -/
theorem coefficientCutoffFamily_aeeq (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu m omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)) :=
  fun _ => Filter.EventuallyEq.rfl

/-- The literal upper multiscale ellipticity observable, evaluated. -/
theorem cutoffUpperEllipticityLiteral_eq (M : ABKModel d) (m : ℤ) {s : ℝ}
    (q : CoarseEllipticityExponent) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffUpperEllipticityLiteral M m m s q omega =
      Ch02.LambdaSq (originCube d m) s q.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) := by
  let : NeZero d := neZero_of_model M
  change Ch04.LambdaSqCoeffField (originCube d m) s q.1
      (Cutoff.coefficientCutoff M.nu m omega) = _
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)]
  exact (Ch02.LambdaSq_eq_ofAEEq (coefficientCutoffFamily_aeeq M m omega)
    (originCube d m) s q.1).symm

/-- The literal inverse lower multiscale ellipticity observable, evaluated. -/
theorem cutoffLowerEllipticityInvLiteral_eq (M : ABKModel d) (m : ℤ) {s : ℝ}
    (q : CoarseEllipticityExponent) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M m m s q omega =
      (Ch02.lambdaSq (originCube d m) s q.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))⁻¹ := by
  let : NeZero d := neZero_of_model M
  change (Ch04.lambdaSqCoeffField (originCube d m) s q.1
      (Cutoff.coefficientCutoff M.nu m omega))⁻¹ = _
  rw [Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)]
  exact congrArg Inv.inv
    (Ch02.lambdaSq_eq_ofAEEq (coefficientCutoffFamily_aeeq M m omega)
      (originCube d m) s q.1).symm

/-- **`l.mathcal.E.to.Lambdas` on the Section 3 carriers, at `q = 2`.** -/
theorem sq_cutoffHomogenizationError_le (M : ABKModel d) (m r : ℤ) {s : ℝ}
    (hs : 0 < s) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationErrorAtComparatorScale M m r ⟨s, hs⟩ omega ^ 2 ≤
        2 * (Observable.cutoffUpperEllipticity M m m s hs exponentTwo omega *
              (Annealed.sigmaBar M r : ℝ)⁻¹) +
          2 * (Observable.cutoffLowerEllipticityInv M m m s hs exponentTwo omega *
              (Annealed.sigmaBar M r : ℝ)) := by
  let : NeZero d := neZero_of_model M
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M r : ℝ) := (Annealed.sigmaBar M r).2
  filter_upwards
    [Observable.cutoffHomogenizationErrorAtComparatorScale_ae_eq_homogenizationErrorOnCube
        M m r ⟨s, hs⟩,
      Observable.cutoffUpperEllipticity_ae_eq_literal M m m s hs exponentTwo,
      Observable.cutoffLowerEllipticityInv_ae_eq_literal M m m s hs exponentTwo]
    with omega hE hU hL
  have hcomp : Observable.isotropicComparatorMatrix (Annealed.sigmaBar M r) =
      scalarMatrix (d := d) ((Annealed.sigmaBar M r : ℝ)) := rfl
  have hq : (exponentTwo : CoarseEllipticityExponent).1 =
      (Ch02.MultiscaleExponent.finite 2) := rfl
  rw [hE, hcomp, hU, hL, cutoffUpperEllipticityLiteral_eq,
    cutoffLowerEllipticityInvLiteral_eq, hq]
  have hkey :=
    ErrorComparison.half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity
      (originCube d m) (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) hs hsigma
  have hUpper : (0 : ℝ) ≤ (Annealed.sigmaBar M r : ℝ)⁻¹ *
      Ch02.LambdaSq (originCube d m) s (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) :=
    mul_nonneg (inv_nonneg.2 hsigma.le)
      (Ch02.LambdaSq_nonneg (originCube d m)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) hs (by norm_num))
  have hLower : (0 : ℝ) ≤ (Annealed.sigmaBar M r : ℝ) *
      (Ch02.lambdaSq (originCube d m) s (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))⁻¹ :=
    mul_nonneg hsigma.le
      (inv_nonneg.2 (Ch02.lambdaSq_nonneg (originCube d m)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) hs (by norm_num)))
  have hmax := max_le_add_of_nonneg hUpper hLower
  linarith only [hkey, hmax,
    mul_comm (Ch02.LambdaSq (originCube d m) s (Ch02.MultiscaleExponent.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))
      ((Annealed.sigmaBar M r : ℝ))⁻¹,
    mul_comm ((Ch02.lambdaSq (originCube d m) s (Ch02.MultiscaleExponent.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))⁻¹)
      ((Annealed.sigmaBar M r : ℝ))]

/-! ## Elementary consequences of the admissibility window -/

/-- The upper gate `E <= gamma^{-1/5}` of `e.percolation.admissibility.tails`
in polynomial form. -/
theorem pow_five_le_inv_of_le_rpow {E gamma : ℝ} (hE : 0 ≤ E) (hgamma : 0 < gamma)
    (h : E ≤ gamma ^ (-(1 / 5 : ℝ))) : E ^ 5 ≤ gamma⁻¹ := by
  have h1 : (gamma ^ (-(1 / 5 : ℝ))) ^ (5 : ℕ) = gamma⁻¹ := by
    rw [← Real.rpow_natCast (gamma ^ (-(1 / 5 : ℝ))) 5, ← Real.rpow_mul hgamma.le,
      show -(1 / 5 : ℝ) * ((5 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  calc E ^ 5 ≤ (gamma ^ (-(1 / 5 : ℝ))) ^ (5 : ℕ) := pow_le_pow_left₀ hE h 5
    _ = gamma⁻¹ := h1

/-- The reciprocal exponential rate of the rare lane is at least the cube of the
lower gate: `E^{-2} gamma^{-1} >= E ^ 3`.  Combined with `Ctail <= E` this is
what makes the rare-lane and window gates below closable at a constant chosen
after `Ccg`. -/
theorem cube_le_rate {E gamma : ℝ} (hE : 0 < E)
    (h5 : E ^ 5 ≤ gamma⁻¹) : E ^ 3 ≤ (E⁻¹) ^ 2 * gamma⁻¹ := by
  have hEsq : (0 : ℝ) < E ^ 2 := by positivity
  have hkey : E ^ 3 * E ^ 2 ≤ ((E⁻¹) ^ 2 * gamma⁻¹) * E ^ 2 := by
    have hinv : (E⁻¹) ^ 2 * E ^ 2 = 1 := by
      field_simp
    calc E ^ 3 * E ^ 2 = E ^ 5 := by ring
      _ ≤ gamma⁻¹ := h5
      _ = ((E⁻¹) ^ 2 * gamma⁻¹) * E ^ 2 := by
          rw [mul_comm ((E⁻¹) ^ 2) gamma⁻¹, mul_assoc, hinv, mul_one]
  exact le_of_mul_le_mul_right hkey hEsq

/-! ## The three amplitude gates

These three lemmas are the exact price. -/

/-- **The deterministic gate.**  The doubled deterministic parts of
`e.cg.ellip.lower` and `e.cg.ellip.upper` are below `Ctail ^ 2`, so their square
root is below the deterministic shift `Ctail` of `e.tail.bounds`. -/
theorem tailAmplitudeGate_det {Ccg Ctail gamma s : ℝ} (hCcg : 0 < Ccg)
    (hgamma : 0 < gamma) (hsg : gamma ≤ s) (hC : 4 * Ccg ≤ Ctail ^ 2) :
    2 * Ccg + 2 * (Ccg * s * (2 * s - gamma)⁻¹) ≤ Ctail ^ 2 := by
  have hs : 0 < s := lt_of_lt_of_le hgamma hsg
  have hgap : 0 < 2 * s - gamma := by linarith only [hs, hsg]
  have hratio : s * (2 * s - gamma)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hgap, one_mul]
    linarith only [hsg]
  have hmul : Ccg * s * (2 * s - gamma)⁻¹ ≤ Ccg :=
    calc Ccg * s * (2 * s - gamma)⁻¹ = Ccg * (s * (2 * s - gamma)⁻¹) := by ring
      _ ≤ Ccg * 1 := mul_le_mul_of_nonneg_left hratio hCcg.le
      _ = Ccg := mul_one Ccg
  linarith only [hmul, hC]

/-- **The middle gate.**  The doubled `Gamma_1` amplitude of `e.cg.ellip.upper`
is below the square of the `Gamma_2` amplitude of `e.tail.bounds`.

Only `gamma <= s` is used, not the printed `4 gamma <= s`; this is the formal
content. -/
theorem tailAmplitudeGate_middle {Ccg Ctail cstar gamma s : ℝ}
    (hCcg : 0 < Ccg) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hsg : gamma ≤ s)
    (hC : 2 * Ccg ≤ Ctail ^ 2) :
    2 * (Ccg * cstar⁻¹ * s * gamma * (2 * s - gamma)⁻¹ ^ 3) ≤
      (Ctail * (Real.sqrt cstar)⁻¹ * s⁻¹ * Real.sqrt gamma) ^ 2 := by
  have hs : 0 < s := lt_of_lt_of_le hgamma hsg
  have hgap : 0 < 2 * s - gamma := by linarith only [hs, hsg]
  have hsgap : s ≤ 2 * s - gamma := by linarith only [hsg]
  have h1 : Real.sqrt cstar ^ 2 = cstar := Real.sq_sqrt hcstar.le
  have h2 : Real.sqrt gamma ^ 2 = gamma := Real.sq_sqrt hgamma.le
  have hrhs : (Ctail * (Real.sqrt cstar)⁻¹ * s⁻¹ * Real.sqrt gamma) ^ 2 =
      Ctail ^ 2 * cstar⁻¹ * (s⁻¹) ^ 2 * gamma := by
    rw [show (Ctail * (Real.sqrt cstar)⁻¹ * s⁻¹ * Real.sqrt gamma) ^ 2 =
        Ctail ^ 2 * (Real.sqrt cstar ^ 2)⁻¹ * (s⁻¹) ^ 2 * (Real.sqrt gamma ^ 2) by
      ring, h1, h2]
  rw [hrhs]
  have hcube : s ^ 3 ≤ (2 * s - gamma) ^ 3 := pow_le_pow_left₀ hs.le hsgap 3
  have hnum : 2 * Ccg * s ^ 3 ≤ Ctail ^ 2 * (2 * s - gamma) ^ 3 := by
    have h1 : 2 * Ccg * s ^ 3 ≤ Ctail ^ 2 * s ^ 3 :=
      mul_le_mul_of_nonneg_right hC (pow_pos hs 3).le
    have h2 : Ctail ^ 2 * s ^ 3 ≤ Ctail ^ 2 * (2 * s - gamma) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (sq_nonneg Ctail)
    linarith only [h1, h2]
  have hkey : (2 * (Ccg * cstar⁻¹ * s * gamma * (2 * s - gamma)⁻¹ ^ 3)) *
      (s ^ 2 * (2 * s - gamma) ^ 3) ≤
      (Ctail ^ 2 * cstar⁻¹ * (s⁻¹) ^ 2 * gamma) * (s ^ 2 * (2 * s - gamma) ^ 3) := by
    have hl : (2 * (Ccg * cstar⁻¹ * s * gamma * (2 * s - gamma)⁻¹ ^ 3)) *
        (s ^ 2 * (2 * s - gamma) ^ 3) = cstar⁻¹ * gamma * (2 * Ccg * s ^ 3) := by
      field_simp
      try ring
    have hr : (Ctail ^ 2 * cstar⁻¹ * (s⁻¹) ^ 2 * gamma) * (s ^ 2 * (2 * s - gamma) ^ 3) =
        cstar⁻¹ * gamma * (Ctail ^ 2 * (2 * s - gamma) ^ 3) := by
      field_simp
      try ring
    rw [hl, hr]
    exact mul_le_mul_of_nonneg_left hnum
      (mul_nonneg (inv_nonneg.2 hcstar.le) hgamma.le)
  exact le_of_mul_le_mul_right hkey (by positivity)

/-- **The rare-lane gate.**  The merged heavy leg, at the merge constant `324`
of `isBigOWith_gammaSigma_add_of_nonneg` at `sigma = 1/4`, is below the square of
the rare amplitude of `e.tail.bounds`. -/
theorem tailAmplitudeGate_heavy {Ccg Ctail X : ℝ} (hCcg : 0 < Ccg)
    (hX : 0 < X) (h4 : 4 * Ccg ≤ Ctail) (hbig : 646 * Ccg ≤ X) :
    324 * Real.exp (-(Ccg⁻¹ * X)) ≤ (Real.exp (-(Ctail⁻¹ * X))) ^ 2 := by
  have hlog : Real.log 324 ≤ 323 := by
    have := Real.log_le_sub_one_of_pos (x := (324 : ℝ)) (by norm_num)
    linarith only [this]
  have h324 : (324 : ℝ) = Real.exp (Real.log 324) :=
    (Real.exp_log (by norm_num)).symm
  have hCcgne : Ccg ≠ 0 := ne_of_gt hCcg
  have hinv : Ctail⁻¹ ≤ (4 * Ccg)⁻¹ := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * Ccg) h4
    simpa only [one_div] using h
  have hrate : 2 * (Ctail⁻¹ * X) ≤ (2 * Ccg)⁻¹ * X := by
    have h1 : Ctail⁻¹ * X ≤ (4 * Ccg)⁻¹ * X :=
      mul_le_mul_of_nonneg_right hinv hX.le
    have h2 : (2 : ℝ) * ((4 * Ccg)⁻¹ * X) = (2 * Ccg)⁻¹ * X := by
      field_simp
      try ring
    linarith only [h2, mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)]
  have hgap : 323 ≤ Ccg⁻¹ * X - (2 * Ccg)⁻¹ * X := by
    have hid : Ccg⁻¹ * X - (2 * Ccg)⁻¹ * X = (2 * Ccg)⁻¹ * X := by
      field_simp
      try ring
    have hstep : (2 * Ccg)⁻¹ * (646 * Ccg) ≤ (2 * Ccg)⁻¹ * X :=
      mul_le_mul_of_nonneg_left hbig
        (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * Ccg))
    have heq : (2 * Ccg)⁻¹ * (646 * Ccg) = 323 := by
      field_simp
      try ring
    rw [heq] at hstep
    rw [hid]
    exact hstep
  have hexp : Real.log 324 + (-(Ccg⁻¹ * X)) ≤ -(2 * (Ctail⁻¹ * X)) := by
    linarith only [hlog, hgap, hrate]
  calc 324 * Real.exp (-(Ccg⁻¹ * X))
      = Real.exp (Real.log 324 + (-(Ccg⁻¹ * X))) := by
        rw [Real.exp_add, ← h324]
    _ ≤ Real.exp (-(2 * (Ctail⁻¹ * X))) := Real.exp_le_exp.2 hexp
    _ = (Real.exp (-(Ctail⁻¹ * X))) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- **The window gate.**  The printed floor `4 gamma <= s` of `p.tail.bounds`
implies the parameter-dependent floor
`gamma/2 + exp(-Ccg^{-1} E^{-2} gamma^{-1}) <= s` of
`p.cg.ellipticity.bounds`. -/
theorem tailWindowGate {Ccg Ctail E gamma s : ℝ} (hCcg : 0 < Ccg)
    (hCtail : 0 < Ctail) (hgamma : 0 < gamma) (hCtailE : Ctail ≤ E)
    (h5 : E ^ 5 ≤ gamma⁻¹) (hC2 : 2 * Ccg ^ 2 ≤ Ctail) (hs : 4 * gamma ≤ s) :
    gamma / 2 + Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹)) ≤ s := by
  have hE : 0 < E := lt_of_lt_of_le hCtail hCtailE
  have hy : 0 < Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹ := by positivity
  set y : ℝ := Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹ with hydef
  have hquad : y ^ 2 / 4 ≤ Real.exp y := by
    have hhalf : 1 + y / 2 ≤ Real.exp (y / 2) := by
      have h := Real.add_one_le_exp (y / 2)
      linarith only [h]
    have hsq : Real.exp y = Real.exp (y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hsq]
    have hy2 : (0 : ℝ) ≤ y / 2 := by linarith only [hy]
    have hle : y / 2 ≤ Real.exp (y / 2) := by linarith only [hhalf]
    calc y ^ 2 / 4 = (y / 2) ^ 2 := by ring
      _ ≤ Real.exp (y / 2) ^ 2 := pow_le_pow_left₀ hy2 hle 2
  have hexp_le : Real.exp (-y) ≤ 4 / y ^ 2 := by
    rw [le_div_iff₀ (pow_pos hy 2), Real.exp_neg, inv_mul_eq_div,
      div_le_iff₀ (Real.exp_pos y)]
    linarith only [hquad]
  have hbound : 4 / y ^ 2 ≤ 7 / 2 * gamma := by
    have hEne : E ≠ 0 := ne_of_gt hE
    have hgne : gamma ≠ 0 := ne_of_gt hgamma
    have hCne : Ccg ≠ 0 := ne_of_gt hCcg
    have hEfour : E ^ 4 * gamma ≤ E⁻¹ := by
      have h2 : E ^ 5 * gamma ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right h5 hgamma.le
        rwa [inv_mul_cancel₀ hgne] at h
      have hmul : (E ^ 4 * gamma) * E ≤ E⁻¹ * E := by
        rw [inv_mul_cancel₀ hEne]
        calc (E ^ 4 * gamma) * E = E ^ 5 * gamma := by ring
          _ ≤ 1 := h2
      exact le_of_mul_le_mul_right hmul hE
    have hdiv : 4 / y ^ 2 = 4 * Ccg ^ 2 * E ^ 4 * gamma ^ 2 := by
      rw [hydef]
      field_simp
      try ring
    rw [hdiv]
    have hkey : 4 * Ccg ^ 2 * (E ^ 4 * gamma) ≤ 7 / 2 := by
      have h1 : 4 * Ccg ^ 2 * (E ^ 4 * gamma) ≤ 4 * Ccg ^ 2 * E⁻¹ :=
        mul_le_mul_of_nonneg_left hEfour (by positivity)
      have h2 : 4 * Ccg ^ 2 * E⁻¹ ≤ 2 * Ctail * E⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith only [hC2]) (le_of_lt (inv_pos.2 hE))
      have h3 : 2 * Ctail * E⁻¹ ≤ 2 := by
        have hct : Ctail * E⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hE, one_mul]
          exact hCtailE
        linarith only [hct]
      linarith only [h1, h2, h3]
    calc 4 * Ccg ^ 2 * E ^ 4 * gamma ^ 2
        = 4 * Ccg ^ 2 * (E ^ 4 * gamma) * gamma := by ring
      _ ≤ 7 / 2 * gamma := mul_le_mul_of_nonneg_right hkey hgamma.le
  linarith only [hexp_le, hbound, hs]

/-- Squares dominate: `A <= B ^ 2` with `B >= 0` gives `sqrt A <= B`. -/
theorem sqrt_le_of_le_sq {A B : ℝ} (hB : 0 ≤ B) (h : A ≤ B ^ 2) :
    Real.sqrt A ≤ B := by
  calc Real.sqrt A ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB

/-- The deterministic lower profile of `e.cg.ellip.lower` at `q = 2`: the
`q >= 2` branch of `lowerEllipticityProfile`. -/
theorem lowerEllipticityProfile_exponentTwo (C gamma s : ℝ) :
    lowerEllipticityProfile C gamma s exponentTwo = C * s * (2 * s - gamma)⁻¹ := by
  change (if (2 : ℝ) < 2 then C * Real.rpow (s / (2 * s - gamma)) (2 / 2)
      else C * s * (2 * s - gamma)⁻¹) = C * s * (2 * s - gamma)⁻¹
  rw [ite_eq_right (by norm_num : ¬((2 : ℝ) < 2))]

/-- The merge constant of `isBigOWith_gammaSigma_add_of_nonneg` at
`sigma = 1/4`. -/
theorem mergeConstant_quarter :
    ((3 : ℝ) * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ))⁻¹ = 81 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith only [h]
  rw [max_eq_left hlog2, mul_one,
    show ((1 / 4 : ℝ))⁻¹ = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-! ## The provider -/

/-- **`p.tail.bounds` from `p.cg.ellipticity.bounds`** (ABK26). -/
theorem tail_bounds_of_coarse_ellipticity_bounds (d : ℕ)
    (hcg : ∃ Ccg : ℝ, 0 < Ccg ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Ccg / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsLowerIntegerFamilyOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2))
                  (fun L : ℤ =>
                    fun omega =>
                      Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Ccg M.gamma s q)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
                Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 1)
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 3))
                  (fun omega =>
                    Observable.cutoffUpperEllipticity
                        M m m s
                        (by
                          exact
                            (add_pos
                              (div_pos M.shellPrefix.gamma_pos (by norm_num))
                            (Real.exp_pos
                              (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                  M.gamma⁻¹)))).trans_le hsWindow.1)
                        q omega *
                      (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                  Ccg
                  (Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma *
                    (2 * s - M.gamma)⁻¹ ^ 3)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (4 * M.gamma) 1,
          max Ctail (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
            (Cutoff.cutoffSampleLaw M).toMeasure
            (HCPolySupport.IndependentSums.gammaSigma 2)
            (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
            (Observable.cutoffHomogenizationErrorAtComparatorScale
              M m (m - 1)
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 4)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
            Ctail
            (Ctail * (Real.sqrt (Disorder.cstar M))⁻¹ *
              s⁻¹ * Real.sqrt M.gamma)
            (Real.exp
              (-(Ctail⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨Ccg, hCcgpos, hcg⟩ := hcg
  refine ⟨Real.exp (4 * Ccg) + 646 * Ccg + 2 * Ccg ^ 2 + 2, by positivity, ?_⟩
  set Ctail : ℝ := Real.exp (4 * Ccg) + 646 * Ccg + 2 * Ccg ^ 2 + 2 with hCtaildef
  have hexp4pos : 0 < Real.exp (4 * Ccg) := Real.exp_pos _
  have hCcgsq : (0 : ℝ) ≤ Ccg ^ 2 := sq_nonneg Ccg
  have hCtail2 : 2 ≤ Ctail := by
    rw [hCtaildef]; linarith only [hexp4pos, hCcgpos, hCcgsq]
  have hCtailpos : 0 < Ctail := by linarith only [hCtail2]
  have hexp4 : Real.exp (4 * Ccg) ≤ Ctail := by
    rw [hCtaildef]; linarith only [hCcgpos, hCcgsq]
  have h646 : 646 * Ccg ≤ Ctail := by
    rw [hCtaildef]; linarith only [hexp4pos, hCcgsq]
  have h2sq : 2 * Ccg ^ 2 ≤ Ctail := by
    rw [hCtaildef]; linarith only [hexp4pos, hCcgpos]
  have h4Ccg : 4 * Ccg ≤ Ctail := by linarith only [h646, hCcgpos]
  have hCtailsq : Ctail ≤ Ctail ^ 2 :=
    calc Ctail = 1 * Ctail := (one_mul Ctail).symm
      _ ≤ Ctail * Ctail :=
          mul_le_mul_of_nonneg_right (by linarith only [hCtail2]) hCtailpos.le
      _ = Ctail ^ 2 := (pow_two Ctail).symm
  have hdetGate : 4 * Ccg ≤ Ctail ^ 2 := by linarith only [h4Ccg, hCtailsq]
  have hmidGate : 2 * Ccg ≤ Ctail ^ 2 := by linarith only [hdetGate, hCcgpos]
  intro M m E hstate s hsWindow hE1 hE2
  -- standing parameter facts
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have h4gs : 4 * M.gamma ≤ s := hsWindow.1
  have hs1 : s ≤ 1 := hsWindow.2
  have hspos : 0 < s := by linarith only [hgamma, h4gs]
  have hgs : M.gamma ≤ s := by linarith only [hgamma, h4gs]
  have hgap : (0 : ℝ) < 2 * s - M.gamma := by linarith only [hspos, hgs]
  have hDnonneg : (0 : ℝ) ≤ 2 * Ccg + 2 * (Ccg * s * (2 * s - M.gamma)⁻¹) := by
    have h1 : (0 : ℝ) ≤ Ccg * s * (2 * s - M.gamma)⁻¹ :=
      mul_nonneg (mul_nonneg hCcgpos.le hspos.le) (inv_pos.2 hgap).le
    linarith only [h1, hCcgpos]
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hCtailE : Ctail ≤ (E : ℝ) := le_trans (le_max_left _ _) hE1
  have hcstarE : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := le_trans (le_max_right _ _) hE1
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le hCtailpos hCtailE
  have h5 : (E : ℝ) ^ 5 ≤ M.gamma⁻¹ :=
    pow_five_le_inv_of_le_rpow hEpos.le hgamma hE2
  have hXpos : (0 : ℝ) < ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
  have hXbig : 646 * Ccg ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by
    have hcube := cube_le_rate hEpos h5
    have hEge1 : (1 : ℝ) ≤ (E : ℝ) := E.2
    have hEsq : (E : ℝ) ≤ (E : ℝ) ^ 2 :=
      calc (E : ℝ) = 1 * (E : ℝ) := (one_mul _).symm
        _ ≤ (E : ℝ) * (E : ℝ) := mul_le_mul_of_nonneg_right hEge1 hEpos.le
        _ = (E : ℝ) ^ 2 := (pow_two _).symm
    have h1 : Ctail ≤ (E : ℝ) ^ 3 :=
      calc Ctail ≤ (E : ℝ) := hCtailE
        _ ≤ (E : ℝ) ^ 2 := hEsq
        _ = 1 * (E : ℝ) ^ 2 := (one_mul _).symm
        _ ≤ (E : ℝ) * (E : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hEge1 (sq_nonneg _)
        _ = (E : ℝ) ^ 3 := by ring
    linarith only [h646, h1, hcube]
  -- the coarse-ellipticity payload at `sigma = 1/4`, `q = 2`
  have hwin : M.gamma / 2 +
      Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ s :=
    tailWindowGate hCcgpos hCtailpos hgamma hCtailE h5 h2sq h4gs
  have hsWindowCg : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 :=
    ⟨hwin, hs1⟩
  have hElow : max (Real.exp (Ccg / (1 / 4 : ℝ))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ hcstarE
    rw [show Ccg / (1 / 4 : ℝ) = 4 * Ccg by ring]
    exact le_trans hexp4 hCtailE
  obtain ⟨hlower, hupper⟩ :=
    hcg M m E hstate (1 / 4) ⟨by norm_num, by norm_num⟩ hElow hE2 exponentTwo s
      hsWindowCg
  obtain ⟨W, hWadm, hWpos, _hWmeasX, hWmeas, hWdom, hWtail⟩ := hlower
  obtain ⟨_hUmeas, Y, Z, _hΨ₁, _hΨ₂, hA₁pos, hA₂pos, _hUmeas', hYmeas, hZmeas,
    hUdom, hYtail, hZtail⟩ := hupper
  clear hWadm
  -- normalize the two `Gamma` exponents produced by `sigma = 1/4`
  rw [show ((1 : ℝ) - 1 / 4) / 2 = 3 / 8 by norm_num] at hWtail
  rw [show ((1 : ℝ) - 1 / 4) / 3 = 1 / 4 by norm_num] at hZtail
  -- restate the two pointwise dominations at a single positivity proof
  have hUdom' : ∀ omega,
      Observable.cutoffUpperEllipticity M m m s hspos exponentTwo omega *
          (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ - Ccg ≤ Y omega + Z omega := hUdom
  have hWdom' : ∀ omega,
      Observable.cutoffLowerEllipticityInv M m m s hspos exponentTwo omega *
          (Annealed.sigmaBar M (m - 1) : ℝ) ≤
        lowerEllipticityProfile Ccg M.gamma s exponentTwo + W omega := by
    intro omega
    exact hWdom omega m (by omega)
  -- the three nonnegative, doubled witnesses
  set Y₀ : Cutoff.CutoffSample d → ℝ := fun omega => 2 * max 0 (Y omega) with hY₀def
  set Z₀ : Cutoff.CutoffSample d → ℝ := fun omega => 2 * max 0 (Z omega) with hZ₀def
  set W₀ : Cutoff.CutoffSample d → ℝ := fun omega => 2 * max 0 (W omega) with hW₀def
  have hY₀tail : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1) Y₀
      (2 * (Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma * (2 * s - M.gamma)⁻¹ ^ 3)) :=
    IsBigOWith.const_mul (by norm_num) (isBigOWith_max_zero hA₁pos hYtail)
  have hZ₀tail : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z₀
      (2 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) :=
    IsBigOWith.const_mul (by norm_num) (isBigOWith_max_zero hA₂pos hZtail)
  have hW₀tail : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) W₀
      (2 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) :=
    HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
      (by norm_num : (1 / 4 : ℝ) ≤ 3 / 8)
      (IsBigOWith.const_mul (by norm_num) (isBigOWith_max_zero hWpos hWtail))
  -- merge the two rare lanes
  have hmerge := isBigOWith_gammaSigma_add_of_nonneg
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (Y := Z₀) (Z := W₀)
    (σ := 1 / 4) (by norm_num) (by positivity) (by positivity) hZ₀tail hW₀tail
  rw [max_self, mergeConstant_quarter] at hmerge
  have hmergeAmp : 2 * (81 * (2 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) =
      324 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by ring
  rw [hmergeAmp] at hmerge
  -- the almost-everywhere three-term bound on the square
  have hsq : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationErrorAtComparatorScale M m (m - 1) ⟨s, hspos⟩
          omega ^ 2 ≤
        (2 * Ccg + 2 * (Ccg * s * (2 * s - M.gamma)⁻¹)) + Y₀ omega +
          (Z₀ omega + W₀ omega) := by
    filter_upwards [sq_cutoffHomogenizationError_le M m (m - 1) hspos] with omega hbridge
    have hU := hUdom' omega
    have hW' := hWdom' omega
    rw [lowerEllipticityProfile_exponentTwo] at hW'
    have hY : Y omega ≤ max 0 (Y omega) := le_max_right _ _
    have hZ : Z omega ≤ max 0 (Z omega) := le_max_right _ _
    have hWle : W omega ≤ max 0 (W omega) := le_max_right _ _
    simp only [hY₀def, hZ₀def, hW₀def]
    linarith only [hbridge, hU, hW', hY, hZ, hWle]
  -- the square-root step
  have hmain := isDeterministicShiftTwoTermOneSidedOrlicz_of_sq_le
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (X := Observable.cutoffHomogenizationErrorAtComparatorScale M m (m - 1) ⟨s, hspos⟩)
    (Y := Y₀) (Z := fun omega => Z₀ omega + W₀ omega)
    (D := 2 * Ccg + 2 * (Ccg * s * (2 * s - M.gamma)⁻¹))
    (A₁ := 2 * (Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma * (2 * s - M.gamma)⁻¹ ^ 3))
    (A₂ := 324 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))
    (σ₁ := 1) (σ₂ := 1 / 4) (b := Ctail)
    (B₁ := Ctail * (Real.sqrt (Disorder.cstar M))⁻¹ * s⁻¹ * Real.sqrt M.gamma)
    (B₂ := Real.exp (-(Ctail⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))
    (by norm_num) (by norm_num)
    (Observable.measurable_cutoffHomogenizationErrorAtComparatorScale M m (m - 1)
      ⟨s, hspos⟩)
    ((measurable_const.max hYmeas).const_mul 2)
    (((measurable_const.max hZmeas).const_mul 2).add
      ((measurable_const.max hWmeas).const_mul 2))
    (Observable.cutoffHomogenizationErrorAtComparatorScale_nonneg M m (m - 1)
      ⟨s, hspos⟩)
    (fun omega => by simp only [hY₀def]; positivity)
    (fun omega => by simp only [hZ₀def, hW₀def]; positivity)
    hDnonneg (by positivity) (by positivity) hsq hY₀tail hmerge
    (sqrt_le_of_le_sq hCtailpos.le
      (tailAmplitudeGate_det hCcgpos hgamma hgs hdetGate))
    (sqrt_le_of_le_sq (by positivity)
      (tailAmplitudeGate_middle hCcgpos hcstar hgamma hgs hmidGate))
    (by positivity)
    (sqrt_le_of_le_sq (Real.exp_pos _).le
      (by
        have h := tailAmplitudeGate_heavy (Ccg := Ccg) (Ctail := Ctail)
          (X := ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) hCcgpos hXpos h4Ccg hXbig
        rw [show Ctail⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ =
            Ctail⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) by ring,
          show Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ =
            Ccg⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) by ring]
        exact h))
    (Real.exp_pos _)
  rw [show (2 : ℝ) * 1 = 2 by norm_num,
    show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at hmain
  exact hmain

end

end Algsuperdiff.Section3.Provider.Tail
