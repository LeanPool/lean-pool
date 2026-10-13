/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationStationarity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsCloseEighth

/-!
# LocalizationFluctuationNumericEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The numeric ellipticity moment of Step 2, and the closure

`LocalizationFluctuationEllipticity.gaugedEllipticitySum` is the quantity the
Step-2 fluctuation fold integrates, `shom^{-1} Lambda_{s,2}(Q; a) + shom
lambda_{s,2}^{-1}(Q; a)`, and the two halves are proved:

* the **geometric** half,
  `LocalizationFluctuationAncestor.doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor`,
  which reads the per-cell display at the cell's own scale-`m` ancestor;
* the **probabilistic** half,
  `LocalizationFluctuationStationarity.integral_gaugedEllipticitySum_pow_ancestorAtScale_eq_originCube`,
  which transports the annealed moment from that ancestor back to `cu_m`.

What was still missing is the **number**: a bound on the annealed fourth moment
of the gauged sum at `cu_m` itself.

## The carrier bridge

The anchor speaks about `Observable.cutoffUpperEllipticity` and
`Observable.cutoffLowerEllipticityInv`, i.e. about `Ch04.LambdaSqCoeffField`
and `Ch04.lambdaSqCoeffField` of the *coefficient field* `coefficientCutoff
M.nu L`, while `gaugedEllipticitySum` reads `Ch02.LambdaSq` and `Ch02.lambdaSq`
of the *triadic family* `coefficientCutoffTriadicCoeffFamily M L`.  On the
a.e.-elliptic support the Chapter-4 observables **are** the Chapter-2 ones of
the canonical dependent family (`Ch04.LambdaSqCoeffField`'s own `dite_eq_left`
branch), and the two families have the same underlying coefficient field on
every cube, so `Ch02.LambdaSq_eq_ofAEEq` identifies them exactly.  The exported
observables are their literals
(`Observable.cutoffUpperEllipticity_eq_literal`), the clamp being inert.
`gaugedEllipticitySum_eq_cutoffObservables` is the resulting identity; nothing
is lost and no inequality is used.

## The exponent

`gaugedEllipticitySum` is hard-coded at the Chapter-2 exponent `q = 2`, whereas
the proved
`PrincipalResponseMomentsCloseEighth.integral_coarseEllipticityGauge_rpow_eight_le`
instantiates the anchor at `q = 1`.  The anchor is quantified over **every**
admissible `q`, and the corrected lower profile collapses to `Ccg` at `s =
gamma` for `q = 2` as well -- there through the `q >= 2` branch `Ccg * s * (2s
- gamma)^{-1}`, whose value at `s = gamma` is `Ccg` exactly
(`lowerEllipticityProfile_at_gamma_two`).  So the `q = 2` instantiation runs
verbatim, with the same three lanes and the same constants.

## From the eighth moment to the fourth

The engine `integral_rpow_eight_le_of_shift_add_three_orlicz` produces the
eighth moment.  The fourth follows by Cauchy--Schwarz against the constant `1`
on the probability space (`sq_integral_le_integral_sq_of_isProbabilityMeasure`
below, proved by expanding `0 <= E[(f - E f)^2]`), which costs nothing:
`E[X^4] <= E[X^8]^{1/2} <= ((C cstar^{-1} gamma^{-1})^8)^{1/2}`.

## What is proved

* `coarseExponentTwo`, `lowerEllipticityProfile_at_gamma_two`.
* `aeeq_triadicCoeffFamily_coefficientCutoff`,
  `LambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq`,
  `lambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq`,
  `gaugedEllipticitySum_eq_cutoffObservables` -- the bridge, exact identities.
* `measurable_gaugedEllipticitySum_originCube` -- the measurability the
  stationarity transport needs, as a theorem rather than a binder.
* `integral_gaugedEllipticitySum_rpow_eight_le` -- the eighth moment at `q = 2`.
* `integral_gaugedEllipticitySum_pow_four_le` -- **the numeric fourth moment**,
  `E[(shom_{m-1}^{-1} Lambda_{gamma,2}(cu_m) + shom_{m-1} lambda_{gamma,2}^{-1}(cu_m))^4]
   <= (C cstar^{-1} gamma^{-1})^4`.
* `integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le` -- **the
  end-to-end closure**: the same numeric bound at the *cell's own scale-`m`
  ancestor*, which is the carrier the geometric half delivers.

## Binders

`integral_gaugedEllipticitySum_pow_four_le` carries exactly the anchor's own
premises -- the induction state at `m - 1`, `max (exp (2C)) cstar^{-1} <= E`,
`E <= gamma^{-1/5}`, and the window gate `gamma/2 + exp(-C^{-1}E^{-2}gamma^{-1})
<= gamma` which says that `s = gamma` lies in the anchor's own window -- and
nothing else.  The ancestor version adds `hm : R.scale <= m`, the existence of
the ancestor.  No moment, smallness or measurability proposition is assumed: the
measurability that the stationarity transport asks for is **produced** by
`measurable_gaugedEllipticitySum_originCube`.

## The `sigmabar` conversion

The anchor's gauge is `sigmabar_{m-1}`; a consumer reading the fold at
`sigmabar_{m-h}` converts with `gaugedEllipticitySum_gauge_change` from the
proved running-carrier caps `Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar`
(down) and `DisplayBridge.sigmaBar_le_thirtySix_mul_sigmaBar` (up), which are
the lower-infinite-carrier producers names, in this repository's `cstar <= 3/2`
form.  The up cap carries its own gap gate `m <= n + cstar gamma^{-1}`, which
the recurrence's `h <= 6 cstar gamma^{-1}` does **not** imply; the conversion
is therefore left to the caller, who has the shell data, rather than performed
here under a smuggled gate.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, and the moment average;
  `p.cg.ellipticity.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-- The admissible finite exponent `q = 2` at which `gaugedEllipticitySum`
reads the two multiscale ellipticity constants. -/
def coarseExponentTwo : CoarseEllipticityExponent :=
  ⟨.finite 2, by norm_num⟩

/-- **The corrected lower profile is `Ccg` at `s = cgamma`, `q = 2`.**  The `q >=
2` branch is `Ccg s (2s - cgamma)^{-1}`, which is `Ccg` exactly at `s =
cgamma`. -/
theorem lowerEllipticityProfile_at_gamma_two (Ccg gamma : ℝ) (hgamma : 0 < gamma) :
    lowerEllipticityProfile Ccg gamma gamma coarseExponentTwo = Ccg := by
  have hstep : lowerEllipticityProfile Ccg gamma gamma coarseExponentTwo =
      if (2 : ℝ) < 2 then Ccg * Real.rpow (gamma / (2 * gamma - gamma)) (2 / 2)
        else Ccg * gamma * (2 * gamma - gamma)⁻¹ := rfl
  rw [hstep, ite_eq_right (by norm_num : ¬((2 : ℝ) < 2)),
    show (2 : ℝ) * gamma - gamma = gamma by ring]
  field_simp

variable {d : ℕ}

/-! ## The carrier bridge -/

/-- **Unconditional.**  The canonical dependent Chapter-2 family of the cutoff
coefficient *field* and the Chapter-2 family of the cutoff are a.e. equal on
every cube: they carry the very same underlying coefficient field, and differ
only in the locally derived ellipticity witness. -/
theorem aeeq_triadicCoeffFamily_coefficientCutoff [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu L omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega))
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) :=
  fun _ => Filter.EventuallyEq.rfl

/-- **The upper half of the bridge, an exact identity.**  The Chapter-2 upper
multiscale ellipticity of the cutoff family at `cu_m` and exponent `q = 2` is
the anchor's own observable `Observable.cutoffUpperEllipticity`. -/
theorem LambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq [NeZero d]
    (M : ABKModel d) (m L : ℤ) {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    Ch02.LambdaSq (originCube d m) s (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) =
      Observable.cutoffUpperEllipticity M m L s hs coarseExponentTwo omega := by
  have hell := Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  rw [Observable.cutoffUpperEllipticity_eq_literal]
  show Ch02.LambdaSq (originCube d m) s (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) =
    Ch04.LambdaSqCoeffField (originCube d m) s (Ch02.MultiscaleExponent.finite 2)
      (Cutoff.coefficientCutoff M.nu L omega)
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left hell]
  exact (Ch02.LambdaSq_eq_ofAEEq (aeeq_triadicCoeffFamily_coefficientCutoff M L omega)
    (originCube d m) s (.finite 2)).symm

/-- **The lower half of the bridge, an exact identity.** -/
theorem lambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq [NeZero d]
    (M : ABKModel d) (m L : ℤ) {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    (Ch02.lambdaSq (originCube d m) s (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ =
      Observable.cutoffLowerEllipticityInv M m L s hs coarseExponentTwo omega := by
  have hell := Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  rw [Observable.cutoffLowerEllipticityInv_eq_literal]
  show (Ch02.lambdaSq (originCube d m) s (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ =
    (Ch04.lambdaSqCoeffField (originCube d m) s (Ch02.MultiscaleExponent.finite 2)
      (Cutoff.coefficientCutoff M.nu L omega))⁻¹
  rw [Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left hell]
  rw [Ch02.lambdaSq_eq_ofAEEq (aeeq_triadicCoeffFamily_coefficientCutoff M L omega)
    (originCube d m) s (.finite 2)]

/-- **The bridge.**  The gauged ellipticity sum of the cutoff family at `cu_m` is
the anchor's own gauged sum of observables. -/
theorem gaugedEllipticitySum_eq_cutoffObservables [NeZero d] (M : ABKModel d) (m L : ℤ)
    {s : ℝ} (hs : 0 < s) (sigmaBar : ℝ) (omega : Cutoff.CutoffSample d) :
    gaugedEllipticitySum sigmaBar (originCube d m) s
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) =
      Observable.cutoffUpperEllipticity M m L s hs coarseExponentTwo omega * sigmaBar⁻¹ +
        Observable.cutoffLowerEllipticityInv M m L s hs coarseExponentTwo omega *
          sigmaBar := by
  unfold gaugedEllipticitySum
  rw [LambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq M m L hs omega,
    lambdaSq_originCube_coefficientCutoffTriadicCoeffFamily_eq M m L hs omega]
  ring

/-- **The measurability the stationarity transport asks for, as a theorem.**
The gauged ellipticity sum at `cu_m` is a measurable function of the sample. -/
theorem measurable_gaugedEllipticitySum_originCube [NeZero d] (M : ABKModel d) (m L : ℤ)
    {s : ℝ} (hs : 0 < s) (sigmaBar : ℝ) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      gaugedEllipticitySum sigmaBar (originCube d m) s
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) := by
  have hEq : (fun omega : Cutoff.CutoffSample d =>
      gaugedEllipticitySum sigmaBar (originCube d m) s
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)) =
      fun omega =>
        Observable.cutoffUpperEllipticity M m L s hs coarseExponentTwo omega * sigmaBar⁻¹ +
          Observable.cutoffLowerEllipticityInv M m L s hs coarseExponentTwo omega *
            sigmaBar := by
    funext omega
    exact gaugedEllipticitySum_eq_cutoffObservables M m L hs sigmaBar omega
  rw [hEq]
  exact ((Observable.measurable_cutoffUpperEllipticity M m L s hs
      coarseExponentTwo).mul_const _).add
    ((Observable.measurable_cutoffLowerEllipticityInv M m L s hs
      coarseExponentTwo).mul_const _)

/-! ## Cauchy--Schwarz against the constant on a probability space -/

/-- **Unconditional apart from the two integrabilities.**  On a probability
space the square of the mean is below the mean of the square. -/
theorem sq_integral_le_integral_sq_of_isProbabilityMeasure {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {f : Omega → ℝ} (hf : Integrable f mu) (hf2 : Integrable (fun x => f x ^ 2) mu) :
    (∫ x, f x ∂mu) ^ 2 ≤ ∫ x, f x ^ 2 ∂mu := by
  set c : ℝ := ∫ x, f x ∂mu with hc
  have hexp : (fun x => (f x - c) ^ 2) =
      fun x => f x ^ 2 + (-(2 * c) * f x + c ^ 2) := by
    funext x
    ring
  have hint2 : Integrable (fun x => -(2 * c) * f x + c ^ 2) mu :=
    (hf.const_mul (-(2 * c))).add (integrable_const _)
  have hnn : (0 : ℝ) ≤ ∫ x, (f x - c) ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  rw [hexp, integral_add hf2 hint2,
    integral_add (hf.const_mul (-(2 * c))) (integrable_const _),
    integral_const_mul] at hnn
  have hconst : ∫ _x : Omega, c ^ 2 ∂mu = c ^ 2 := by simp
  rw [hconst, ← hc] at hnn
  nlinarith [hnn]

/-! ## The eighth moment at `q = 2` -/

/-- The aggregate lane constant of the display at `sigma = 1/2`: the two
deterministic shifts plus the three class constants of the lanes. -/
def gaugeEighthLaneConst (Ccg : ℝ) : ℝ :=
  4 * (2 * Ccg + orliczEighthMomentScale 1 * Ccg +
    orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) +
    orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2))

/-- **The eighth moment of the gauged ellipticity sum at `cu_m`, at the
Chapter-2 exponent `q = 2`.**

This is the `q = 2` instance of the anchor at `s = cgamma`, `sigma = 1/2`, read
through the carrier bridge, so that the observable is literally
`gaugedEllipticitySum` -- the quantity the Step-2 fold integrates.

on the permitted frozen theorem `coarse_ellipticity_bounds` and on its own
premises `hstate`, `hE`, `hEupper`, `hgap`. -/
theorem integral_gaugedEllipticitySum_rpow_eight_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        MemLp
            (fun omega : Cutoff.CutoffSample d =>
              gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                (originCube d m) M.gamma
                (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))
            8 (Cutoff.cutoffSampleLaw M).toMeasure ∧
          ∫ omega : Cutoff.CutoffSample d,
              gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                  (originCube d m) M.gamma
                  (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ^ (8 : ℝ)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
            (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (8 : ℝ) := by
  obtain ⟨Ccg, hCcg0, hCcg⟩ := Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d
  have hk10 : 0 < orliczEighthMomentScale 1 :=
    orliczEighthMomentScale_pos (by norm_num)
  have hk20 : 0 < orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) :=
    orliczEighthMomentScale_pos (by norm_num)
  have hk30 : 0 < orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) :=
    orliczEighthMomentScale_pos (by norm_num)
  refine ⟨max Ccg (gaugeEighthLaneConst Ccg), lt_of_lt_of_le hCcg0 (le_max_left _ _), ?_⟩
  intro M m E hstate hE hEupper hgap
  have hL : m - 1 ≤ m := by omega
  set C : ℝ := max Ccg (gaugeEighthLaneConst Ccg) with hC
  have hCcgleC : Ccg ≤ C := by rw [hC]; exact le_max_left _ _
  have hLaneC : gaugeEighthLaneConst Ccg ≤ C := by rw [hC]; exact le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hCcg0 hCcgleC
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstarPos : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  -- the anchor's premises at `sigma = 1/2`
  have hsigma : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_refl _⟩
  have hEanchor : max (Real.exp (Ccg / (1 / 2))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hE)
    refine le_trans (Real.exp_le_exp.2 ?_) ((le_max_left _ _).trans hE)
    have hdiv : Ccg / (1 / 2 : ℝ) = 2 * Ccg := by ring
    rw [hdiv]
    linarith
  have hXpos : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
  have hexpMono :
      Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by
    refine Real.exp_le_exp.2 ?_
    have hinv : C⁻¹ ≤ Ccg⁻¹ := inv_anti₀ hCcg0 hCcgleC
    have hstep : C⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) ≤
        Ccg⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_right hinv hXpos
    linarith [hstep]
  have hwin : M.gamma ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 := by
    constructor
    · linarith [hexpMono, hgap]
    · linarith [M.shellPrefix.gamma_le_quarter]
  obtain ⟨hLower, hUpper⟩ :=
    hCcg M m E hstate (1 / 2) hsigma hEanchor hEupper coarseExponentTwo M.gamma hwin
  obtain ⟨W, hW⟩ := hLower
  obtain ⟨_hUmeas, Y, Z, _hPsi1, _hPsi2, hA1pos, hA2pos, _hshiftMeas, hYm, hZm,
    hdomYZ, hYt, hZt⟩ := hUpper
  have hprof := lowerEllipticityProfile_at_gamma_two Ccg M.gamma hgammaPos
  have hA1eq :
      Ccg * (Disorder.cstar M)⁻¹ * M.gamma * M.gamma * (2 * M.gamma - M.gamma)⁻¹ ^ 3 =
        Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by
    rw [show 2 * M.gamma - M.gamma = M.gamma by ring]
    field_simp
  -- the bridge, at the anchor's own gauge
  have hbridge : ∀ omega : Cutoff.CutoffSample d,
      gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m) M.gamma
          (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) =
        Observable.cutoffUpperEllipticity M m m M.gamma M.shellPrefix.gamma_pos
              coarseExponentTwo omega * (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
          Observable.cutoffLowerEllipticityInv M m m M.gamma M.shellPrefix.gamma_pos
              coarseExponentTwo omega * (Annealed.sigmaBar M (m - 1) : ℝ) := fun omega =>
    gaugedEllipticitySum_eq_cutoffObservables M m m M.shellPrefix.gamma_pos
      ((Annealed.sigmaBar M (m - 1) : ℝ)) omega
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M (m - 1) : ℝ) :=
    (Annealed.sigmaBar M (m - 1)).2
  have hX0 : ∀ omega : Cutoff.CutoffSample d,
      0 ≤ gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m)
        M.gamma (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) := fun omega =>
    gaugedEllipticitySum_nonneg (originCube d m) _ hsigpos.le hgammaPos
  have hdom : ∀ omega : Cutoff.CutoffSample d,
      gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m) M.gamma
          (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ≤
        2 * Ccg + Y omega + Z omega + W omega := by
    intro omega
    have hup := hdomYZ omega
    have hlow := hW.dominates omega m hL
    rw [hprof] at hlow
    simp only at hup hlow
    rw [hbridge omega]
    linarith
  have hXm : AEStronglyMeasurable
      (fun omega : Cutoff.CutoffSample d =>
        gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m)
          M.gamma (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_gaugedEllipticitySum_originCube M m m M.shellPrefix.gamma_pos
      _).aestronglyMeasurable
  have hmain := integral_rpow_eight_le_of_shift_add_three_orlicz
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (b := 2 * Ccg) (s1 := 1)
    (by norm_num) (by norm_num) (by norm_num) hA1pos hA2pos hW.scale_pos
    (by linarith) hYm hZm hW.measurable_witness hYt hZt hW.tail hXm hX0 hdom
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  rw [hA1eq]
  have hcinvPos : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstarPos
  have hginvPos : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgammaPos
  have hcinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    calc (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ := by norm_num
      _ ≤ (Disorder.cstar M)⁻¹ :=
          inv_anti₀ hcstarPos (Provider.Disorder.cstar_le_three_halves M)
  have hginv : (4 : ℝ) ≤ M.gamma⁻¹ := by
    calc (4 : ℝ) = ((1 : ℝ) / 4)⁻¹ := by norm_num
      _ ≤ M.gamma⁻¹ := inv_anti₀ hgammaPos M.shellPrefix.gamma_le_quarter
  have ht1 : (1 : ℝ) ≤ (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by
    have h := mul_le_mul hcinv hginv (by norm_num : (0 : ℝ) ≤ 4) hcinvPos.le
    linarith
  have ht0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by linarith
  have hAnn : (0 : ℝ) ≤ Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ :=
    (mul_pos (mul_pos hCcg0 hcinvPos) hginvPos).le
  have hsmall : Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have hnn : (0 : ℝ) ≤ Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
    linarith
  have hexpT : Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := hsmall.trans ht1
  refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
  · have h1 : (0 : ℝ) ≤ orliczEighthMomentScale 1 *
        (Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) := mul_nonneg hk10.le hAnn
    have h2 : (0 : ℝ) ≤ orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
        Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
      mul_nonneg hk20.le (Real.exp_pos _).le
    have h3 : (0 : ℝ) ≤ orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
        Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
      mul_nonneg hk30.le (Real.exp_pos _).le
    linarith
  · have h0 : 2 * Ccg ≤ 2 * Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      le_mul_of_one_le_right (by linarith) ht1
    have h2 : orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hexpT hk20.le
    have h3 : orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hexpT hk30.le
    have hkey : 4 * (2 * Ccg + orliczEighthMomentScale 1 *
          (Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) +
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) +
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ≤
        gaugeEighthLaneConst Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) := by
      rw [gaugeEighthLaneConst]
      linarith
    refine hkey.trans ?_
    calc gaugeEighthLaneConst Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹)
        ≤ C * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
          mul_le_mul_of_nonneg_right hLaneC ht0
      _ = C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by ring

/-! ## The numeric fourth moment -/

/-- **The numeric fourth moment of the Step-2 gauged ellipticity sum.**

on the permitted frozen theorem `coarse_ellipticity_bounds` and on its own
premises. -/
theorem integral_gaugedEllipticitySum_pow_four_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        ∫ omega : Cutoff.CutoffSample d,
            gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                (originCube d m) M.gamma
                (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ^ (4 : ℕ)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
          (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (4 : ℕ) := by
  obtain ⟨C, hC0, hmain⟩ := integral_gaugedEllipticitySum_rpow_eight_le d
  refine ⟨C, hC0, ?_⟩
  intro M m E hstate hE hEupper hgap
  obtain ⟨hmem, hbound⟩ := hmain M m E hstate hE hEupper hgap
  set X : Cutoff.CutoffSample d → ℝ := fun omega =>
    gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m) M.gamma
      (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) with hXdef
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M (m - 1) : ℝ) :=
    (Annealed.sigmaBar M (m - 1)).2
  have hX0 : ∀ omega, 0 ≤ X omega := fun omega =>
    gaugedEllipticitySum_nonneg (originCube d m) _ hsigpos.le hgammaPos
  -- the eighth power is integrable, and its integral is the bounded one
  have hint8 : Integrable (fun omega => X omega ^ (8 : ℕ))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have h := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun omega : Cutoff.CutoffSample d =>
        ‖X omega‖ ^ ((8 : ℝ≥0∞).toReal)) = fun omega => X omega ^ (8 : ℕ) := by
      funext omega
      rw [Real.norm_of_nonneg (hX0 omega),
        show ((8 : ℝ≥0∞).toReal) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [hfun] at h
  have hint4 : Integrable (fun omega => X omega ^ (4 : ℕ))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hmajInt : Integrable
        (fun omega => 1 + X omega ^ (8 : ℕ)) (Cutoff.cutoffSampleLaw M).toMeasure :=
      (integrable_const _).add hint8
    refine hmajInt.mono' ((hmem.aestronglyMeasurable).pow 4) ?_
    refine Filter.Eventually.of_forall fun omega => ?_
    have h0 := hX0 omega
    rw [Real.norm_of_nonneg (by positivity)]
    rcases le_or_gt (X omega) 1 with hle | hlt
    · have : X omega ^ (4 : ℕ) ≤ 1 := pow_le_one₀ h0 hle
      have h8 : (0 : ℝ) ≤ X omega ^ (8 : ℕ) := by positivity
      linarith
    · have : X omega ^ (4 : ℕ) ≤ X omega ^ (8 : ℕ) :=
        pow_le_pow_right₀ hlt.le (by norm_num)
      linarith
  have hcs : (∫ omega, X omega ^ (4 : ℕ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ 2 ≤
      ∫ omega, (X omega ^ (4 : ℕ)) ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    refine sq_integral_le_integral_sq_of_isProbabilityMeasure hint4 ?_
    have hfun : (fun omega : Cutoff.CutoffSample d => (X omega ^ (4 : ℕ)) ^ 2) =
        fun omega => X omega ^ (8 : ℕ) := by
      funext omega
      ring
    rw [hfun]
    exact hint8
  have heq8 : ∫ omega, (X omega ^ (4 : ℕ)) ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ omega, X omega ^ (8 : ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    show (X omega ^ (4 : ℕ)) ^ 2 = X omega ^ (8 : ℝ)
    rw [show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hrpow : (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (8 : ℝ) =
      ((C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (4 : ℕ)) ^ 2 := by
    rw [show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hAnn : (0 : ℝ) ≤ (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (4 : ℕ) := by
    have hcinvPos : (0 : ℝ) < (Disorder.cstar M)⁻¹ :=
      inv_pos.2 (Disorder.cstar_characterization M).1
    have hginvPos : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgammaPos
    positivity
  have hI0 : (0 : ℝ) ≤ ∫ omega, X omega ^ (4 : ℕ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg fun omega => by positivity
  have hsq : (∫ omega, X omega ^ (4 : ℕ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ 2 ≤
      ((C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (4 : ℕ)) ^ 2 := by
    rw [← hrpow]
    exact le_trans (hcs.trans (le_of_eq heq8)) hbound
  by_contra hcon
  push Not at hcon
  exact absurd hsq (not_le.mpr (pow_lt_pow_left₀ hcon hAnn (by norm_num : (2 : ℕ) ≠ 0)))

/-! ## The end-to-end closure -/

/-- **The numeric fourth moment at the cell's own scale-`m` ancestor.**

The geometric half
(`doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor`) puts the per-cell
display on `ancestorAtScale R m`; the probabilistic half
(`integral_gaugedEllipticitySum_pow_ancestorAtScale_eq_originCube`) moves the
annealed fourth moment from there to `cu_m`; and the value of that moment is
the number below.  No printed quantifier changes.

on `hm : R.scale <= m` (the ancestor exists) and on the anchor's own premises.
The measurability that the transport asks for is **produced**, not assumed. -/
theorem integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        ∀ R : TriadicCube d, R.scale ≤ m →
          ∫ omega : Cutoff.CutoffSample d,
              gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                  (ancestorAtScale R m) M.gamma
                  (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ^ (4 : ℕ)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
            (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (4 : ℕ) := by
  obtain ⟨C, hC0, hmain⟩ := integral_gaugedEllipticitySum_pow_four_le d
  refine ⟨C, hC0, ?_⟩
  intro M m E hstate hE hEupper hgap R hm
  have hmeas : AEStronglyMeasurable
      (fun omega : Cutoff.CutoffSample d =>
        gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m)
          M.gamma (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ^ (4 : ℕ))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((measurable_gaugedEllipticitySum_originCube M m m M.shellPrefix.gamma_pos
      _).pow_const 4).aestronglyMeasurable
  rw [integral_gaugedEllipticitySum_pow_ancestorAtScale_eq_originCube M m m R hm
    ((Annealed.sigmaBar M (m - 1) : ℝ)) M.gamma 4 hmeas]
  exact hmain M m E hstate hE hEupper hgap

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
