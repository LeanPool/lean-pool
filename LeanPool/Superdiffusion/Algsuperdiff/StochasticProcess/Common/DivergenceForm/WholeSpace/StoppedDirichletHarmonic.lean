/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Process

/-!
# StoppedDirichletHarmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Stopped identities for functions represented by the exit distribution

Let `Q` be the continuous-path process of a conservative Feller kernel semigroup and let `U` be an
open set with exit time `tau`.  A function `h` is *represented by the exit distribution of `U`*
when
  `h y = E_y[h(X_tau)]`  for every `y` of `U`

(`HasExitMeanValueOn`).  This is the mean-value formulation of harmonicity relative to the
process: it says nothing about smoothness, and it is a statement about `h` and `U` alone, not
about the conclusions proved from it below.

Two identities for the stopped process follow, for every deterministic horizon `t`.

* A function represented by the exit distribution is also represented by the *stopped* position
  (`integral_eval_exitTimeTrunc_eq_of_hasExitMeanValueOn`):
    `E_x[h(X_{t and tau})] = h x`.
  The proof splits the path space at the survival event `{t < tau}`.  Off it the stopped position
  is already the exit position.  On it the stopped position is `X_t`, where the representation is
  available because `X_t` lies in `U`; the restricted Markov property at the deterministic time
  `t` then rewrites the resulting restarted expectation as the expectation of the exit value of
  the shifted path, and shifting does not move the exit position once the exit time is finite.

* Subtracting a multiple of the expected exit time `w y = E_y[tau]` produces the second stopped
  identity (`integral_eval_exitTimeTrunc_eq_add_of_hasExitMeanValueOn`): if
    `u = h - sigma * w`,
  then
    `E_x[u(X_{t and tau})] = u x + sigma * E_x[t and tau]`.
  The whole content of the second identity beyond the first is the remaining-exit-time identity of
  `StoppedDirichlet.lean`, whose proof needs no generator either.  The expected stopped time is
  also written with the horizon exposed, `E_x[t and tau] = t - E_x[(t - tau) on {tau <= t}]`.

Neither identity refers to a generator or to a domain of one.  What must be supplied from the
analytic side is exactly the hypothesis `HasExitMeanValueOn`: that the continuous representative
of the Dirichlet solution with the given boundary values is reproduced by the exit distribution of
the domain.
-/

namespace DivergenceFormProcess.StoppedDirichlet

open MeasureTheory ProbabilityTheory
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- A function is represented by the exit distribution of `U` when, from every starting point of
`U`, its value is the expectation of its value at the exit position. -/
def HasExitMeanValueOn (U : Set alpha) (h : alpha → ℝ) : Prop :=
  ∀ y ∈ U, ∫ omega, h (exitPosition U omega)
    ∂(IsConservative.continuousProcess P hP y) = h y

variable [LocallyCompactSpace alpha]

/-- **A function represented by the exit distribution is represented by the stopped position.**
For every deterministic horizon, the expectation of the function at the position stopped on
leaving `U` is its value at the starting point. -/
theorem integral_eval_exitTimeTrunc_eq_of_hasExitMeanValueOn
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {h : alpha → ℝ} (hh : Measurable h)
    (C : ℝ) (hC : ∀ y, ‖h y‖ ≤ C) (hharm : HasExitMeanValueOn P hP U h)
    (t : NNReal) {x : alpha} (hx : x ∈ U)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    ∫ omega, h (omega (ContinuousPath.exitTimeTrunc U t omega))
      ∂(IsConservative.continuousProcess P hP x) = h x := by
  set mu := IsConservative.continuousProcess P hP x with hmu
  set S := survivalEvent (alpha := alpha) U t with hSdef
  have hSfilt := measurableSet_survivalEvent_canonicalFiltration (alpha := alpha) hU t
  have hSmeas := measurableSet_survivalEvent (alpha := alpha) hU t
  have hFmeas : StronglyMeasurable (fun eta : ContinuousPath alpha ↦ h (exitPosition U eta)) :=
    (hh.comp (measurable_exitPosition hU)).stronglyMeasurable
  have hFbound : ∀ eta : ContinuousPath alpha, ‖h (exitPosition U eta)‖ ≤ C := fun eta ↦ hC _
  have hFint : Integrable (fun eta : ContinuousPath alpha ↦ h (exitPosition U eta)) mu :=
    Integrable.of_bound hFmeas.aestronglyMeasurable C (Filter.Eventually.of_forall hFbound)
  have hTint : Integrable (fun omega : ContinuousPath alpha ↦
      h (omega (ContinuousPath.exitTimeTrunc U t omega))) mu :=
    Integrable.of_bound
      ((hh.comp (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU
          t))).stronglyMeasurable).aestronglyMeasurable C (Filter.Eventually.of_forall fun _ ↦ hC _)
  have haefin : ∀ᵐ omega ∂mu, ContinuousPath.exitTime U omega < ⊤ :=
    ae_lt_top (ContinuousPath.measurable_exitTime U hU) hwfin
  have hsurvival : ∫ omega in S, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu =
      ∫ omega in S, h (exitPosition U omega) ∂mu := by
    have hone : ∫ omega in S, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu =
        ∫ omega in S, h (omega t) ∂mu := by
      refine setIntegral_congr_fun hSmeas fun omega homega ↦ ?_
      rw [exitTimeTrunc_of_mem_survivalEvent homega]
    have htwo : ∫ omega in S, h (omega t) ∂mu =
        ∫ omega in S, (∫ eta, h (exitPosition U eta)
          ∂(IsConservative.continuousProcess P hP (omega t))) ∂mu := by
      refine setIntegral_congr_fun hSmeas fun omega homega ↦ ?_
      exact (hharm (omega t) (ContinuousPath.mem_of_lt_exitTime U omega t homega)).symm
    have hthree : ∫ omega in S, (∫ eta, h (exitPosition U eta)
          ∂(IsConservative.continuousProcess P hP (omega t))) ∂mu =
        ∫ omega in S, h (exitPosition U (ContinuousPath.shift t omega)) ∂mu :=
      (setIntegral_shift P hP hFeller hK t x _ hFmeas C hFbound S hSfilt).symm
    have hfour : ∫ omega in S, h (exitPosition U (ContinuousPath.shift t omega)) ∂mu =
        ∫ omega in S, h (exitPosition U omega) ∂mu := by
      refine setIntegral_congr_ae hSmeas ?_
      filter_upwards [haefin] with omega hfin homega
      rw [exitPosition_shift homega hfin.ne]
    rw [hone, htwo, hthree, hfour]
  have hexit : ∫ omega in Sᶜ, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu =
      ∫ omega in Sᶜ, h (exitPosition U omega) ∂mu := by
    refine setIntegral_congr_fun hSmeas.compl fun omega homega ↦ ?_
    rw [eval_exitTimeTrunc_of_notMem_survivalEvent homega]
  calc ∫ omega, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu
      = ∫ omega in S, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu +
          ∫ omega in Sᶜ, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu :=
        (integral_add_compl hSmeas hTint).symm
    _ = ∫ omega in S, h (exitPosition U omega) ∂mu +
          ∫ omega in Sᶜ, h (exitPosition U omega) ∂mu := by rw [hsurvival, hexit]
    _ = ∫ omega, h (exitPosition U omega) ∂mu := integral_add_compl hSmeas hFint
    _ = h x := hharm x hx

/-- **The stopped identity for a function with a remaining-time correction.**  If `u` is the
difference of a function represented by the exit distribution and a multiple of the expected exit
time, then the expectation of `u` at the stopped position exceeds its value at the starting point
by the same multiple of the expected stopped time. -/
theorem integral_eval_exitTimeTrunc_eq_add_of_hasExitMeanValueOn
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {h : alpha → ℝ} (hh : Measurable h)
    (C : ℝ) (hC : ∀ y, ‖h y‖ ≤ C) (hharm : HasExitMeanValueOn P hP U h)
    (sigma : ℝ) {u : alpha → ℝ}
    (hu : ∀ y, u y = h y - sigma * (expectedExitTime P hP U y).toReal)
    (t : NNReal) {x : alpha} (hx : x ∈ U)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    ∫ omega, u (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x) =
      u x + sigma * ∫ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x) := by
  set mu := IsConservative.continuousProcess P hP x with hmu
  have hhint : Integrable (fun omega : ContinuousPath alpha ↦
      h (omega (ContinuousPath.exitTimeTrunc U t omega))) mu :=
    Integrable.of_bound
      ((hh.comp (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU
          t))).stronglyMeasurable).aestronglyMeasurable C (Filter.Eventually.of_forall fun _ ↦ hC _)
  have hwint := integrable_expectedExitTime_eval_exitTimeTrunc P hP hFeller hK hU t hx hwfin
  have hsplit : ∫ omega, u (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu =
      (∫ omega, h (omega (ContinuousPath.exitTimeTrunc U t omega)) ∂mu) -
        sigma * ∫ omega, (expectedExitTime P hP U
          (omega (ContinuousPath.exitTimeTrunc U t omega))).toReal ∂mu := by
    simp only [hu]
    rw [integral_sub hhint (hwint.const_mul sigma), integral_const_mul]
  have hharmonic := integral_eval_exitTimeTrunc_eq_of_hasExitMeanValueOn
    P hP hFeller hK hU hh C hC hharm t hx hwfin
  have hremaining := integral_expectedExitTime_add P hP hFeller hK hU t hx hwfin
  rw [hsplit, hharmonic, hu x, ← hremaining]
  ring

omit [LocallyCompactSpace alpha] in
/-- The expected stopped time with the horizon exposed: it is the horizon less the expected
shortfall on the event that the exit has already occurred. -/
theorem integral_exitTimeTrunc_eq_sub {U : Set alpha} (hU : IsOpen U) (t : NNReal) (x : alpha) :
    (∫ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x)) =
      (t : ℝ) - ∫ omega, Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega
        ∂(IsConservative.continuousProcess P hP x) := by
  set mu := IsConservative.continuousProcess P hP x with hmu
  have hSmeas := measurableSet_survivalEvent (alpha := alpha) hU t
  have hgmeas : Measurable fun omega : ContinuousPath alpha ↦
      Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega :=
    (measurable_const.sub
      (ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime U hU))).indicator
      hSmeas.compl
  have hgbound : ∀ omega : ContinuousPath alpha,
      ‖Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega‖ ≤ (t : ℝ) := by
    intro omega
    by_cases homega : omega ∈ (survivalEvent U t)ᶜ
    · have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp homega
      have hfin : ContinuousPath.exitTime U omega ≠ ⊤ := (hle.trans_lt ENNReal.coe_lt_top).ne
      have hreal : (ContinuousPath.exitTime U omega).toReal ≤ (t : ℝ) := by
        simpa [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top hle
      rw [Set.indicator_of_mem homega, Real.norm_of_nonneg (by linarith)]
      have hpos : (0 : ℝ) ≤ (ContinuousPath.exitTime U omega).toReal := ENNReal.toReal_nonneg
      linarith
    · rw [Set.indicator_of_notMem homega, norm_zero]
      exact NNReal.zero_le_coe
  have hgint : Integrable (fun omega : ContinuousPath alpha ↦
      Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega) mu :=
    Integrable.of_bound hgmeas.stronglyMeasurable.aestronglyMeasurable (t : ℝ)
      (Filter.Eventually.of_forall hgbound)
  have hpointwise : ∀ omega : ContinuousPath alpha,
      ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ) =
        (t : ℝ) - Set.indicator (survivalEvent U t)ᶜ
          (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega := by
    intro omega
    by_cases homega : omega ∈ survivalEvent U t
    · rw [Set.indicator_of_notMem (by simpa using homega),
        exitTimeTrunc_of_mem_survivalEvent homega, sub_zero]
    · have hmemc : omega ∈ (survivalEvent U t)ᶜ := homega
      rw [Set.indicator_of_mem hmemc, exitTimeTrunc_of_notMem_survivalEvent homega]
      have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp homega
      have hfin : ContinuousPath.exitTime U omega ≠ ⊤ := (hle.trans_lt ENNReal.coe_lt_top).ne
      rw [ENNReal.coe_toNNReal_eq_toReal]
      ring
  simp only [hpointwise]
  rw [integral_sub (integrable_const _) hgint]
  simp

end Process

section OnePoint

open HCPolySupport
open scoped ENNReal

variable {d : ℕ} {R : PositiveC0ContractiveResolvent (Vec d)}

/-- The image of an open subset of the live space is open in the compactification. -/
theorem isOpen_image_coe_of_isOpen {V : Set (Vec d)} (hV : IsOpen V) :
    IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' V) :=
  OnePoint.isOpen_image_coe.mpr hV

end OnePoint

end

end DivergenceFormProcess.StoppedDirichlet
