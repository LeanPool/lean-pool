/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.OnePointRealExtension
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperKernelBridge

/-!
# CruxUpperFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The whole-space penalized comparison family

The comparison family of the exterior penalization at index `n` is the signed
real exterior-penalized resolvent on the live space, assembled at the added
point with the resolvent of the observable there.  The added point is
absorbing, so its value is the observable's value divided by the shift, and
the exterior potential vanishes there.

This module proves the four properties the killed-resolvent comparison
consumes: measurability, boundedness, the resolvent identity, and the
subtraction-free perturbation identity against the kernel resolvent of the
compactified semigroup.  The identification of the kernel resolvent with the
analytic minimal resolvent is the named explicit hypothesis of the analytic
layer.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup ProbabilityTheory
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The real kernel resolvent at the added absorbing point divides by the
shift. -/
theorem onePointKernelResolventReal_infty_eq_div
    (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ} (hlam : 0 < lam)
    {G : OnePoint (Vec d) → ℝ} (hG : Measurable G) :
    R.onePointKernelSemigroup.kernelResolventReal lam G OnePoint.infty =
      G OnePoint.infty / lam := by
  rw [onePointKernelResolventReal_infty R lam hG]
  have hg : (fun t : ℝ ↦ Real.exp (-lam * t) * G OnePoint.infty) =
      fun t : ℝ ↦ G OnePoint.infty * Real.exp (-(lam * t)) := by
    funext t
    rw [neg_mul]
    ring
  rw [hg, MeasureTheory.integral_const_mul]
  have hscale := integral_comp_mul_left_Ioi (fun x : ℝ ↦ Real.exp (-x)) 0 hlam
  rw [mul_zero] at hscale
  rw [hscale, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]
  field_simp

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- **The whole-space penalized comparison family.**  On the live space it is
the signed real exterior-penalized resolvent; at the added point it is the
kernel resolvent of the observable there. -/
def penalizedComparisonFamily {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ)
    (R : PositiveC0ContractiveResolvent (Vec d)) (lam : ℝ)
    (F : OnePoint (Vec d) → ℝ) : OnePoint (Vec d) → ℝ := by
  classical
  exact if h : 0 < lam ∧ Measurable F ∧ ∃ E, ∀ z, |F z| ≤ E then
      onePointRealExtension
          (A.analyticPenalizedResolventReal hV n ⟨lam, h.1⟩
            (fun y ↦ F (y : OnePoint (Vec d)))
            (h.2.1.comp OnePoint.continuous_coe.measurable)
            (fun y ↦ Classical.choose_spec h.2.2 (y : OnePoint (Vec d)))) +
        ({OnePoint.infty} : Set (OnePoint (Vec d))).indicator
          (fun _ ↦ R.onePointKernelSemigroup.kernelResolventReal lam F
            OnePoint.infty)
    else 0

/-- At a live point the comparison family is the signed real
exterior-penalized resolvent of the restricted observable. -/
theorem penalizedComparisonFamily_coe {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ)
    (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ} (hlam : 0 < lam)
    {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) (x : Vec d) :
    A.penalizedComparisonFamily hV n R lam F (x : OnePoint (Vec d)) =
      A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
        (fun y ↦ F (y : OnePoint (Vec d)))
        (hF.comp OnePoint.continuous_coe.measurable)
        (fun y ↦ hFE (y : OnePoint (Vec d))) x := by
  classical
  have hcond : 0 < lam ∧ Measurable F ∧ ∃ E, ∀ z, |F z| ≤ E := ⟨hlam, hF, ⟨E, hFE⟩⟩
  have hxinf : (x : OnePoint (Vec d)) ∉
      ({OnePoint.infty} : Set (OnePoint (Vec d))) := by simp
  rw [penalizedComparisonFamily, dite_eq_left hcond]
  simp only [Pi.add_apply, onePointRealExtension_coe,
    Set.indicator_of_notMem hxinf, add_zero]
  exact A.analyticPenalizedResolventReal_bound_irrel hV n ⟨lam, hlam⟩
    (hF.comp OnePoint.continuous_coe.measurable) _ _ x

/-- At the added point the comparison family is the kernel resolvent of the
observable there. -/
theorem penalizedComparisonFamily_infty {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ}
    (hlam : 0 < lam) {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) :
    A.penalizedComparisonFamily hV n R lam F OnePoint.infty =
      R.onePointKernelSemigroup.kernelResolventReal lam F OnePoint.infty := by
  classical
  have hcond : 0 < lam ∧ Measurable F ∧ ∃ E, ∀ z, |F z| ≤ E := ⟨hlam, hF, ⟨E, hFE⟩⟩
  rw [penalizedComparisonFamily, dite_eq_left hcond]
  simp only [Pi.add_apply, onePointRealExtension_infty,
    Set.indicator_of_mem (Set.mem_singleton (OnePoint.infty : OnePoint (Vec d))),
    zero_add]

/-- The comparison family is measurable. -/
theorem measurable_penalizedComparisonFamily {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ}
    (hlam : 0 < lam) {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) :
    Measurable (A.penalizedComparisonFamily hV n R lam F) := by
  classical
  have hcond : 0 < lam ∧ Measurable F ∧ ∃ E, ∀ z, |F z| ≤ E := ⟨hlam, hF, ⟨E, hFE⟩⟩
  rw [penalizedComparisonFamily, dite_eq_left hcond]
  exact (measurable_onePointRealExtension
    (A.measurable_analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
      (hF.comp OnePoint.continuous_coe.measurable) _)).add
    (measurable_const.indicator OnePoint.isClosed_infty.measurableSet)

/-- The comparison family inherits the sharp maximum-principle bound. -/
theorem abs_penalizedComparisonFamily_le {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ}
    (hlam : 0 < lam) {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) (z : OnePoint (Vec d)) :
    |A.penalizedComparisonFamily hV n R lam F z| ≤ E / lam := by
  induction z using OnePoint.rec with
  | infty =>
      rw [A.penalizedComparisonFamily_infty hV n R hlam hF hFE]
      exact R.onePointKernelSemigroup.norm_kernelResolventReal_le hlam hFE
        OnePoint.infty
  | coe x =>
      rw [A.penalizedComparisonFamily_coe hV n R hlam hF hFE x]
      exact A.abs_analyticPenalizedResolventReal_le hV n ⟨lam, hlam⟩
        (hF.comp OnePoint.continuous_coe.measurable) _ x

/-- The live restriction of the comparison family is the signed real
exterior-penalized resolvent of the live restriction of the observable. -/
theorem penalizedComparisonFamily_comp_coe {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d)) {lam : ℝ}
    (hlam : 0 < lam) {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) :
    (fun y : Vec d ↦
        A.penalizedComparisonFamily hV n R lam F (y : OnePoint (Vec d))) =
      A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
        (fun y ↦ F (y : OnePoint (Vec d)))
        (hF.comp OnePoint.continuous_coe.measurable)
        (fun y ↦ hFE (y : OnePoint (Vec d))) := by
  funext y
  exact A.penalizedComparisonFamily_coe hV n R hlam hF hFE y

/-- **The resolvent identity of the comparison family.** -/
theorem penalizedComparisonFamily_resolventIdentity {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d))
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam)
    {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) :
    A.penalizedComparisonFamily hV n R mu F =
      A.penalizedComparisonFamily hV n R lam F +
        (lam - mu) • A.penalizedComparisonFamily hV n R lam
          (A.penalizedComparisonFamily hV n R mu F) := by
  have hYm : Measurable (A.penalizedComparisonFamily hV n R mu F) :=
    A.measurable_penalizedComparisonFamily hV n R hmu hF hFE
  have hYb : ∀ z, |A.penalizedComparisonFamily hV n R mu F z| ≤ E / mu :=
    A.abs_penalizedComparisonFamily_le hV n R hmu hF hFE
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  induction z using OnePoint.rec with
  | infty =>
      rw [A.penalizedComparisonFamily_infty hV n R hmu hF hFE,
        A.penalizedComparisonFamily_infty hV n R hlam hF hFE,
        A.penalizedComparisonFamily_infty hV n R hlam hYm hYb,
        onePointKernelResolventReal_infty_eq_div R hmu hF,
        onePointKernelResolventReal_infty_eq_div R hlam hF,
        onePointKernelResolventReal_infty_eq_div R hlam hYm,
        A.penalizedComparisonFamily_infty hV n R hmu hF hFE,
        onePointKernelResolventReal_infty_eq_div R hmu hF]
      field_simp
      ring
  | coe x =>
      rw [A.penalizedComparisonFamily_coe hV n R hmu hF hFE x,
        A.penalizedComparisonFamily_coe hV n R hlam hF hFE x,
        A.penalizedComparisonFamily_coe hV n R hlam hYm hYb x]
      have hrestrict := A.penalizedComparisonFamily_comp_coe hV n R hmu hF hFE
      rw [A.analyticPenalizedResolventReal_congr hV n ⟨lam, hlam⟩ hrestrict
        (hYm.comp OnePoint.continuous_coe.measurable)
        (A.measurable_analyticPenalizedResolventReal hV n ⟨mu, hmu⟩
          (hF.comp OnePoint.continuous_coe.measurable) _)
        (fun y ↦ hYb (y : OnePoint (Vec d)))
        (A.abs_analyticPenalizedResolventReal_le hV n ⟨mu, hmu⟩
          (hF.comp OnePoint.continuous_coe.measurable) _) x]
      exact A.analyticPenalizedResolventReal_resolventIdentity hV n ⟨mu, hmu⟩
        ⟨lam, hlam⟩ (hF.comp OnePoint.continuous_coe.measurable) _ x

/-- **The perturbation identity of the comparison family.**  The family solves
the same bounded-potential perturbation equation as the real kernel resolvent
of the compactified semigroup. -/
theorem penalizedComparisonFamily_perturbation {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) {lam : ℝ}
    (hlam : 0 < lam) {F : OnePoint (Vec d) → ℝ} (hF : Measurable F) {E : ℝ}
    (hFE : ∀ z, |F z| ≤ E) :
    A.penalizedComparisonFamily hV n R lam F =
      R.onePointKernelSemigroup.kernelResolventReal lam F -
        R.onePointKernelSemigroup.kernelResolventReal lam
          (fun y ↦ onePointRealExtension
            (wholeSpacePenalizationPotential V n) y *
              A.penalizedComparisonFamily hV n R lam F y) := by
  have hE : 0 ≤ E := (abs_nonneg (F OnePoint.infty)).trans (hFE OnePoint.infty)
  have hFm : Measurable fun y : Vec d ↦ F (y : OnePoint (Vec d)) :=
    hF.comp OnePoint.continuous_coe.measurable
  have hFb : ∀ y : Vec d, |F (y : OnePoint (Vec d))| ≤ E := fun y ↦ hFE _
  have hqm : Measurable (onePointRealExtension
      (wholeSpacePenalizationPotential V n)) :=
    measurable_onePointRealExtension
      (measurable_wholeSpacePenalizationPotential hV n)
  have hYm : Measurable (A.penalizedComparisonFamily hV n R lam F) :=
    A.measurable_penalizedComparisonFamily hV n R hlam hF hFE
  have hload : Measurable fun y ↦ onePointRealExtension
      (wholeSpacePenalizationPotential V n) y *
        A.penalizedComparisonFamily hV n R lam F y := hqm.mul hYm
  have hloadcoe : (fun y : Vec d ↦ onePointRealExtension
      (wholeSpacePenalizationPotential V n) (y : OnePoint (Vec d)) *
        A.penalizedComparisonFamily hV n R lam F (y : OnePoint (Vec d))) =
      fun y : Vec d ↦ wholeSpacePenalizationPotential V n y *
        A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
          (fun z ↦ F (z : OnePoint (Vec d))) hFm hFb y := by
    funext y
    rw [onePointRealExtension_coe,
      A.penalizedComparisonFamily_coe hV n R hlam hF hFE y]
  have hload2 : R.kernelSemigroup.kernelResolventReal lam
      (fun y : Vec d ↦ onePointRealExtension
        (wholeSpacePenalizationPotential V n) (y : OnePoint (Vec d)) *
          A.penalizedComparisonFamily hV n R lam F (y : OnePoint (Vec d))) =
      R.kernelSemigroup.kernelResolventReal lam
        (fun y : Vec d ↦ wholeSpacePenalizationPotential V n y *
          A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
            (fun z ↦ F (z : OnePoint (Vec d))) hFm hFb y) :=
    congrArg (fun g : Vec d → ℝ ↦
      R.kernelSemigroup.kernelResolventReal lam g) hloadcoe
  funext z
  simp only [Pi.sub_apply]
  induction z using OnePoint.rec with
  | infty =>
      rw [A.penalizedComparisonFamily_infty hV n R hlam hF hFE,
        onePointKernelResolventReal_infty_eq_zero R lam hload (by simp), sub_zero]
  | coe x =>
      have hstep := A.analyticPenalizedResolventReal_perturbation hV n
        ⟨lam, hlam⟩ hFm hE hFb x
      have h1 := A.kernelResolventReal_eq_analyticMinimalResolventReal R hid
        ⟨lam, hlam⟩ hFm hFb x
      have h2 := A.kernelResolventReal_eq_analyticMinimalResolventReal R hid
        ⟨lam, hlam⟩
        ((measurable_wholeSpacePenalizationPotential hV n).mul
          (A.measurable_analyticPenalizedResolventReal hV n ⟨lam, hlam⟩ hFm hFb))
        (D := (n : ℝ) * (E / lam)) (fun y ↦ by
          rw [Pi.mul_apply, abs_mul,
            abs_of_nonneg (wholeSpacePenalizationPotential_nonneg V n y)]
          exact mul_le_mul (wholeSpacePenalizationPotential_le V n y)
            (A.abs_analyticPenalizedResolventReal_le hV n ⟨lam, hlam⟩ hFm hFb y)
            (abs_nonneg _) (Nat.cast_nonneg n)) x
      have h2' : R.kernelSemigroup.kernelResolventReal lam
          (fun y : Vec d ↦ wholeSpacePenalizationPotential V n y *
            A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
              (fun y ↦ F (y : OnePoint (Vec d))) hFm hFb y) x =
          A.analyticMinimalResolventReal ⟨lam, hlam⟩
            (fun y : Vec d ↦ wholeSpacePenalizationPotential V n y *
              A.analyticPenalizedResolventReal hV n ⟨lam, hlam⟩
                (fun y ↦ F (y : OnePoint (Vec d))) hFm hFb y) _ _ x := h2
      rw [onePointKernelResolventReal_coe R hcons lam hF x,
        onePointKernelResolventReal_coe R hcons lam hload x]
      show A.penalizedComparisonFamily hV n R lam F (x : OnePoint (Vec d)) =
          R.kernelSemigroup.kernelResolventReal lam
              (fun y : Vec d ↦ F (y : OnePoint (Vec d))) x -
            R.kernelSemigroup.kernelResolventReal lam
              (fun y : Vec d ↦ onePointRealExtension
                (wholeSpacePenalizationPotential V n) (y : OnePoint (Vec d)) *
                  A.penalizedComparisonFamily hV n R lam F
                    (y : OnePoint (Vec d))) x
      rw [hload2, A.penalizedComparisonFamily_coe hV n R hlam hF hFE x, hstep,
        ← h1, ← h2']

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
