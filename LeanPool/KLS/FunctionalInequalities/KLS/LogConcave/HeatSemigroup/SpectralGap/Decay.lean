/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Centered heat decay under a form-domain Poincare inequality

The operator is the actual closed weighted gradient of a full-dimensional log-concave law.
The gap is an explicit hypothesis on its entire form domain. Positive-time smoothing and the
energy derivative extend the result from generator-domain data to arbitrary L2 data.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- The actual heat operator fixes every L2 constant. -/
theorem const_fixed {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    operator m B hν hi ht (L2.const ν c) = L2.const ν c := by
  have hc : L2.const ν c = c • L2.const ν 1 := by
    simpa using L2.const_smul ν c 1
  rw [hc, map_smul]
  simp only [one m B hν hi ht]

/-- Centering commutes with the actual heat operator. -/
theorem center_operator {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν (operator m B hν hi ht f) =
      operator m B hν hi ht (L2.center ν f) := by
  rw [L2.center, L2.center, HeatSemigroup.mean m B hν hi ht f, map_sub,
    const_fixed m B hν hi ht]

/-- Squared norm of a positive-time orbit has derivative minus twice its closed-gradient energy. -/
theorem hasDerivAt_norm_sq_of_pos (f : Lp ℝ 2 (ν : Measure V))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ‖Generated.apply (hν.closedWeightedOperator m B hi)
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) s f‖ ^ 2)
      (-2 * ‖hν.closedWeightedOperator m B hi
        ⟨Generated.apply (hν.closedWeightedOperator m B hi)
          (hν.closedWeightedOperator_isClosed m B hi)
          (hν.dense_domain_closedWeightedOperator m B hi) t f,
          (Generated.mem_adjointComp_domain_apply_of_pos
            (hν.closedWeightedOperator m B hi)
            (hν.closedWeightedOperator_isClosed m B hi)
            (hν.dense_domain_closedWeightedOperator m B hi) f ht).2⟩‖ ^ 2) t := by
  let T := hν.closedWeightedOperator m B hi
  let hT := hν.closedWeightedOperator_isClosed m B hi
  let hd := hν.dense_domain_closedWeightedOperator m B hi
  have hmem := Generated.mem_adjointComp_domain_apply_of_pos T hT hd f ht
  have hder := (Generated.hasDerivAt_apply_of_pos T hT hd f ht).norm_sq
  have henergy := inner_adjointComp hd
    (⟨Generated.apply T hT hd t f, hmem⟩ : (adjointComp T).domain) hmem.2
  convert hder using 1
  simp only [inner_neg_right, mul_neg]
  rw [real_inner_comm, henergy, real_inner_self_eq_norm_sq]
  ring

/-- An explicit form-domain Poincare inequality gives squared-norm decay of every centered
L2 datum, including time zero. -/
theorem norm_center_operator_sq_le_exp (C : ℝ) (hC : 0 < C)
    (hgap :
      ∀ u : (hν.closedWeightedOperator m B hi).domain,
        ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    ‖L2.center ν (operator m B hν hi ht f)‖ ^ 2 ≤ Real.exp (-2 * t / C) * ‖L2.center ν f‖ ^ 2 := by
  let T := hν.closedWeightedOperator m B hi
  let hT := hν.closedWeightedOperator_isClosed m B hi
  let hd := hν.dense_domain_closedWeightedOperator m B hi
  let g := L2.center ν f
  let F : ℝ → ℝ := fun s => ‖Generated.apply T hT hd s g‖ ^ 2
  have hmean : ∀ s : ℝ, 0 ≤ s → L2.mean ν (Generated.apply T hT hd s g) = 0 := by
    intro s hs
    change L2.mean ν (operator m B hν hi hs g) = 0
    rw [HeatSemigroup.mean m B hν hi hs g]
    exact L2.mean_center ν f
  have hcenter :
    ∀ s : ℝ, 0 ≤ s → L2.center ν (Generated.apply T hT hd s g) = Generated.apply T hT hd s g := by
    intro s hs
    simp [L2.center, hmean s hs]
  have hcont : ContinuousOn F (Ici 0) := by
    exact (((Generated.continuousOn T hT hd g).norm).pow 2)
  have hder :
    ∀ s : ℝ,
      ∀ hs : 0 < s,
        HasDerivAt F
          (-2 *
            ‖T
                  ⟨Generated.apply T hT hd s g,
                    (Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hs).2⟩‖ ^
              2)
          s := by
    intro s hs
    convert hasDerivAt_norm_sq_of_pos m B hν hi g hs using 1
  let G : ℝ → ℝ := fun s => Real.exp (2 * s / C) * F s
  have hGcont : ContinuousOn G (Ici 0) := by
    exact
      ((Real.continuous_exp.comp
              (continuous_const.mul continuous_id |>.div_const C)).continuousOn).mul
        hcont
  have hGder : ∀ s ∈ interior (Ici (0 : ℝ)), deriv G s ≤ 0 := by
    intro s hs
    have hspos : 0 < s := by simpa using hs
    have hmem := Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hspos
    have hgap' := hgap ⟨Generated.apply T hT hd s g, hmem.2⟩
    rw [hcenter s hspos.le] at hgap'
    have hF := hder s hspos
    have he :
      HasDerivAt (fun x : ℝ => Real.exp (2 * x / C)) (Real.exp (2 * s / C) * (2 / C)) s := by
      have h := (Real.hasDerivAt_exp ((2 / C) * s)).comp s ((hasDerivAt_id s).const_mul (2 / C))
      have heq (x : ℝ) : (2 / C) * x = 2 * x / C := by ring
      simpa only [Function.comp_def, heq, mul_one] using h
    have hprod := he.mul hF
    have hvalue :
      deriv G s =
        Real.exp (2 * s / C) * (2 / C) * F s +
          Real.exp (2 * s / C) * (-2 * ‖T ⟨Generated.apply T hT hd s g, hmem.2⟩‖ ^ 2) := by
      change HasDerivAt G _ s at hprod
      convert hprod.deriv using 1
    rw [hvalue]
    have hmul : (2 / C) * F s ≤ 2 * ‖T ⟨Generated.apply T hT hd s g, hmem.2⟩‖ ^ 2 := by
      calc
        (2 / C) * F s = (2 * F s) / C := by ring
        _ ≤ 2 * ‖T ⟨Generated.apply T hT hd s g, hmem.2⟩‖ ^ 2 :=
          (div_le_iff₀ hC).2 (by dsimp [F]; nlinarith [hgap'])
    nlinarith [Real.exp_pos (2 * s / C)]
  have hanti :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hGcont
      (fun s hs =>
        (by
          have hspos : 0 < s := by simpa using hs
          have hF := hder s hspos
          have he : DifferentiableAt ℝ (fun x : ℝ => Real.exp (2 * x / C)) s :=
            ((Real.hasDerivAt_exp _).comp s
                (((hasDerivAt_id s).const_mul 2).div_const C)).differentiableAt
          exact (he.mul hF.differentiableAt).differentiableWithinAt))
      hGder
  have hGle := hanti (by simp : (0 : ℝ) ∈ Ici 0) ht ht
  have hzero : F 0 = ‖g‖ ^ 2 := by simp [F, Generated.zero_time]
  have hmain : F t ≤ Real.exp (-2 * t / C) * ‖g‖ ^ 2 := by
    dsimp [G] at hGle
    rw [hzero] at hGle
    simp only [mul_zero, zero_div, Real.exp_zero, one_mul] at hGle
    have hmul := mul_le_mul_of_nonneg_left hGle (Real.exp_pos (-2 * t / C)).le
    have : -2 * t / C + 2 * t / C = 0 := by ring
    calc
      F t = Real.exp (-2 * t / C) * (Real.exp (2 * t / C) * F t) := by
        rw [← mul_assoc, ← Real.exp_add, this]
        simp
      _ ≤ _ := hmul
  rw [center_operator m B hν hi ht]
  exact hmain

/-- Self-adjointness and the half-time law turn centered heat correlation into a squared norm.
The exponent is `-t/C`, while the squared-norm decay above has exponent `-2t/C`. -/
theorem inner_center_operator_le_exp (C : ℝ) (hC : 0 < C)
    (hgap : ∀ u : (hν.closedWeightedOperator m B hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ (L2.center ν f) (operator m B hν hi ht (L2.center ν f)) ≤
      Real.exp (-t / C) * ‖L2.center ν f‖ ^ 2 := by
  let g := L2.center ν f
  have hh : 0 ≤ t / 2 := by linarith
  have hadd : operator m B hν hi ht g =
      operator m B hν hi hh (operator m B hν hi hh g) := by
    have htime : t / 2 + t / 2 = t := by ring
    simpa only [htime] using (HeatSemigroup.add m B hν hi hh hh g)
  have hcorr : inner ℝ g (operator m B hν hi ht g) =
      ‖operator m B hν hi hh g‖ ^ 2 := by
    rw [hadd, ← HeatSemigroup.symmetric m B hν hi hh g
      (operator m B hν hi hh g), real_inner_self_eq_norm_sq]
  have hnorm := norm_center_operator_sq_le_exp m B hν hi C hC hgap f hh
  rw [center_operator m B hν hi hh] at hnorm
  have hexp : -2 * (t / 2) / C = -t / C := by ring
  rw [hexp] at hnorm
  change inner ℝ g (operator m B hν hi ht g) ≤
    Real.exp (-t / C) * ‖g‖ ^ 2
  rw [hcorr]
  exact hnorm

/-- Heat correlation of the centered indicator of a measurable set. The probability mass may
be zero or one, and time zero is included. -/
theorem inner_center_indicator_le_exp (C : ℝ) (hC : 0 < C)
    (hgap : ∀ u : (hν.closedWeightedOperator m B hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    let χ := indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
    inner ℝ (L2.center ν χ) (operator m B hν hi ht (L2.center ν χ)) ≤
      Real.exp (-t / C) * (ν : Measure V).real D * (1 - (ν : Measure V).real D) := by
  dsimp
  have h := inner_center_operator_le_exp m B hν hi C hC hgap
    (indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)) ht
  rw [L2.norm_center_indicatorConstLp_sq] at h
  simpa only [mul_assoc] using h

/-- Literature Poincare bounds give the actual unit-gradient heat decay for all L2 data. -/
theorem norm_center_operator_sq_le_exp_of_literature_le (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    ‖L2.center ν (operator m (ContinuousLinearMap.id ℝ V) hν hi ht f)‖ ^ 2 ≤
      Real.exp (-2 * t / (C : ℝ)) * ‖L2.center ν f‖ ^ 2 := by
  exact norm_center_operator_sq_le_exp m (ContinuousLinearMap.id ℝ V) hν hi
    (C : ℝ) (by exact_mod_cast hC)
    (fun u => hν.closedWeightedOperator_id_gap_of_literature_le m hi C hLit u) f ht

/-- The literature optimum controls centered indicator correlation under the actual unit heat
semigroup, with no additional form-domain hypothesis. -/
theorem inner_center_indicator_le_exp_of_literature_le (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    let χ := indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
    inner ℝ (L2.center ν χ)
      (operator m (ContinuousLinearMap.id ℝ V) hν hi ht (L2.center ν χ)) ≤
      Real.exp (-t / (C : ℝ)) * (ν : Measure V).real D *
        (1 - (ν : Measure V).real D) := by
  exact inner_center_indicator_le_exp m (ContinuousLinearMap.id ℝ V) hν hi
    (C : ℝ) (by exact_mod_cast hC)
    (fun u => hν.closedWeightedOperator_id_gap_of_literature_le m hi C hLit u) hD ht

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
