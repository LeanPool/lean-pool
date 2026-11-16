/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Existence
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian motion in the sense of Mathlib

A `BrownianMotion P` in the sense of `LevyStochCalc.Brownian.Construction`, restricted along the
coercion `ℝ≥0 → ℝ`, is a Brownian motion in the sense of `ProbabilityTheory.IsBrownianReal`: its
value at time `t` has law `gaussianReal 0 t`, its increments along a monotone tuple are mutually
independent, and its paths are almost surely continuous. Mutual independence of the increments
comes from the σ-algebra field `BrownianMotion.joint_increment_independent` through
`iIndep_of_indep_biSup_lt`, a chain criterion for mutual independence of a family of σ-algebras
indexed by a linear order.

## Main statements

* `iIndep_of_indep_biSup_lt` — a family of σ-algebras indexed by a linear order is mutually
  independent as soon as each member is independent of the supremum of its predecessors.
* `BrownianMotion.hasLaw_eval`, `BrownianMotion.hasLaw_increment` — the marginal laws.
* `BrownianMotion.hasIndepIncrements` — mutual independence of the increments.
* `BrownianMotion.isPreBrownianReal`, `BrownianMotion.isBrownianReal`,
  `BrownianMotion.isGaussianProcess` — the Mathlib predicates.
* `BrownianMotion.ofIsPreBrownianReal_w_ae_eq` — the round trip through
  `BrownianMotion.ofIsPreBrownianReal` recovers the paths at nonnegative times.
-/

@[expose] public section

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A family of σ-algebras indexed by a linear order is mutually independent as soon as each
member is independent of the supremum of the members of strictly smaller index. -/
theorem iIndep_of_indep_biSup_lt {ι : Type*} [LinearOrder ι] {m : ι → MeasurableSpace Ω}
    (h : ∀ i, Indep (⨆ j < i, m j) (m i) P) : iIndep m P := by
  classical
  have key : ∀ (S : Finset ι) (f : ι → Set Ω), (∀ i ∈ S, MeasurableSet[m i] (f i)) →
      P (⋂ i ∈ S, f i) = ∏ i ∈ S, P (f i) := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro f _; simp
    | insert a s hlt ih =>
      intro f hf
      have hane : a ∉ s := fun ha ↦ lt_irrefl a (hlt a ha)
      have hfs : ∀ i ∈ s, MeasurableSet[m i] (f i) := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hmeas : MeasurableSet[⨆ j < a, m j] (⋂ i ∈ s, f i) :=
        Finset.measurableSet_biInter (α := Ω) (m := ⨆ j < a, m j) s fun i hi ↦
          le_iSup₂ (f := fun j (_ : j < a) ↦ m j) i (hlt i hi) _ (hfs i hi)
      rw [Finset.set_biInter_insert, Finset.prod_insert hane,
        (Indep_iff _ _ _).1 (h a).symm _ _ (hf a (Finset.mem_insert_self a s)) hmeas,
        ih f hfs]
  rw [iIndep_iff]
  intro S f hf
  exact key S f hf

namespace BrownianMotion

/-- The value of a Brownian motion at a nonnegative time `t` has law `gaussianReal 0 t`. -/
theorem hasLaw_eval (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (W.W (t : ℝ)) (gaussianReal 0 t) P := by
  have hzero : (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) =ᵐ[P] W.W (t : ℝ) := by
    filter_upwards [W.initial_zero] with ω hω using by simp [hω]
  rcases eq_or_lt_of_le t.coe_nonneg with h | h
  · have ht0 : t = 0 := NNReal.coe_injective h.symm
    subst ht0
    rw [gaussianReal_zero_var]
    refine HasLaw.congr (X := fun _ : Ω ↦ (0 : ℝ)) ⟨measurable_const.aemeasurable, by simp⟩ ?_
    filter_upwards [W.initial_zero] with ω hω using by simpa using hω
  · have hmap : P.map (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) = gaussianReal 0 t := by
      rw [W.increment_gaussian (s := 0) (t := (t : ℝ)) le_rfl h]
      congr 1
      apply NNReal.coe_injective
      change (t : ℝ) - 0 = (t : ℝ)
      rw [sub_zero]
    exact HasLaw.congr (X := fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω)
      ⟨((W.measurable_eval _).sub (W.measurable_eval 0)).aemeasurable, hmap⟩ hzero.symm

/-- For `s ≤ t` the increment `W t - W s` of a Brownian motion has law `gaussianReal 0 (t - s)`. -/
theorem hasLaw_increment (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω ↦ W.W (t : ℝ) ω - W.W (s : ℝ) ω) (gaussianReal 0 (t - s)) P := by
  rcases eq_or_lt_of_le hst with h | h
  · subst h
    have hfun : (fun ω ↦ W.W (s : ℝ) ω - W.W (s : ℝ) ω) = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; ring
    rw [tsub_self, gaussianReal_zero_var, hfun]
    exact ⟨measurable_const.aemeasurable, by simp⟩
  · refine ⟨((W.measurable_eval _).sub (W.measurable_eval _)).aemeasurable, ?_⟩
    rw [W.increment_gaussian s.coe_nonneg (NNReal.coe_lt_coe.2 h)]
    congr 1
    apply NNReal.coe_injective
    change (t : ℝ) - (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub hst]

/-- A Brownian motion, read on nonnegative times, has independent increments. -/
theorem hasIndepIncrements (W : BrownianMotion P) :
    HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P := by
  intro n t ht
  refine (iIndepFun_iff_iIndep _ _ _).2 (iIndep_of_indep_biSup_lt fun i ↦ ?_)
  have hab : ((t i.castSucc : ℝ)) ≤ (t i.succ : ℝ) :=
    NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ i))
  have hsub : (⨆ j < i, MeasurableSpace.comap
        (fun ω ↦ W.W (t j.succ : ℝ) ω - W.W (t j.castSucc : ℝ) ω) inferInstance)
      ≤ ⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
        MeasurableSpace.comap (W.W q) inferInstance := by
    refine iSup₂_le fun j hj ↦ ?_
    have hji : (j : ℕ) < (i : ℕ) := hj
    have hjs : ((t j.succ : ℝ)) ≤ (t i.castSucc : ℝ) := by
      refine NNReal.coe_le_coe.2 (ht ?_)
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hjc : ((t j.castSucc : ℝ)) ≤ (t i.castSucc : ℝ) :=
      le_trans (NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ j))) hjs
    have hmem : ∀ {r : ℝ}, r ≤ (t i.castSucc : ℝ) →
        Measurable[⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
          MeasurableSpace.comap (W.W q) inferInstance] (W.W r) := fun {r} hr ↦
      Measurable.of_comap_le (le_iSup₂ (f := fun q (_ : q ∈ Set.Iic ((t i.castSucc : ℝ))) ↦
        MeasurableSpace.comap (W.W q) inferInstance) r hr)
    exact Measurable.comap_le ((hmem hjs).sub (hmem hjc))
  rcases eq_or_lt_of_le hab with hEq | hLt
  · have hconst : (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω)
        = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; rw [hEq]; ring
    have hbot : MeasurableSpace.comap
        (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω) inferInstance
        = (⊥ : MeasurableSpace Ω) := by
      rw [hconst]; exact MeasurableSpace.comap_const 0
    exact indep_of_indep_of_le_right (indep_bot_right _) (le_of_eq hbot)
  · exact indep_of_indep_of_le_left
      (W.joint_increment_independent (t i.castSucc).coe_nonneg hLt) hsub

/-- A Brownian motion, read on nonnegative times, is a pre-Brownian motion. -/
theorem isPreBrownianReal (W : BrownianMotion P) :
    IsPreBrownianReal (fun t : ℝ≥0 ↦ W.W t) P :=
  HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ W.hasLaw_eval t) W.hasIndepIncrements

/-- A Brownian motion, read on nonnegative times, is a Brownian motion in the sense of
`ProbabilityTheory.IsBrownianReal`. -/
theorem isBrownianReal (W : BrownianMotion P) :
    IsBrownianReal (fun t : ℝ≥0 ↦ W.W t) P where
  toIsPreBrownianReal := W.isPreBrownianReal
  cont := by
    filter_upwards [W.continuous_paths] with ω hω
    exact hω.comp NNReal.continuous_coe

/-- A Brownian motion, read on nonnegative times, is a Gaussian process. -/
theorem isGaussianProcess (W : BrownianMotion P) :
    IsGaussianProcess (fun t : ℝ≥0 ↦ W.W t) P :=
  W.isPreBrownianReal.isGaussianProcess

/-- The Brownian motion rebuilt from `BrownianMotion.isPreBrownianReal` has paths
`t ↦ W t - W 0` at nonnegative times. -/
theorem ofIsPreBrownianReal_w_apply (W : BrownianMotion P)
    (hcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ W.W u ω) {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    (BrownianMotion.ofIsPreBrownianReal W.isPreBrownianReal
      (fun u ↦ W.measurable_eval u) hcont).W r ω = W.W r ω - W.W 0 ω := by
  simp [BrownianMotion.ofIsPreBrownianReal, realTime, Real.coe_toNNReal r hr]

/-- The Brownian motion rebuilt from `BrownianMotion.isPreBrownianReal` is almost surely equal to
the original one at each nonnegative time. -/
theorem ofIsPreBrownianReal_w_ae_eq (W : BrownianMotion P)
    (hcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ W.W u ω) {r : ℝ} (hr : 0 ≤ r) :
    (BrownianMotion.ofIsPreBrownianReal W.isPreBrownianReal
      (fun u ↦ W.measurable_eval u) hcont).W r =ᵐ[P] W.W r := by
  filter_upwards [W.initial_zero] with ω hω
  rw [ofIsPreBrownianReal_w_apply W hcont hr ω, hω, sub_zero]

end BrownianMotion

end LevyStochCalc.Brownian
