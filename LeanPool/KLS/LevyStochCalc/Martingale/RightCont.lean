/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Martingales on the right-continuous augmentation of a filtration

An `ℱ`-martingale on `ℝ` whose time slices are right-continuous in `L¹` is a martingale on
the right-continuous augmentation `ℱ₊`: an `ℱ₊ s`-measurable set lies in every `ℱ r` with
`r > s`, so the martingale identity holds on it from every later time, and
right-`L¹`-continuity carries it down to `s`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace LevyStochCalc.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}

/-- An `ℱ`-martingale on `ℝ` whose time slices are right-continuous in `L¹` is a martingale
on the right-continuous augmentation of `ℱ`. -/
lemma martingale_rightCont_of_tendsto_eLpNorm_one (hmart : Martingale F ℱ P)
    (hrc : ∀ s : ℝ, Tendsto (fun r => eLpNorm (F r - F s) 1 P) (𝓝[>] s) (𝓝 0)) :
    Martingale F ℱ.rightCont P := by
  refine ⟨fun i => (hmart.stronglyAdapted i).mono (ℱ.le_rightCont i), ?_⟩
  intro s t hst
  have hm : ℱ.rightCont s ≤ mΩ := (ℱ.rightCont).le s
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (hmart.integrable t) (fun A _ _ => (hmart.integrable s).integrableOn)
    ?_ ((hmart.stronglyAdapted s).mono (ℱ.le_rightCont s)).aestronglyMeasurable).symm
  intro A hA _
  -- `s = t` is trivial; for `s < t` use the constant-near-`s`/limit argument.
  rcases eq_or_lt_of_le hst with rfl | hst'
  · rfl
  -- `r ↦ ∫_A F r → ∫_A F s` from right-`L¹`-continuity.
  have htend_s : Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F s x ∂P)) :=
    tendsto_setIntegral_of_L1' (F s)
      (Eventually.of_forall (fun r => hmart.integrable r)) (hrc s) A
  -- `r ↦ ∫_A F r` is constantly `∫_A F t` on `(s, t)`.
  have heq_ev : ∀ᶠ r in nhdsWithin s (Set.Ioi s),
      (∫ x in A, F t x ∂P) = ∫ x in A, F r x ∂P := by
    refine eventually_of_mem (Ioo_mem_nhdsGT hst') (fun r hr => ?_)
    have h_le : ℱ.rightCont s ≤ ℱ r := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le r hr.1
    exact (hmart.setIntegral_eq (le_of_lt hr.2) (h_le A hA)).symm
  have htend_const : Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F t x ∂P)) :=
    tendsto_const_nhds.congr' heq_ev
  exact tendsto_nhds_unique htend_s htend_const


end LevyStochCalc.Martingale
