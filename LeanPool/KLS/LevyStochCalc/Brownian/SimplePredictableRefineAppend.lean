/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.SimplePredictableRefineCommon

/-!
# Zero-extension of a simple predictable to a larger horizon

Appending one interval carrying the coefficient `0`
(`SimplePredictable.appendInterval`) turns a `SimplePredictable Ω T` into a
`SimplePredictable Ω T'` on a larger horizon with the same `eval`, the same
simple integral and the same adaptedness, so that two approximants on different
horizons can be compared on a common endpoint.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- `Fin.snoc f a` is strictly monotone when `f` is and `f (last) < a`. -/
lemma strictMono_snoc {n : ℕ} {α : Type*} [Preorder α] {f : Fin (n + 1) → α}
    (hf : StrictMono f) {a : α} (ha : f (Fin.last n) < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hf (by rwa [Fin.castSucc_lt_castSucc_iff] at hij)
    · exact absurd hij (not_lt.mpr (Fin.le_last _))
  · rw [Fin.snoc_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact lt_of_le_of_lt (hf.monotone (Fin.le_last i')) ha
    · exact absurd hij (lt_irrefl _)

/-- **Zero-extension to a larger horizon.** Append one interval `(H_last, T']`
carrying coefficient `0`, producing a `SimplePredictable` on the larger horizon
`T'` whose `eval` and `simpleIntegral` are unchanged. Lets two different-horizon
approximants be put on a common endpoint for the difference isometry. -/
noncomputable def SimplePredictable.appendInterval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') : SimplePredictable Ω T' where
  N := H.N + 1
  partition := Fin.snoc H.partition T'
  partition_zero := by rw [Fin.snoc_apply_zero]; exact H.partition_zero
  partition_le_T := by rw [Fin.snoc_last]
  partition_strictMono := strictMono_snoc H.partition_strictMono hlt
  ξ := Fin.snoc H.ξ (fun _ => 0)
  ξ_bounded := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · obtain ⟨M, hM⟩ := H.ξ_bounded i'
      exact ⟨M, fun ω => by rw [Fin.snoc_castSucc]; exact hM ω⟩
    · exact ⟨0, fun ω => by rw [Fin.snoc_last]; simp⟩
  ξ_measurable := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact H.ξ_measurable i'
    · rw [Fin.snoc_last]; exact measurable_const

lemma SimplePredictable.appendInterval_partition_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition = Fin.snoc H.partition T' := rfl

lemma SimplePredictable.appendInterval_xi_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ = Fin.snoc H.ξ (fun _ => 0) := rfl

lemma SimplePredictable.appendInterval_partition_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition (Fin.last (H.N + 1)) = T' := by
  rw [H.appendInterval_partition_eq hlt]
  exact Fin.snoc_last (α := fun _ => ℝ) T' H.partition

/-- Index identity used to relate the appended partition's `castSucc`/`succ`
to the original partition. -/
private lemma appendInterval_succ_castSucc {n : ℕ} (i : Fin n) :
    (Fin.castSucc i).succ = Fin.castSucc i.succ := Fin.ext rfl

/-- Pointwise values of the appended partition / coefficients. -/
lemma SimplePredictable.appendInterval_partition_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin (H.N + 1)) :
    (H.appendInterval hlt).partition (Fin.castSucc j) = H.partition j := by
  rw [H.appendInterval_partition_eq hlt]; exact Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _

lemma SimplePredictable.appendInterval_xi_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin H.N) :
    (H.appendInterval hlt).ξ (Fin.castSucc j) = H.ξ j := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_castSucc]

lemma SimplePredictable.appendInterval_xi_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ (Fin.last H.N) = (fun _ : Ω => (0 : ℝ)) := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_last]

/-- The `eval` of the zero-extension equals the original `eval`. -/
lemma SimplePredictable.appendInterval_eval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (s : ℝ) (ω : Ω) :
    (H.appendInterval hlt).eval s ω = H.eval s ω := by
  unfold SimplePredictable.eval
  change (∑ i : Fin (H.N + 1),
      if (Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc < s
          ∧ s ≤ (Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ
        then (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω else 0)
    = ∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, ite_self, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]

/-- The `simpleIntegral` of the zero-extension equals the original `simpleIntegral`. -/
lemma SimplePredictable.appendInterval_simpleIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (t : ℝ) (ω : Ω) :
    simpleIntegral W (H.appendInterval hlt) t ω = simpleIntegral W H t ω := by
  unfold simpleIntegral
  change (∑ i : Fin (H.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ) t) ω
            - W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc) t) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]

/-- Adaptedness is preserved by the zero-extension. -/
lemma SimplePredictable.appendInterval_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T')
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∀ i : Fin (H.appendInterval hlt).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((H.appendInterval hlt).partition i.castSucc)) ((H.appendInterval hlt).ξ i) := by
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rw [H.appendInterval_xi_castSucc hlt i',
        H.appendInterval_partition_castSucc hlt (Fin.castSucc i')]
    exact h_adapt i'
  · rw [H.appendInterval_xi_last hlt]; exact MeasureTheory.stronglyMeasurable_const

end LevyStochCalc.Brownian.Ito
