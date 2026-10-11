/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-! # Rectangle probabilities and increasing distribution functions

Rectangle increments use lower endpoints on the selected coordinates, hence
the sign is `(-1)^s.card`. The probability identity requires ordered endpoints.
The empty-dimensional rectangle has probability one.
-/

public section

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A corner of a rectangle, choosing the lower endpoint on `s`. -/
@[expose]
def corner (a b : Fin d → I) (s : Finset (Fin d)) (i : Fin d) : I :=
  if i ∈ s then a i else b i

@[simp]
theorem corner_empty (a b : Fin d → I) : corner a b ∅ = b := by
  funext i
  simp [corner]

/-- Apply finite differences in the coordinates of `s`. -/
@[expose]
def partialIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * F (corner a b t)

/-- The alternating sum of a function over all corners of a rectangle. -/
@[expose]
def rectangleIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I) : ℝ :=
  partialIncrement F a b Finset.univ

@[simp]
theorem partialIncrement_empty (F : (Fin d → I) → ℝ) (a b : Fin d → I) :
    partialIncrement F a b ∅ = F b := by
  simp [partialIncrement]

theorem partialIncrement_insert (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    partialIncrement F a b (insert i s) =
      partialIncrement F a b s - partialIncrement F a (Function.update b i (a i)) s := by
  unfold partialIncrement
  rw [Finset.sum_powerset_insert hi, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h => hi (Finset.mem_powerset.mp ht h)
  have hc : corner a b (insert i t) = corner a (Function.update b i (a i)) t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [corner]
    · simp [corner, hji]
  rw [Finset.card_insert_of_notMem hit, pow_succ, hc]
  ring

theorem partialIncrement_singleton (F : (Fin d → I) → ℝ) (a b : Fin d → I) (i : Fin d) :
    partialIncrement F a b {i} = F b - F (Function.update b i (a i)) := by
  change partialIncrement F a b (insert i ∅) = _
  rw [partialIncrement_insert _ _ _ _ _ (by simp)]
  simp

/-- The familiar four-term increment in dimension two. -/
theorem rectangleIncrement_two (F : (Fin 2 → I) → ℝ) (a b : Fin 2 → I) :
    rectangleIncrement F a b = F b - F ![a 0, b 1] - F ![b 0, a 1] + F a := by
  have hu : (Finset.univ : Finset (Fin 2)) = insert 0 {1} := by decide
  rw [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ (by decide),
    partialIncrement_singleton, partialIncrement_singleton]
  have h0 : Function.update b 0 (a 0) = ![a 0, b 1] := by
    funext i; fin_cases i <;> simp
  have h1 : Function.update b 1 (a 1) = ![b 0, a 1] := by
    funext i; fin_cases i <;> simp
  have h01 : Function.update (Function.update b 0 (a 0)) 1 (a 1) = a := by
    funext i; fin_cases i <;> simp
  rw [h01, h0, h1]
  ring

/-- Partial finite differences of a copula CDF are probabilities of partially open boxes:
`Δ_s C (a, b) = P(U ≤ b, Uᵢ > aᵢ for i ∈ s)`. -/
theorem partialIncrement_cdf (C : Copula d) (a b : Fin d → I) (s : Finset (Fin d))
    (hab : a ≤ b) :
    partialIncrement C.cdf a b s = C.toMeasure.real {x | x ≤ b ∧ ∀ i ∈ s, a i < x i} := by
  induction s using Finset.induction_on generalizing b with
  | empty => simp [partialIncrement, cdf, Iic]
  | @insert i s hi ih =>
    have hab' : a ≤ Function.update b i (a i) := by
      intro j
      by_cases hji : j = i
      · subst j; simp
      · simpa [Function.update_of_ne hji] using hab j
    have hinter : {x | x ≤ b ∧ ∀ j ∈ s, a j < x j} ∩ {x | x i ≤ a i} =
        {x | x ≤ Function.update b i (a i) ∧ ∀ j ∈ s, a j < x j} := by
      ext x
      constructor
      · rintro ⟨⟨hxb, hx⟩, hxi⟩
        refine ⟨?_, hx⟩
        intro j
        by_cases hji : j = i
        · subst j; simpa using hxi
        · simpa [Function.update_of_ne hji] using hxb j
      · rintro ⟨hxb, hx⟩
        refine ⟨⟨?_, hx⟩, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            exact (by simpa using hxb i : x i ≤ a i).trans (hab i)
          · simpa [Function.update_of_ne hji] using hxb j
        · simpa using hxb i
    have hdiff : {x | x ≤ b ∧ ∀ j ∈ s, a j < x j} \ {x | x i ≤ a i} =
        {x | x ≤ b ∧ ∀ j ∈ insert i s, a j < x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_sdiff, Finset.mem_insert, forall_eq_or_imp, not_le]
      tauto
    rw [partialIncrement_insert _ _ _ _ _ hi, ih b hab, ih _ hab']
    have h := measureReal_inter_add_sdiff (μ := C.toMeasure)
      (s := {x | x ≤ b ∧ ∀ j ∈ s, a j < x j}) (t := {x | x i ≤ a i})
      (measurableSet_le (measurable_pi_apply i) measurable_const)
    rw [hinter, hdiff] at h
    linarith

/-- The alternating CDF sum equals the probability of the half-open rectangle. -/
theorem rectangleIncrement_cdf (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement C.cdf a b = C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) := by
  rw [rectangleIncrement, partialIncrement_cdf C a b _ hab]
  congr 1
  ext x
  simp only [mem_ofPred_eq, Finset.mem_univ, forall_const, mem_univ_pi, mem_Ioc, Pi.le_def]
  exact ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩

/-- Nonnegative rectangle increments: the classical `d`-increasing property. -/
theorem rectangleIncrement_cdf_nonneg (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    0 ≤ rectangleIncrement C.cdf a b := by
  rw [C.rectangleIncrement_cdf a b hab]
  exact measureReal_nonneg

/-- Bivariate rectangle probabilities written as four CDF evaluations. -/
theorem measureReal_rectangle_two (C : Copula 2) (a b : Fin 2 → I) (hab : a ≤ b) :
    C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) =
      C.cdf b - C.cdf ![a 0, b 1] - C.cdf ![b 0, a 1] + C.cdf a := by
  rw [← C.rectangleIncrement_cdf a b hab, rectangleIncrement_two]

end ProbabilityTheory.Copula
