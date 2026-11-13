/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Classical.Basic

/-! # Regularity derived from the classical copula conditions

Rectangle increments split additively along each coordinate. Positivity then gives
monotonicity and the Lipschitz estimate; continuity is a consequence of the
classical conditions, rather than an extra hypothesis.
-/

public section

open Set
open scoped unitInterval BigOperators NNReal

namespace ProbabilityTheory.Copula

variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem partialIncrement_congr_lower (a a' b : Fin d → I) (s : Finset (Fin d))
    (ha : ∀ i ∈ s, a i = a' i) : partialIncrement F a b s = partialIncrement F a' b s := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 2
  funext i
  by_cases hi : i ∈ t
  · simp only [corner, hi, ↓reduceIte, ha i (Finset.mem_powerset.mp ht hi)]
  · simp only [corner, hi, ↓reduceIte]

/-- Finite additivity under a cut, including cuts at the endpoints. -/
theorem rectangleIncrement_split (a b : Fin d → I) (i : Fin d) (t : I) :
    rectangleIncrement F a b =
      rectangleIncrement F a (Function.update b i t) +
        rectangleIncrement F (Function.update a i t) b := by
  let s := Finset.univ.erase i
  have hi : i ∉ s := by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ,
    and_true, not_false_eq_true, s]
  have hu : Finset.univ = insert i s := (Finset.insert_erase (Finset.mem_univ i)).symm
  have hl (c : Fin d → I) : partialIncrement F (Function.update a i t) c s =
      partialIncrement F a c s := partialIncrement_congr_lower _ _ _ _ (by
        intro j hj
        exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)
  simp only [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ hi,
    Function.update_self, Function.update_idem, hl]
  ring

theorem rectangleIncrement_eq_zero_of_eq (a b : Fin d → I) (i : Fin d)
    (hi : a i = b i) : rectangleIncrement F a b = 0 := by
  have hu : Finset.univ = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ (by simp), hi,
    Function.update_eq_self, sub_self]

theorem IsClassical.partialIncrement_zero_lower (hF : IsClassical F)
    (a b : Fin d → I) (s : Finset (Fin d)) (ha : ∀ i ∈ s, a i = 0) :
    partialIncrement F a b s = F b := by
  unfold partialIncrement
  rw [Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, corner_empty, one_mul]
  · intro t ht hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [hF.grounded _ i (by simp only [corner, hi, ↓reduceIte,
      ha i (Finset.mem_powerset.mp ht hi)]), mul_zero]
  · simp only [Finset.mem_powerset, Finset.empty_subset, not_true_eq_false, Finset.card_empty,
    pow_zero,
    corner_empty, one_mul, IsEmpty.forall_iff]

theorem IsClassical.rectangleIncrement_zero_lower (hF : IsClassical F) (b : Fin d → I) :
    rectangleIncrement F (fun _ => 0) b = F b :=
  hF.partialIncrement_zero_lower _ _ _ (by simp)

theorem IsClassical.rectangleIncrement_slab (hF : IsClassical F) (b : Fin d → I)
    (i : Fin d) (t : I) :
    rectangleIncrement F (Function.update (fun _ => 0) i t) b =
      F b - F (Function.update b i t) := by
  have hu : Finset.univ = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ (by simp),
    hF.partialIncrement_zero_lower, hF.partialIncrement_zero_lower]
  · simp only [Function.update_self]
  all_goals intro j hj; simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem compare_by_updates (G : (Fin d → I) → ℝ) (a b : Fin d → I) (hab : a ≤ b)
    (hstep : ∀ x, a ≤ x → x ≤ b → ∀ i, G x ≤ G (Function.update x i (b i))) : G a ≤ G b := by
  have h (s : Finset (Fin d)) : G a ≤ G (s.piecewise b a) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty, Std.le_refl]
    | @insert i s hi ih =>
      have ha : a ≤ s.piecewise b a := by
        intro j; by_cases hj : j ∈ s <;> simp only [Finset.piecewise, hj, ↓reduceIte, hab j,
          Std.le_refl]
      have hb : s.piecewise b a ≤ b := by
        intro j; by_cases hj : j ∈ s <;> simp only [Finset.piecewise, hj, ↓reduceIte, hab j,
          Std.le_refl]
      rw [Finset.piecewise_insert]
      exact ih.trans (hstep _ ha hb i)
  simpa only [ge_iff_le, Finset.piecewise_univ] using h Finset.univ

/-- Rectangle mass increases when its upper endpoint increases. -/
theorem IsClassical.rectangleIncrement_mono_upper (hF : IsClassical F)
    (a b c : Fin d → I) (hab : a ≤ b) (hbc : b ≤ c) :
    rectangleIncrement F a b ≤ rectangleIncrement F a c := by
  apply compare_by_updates (rectangleIncrement F a) b c hbc
  intro x hbx hxc i
  have hsplit := rectangleIncrement_split (F := F) a (Function.update x i (c i)) i (x i)
  simp only [Function.update_idem, Function.update_eq_self] at hsplit
  have hnonneg := hF.increasing (Function.update a i (x i)) (Function.update x i (c i)) (by
    intro j
    by_cases hj : j = i
    · subst j; simpa only [Function.update_self] using hxc i
    · simpa only [Function.update_of_ne hj] using (hab j).trans (hbx j))
  linarith

/-- Coordinatewise monotonicity follows from the rectangle condition. -/
theorem IsClassical.monotone (hF : IsClassical F) : Monotone F := by
  intro a b hab
  simpa only [hF.rectangleIncrement_zero_lower] using
    hF.rectangleIncrement_mono_upper (fun _ => 0) a b (fun i => (a i).property.1) hab

theorem IsClassical.update_sub_le (hF : IsClassical F) (u : Fin d → I)
    (i : Fin d) (t : I) (ht : u i ≤ t) :
    F (Function.update u i t) - F u ≤ (t : ℝ) - (u i : ℝ) := by
  have h := hF.rectangleIncrement_mono_upper (Function.update (fun _ => 0) i (u i))
    (Function.update u i t) (Function.update (fun _ => 1) i t) (by
      intro j
      by_cases hj : j = i
      · subst j; simpa only [Function.update_self] using ht
      · simp only [Function.update_of_ne hj, zero_le]) (by
      intro j
      by_cases hj : j = i
      · subst j; simp only [Function.update_self, Std.le_refl]
      · simp only [Function.update_of_ne hj, unitInterval.le_one'])
  simpa only [hF.rectangleIncrement_slab, Function.update_idem, Function.update_eq_self,
    hF.marginal] using h

theorem IsClassical.sub_le_sum_of_le (hF : IsClassical F) (a b : Fin d → I) (hab : a ≤ b) :
    F b - F a ≤ ∑ i, ((b i : ℝ) - (a i : ℝ)) := by
  have h (s : Finset (Fin d)) : F (s.piecewise b a) - F a ≤
      ∑ i ∈ s, ((b i : ℝ) - (a i : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty, sub_self, Finset.sum_sub_distrib,
      Finset.sum_empty, Std.le_refl]
    | @insert i s hi ih =>
      have hx : s.piecewise b a i = a i := by simp only [hi, not_false_eq_true,
        Finset.piecewise_eq_of_notMem]
      have hs := hF.update_sub_le (s.piecewise b a) i (b i) (by rw [hx]; exact hab i)
      rw [Finset.piecewise_insert, Finset.sum_insert hi]
      rw [hx] at hs
      linarith
  simpa only [Finset.sum_sub_distrib, tsub_le_iff_right, ge_iff_le,
    Finset.piecewise_univ] using h Finset.univ

theorem IsClassical.sub_le_sum_abs (hF : IsClassical F) (a b : Fin d → I) :
    F a - F b ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := by
  have h := hF.sub_le_sum_of_le b (a ⊔ b) le_sup_right
  have hm := hF.monotone (show a ≤ a ⊔ b from le_sup_left)
  have hs : ∑ i, (((a ⊔ b) i : ℝ) - (b i : ℝ)) ≤
      ∑ i, |(a i : ℝ) - (b i : ℝ)| := by
    apply Finset.sum_le_sum
    intro i _
    change max (a i : ℝ) (b i : ℝ) - (b i : ℝ) ≤ _
    rw [← max_sub_sub_right, sub_self]
    exact max_le (le_abs_self _) (abs_nonneg _)
  linarith

/-- The sharp Lipschitz estimate in the sum of coordinate distances. -/
theorem IsClassical.abs_sub_le_sum_abs (hF : IsClassical F) (a b : Fin d → I) :
    |F a - F b| ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := by
  rw [abs_le]
  constructor
  · have h := hF.sub_le_sum_abs b a
    simp only [abs_sub_comm] at h
    linarith
  · exact hF.sub_le_sum_abs a b

theorem IsClassical.lipschitzWith (hF : IsClassical F) : LipschitzWith (d : ℝ≥0) F := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  calc
    dist (F a) (F b) = |F a - F b| := Real.dist_eq _ _
    _ ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := hF.abs_sub_le_sum_abs a b
    _ ≤ ∑ _ : Fin d, dist a b := Finset.sum_le_sum fun i _ => by
      simpa only [Subtype.dist_eq, Real.dist_eq] using dist_le_pi_dist a b i
    _ = (d : ℝ≥0) * dist a b := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, NNReal.coe_natCast]

theorem IsClassical.continuous (hF : IsClassical F) : Continuous F := hF.lipschitzWith.continuous

end ProbabilityTheory.Copula
