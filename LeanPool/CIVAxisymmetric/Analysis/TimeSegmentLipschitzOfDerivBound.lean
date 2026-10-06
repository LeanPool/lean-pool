/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
The exact two-point, symmetric-in-`|τ - τ'|` Lipschitz bound that a uniform derivative bound
on an interval gives — the abstract real-analysis fact behind the time-pairing estimate
`hpair` in the corresponding statement (the pairing bound `|g τ - g τ'| ≤ C |τ - τ'|`).
-/

public section

open Set

noncomputable section

namespace CIV



theorem abs_sub_le_of_hasDerivWithinAt_le {g D : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt g (D x) (Icc a b) x)
    (hbound : ∀ x ∈ Ico a b, |D x| ≤ C) :
    |g b - g a| ≤ C * (b - a) := by
  have _ := hC
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun x hx => by simpa [Real.norm_eq_abs] using hbound x hx) b (right_mem_Icc.2 hab)
  simpa [Real.norm_eq_abs] using h

theorem abs_sub_le_of_hasDerivWithinAt_le_abs {g D : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt g (D x) (Icc a b) x)
    (hbound : ∀ x ∈ Ico a b, |D x| ≤ C) {τ τ' : ℝ} (hτ : τ ∈ Icc a b) (hτ' : τ' ∈ Icc a b) :
    |g τ - g τ'| ≤ C * |τ - τ'| := by
  have _ := hab
  rcases hτ with ⟨hτl, hτu⟩
  rcases hτ' with ⟨hτ'l, hτ'u⟩
  rcases le_total τ' τ with hle | hle
  · have hsub_icc : Icc τ' τ ⊆ Icc a b := Icc_subset_Icc hτ'l hτu
    have hsub_ico : Ico τ' τ ⊆ Ico a b := Ico_subset_Ico hτ'l hτu
    have h := abs_sub_le_of_hasDerivWithinAt_le hle hC
      (fun x hx => (hderiv x (hsub_icc hx)).mono hsub_icc)
      (fun x hx => hbound x (hsub_ico hx))
    have habs : |τ - τ'| = τ - τ' := abs_of_nonneg (sub_nonneg.2 hle)
    rw [habs]
    exact h
  · have hsub_icc : Icc τ τ' ⊆ Icc a b := Icc_subset_Icc hτl hτ'u
    have hsub_ico : Ico τ τ' ⊆ Ico a b := Ico_subset_Ico hτl hτ'u
    have h := abs_sub_le_of_hasDerivWithinAt_le hle hC
      (fun x hx => (hderiv x (hsub_icc hx)).mono hsub_icc)
      (fun x hx => hbound x (hsub_ico hx))
    have habs : |τ - τ'| = τ' - τ := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
    rw [habs]
    rw [abs_sub_comm]
    exact h

theorem abs_sub_le_of_forall_hasDerivAt_le {g D : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hderiv : ∀ x, HasDerivAt g (D x) x) (hbound : ∀ x ∈ Icc a b, |D x| ≤ C)
    {τ τ' : ℝ} (hτ : τ ∈ Icc a b) (hτ' : τ' ∈ Icc a b) :
    |g τ - g τ'| ≤ C * |τ - τ'| := by
  exact abs_sub_le_of_hasDerivWithinAt_le_abs hab hC
    (fun x hx => (hderiv x).hasDerivWithinAt) (fun x hx => hbound x (Set.Ico_subset_Icc_self
      hx)) hτ hτ'

end CIV
