/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic

/-!
# Counting directed nuclear pairs

Each increasing pair occurs in the directed boundary sum once in each orientation.
-/

@[expose] public section

namespace LiebThirring

/-- A directed pair is an increasing pair together with its orientation. -/
def directedNuclearPairEquiv (M : ℕ) :
    (Σ k : Fin M, {l : Fin M // l ≠ k}) ≃ NuclearPair M ⊕ NuclearPair M where
  toFun p := if h : p.1 < p.2.val then
      Sum.inl ⟨(p.1, p.2.val), h⟩
    else Sum.inr ⟨(p.2.val, p.1), lt_of_le_of_ne (le_of_not_gt h) p.2.property⟩
  invFun p := match p with
    | Sum.inl p => ⟨p.val.1, ⟨p.val.2, (ne_of_lt p.property).symm⟩⟩
    | Sum.inr p => ⟨p.val.2, ⟨p.val.1, ne_of_lt p.property⟩⟩
  left_inv p := by
    rcases p with ⟨k, l, hl⟩
    by_cases h : k < l
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]
  right_inv p := by
    cases p with
    | inl p =>
      dsimp only
      rw [dite_eq_left p.property]
    | inr p =>
      dsimp only
      rw [dite_eq_right (not_lt_of_gt p.property)]

/-- A symmetric directed sum is twice its sum over increasing pairs. -/
theorem sum_directedNuclearPairs {M : ℕ} {A : Type*} [AddCommMonoid A]
    (f : ∀ k l : Fin M, k ≠ l → A)
    (hf : ∀ (k l : Fin M) (hkl : k ≠ l), f k l hkl = f l k hkl.symm) :
    (∑ k : Fin M, ∑ l : {l : Fin M // l ≠ k}, f k l.val l.property.symm) =
      (∑ p : NuclearPair M, f p.val.1 p.val.2 (ne_of_lt p.property)) +
      ∑ p : NuclearPair M, f p.val.1 p.val.2 (ne_of_lt p.property) := by
  classical
  let g : NuclearPair M ⊕ NuclearPair M → A := Sum.elim
    (fun p => f p.val.1 p.val.2 (ne_of_lt p.property))
    (fun p => f p.val.2 p.val.1 (ne_of_lt p.property).symm)
  calc
    _ = ∑ p : (Σ k : Fin M, {l : Fin M // l ≠ k}), f p.1 p.2.val p.2.property.symm :=
      (Fintype.sum_sigma _).symm
    _ = ∑ p : NuclearPair M ⊕ NuclearPair M, g p := by
      apply Fintype.sum_equiv (directedNuclearPairEquiv M)
      rintro ⟨k, l, hl⟩
      dsimp only [directedNuclearPairEquiv, Equiv.coe_fn_mk]
      by_cases h : k < l
      · simp only [dite_eq_left h, g, Sum.elim_inl]
      · simp only [dite_eq_right h, g, Sum.elim_inr]
    _ = _ := by
      rw [Fintype.sum_sum_type]
      dsimp only [g, Sum.elim_inl, Sum.elim_inr]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      exact (hf _ _ (ne_of_lt p.property)).symm

end LiebThirring

end
