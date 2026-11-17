/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Shared operations on first-order syntax

Term restriction, subformula closure and binder-depth bounds used by the
fixed-point and Tseitin translations share one implementation and its laws.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder Language Structure

/-! ### Stripping a relational summand out of terms -/

section Strip

variable {L₀ R : Language.{0, 0}} [R.IsRelational] {α : Type}

/-- A term over `L₀.sum R` with `R` relational is a term over `L₀`: the
summand contributes no function symbols. -/
def stripTerm : (L₀.sum R).Term α → L₀.Term α
  | .var a => .var a
  | .func (Sum.inl f) ts => .func f fun i => stripTerm (ts i)
  | .func (Sum.inr f) _ => isEmptyElim f

/-- Reembedding a stripped term into the relational expansion returns the term. -/
theorem sumInl_onTerm_stripTerm (t : (L₀.sum R).Term α) :
    LHom.sumInl.onTerm (stripTerm t) = t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      cases f with
      | inl f =>
          change Term.func (Sum.inl f) (fun i => LHom.sumInl.onTerm (stripTerm (ts i))) = _
          exact congrArg _ (funext ih)
      | inr f => exact isEmptyElim f

/-- Stripping a relational extension preserves term realization in every expansion. -/
theorem realize_stripTerm {A : Type} [L₀.Structure A] [(L₀.sum R).Structure A]
    [(LHom.sumInl : L₀ →ᴸ L₀.sum R).IsExpansionOn A] (v : α → A)
    (t : (L₀.sum R).Term α) : (stripTerm t).realize v = t.realize v := by
  conv_rhs => rw [← sumInl_onTerm_stripTerm t]
  exact (LHom.realize_onTerm _ _ _).symm

end Strip

/-! ### The subformula closure of a sentence, as a list -/

section Subformulas

variable {Lg : Language.{0, 0}}

/-- The subformulas of a bounded formula over `Empty`, each with its binder
depth, as a list; the formula itself is included. -/
def subs : ∀ {n : ℕ}, Lg.BoundedFormula Empty n → List (Σ n' : ℕ, Lg.BoundedFormula Empty n')
  | n, .falsum => [⟨n, .falsum⟩]
  | n, .equal t u => [⟨n, .equal t u⟩]
  | n, .rel r ts => [⟨n, .rel r ts⟩]
  | n, .imp a b => ⟨n, a.imp b⟩ :: (subs a ++ subs b)
  | n, .all a => ⟨n, a.all⟩ :: subs a

theorem self_mem_subs {n : ℕ} (φ : Lg.BoundedFormula Empty n) : ⟨n, φ⟩ ∈ subs φ := by
  cases φ <;> simp [subs]

theorem subs_trans {n : ℕ} {φ : Lg.BoundedFormula Empty n}
    {x : Σ n', Lg.BoundedFormula Empty n'} (hx : x ∈ subs φ) : subs x.2 ⊆ subs φ := by
  obtain ⟨nx, ψ⟩ := x
  induction φ with
  | falsum =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | equal t u =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | rel r ts =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | imp a b iha ihb =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
      obtain rfl := eq_of_heq h
      exact fun y hy => hy
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.Subset.trans (iha hx)
          (List.subset_cons_of_subset _ (List.subset_append_left _ _))
      · exact List.Subset.trans (ihb hx)
          (List.subset_cons_of_subset _ (List.subset_append_right _ _))
  | all a iha =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
      obtain rfl := eq_of_heq h
      exact fun y hy => hy
    · exact List.Subset.trans (iha hx) (List.subset_cons_self _ _)

theorem left_mem_subs_imp {n : ℕ} (a b : Lg.BoundedFormula Empty n) :
    (⟨n, a⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs (a.imp b) := by
  rw [subs, List.mem_cons]
  exact Or.inr (List.mem_append_left _ (self_mem_subs a))

theorem right_mem_subs_imp {n : ℕ} (a b : Lg.BoundedFormula Empty n) :
    (⟨n, b⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs (a.imp b) := by
  rw [subs, List.mem_cons]
  exact Or.inr (List.mem_append_right _ (self_mem_subs b))

theorem mem_subs_all {n : ℕ} (a : Lg.BoundedFormula Empty (n + 1)) :
    (⟨n + 1, a⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs a.all := by
  rw [subs, List.mem_cons]
  exact Or.inr (self_mem_subs a)

variable {α : Type}

/-- A bound on all binder depths occurring in a bounded formula. -/
def contextBound : ∀ {n : ℕ}, Lg.BoundedFormula α n → ℕ
  | _, .imp a b => max (contextBound a) (contextBound b)
  | _, .all a => contextBound a
  | n, _ => n

theorem le_contextBound : ∀ {n : ℕ} (φ : Lg.BoundedFormula α n), n ≤ contextBound φ
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel _ _ => le_rfl
  | _, .imp a _ => le_trans (le_contextBound a) (le_max_left _ _)
  | _, .all a => le_trans (Nat.le_succ _) (le_contextBound a)

theorem fst_le_contextBound {n : ℕ} {φ : Lg.BoundedFormula Empty n}
    {x : Σ n', Lg.BoundedFormula Empty n'} (hx : x ∈ subs φ) : x.1 ≤ contextBound φ := by
  induction φ with
  | falsum =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | equal t u =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | rel r ts =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | imp a b iha ihb =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [congrArg Sigma.fst hx]
      exact le_contextBound _
    · rcases List.mem_append.mp hx with hx | hx
      · exact le_trans (iha hx) (le_max_left _ _)
      · exact le_trans (ihb hx) (le_max_right _ _)
  | all a iha =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [congrArg Sigma.fst hx]
      exact le_contextBound _
    · exact iha hx

end Subformulas

end DescriptiveComplexity
