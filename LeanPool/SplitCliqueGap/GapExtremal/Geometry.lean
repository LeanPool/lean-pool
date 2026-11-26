/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Cap
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Geometry of the selected directions (ledger L2.3, L5.1–L5.4)

Points are `F × W` (first coordinate = colour), directions are `u c = (1, c)` for `c` in a cap `C ⊆
W`.

* `dep_zero` (L2.3): three distinct directions of a cap are linearly independent, in the form
  `α + β + γ = 0`, `α a + β b + γ c = 0` ⇒ `α = β = γ = 0`.
* `par_eq` : two parallel nonzero differences `t • u c = t' • u c'` force `t = t'` and `c = c'`.
-/

@[expose] public section

namespace GapExtremal

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- The direction `(1, c)`. -/
def u (c : W) : F × W := (1, c)

theorem smul_u (t : F) (c : W) : t • (u c : F × W) = (t, t • c) := by simp [u]

/-- Equal multiples of directions have equal scalars and (if nonzero) equal directions. -/
theorem par_eq {t t' : F} {c c' : W} (h : t • (u c : F × W) = t' • u c') : t = t' ∧ (t ≠ 0 → c
  = c') := by
  rw [smul_u, smul_u, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  refine ⟨rfl, fun ht => ?_⟩
  have := congrArg (fun v : W => t⁻¹ • v) h2
  simpa [smul_smul, inv_mul_cancel₀ ht] using this

/-- **L2.3.** Three distinct points of a cap give independent directions. -/
theorem dep_zero {C : Set W} (hC : IsCap F C) {a b c : W} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {α β γ : F} (hsum : α + β + γ = 0)
    (hvec : α • a + β • b + γ • c = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  by_cases hγ : γ = 0
  · subst hγ
    have hβ : β = -α := by linear_combination hsum
    subst hβ
    have : α • (a - b) = 0 := by
      rw [smul_sub]; simpa [sub_eq_add_neg, neg_smul] using hvec
    by_cases hα : α = 0
    · exact ⟨hα, by simp [hα], rfl⟩
    · exfalso
      have h2 := congrArg (fun v : W => α⁻¹ • v) this
      simp only [smul_smul, inv_mul_cancel₀ hα, one_smul, smul_zero] at h2
      exact hab (sub_eq_zero.mp h2)
  · exfalso
    -- `c = a + t (b - a)` with `t = β / (α + β) = -β / γ`
    set t : F := -β / γ with ht
    have hc' : c = a + t • (b - a) := by
      have hαβ : α + β = -γ := by linear_combination hsum
      have : γ • c = -(α • a + β • b) := by
        rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; simpa [add_assoc] using hvec
      have hα : α = -γ - β := by linear_combination hαβ
      rw [hα] at this
      have : c = γ⁻¹ • (-((-γ - β) • a + β • b)) := by
        rw [← this, smul_smul, inv_mul_cancel₀ hγ, one_smul]
      rw [this, ht]
      simp only [smul_neg, smul_add, smul_smul, sub_smul, neg_smul, div_eq_mul_inv, smul_sub]
      rw [inv_mul_cancel₀ hγ]
      module
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul, add_zero] at hc'
      exact hac hc'.symm
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, one_smul, add_sub_cancel] at hc'
      exact hbc hc'.symm
    exact hC ha hb hab t ht0 ht1 (hc' ▸ hc)

end GapExtremal
