/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Finite

/-!
# Vector spaces: the conjecture of Kazhdan and Polishchuk for finite groups

D. Kazhdan, A. Polishchuk, Almost invariant subspaces and operators, arXiv 2107.08085: end of the
introduction.
The bound `r (r+1)^(r+1)` is replaced by a total of less than `2 r`.
-/

@[expose] public section

open Submodule

namespace AlmostInvariant

/-- A linear automorphism acts on the lattice of submodules. -/
def linearAct {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G] (ρ : G →* (M ≃ₗ[R]
    M)) :
    G →* (Submodule R M ≃o Submodule R M) where
  toFun g := Submodule.orderIsoMapComap (ρ g)
  map_one' := by
    ext S x
    simp
  map_mul' g h := by
    ext S x
    simp only [map_mul, Submodule.orderIsoMapComap_apply, RelIso.mul_apply, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩

theorem linearAct_apply {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G] (ρ : G →*
    (M ≃ₗ[R] M)) (g : G)
    (S : Submodule R M) : act (linearAct ρ) g S = S.map (ρ g : M →ₗ[R] M) := rfl

/-- Modules over any ring, length in place of dimension. -/
theorem almost_invariant_module {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G]
    [Finite G]
    (ρ : G →* (M ≃ₗ[R] M)) (A : Submodule R M) (r : ℕ)
    (hr : ∀ g, Module.length R (A ⧸ (A.map (ρ g : M →ₗ[R] M)).submoduleOf A) ≤ r) :
    ∃ W : Submodule R M, (∀ g, W.map (ρ g : M →ₗ[R] M) = W) ∧
      (Nat.card G : ℕ∞) * (Module.length R (A ⧸ W.submoduleOf A) + Module.length R (W ⧸
          A.submoduleOf W))
        ≤ 2 * r * (Nat.card G - 1 : ℕ) := by
  have := Fintype.ofFinite G
  obtain ⟨W, hW, h⟩ := exists_invariant_of_le (linearAct ρ) A r hr
  rw [Nat.card_eq_fintype_card]
  exact ⟨W, hW, h⟩

/-- **The conjecture of Kazhdan and Polishchuk for finite groups**, with a linear bound. -/
theorem almost_invariant {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Group G]
    [Finite G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∃ a b : ℕ, Module.rank K (A ⧸ W.submoduleOf A) = a ∧ Module.rank K (W ⧸ A.submoduleOf W) = b ∧
        a + b ≤ 2 * r ∧ (0 < r → a + b < 2 * r) := by
  have hr' : ∀ g, Module.length K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r := by
    intro g
    rw [Module.length_eq_rank]
    have h := OrderHomClass.mono Cardinal.toENat (hr g)
    simpa using h
  obtain ⟨W, hW, h⟩ := almost_invariant_module ρ A r hr'
  have hc : 0 < Nat.card G := Nat.card_pos
  have hsum : Module.length K (A ⧸ W.submoduleOf A) + Module.length K (W ⧸ A.submoduleOf W)
      ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast hc.ne')] at h
    exact (ENat.natCast_ne_top (2 * r * (Nat.card G - 1))) (top_le_iff.mp (by exact_mod_cast h))
  have ha : Module.length K (A ⧸ W.submoduleOf A) ≠ ⊤ := ne_top_of_le_ne_top hsum le_self_add
  have hb : Module.length K (W ⧸ A.submoduleOf W) ≠ ⊤ := ne_top_of_le_ne_top hsum le_add_self
  obtain ⟨a, ea⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b, eb⟩ := ENat.ne_top_iff_exists.mp hb
  rw [← ea, ← eb] at h
  have hn : Nat.card G * (a + b) ≤ 2 * r * (Nat.card G - 1) := by exact_mod_cast h
  refine ⟨W, hW, a, b, ?_, ?_, ?_, ?_⟩
  · rw [Module.length_eq_rank] at ea
    exact Cardinal.toENat_eq_natCast.mp ea.symm
  · rw [Module.length_eq_rank] at eb
    exact Cardinal.toENat_eq_natCast.mp eb.symm
  · by_contra hlt
    push Not at hlt
    have : Nat.card G * (2 * r + 1) ≤ Nat.card G * (a + b) := Nat.mul_le_mul_left _ hlt
    have : 2 * r * (Nat.card G - 1) ≤ 2 * r * Nat.card G := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  · intro hr0
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card G * (2 * r) ≤ Nat.card G * (a + b) := Nat.mul_le_mul_left _ hlt
    have h2 : 2 * r * (Nat.card G - 1) + 2 * r = 2 * r * Nat.card G := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hc]
    nlinarith

end AlmostInvariant
