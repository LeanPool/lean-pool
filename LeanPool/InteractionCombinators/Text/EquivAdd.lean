/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.RenameInj
public import LeanPool.InteractionCombinators.Text.RenameMany
import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Equivalence inside a larger net

A net is a graph whose wires are written as names (Lafont 1997, Section 1.1, page 71). Two nets
that are the same graph stay the same graph when a context `Γ` is added beside them
(`Equiv.add_right`), as long as both larger nets are linear.

The derivation of `Equiv N M` may pass through nets whose internal wires carry names that occur
in `Γ`. Those intermediate nets are renamed first, by an injective `f` that fixes the names of
`N` and of `M` and sends every other name above all the names of `N`, `M` and `Γ`
(`Equiv.bind_var_add_right`). After the renaming, every intermediate net fits beside `Γ`.

Contents, in the order of the file:

1. Auxiliary lemma: `Equiv.bind_var_add_right`, a derivation of equivalence, renamed
   injectively, done beside a context.
2. Main result: `Equiv.add_right`, equivalent nets stay equivalent beside a context `Γ` when both
   larger nets are linear.
3. An example: a wire substituted away beside an `era` cell.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: a renamed derivation beside a context
-- ============================================================================================

/-- A derivation of equivalence, renamed by an injective `f`, can be done beside a context `Γ`,
provided every renamed net that is linear and has the free ports of `N₀` fits linearly beside
`Γ`. Every net of the derivation from such a `K` is linear and has the free ports of `N₀`
(Lafont 1997, Section 1.1, page 71: wires and free ports are properties of the graph). -/
theorem Equiv.bind_var_add_right
    -- the reference net `N₀`, whose free ports every net of the derivation has, and the two ends
    -- of the derivation
    {N₀ K L : Net S ℕ}
    -- the renaming, injective
    (f : ℕ → ℕ)
    (hf : Function.Injective f)
    -- the context, and the hypothesis that every linear net with the free ports of `N₀`, once
    -- renamed, fits linearly beside it
    (Γ : Net S ℕ)
    (hgood : ∀ K : Net S ℕ, K.Linear → (∀ y, K.vars.count y = 1 ↔ N₀.vars.count y = 1) →
      ((K.bind fun y => var (f y)) + Γ).Linear)
    -- the derivation, from a linear net `K` with the free ports of `N₀`
    (h : Equiv K L)
    (hK : K.Linear)
    (hfree : ∀ y, K.vars.count y = 1 ↔ N₀.vars.count y = 1) :
    -- the renamed ends are equivalent beside `Γ`
    Equiv ((K.bind fun y => var (f y)) + Γ) ((L.bind fun y => var (f y)) + Γ) := by
  revert hK hfree
  induction h with
  | rel K L h => exact fun hK hfree => ((h.bind_var f hf).add_right Γ (hgood K hK hfree)).equiv
  | refl _ => exact fun _ _ => Equiv.refl _
  | symm K L h ih =>
    intro hL hfree
    exact (ih (Equiv.linear (Equiv.symm h) hL) fun y => (Equiv.free_iff h y).trans (hfree y)).symm
  | trans K M L h₁ _ ih₁ ih₂ =>
    intro hK hfree
    exact (ih₁ hK hfree).trans
      (ih₂ (Equiv.linear h₁ hK) fun y => (Equiv.free_iff h₁ y).symm.trans (hfree y))

-- ============================================================================================
-- 2. Main result: equivalence beside a context
-- ============================================================================================

/-- Equivalent nets stay equivalent inside a larger net, when both larger nets are linear.
Linearity of `N + Γ` and of `M + Γ` says that `Γ` uses no internal wire of `N` or of `M`: the
context is plugged only into free ports, which `N` and `M` share (Lafont 1997, Section 1.1,
page 71: a net is a graph, and its wires may be named arbitrarily). -/
theorem Equiv.add_right
    -- the two equivalent nets
    {N M : Net S ℕ}
    -- the context
    (Γ : Net S ℕ)
    -- the equivalence
    (h : Equiv N M)
    -- both larger nets are linear
    (hN : (N + Γ).Linear)
    (hM : (M + Γ).Linear) :
    -- the larger nets are equivalent
    Equiv (N + Γ) (M + Γ) := by
  -- a bound on every name of `N`, `M` and `Γ`
  set B := (N.vars + M.vars + Γ.vars).sup + 1 with hB
  have hlt : ∀ x ∈ N.vars + M.vars + Γ.vars, x < B := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup hx)
  have hltN : ∀ x ∈ N.vars, x < B := fun x hx => hlt x (by simp [hx])
  have hltM : ∀ x ∈ M.vars, x < B := fun x hx => hlt x (by simp [hx])
  have hltΓ : ∀ x ∈ Γ.vars, x < B := fun x hx => hlt x (by simp [hx])
  -- fix the names of `N` and `M`, send the others above `B`
  let f : ℕ → ℕ := fun x => if x ∈ N.vars ∨ x ∈ M.vars then x else x + B
  have hfV : ∀ x, x ∈ N.vars ∨ x ∈ M.vars → f x = x := fun x hx => by simp [f, hx]
  have hfO : ∀ x, ¬(x ∈ N.vars ∨ x ∈ M.vars) → f x = x + B := fun x hx => by simp [f, hx]
  have hVB : ∀ x, x ∈ N.vars ∨ x ∈ M.vars → x < B := fun x hx =>
    hx.elim (hltN x) (hltM x)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ N.vars ∨ x ∈ M.vars <;> by_cases hy : y ∈ N.vars ∨ y ∈ M.vars
    · rwa [hfV x hx, hfV y hy] at hxy
    · rw [hfV x hx, hfO y hy] at hxy
      have := hVB x hx
      omega
    · rw [hfO x hx, hfV y hy] at hxy
      have := hVB y hy
      omega
    · rw [hfO x hx, hfO y hy] at hxy
      omega
  -- `f` fixes `N` and `M`
  have hfixN : (N.bind fun y => var (f y)) = N := by
    rw [Net.bind_congr (g := var) fun x hx => by rw [hfV x (Or.inl hx)]]
    exact Net.bind_var_self N
  have hfixM : (M.bind fun y => var (f y)) = M := by
    rw [Net.bind_congr (g := var) fun x hx => by rw [hfV x (Or.inr hx)]]
    exact Net.bind_var_self M
  have hNl : N.Linear := fun y => by
    have := hN y
    rw [Net.vars_add, Multiset.count_add] at this
    omega
  have hMl : M.Linear := fun y => by
    have := hM y
    rw [Net.vars_add, Multiset.count_add] at this
    omega
  -- every renamed net with the free ports of `N` fits beside `Γ`
  have hgood : ∀ K : Net S ℕ, K.Linear → (∀ y, K.vars.count y = 1 ↔ N.vars.count y = 1) →
      ((K.bind fun y => var (f y)) + Γ).Linear := by
    intro K hK hKf z
    have hNz := hN z
    have hMz := hM z
    rw [Net.vars_add, Multiset.count_add] at hNz hMz ⊢
    rw [Net.vars_bind_var]
    by_cases hz : ∃ x, f x = z
    · obtain ⟨x, rfl⟩ := hz
      rw [Multiset.count_map_eq_count' f _ hf x]
      by_cases hx : x ∈ N.vars ∨ x ∈ M.vars
      · rw [hfV x hx] at hNz hMz ⊢
        have hKx := hK x
        have hNx := hNl x
        have hMx := hMl x
        have hNMx := h.free_iff x
        have hKfx := hKf x
        rcases hx with hx | hx
        · have := Multiset.one_le_count_iff_mem.2 hx
          omega
        · have := Multiset.one_le_count_iff_mem.2 hx
          omega
      · have hΓ : x + B ∉ Γ.vars := fun hm => by
          have := hltΓ _ hm
          omega
        rw [hfO x hx, Multiset.count_eq_zero_of_notMem hΓ]
        exact hK x
    · have hm : z ∉ K.vars.map f := fun hm => by
        obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hm
        exact hz ⟨x, hx⟩
      rw [Multiset.count_eq_zero_of_notMem hm]
      omega
  have := Equiv.bind_var_add_right f hf Γ hgood h hNl fun _ => Iff.rfl
  rwa [hfixN, hfixM] at this

-- ============================================================================================
-- 3. Example
-- ============================================================================================

section Example

open Comb

/-- Non-vacuity: the wire `2` between a `con` cell and the free port `3` is substituted away,
beside a context `Γ` that plugs an `era` cell into the free port `3`. -/
example :
    Equiv
      (({s(var 2, mkCon (var 0) (var 1)), s(var 3, var 2)} : Net sig ℕ) + {s(var 3, mkEra)})
      (({s(var 3, mkCon (var 0) (var 1))} : Net sig ℕ) + {s(var 3, mkEra)}) := by
  have hW : Wire ({s(var 2, mkCon (var 0) (var 1)), s(var 3, var 2)} : Net sig ℕ)
      {s(var 3, mkCon (var 0) (var 1))} := by
    refine (Wire.mk 2 (mkCon (var 0) (var 1)) (var 3) (var 2) 0 ?_ (by simp)).cast rfl ?_
    · intro x
      simp [Multiset.count_cons, Multiset.count_singleton]
      split_ifs <;> omega
    · simp [Term.subst]
  refine Equiv.add_right _ hW.equiv ?_ ?_
  · intro x
    simp [Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega
  · intro x
    simp [Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega

end Example

end INet
