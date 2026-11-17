/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Balanced.SwapOn
public import LeanPool.BalancedEdgeColourings.Overfull.Counting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Equitable strong colourings (Rudašová–Soták), part A: notions and counts

A *strong* (vertex-distinguishing) colouring is a total proper colouring in which distinct
vertices have distinct colour sets. `vcnt c θ` is the number of vertices at which `θ` is present,
that is twice the number of edges coloured `θ`; a colouring is *equitable* if
`vcnt c x ≤ vcnt c y + 2` for all colours `x, y` (class sizes differ by at most one).

`vcnt_swapOn`: after a simultaneous Kempe change on `X`, `θ` is present at `v ∉ X` as before and
at `v ∈ X` iff `(a b) θ` was present.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- A strong (vertex-distinguishing) proper colouring of all edges. -/
def Strong (c : PEC G (Fin k)) : Prop := Total c ∧ Function.Injective (colSet c)

open Classical in
/-- The number of vertices at which `θ` is present. -/
noncomputable def vcnt (c : PEC G (Fin k)) (θ : Fin k) : ℕ :=
  #(univ.filter fun v => θ ∈ colSet c v)

/-- Colour classes differ in size by at most one. -/
def Equitable (c : PEC G (Fin k)) : Prop := ∀ x y : Fin k, vcnt c x ≤ vcnt c y + 2

/-- `Σ_θ vcnt(θ)²`. -/
noncomputable def cost2 (c : PEC G (Fin k)) : ℕ := ∑ θ : Fin k, vcnt c θ ^ 2

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem vcnt_even (c : PEC G (Fin k)) (θ : Fin k) : Even (vcnt c θ) := by
  classical
  have h := even_card_not_free c θ
  unfold vcnt
  convert h using 3
  exact mem_colSet

open Classical in
omit [DecidableRel G.Adj] in
theorem vcnt_swapOn {c : PEC G (Fin k)} {a b : Fin k} {X : Finset V} (hX : KClosed c a b X)
    (θ : Fin k) :
    vcnt (swapOn c a b X hX) θ = #(univ.filter fun v => v ∉ X ∧ θ ∈ colSet c v) +
      #(univ.filter fun v => v ∈ X ∧ Equiv.swap a b θ ∈ colSet c v) := by
  classical
  unfold vcnt
  rw [← card_union_of_disjoint]
  · congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_union]
    by_cases hv : v ∈ X
    · rw [colSet_swapOn_of_mem hX hv, mem_swapSet]; tauto
    · rw [colSet_swapOn_of_not_mem hX hv]; tauto
  · exact disjoint_filter.2 fun v _ h1 h2 => h1.1 h2.1

open Classical in
omit [DecidableRel G.Adj] in
theorem vcnt_split (c : PEC G (Fin k)) (X : Finset V) (θ : Fin k) :
    vcnt c θ = #(univ.filter fun v => v ∉ X ∧ θ ∈ colSet c v) +
      #(univ.filter fun v => v ∈ X ∧ θ ∈ colSet c v) := by
  classical
  unfold vcnt
  rw [← card_union_of_disjoint]
  · congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_union]
    tauto
  · exact disjoint_filter.2 fun v _ h1 h2 => h1.1 h2.1

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Moving `d` from `vcnt a` to `vcnt b`, with `0 < d < vcnt a − vcnt b`, lowers `cost2`. -/
theorem cost2_lt {c c' : PEC G (Fin k)} {a b : Fin k} (hab : a ≠ b) {d : ℕ}
    (ha : vcnt c' a + d = vcnt c a) (hb : vcnt c' b = vcnt c b + d)
    (hθ : ∀ θ, θ ≠ a → θ ≠ b → vcnt c' θ = vcnt c θ) (hd : 0 < d)
    (hgap : vcnt c b + d < vcnt c a) : cost2 c' < cost2 c := by
  classical
  unfold cost2
  rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ (mem_univ a),
    ← add_sum_erase _ _ (mem_erase.2 ⟨hab.symm, mem_univ b⟩),
    ← add_sum_erase _ _ (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]
  have hrest : ∑ θ ∈ (univ.erase a).erase b, vcnt c' θ ^ 2 =
      ∑ θ ∈ (univ.erase a).erase b, vcnt c θ ^ 2 := by
    refine sum_congr rfl fun θ hθ' => ?_
    simp only [mem_erase] at hθ'
    rw [hθ θ hθ'.2.1 hθ'.1]
  rw [hrest]
  have key : ∀ A B d : ℕ, 0 < d → B + d < A → (A - d) ^ 2 + (B + d) ^ 2 < A ^ 2 + B ^ 2 := by
    intro A B d hd0 h
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt h
    have e : A - d = B + m + 1 := by omega
    rw [e, hm]
    nlinarith [Nat.mul_pos hd0 hd0, Nat.mul_le_mul_left d (Nat.zero_le (B + m + 1))]
  have hA : vcnt c' a = vcnt c a - d := by omega
  rw [hA, hb]
  have := key (vcnt c a) (vcnt c b) d hd hgap
  omega
end Balanced

end LeanPool.BalancedEdgeColourings
