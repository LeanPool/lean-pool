/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Ordering ports by vertex and local priority

For XII (4.5), page 253, the circle ports are grouped by vertex.
Within each vertex block, place the two Hamilton ports first.
Sorting by vertex, local priority, and a distinct tie-breaking
index gives the required enumeration. The final index only breaks
ties and does not change either prescribed order.
-/

public section

namespace GraphMinor.GM12

/-- Enumerate all ports in vertex blocks, respecting any assigned
strict local priorities. This supplies the port order for the
crossing drawing in XII (4.5), page 253. -/
theorem exists_port_ordering {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (priority : Fin n × Bool → ℕ) :
    ∃ ρ : (Fin n × Bool) ≃ Fin (2 * n),
      Monotone (fun i => κ (ρ.symm i)) ∧
      (∀ x y, κ x < κ y → ρ x < ρ y) ∧
      ∀ x y, κ x = κ y → priority x < priority y → ρ x < ρ y := by
  classical
  have hcard : Fintype.card (Fin n × Bool) = 2 * n := by simp [Nat.mul_comm]
  let ε : (Fin n × Bool) ≃ Fin (2 * n) := Fintype.equivFinOfCardEq hcard
  let K := Fin m ×ₗ (ℕ ×ₗ Fin (2 * n))
  let key : Fin n × Bool → K := fun x => toLex (κ x, toLex (priority x, ε x))
  have hkey : Function.Injective key := by
    intro x y hxy
    apply ε.injective
    exact congrArg (fun z : K => (ofLex (ofLex z).2).2) hxy
  let τ : (Fin n × Bool) ≃ Set.range key := Equiv.ofInjective key hkey
  let : Fintype (Set.range key) := (Set.finite_range key).fintype
  have hcardK : Fintype.card (Set.range key) = 2 * n :=
    (Fintype.card_congr τ).symm.trans hcard
  let σ : Fin (2 * n) ≃o Set.range key := Fintype.orderIsoFinOfCardEq _ hcardK
  have hτ : ∀ z : Set.range key, key (τ.symm z) = z.val := fun z =>
    congrArg Subtype.val (τ.apply_symm_apply z)
  refine ⟨τ.trans σ.symm.toEquiv, ?_, ?_, ?_⟩
  · intro i j hij
    have h : key (τ.symm (σ i)) ≤ key (τ.symm (σ j)) := by
      rw [hτ, hτ]
      exact σ.monotone hij
    exact (Prod.Lex.le_iff'.mp h).1
  · intro x y hxy
    apply σ.symm.strictMono
    change key x < key y
    exact Prod.Lex.lt_iff.mpr (Or.inl hxy)
  · intro x y hκ hpriority
    apply σ.symm.strictMono
    change key x < key y
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨hκ, Prod.Lex.lt_iff.mpr (Or.inl hpriority)⟩)

end GraphMinor.GM12
