/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Hosts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# T406-q: the gap of the construction (ledger Cor. 9.2)

For a finite field `F`, a finite `F`-module `W`, an embedding `σ : Fin 6 ↪ F` and a separable cap
`C ⊆ W`,
the split graph `G(C) = hostGraph (palette C σ hS)` on `(F × W) ⊕ HostIdx F W` satisfies

  `gap G(C) ≥ |C| · |W| / 3`,   `|V(G(C))| ≤ 3 q³ |W|`   (`q = |F| ≥ 2`).
-/

@[expose] public section

namespace GapExtremal

open Finset

/-- Split graphs: a clique and an independent set covering all vertices. -/
def IsSplit {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ K : Set V, (∀ x ∈ K, ∀ y ∈ K, x ≠ y → G.Adj x y) ∧ (∀ x ∉ K, ∀ y ∉ K, ¬ G.Adj x y)

theorem isSplit_hostGraph {V H : Type*}
    (N : H → Finset V) : IsSplit (hostGraph N) := by
  refine ⟨Set.range Sum.inl, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact fun e => h (by rw [e])
  · rintro (x | h) hx (y | h') hy
    · exact absurd ⟨x, rfl⟩ hx
    · exact absurd ⟨x, rfl⟩ hx
    · exact absurd ⟨y, rfl⟩ hy
    · exact hostGraph_inr_inr N h h'

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

/-- **T406-q.** -/
theorem gap_ge_third (σ : Fin 6 ↪ F) {C : Finset W} (hC : IsCap F (C : Set W))
    (hS : IsSep F (C : Set W)) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (palette C σ hS)) := by
  have h := gap_ge (hostHyp (σ := σ) hS) (8 * (blocks (F := F) C).card)
    (fun T hT => I_le (σ := σ) hC hT)
    (resPack_ysrc (C := C) (σ := σ))
  have hv := value_ysrc (C := C) (σ := σ)
  rw [card_blocks] at h
  push_cast at h ⊢
  linarith

omit [AddCommGroup W] [DecidableEq F] [DecidableEq W] [Module F W] in
/-- Order of the construction. -/
theorem card_vertices_le (hq : 2 ≤ Fintype.card F) :
    Fintype.card ((F × W) ⊕ HostIdx F W) ≤ 3 * Fintype.card F ^ 3 * Fintype.card W := by
  simp only [HostIdx, Fintype.card_sum, Fintype.card_prod, Sym2.card]
  set q := Fintype.card F
  set m := Fintype.card W
  have h1 : (q + 1).choose 2 ≤ q * q := by
    rw [Nat.choose_two_right]
    apply Nat.div_le_of_le_mul
    simp only [Nat.add_sub_cancel]
    nlinarith
  have e1 : q * m * (q + 1).choose 2 ≤ q * m * (q * q) := Nat.mul_le_mul_left _ h1
  have e2 : q * m ≤ q * m * (q * q) := Nat.le_mul_of_pos_right _ (by positivity)
  have e3 : q * m * (q * q) = q ^ 3 * m := by ring
  calc q * m + (q * m * (q * q) + q * m * (q + 1).choose 2)
      ≤ q * m * (q * q) + (q * m * (q * q) + q * m * (q * q)) := by omega
    _ = 3 * q ^ 3 * m := by rw [e3]; ring

end GapExtremal
