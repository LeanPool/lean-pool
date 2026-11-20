/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.Basic

/-!
# Adjacency in the graphs of the frozen statement file

Unfolding lemmas for `tensorProd`, `wheel`, `mycielskian` and `extMycielskian` of
`Research/WordRepTensor/Challenge.lean`, and adjacency in Mathlib's `cycleGraph` in terms of
the values of the vertices (written by Claude, 2026-09-28).
-/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

/-! ## Cycles -/

theorem fin_sub_val {n : ℕ} (x y : Fin n) :
    (x - y).val = if y.val ≤ x.val then x.val - y.val else n + x.val - y.val := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr h
  · exact Fin.coe_sub_iff_lt.mpr (by omega)

theorem cyc_adj_iff {n : ℕ} (a b : Fin n) :
    (cycleGraph n).Adj a b ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ (a.val = 0 ∧ b.val + 1 = n) ∨
        (b.val = 0 ∧ a.val + 1 = n)) ∧ 3 ≤ n ∨
      (n = 2 ∧ a ≠ b) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [cycleGraph_adj', fin_sub_val, fin_sub_val]
  constructor
  · intro h
    by_cases hn : 3 ≤ n
    · left
      refine ⟨?_, hn⟩
      split_ifs at h <;> omega
    · right
      have hne : a ≠ b := by
        rintro rfl
        simp at h
      refine ⟨?_, hne⟩
      have : a.val ≠ b.val := fun h' => hne (Fin.ext h')
      split_ifs at h <;> omega
  · rintro (⟨h, hn⟩ | ⟨hn, hne⟩)
    · split_ifs <;> omega
    · have : a.val ≠ b.val := fun h' => hne (Fin.ext h')
      split_ifs <;> omega

theorem cyc_adj_iff' {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) :
    (cycleGraph n).Adj a b ↔
      a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ (a.val = 0 ∧ b.val + 1 = n) ∨
        (b.val = 0 ∧ a.val + 1 = n) := by
  rw [cyc_adj_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl ⟨h, hn⟩

theorem fin_val_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (i + 1).val = if i.val + 1 < n then i.val + 1 else 0 := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hi := i.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : i.val + 1 = n := by omega
    rw [this, Nat.mod_self]

/-! ## Unfolding the graphs of the statement file -/

theorem tensorProd_adj {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) (p q : α × β) :
    (tensorProd G H).Adj p q ↔ G.Adj p.1 q.1 ∧ H.Adj p.2 q.2 := Iff.rfl

section Wheel

variable {n : ℕ}

theorem wheel_adj_inl_inl (i j : Fin n) :
    (wheel n).Adj (.inl i) (.inl j) ↔ (cycleGraph n).Adj i j := by
  unfold wheel
  rw [SimpleGraph.fromRel_adj]
  simp only [wheelRel, decide_eq_true_eq, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

theorem wheel_adj_inl_inr (i : Fin n) (u : Unit) : (wheel n).Adj (.inl i) (.inr u) := by
  unfold wheel
  rw [SimpleGraph.fromRel_adj]
  simp [wheelRel]

theorem wheel_adj_inr_inl (i : Fin n) (u : Unit) : (wheel n).Adj (.inr u) (.inl i) :=
  (wheel_adj_inl_inr i u).symm

theorem wheel_not_adj_inr_inr (u v : Unit) : ¬ (wheel n).Adj (.inr u) (.inr v) := by
  unfold wheel
  rw [SimpleGraph.fromRel_adj]
  simp [wheelRel]

end Wheel

section Myc

variable {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem myc_adj_inl_inl (a b : V) :
    (mycielskian G).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp only [mycRel, decide_eq_true_eq, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

theorem myc_adj_inl_sh (a b : V) :
    (mycielskian G).Adj (.inl a) (.inr (.inl b)) ↔ G.Adj a b := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [mycRel]

theorem myc_adj_sh_inl (a b : V) :
    (mycielskian G).Adj (.inr (.inl b)) (.inl a) ↔ G.Adj a b := by
  rw [SimpleGraph.adj_comm]
  exact myc_adj_inl_sh G a b

theorem myc_not_adj_inl_root (a : V) (u : Unit) :
    ¬ (mycielskian G).Adj (.inl a) (.inr (.inr u)) := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [mycRel]

theorem myc_not_adj_root_inl (a : V) (u : Unit) :
    ¬ (mycielskian G).Adj (.inr (.inr u)) (.inl a) := by
  rw [SimpleGraph.adj_comm]
  exact myc_not_adj_inl_root G a u

theorem myc_not_adj_sh_sh (a b : V) :
    ¬ (mycielskian G).Adj (.inr (.inl a)) (.inr (.inl b)) := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [mycRel]

theorem myc_adj_sh_root (a : V) (u : Unit) :
    (mycielskian G).Adj (.inr (.inl a)) (.inr (.inr u)) := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [mycRel]

theorem myc_adj_root_sh (a : V) (u : Unit) :
    (mycielskian G).Adj (.inr (.inr u)) (.inr (.inl a)) :=
  (myc_adj_sh_root G a u).symm

theorem myc_not_adj_root_root (u v : Unit) :
    ¬ (mycielskian G).Adj (.inr (.inr u)) (.inr (.inr v)) := by
  unfold mycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [mycRel]

end Myc

section Ext

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ext_adj_inl_inl (a b : V) :
    (extMycielskian G).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp only [extMycRel, decide_eq_true_eq, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

theorem ext_adj_inl_sh (a b : V) :
    (extMycielskian G).Adj (.inl a) (.inr (.inl b)) ↔ a ≠ b := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [extMycRel]

theorem ext_adj_sh_inl (a b : V) :
    (extMycielskian G).Adj (.inr (.inl b)) (.inl a) ↔ a ≠ b := by
  rw [SimpleGraph.adj_comm]
  exact ext_adj_inl_sh G a b

theorem ext_not_adj_inl_root (a : V) (u : Unit) :
    ¬ (extMycielskian G).Adj (.inl a) (.inr (.inr u)) := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [extMycRel]

theorem ext_not_adj_root_inl (a : V) (u : Unit) :
    ¬ (extMycielskian G).Adj (.inr (.inr u)) (.inl a) := by
  rw [SimpleGraph.adj_comm]
  exact ext_not_adj_inl_root G a u

theorem ext_not_adj_sh_sh (a b : V) :
    ¬ (extMycielskian G).Adj (.inr (.inl a)) (.inr (.inl b)) := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [extMycRel]

theorem ext_adj_sh_root (a : V) (u : Unit) :
    (extMycielskian G).Adj (.inr (.inl a)) (.inr (.inr u)) := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [extMycRel]

theorem ext_adj_root_sh (a : V) (u : Unit) :
    (extMycielskian G).Adj (.inr (.inr u)) (.inr (.inl a)) :=
  (ext_adj_sh_root G a u).symm

theorem ext_not_adj_root_root (u v : Unit) :
    ¬ (extMycielskian G).Adj (.inr (.inr u)) (.inr (.inr v)) := by
  unfold extMycielskian
  rw [SimpleGraph.fromRel_adj]
  simp [extMycRel]

end Ext

end WordRepTensor
