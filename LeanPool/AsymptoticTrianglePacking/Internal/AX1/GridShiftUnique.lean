/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Diagonal grid labelling: each block-pair is used at most once.

For the deterministic (probability-free) route to `ReducedFamilyResidual` (RESIDUAL.md §3(b)),
one labels the sub-triples of a cluster triple by `(f(j,k), j, k)` with `f(j,k) = (j+k) mod n`.
The point of the diagonal shift `f` is that **each of the three block-pairs is used at most once**:
the maps `(j,k) ↦ (f(j,k), j)`, `(j,k) ↦ (f(j,k), k)` and `(j,k) ↦ (j,k)` are all injective on
`Fin n × Fin n`.  This file proves exactly that — the combinatorial core of the grid design, with
no probability.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-! # GridShiftUnique -/

@[expose] public section

open Finset

namespace Nibble.AX1

/-- The shift `f(j,k) = (j+k) mod n`. -/
def gridShift (n : ℕ) (j k : Fin n) : ℕ := (j.val + k.val) % n

/-- **The `U`–`W` block pair is used at most once**: `(j,k) ↦ (f(j,k), j)` is injective. -/
theorem gridShift_UW_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.1.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [gridShift, Prod.mk.injEq] at h
  obtain ⟨hs, hj⟩ := h
  have hjj : j = j' := Fin.ext hj
  subst hjj
  -- hs : (j + k) % n = (j + k') % n, and k, k' < n ⇒ k = k'
  have hmod : k.val % n = k'.val % n :=
    Nat.ModEq.add_left_cancel' j.val (by simpa [Nat.ModEq] using hs)
  have hk : k.val = k'.val := by
    rwa [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt k'.isLt] at hmod
  exact Prod.ext rfl (Fin.ext hk)

/-- **The `U`–`X` block pair is used at most once**: `(j,k) ↦ (f(j,k), k)` is injective. -/
theorem gridShift_UX_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.2.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [gridShift, Prod.mk.injEq] at h
  obtain ⟨hs, hk⟩ := h
  have hkk : k = k' := Fin.ext hk
  subst hkk
  -- hs : (j + k) % n = (j' + k) % n, i.e. (k + j) % n = (k + j') % n after commuting
  have hs' : (k.val + j.val) % n = (k.val + j'.val) % n := by
    rw [Nat.add_comm k.val j.val, Nat.add_comm k.val j'.val]; exact hs
  have hmod : j.val % n = j'.val % n :=
    Nat.ModEq.add_left_cancel' k.val (by simpa [Nat.ModEq] using hs')
  have hj : j.val = j'.val := by
    rwa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hmod
  exact Prod.ext (Fin.ext hj) rfl

/-- **The `W`–`X` block pair is used at most once**: `(j,k) ↦ (j,k)` is injective (trivial). -/
theorem gridShift_WX_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (p.1.val, p.2.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- **Consequence: the diagonal grid labelling is injective** — distinct `(j,k)` give distinct
sub-triples `(f(j,k), j, k)`.  (Immediate from any one of the block-pair injectivities, e.g.
`WX`.) -/
theorem gridShift_label_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.1.val, p.2.val)) := by
  intro p q h
  have : (p.1.val, p.2.val) = (q.1.val, q.2.val) := by
    simpa using congrArg (fun t => (t.2.1, t.2.2)) h
  exact gridShift_WX_injective this

end Nibble.AX1
