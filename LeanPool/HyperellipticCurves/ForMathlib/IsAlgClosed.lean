/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Transport of algebraic closedness along a ring isomorphism

`IsAlgClosed.of_ringEquiv'` is the universe-polymorphic form of Mathlib's
`IsAlgClosed.of_ringEquiv`, whose statement gratuitously constrains the two fields to lie in
the same universe although its proof (reproduced verbatim here) never uses that. It should
replace `IsAlgClosed.of_ringEquiv` upstream.
-/

@[expose] public section

open Polynomial

/-- A field isomorphic to an algebraically closed field is algebraically closed. This is
`IsAlgClosed.of_ringEquiv` without its same-universe restriction. -/
theorem IsAlgClosed.of_ringEquiv' {k k' : Type*} [Field k] [Field k'] [IsAlgClosed k]
    (e : k ≃+* k') : IsAlgClosed k' := by
  refine IsAlgClosed.of_exists_root _ fun q hqm hq ↦ ?_
  have hqe : degree (q.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hq)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := k) (q.map e.symm.toRingHom) hqe
  refine ⟨e x, ?_⟩
  rw [IsRoot] at hx
  refine e.symm.injective ?_
  rw [map_zero, ← hx]
  clear hx hqe hq hqm
  induction q using Polynomial.induction_on <;> simp_all

end
