/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.FieldTheory.Minpoly.ConjRootClass


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Conjugate decomposition

Decomposes sums into Frobenius-conjugate classes in the extension-field argument of
Carlitz (1969).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

/-- Partition an algebra extension into its conjugacy classes over the base field. -/
noncomputable def conjSigmaEquiv
    (F L : Type*) [Field F] [Field L] [Algebra F L] :
    (Σ c : ConjRootClass F L, c.carrier) ≃ L where
  toFun z := z.2.1
  invFun x := ⟨ConjRootClass.mk F x, ⟨x, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨c, ⟨x, hx⟩⟩
    have hc : ConjRootClass.mk F x = c :=
      ConjRootClass.mem_carrier.mp hx
    subst c
    rfl
  right_inv x := rfl

theorem sum_eq_sum_conjRootClass
    {F L M : Type*} [Field F] [Field L] [Algebra F L]
    [Fintype L] [Fintype (ConjRootClass F L)]
    [∀ c : ConjRootClass F L, Fintype c.carrier]
    [AddCommMonoid M] (f : L → M) :
    (∑ x : L, f x) =
      ∑ c : ConjRootClass F L, ∑ x : c.carrier, f x.1 := by
  classical
  symm
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (conjSigmaEquiv F L)
    (fun z => f z.2.1) f (fun _ => rfl)


end KloostermanWeil.Carlitz
