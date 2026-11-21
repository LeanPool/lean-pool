/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Parity sums over darts

The same edge-pair argument applies to the darts of a simple graph and to those of a
combinatorial map, including maps with loops.
-/

@[expose] public section

namespace Kasteleyn

open Finset Module

lemma ZMod.two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

lemma ZMod.two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

section Darts

variable {D E X : Type*} [Fintype D] [DecidableEq X]

/-- Sum the values of an edge cochain over the fibres of a function on the darts. -/
def dartFibreSum (edgeOf : D → E) (g : D → X) :
    (E → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun c x := ∑ d with g d = x, c (edgeOf d)
  map_add' a b := by
    funext x
    simp [sum_add_distrib]
  map_smul' r a := by
    funext x
    simp [mul_sum]

/-- The indicator of an edge with two distinct darts contributes once at each dart's image. -/
lemma dartFibreSum_single [DecidableEq D] [DecidableEq E] (edgeOf : D → E) (g : D → X)
    {d e : D} (hd : d ≠ e) (hpair : ({d' | edgeOf d' = edgeOf d} : Finset D) = {d, e}) :
    dartFibreSum edgeOf g (Pi.single (edgeOf d) 1) = Pi.single (g d) 1 + Pi.single (g e) 1 := by
  funext x
  change ∑ d' with g d' = x, (Pi.single (edgeOf d) 1 : E → ZMod 2) (edgeOf d') = _
  rw [sum_filter]
  have h d' : (if g d' = x then (Pi.single (edgeOf d) 1 : E → ZMod 2) (edgeOf d') else 0) =
      if edgeOf d' = edgeOf d then (if g d' = x then 1 else 0) else 0 := by
    by_cases hg : g d' = x <;> by_cases he : edgeOf d' = edgeOf d <;> simp [hg, he]
  rw [sum_congr rfl fun d' _ => h d', ← sum_filter, hpair, sum_pair hd]
  simp [Pi.single_apply, eq_comm]

end Darts

/-! ### Functions with total sum zero -/

/-- The sum of the values of a function on a finite type. -/
def sumLin (X : Type*) [Fintype X] : (X → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun p := ∑ x, p x
  map_add' a b := by simp [sum_add_distrib]
  map_smul' r a := by simp [mul_sum]

/-- The functions on a finite type with total sum zero. -/
def sumZero (X : Type*) [Fintype X] : Submodule (ZMod 2) (X → ZMod 2) :=
  LinearMap.ker (sumLin X)

lemma mem_sumZero {X : Type*} [Fintype X] {p : X → ZMod 2} : p ∈ sumZero X ↔ ∑ x, p x = 0 :=
  Iff.rfl

lemma finrank_sumZero {X : Type*} [Fintype X] [Nonempty X] :
    finrank (ZMod 2) (sumZero X) + 1 = Fintype.card X := by
  classical
  have hφ : LinearMap.range (sumLin X) = ⊤ := by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨Pi.single x₀ r, by simp [sumLin]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin X)
  rw [hφ, finrank_top, finrank_self, Module.finrank_fintype_fun_eq_card] at h
  change 1 + finrank (ZMod 2) (sumZero X) = _ at h
  omega

/-- If indicators for adjacent pairs are in the range, then so is every sum-zero
function on a type reachable from one point. -/
lemma sumZero_le_range_of_reachable {E X : Type*} [Fintype X] [DecidableEq X]
    (f : (E → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2)) {adjacent : X → X → Prop} (root : X)
    (reach : ∀ x, Relation.ReflTransGen adjacent root x)
    (pair_mem : ∀ {a b}, adjacent a b →
      Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ LinearMap.range f) :
    sumZero X ≤ LinearMap.range f := by
  classical
  have hpair (x : X) : Pi.single root (1 : ZMod 2) + Pi.single x 1 ∈ LinearMap.range f := by
    induction reach x with
    | refl =>
      convert (LinearMap.range f).zero_mem
      funext z
      exact ZMod.two_add_self _
    | @tail a b _ hab ih =>
      convert (LinearMap.range f).add_mem ih (pair_mem hab) using 1
      funext z
      simp only [Pi.add_apply]
      rw [add_assoc, ← add_assoc (Pi.single a 1 z), ZMod.two_add_self, zero_add]
  intro p hp
  rw [mem_sumZero] at hp
  have hp' : p = ∑ y, p y • (Pi.single root (1 : ZMod 2) + Pi.single y 1) := by
    funext z
    by_cases hz : z = root
    · subst hz
      simp [Finset.sum_apply, Pi.single_apply, sum_add_distrib, hp]
    · simp [Finset.sum_apply, Pi.single_apply, hz]
  rw [hp']
  exact (LinearMap.range f).sum_mem fun x _ => (LinearMap.range f).smul_mem _ (hpair x)

end Kasteleyn
