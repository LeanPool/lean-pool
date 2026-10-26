/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
(a56de2e9-7a5d-52b3-ac23-cf4f9c005577) by Claude (2026-09-05).

Proof based on Prove2Me submission 0e225520-8f2c-5b33-894a-9f2b9a1b7c36
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Vanishing orbit sums give a coboundary G∘ f-G

Let $X$ be a type, $A$ an additive commutative group, and $f\colon X\to X$ a self-map. Assume that
every point of $X$ is periodic for $f$, in the sense that its minimal period `Function.minimalPeriod
f x` is strictly positive, and let $v\colon X\to A$ be an arbitrary function. Assume further that
for every $x\in X$ the sum of $v$ along the orbit segment of length the minimal period of $x$
vanishes, i.e. $\sum_{k<\operatorname{minimalPeriod}(f,x)} v(f^{[k]}(x))=0$, the sum being taken
over `Finset.range (Function.minimalPeriod f x)` with $f^{[k]}$ the $k$-fold iterate. The conclusion
is the existence of a function $G\colon X\to A$ such that $v(x)=G(f(x))-G(x)$ for every $x\in X$. No
finiteness, measurability or structure hypotheses are imposed on $X$, and $f$ is not assumed
injective beyond what pointwise periodicity forces.

This is the elementary statement that, for a pointwise periodic self-map, a function with vanishing
sums over all minimal orbits is a coboundary for the operator $G\mapsto G\circ f-G$; for $f$ a
permutation coming from a group element it is the computation of $H^1$ of a cyclic group acting on a
permutation module. It is used in the construction of parabolic cocycles and the Hecke-equivariant
comparison for $\Gamma_0(Np)\le\Gamma_0(N)$, notably by
[`HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles`](thm.html#HeckeEis.
coeffHeckeFun_mem_coeffParabolicCocycles) and
[`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms`](thm.html#HeckeEis.
exists_coeffH1par_projLineRepSL_equiv_parabolicHoms).

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero.lean

Prove2Me submission: `0e225520-8f2c-5b33-894a-9f2b9a1b7c36` (ACCEPTED).
-/

section privateSection

namespace P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero

namespace Function
p2m_export "Function"
  "minimalPeriod_apply_iterate minimalPeriod_pos_iff_mem_periodicPts iterate_succ_apply' \
    iterate_add_apply iterate_zero_apply isPeriodicPt_minimalPeriod minimalPeriod IsPeriodicPt \
    iterate_eq_iterate_iff_of_lt_minimalPeriod"
p2m_open "Function"
namespace OrbitPrimitive

variable {X : Type*} (f : X → X) (hf : ∀ x : X, 0 < minimalPeriod f x)

def rel (x y : X) : Prop := ∃ k : ℕ, f^[k] x = y

include hf in
theorem rel_symm {x y : X} (h : rel f x y) : rel f y x := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨minimalPeriod f x * k - k, ?_⟩
  have hper : IsPeriodicPt f (minimalPeriod f x) x := isPeriodicPt_minimalPeriod f x
  have h1 : f^[minimalPeriod f x * k - k] (f^[k] x) = f^[minimalPeriod f x * k] x := by
    rw [← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k (hf x))]
  rw [h1]
  exact (hper.mul_const k).eq

theorem rel_refl (x : X) : rel f x x := ⟨0, rfl⟩

theorem rel_trans {x y z : X} (h₁ : rel f x y) (h₂ : rel f y z) : rel f x z := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, rfl⟩ := h₂
  exact ⟨l + k, by rw [iterate_add_apply]⟩

def orbitSetoid (hf : ∀ x : X, 0 < minimalPeriod f x) : Setoid X where
  r := rel f
  iseqv := ⟨rel_refl f, rel_symm f hf, rel_trans f⟩

noncomputable def base (x : X) : X := (Quotient.mk (orbitSetoid f hf) x).out

theorem rel_base (x : X) : rel f (base f hf x) x := by
  have h : Quotient.mk (orbitSetoid f hf) (base f hf x) = Quotient.mk (orbitSetoid f hf) x :=
    Quotient.out_eq _
  exact Quotient.exact (s := orbitSetoid f hf) h

theorem base_apply (x : X) : base f hf (f x) = base f hf x := by
  unfold base
  congr 1
  apply Quotient.sound
  change rel f (f x) x
  exact rel_symm f hf ⟨1, rfl⟩

open Classical in
noncomputable def idx (x : X) : ℕ :=
  Nat.find (show ∃ k : ℕ, f^[k] (base f hf x) = x from rel_base f hf x)

open Classical in
theorem iterate_idx (x : X) : f^[idx f hf x] (base f hf x) = x := Nat.find_spec (rel_base f hf x)

open Classical in
theorem idx_lt (x : X) : idx f hf x < minimalPeriod f (base f hf x) := by
  by_contra h
  push Not at h
  have hm := hf (base f hf x)
  have key : f^[idx f hf x - minimalPeriod f (base f hf x)] (base f hf x) = x := by
    have e : f^[idx f hf x - minimalPeriod f (base f hf x)] (f^[minimalPeriod f (base f hf x)] (base
      f hf x))
        = f^[idx f hf x] (base f hf x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel h]
    rw [show f^[minimalPeriod f (base f hf x)] (base f hf x) = base f hf x from
      (isPeriodicPt_minimalPeriod f _).eq, iterate_idx] at e
    exact e
  have := Nat.find_min (rel_base f hf x)
    (m := idx f hf x - minimalPeriod f (base f hf x)) (by
      unfold idx at *
      omega)
  exact this key

open Classical in
theorem idx_apply (x : X) :
    (idx f hf (f x) = idx f hf x + 1 ∧ idx f hf x + 1 < minimalPeriod f (base f hf x)) ∨
    (idx f hf (f x) = 0 ∧ idx f hf x + 1 = minimalPeriod f (base f hf x)) := by
  have hb : base f hf (f x) = base f hf x := base_apply f hf x
  have hlt := idx_lt f hf x
  have hstep : f^[idx f hf x + 1] (base f hf x) = f x := by
    rw [iterate_succ_apply', iterate_idx]
  rcases Nat.lt_or_ge (idx f hf x + 1) (minimalPeriod f (base f hf x)) with h | h
  · left
    refine ⟨?_, h⟩
    have hle : idx f hf (f x) ≤ idx f hf x + 1 := by
      unfold idx
      exact Nat.find_min' _ (by rw [hb]; exact hstep)
    have hlt' : idx f hf (f x) < minimalPeriod f (base f hf x) := lt_of_le_of_lt hle h
    have heq : f^[idx f hf (f x)] (base f hf x) = f^[idx f hf x + 1] (base f hf x) := by
      rw [hstep, ← hb, iterate_idx]
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod hlt' h).mp heq
  · right
    have heq : idx f hf x + 1 = minimalPeriod f (base f hf x) := le_antisymm hlt (by exact h)
    refine ⟨?_, heq⟩
    have : f x = base f hf x := by
      rw [← hstep, heq]
      exact (isPeriodicPt_minimalPeriod f _).eq
    unfold idx
    apply (Nat.find_eq_zero (rel_base f hf (f x))).mpr
    show f^[0] (base f hf (f x)) = f x
    rw [hb, iterate_zero_apply, this]

end OrbitPrimitive

open OrbitPrimitive in
theorem OrbitPrimitive.main {X : Type*} {A : Type*} [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x := by
  classical
  refine ⟨fun x => ∑ k ∈ Finset.range (idx f hf x), v (f^[k] (base f hf x)), fun x => ?_⟩
  simp only
  rw [base_apply f hf x]
  rcases idx_apply f hf x with ⟨h1, -⟩ | ⟨h0, hm⟩
  · rw [h1, Finset.sum_range_succ, iterate_idx, add_sub_cancel_left]
  · rw [h0, Finset.sum_range_zero, zero_sub]
    have htot := hv (base f hf x)
    rw [← hm, Finset.sum_range_succ, iterate_idx] at htot
    exact (neg_eq_of_add_eq_zero_left htot).symm ▸ (neg_neg _).symm

end Function

theorem solution {X : Type*} {A : Type*} [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < Function.minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (Function.minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x :=
  Function.OrbitPrimitive.main f hf v hv

end S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
end P2MW
export P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero (solution)

end privateSection

public section publicSection

theorem Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero {X : Type*} {A : Type*}
  [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < Function.minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (Function.minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x :=
      _root_.P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero.solution f hf v
      hv

end publicSection
