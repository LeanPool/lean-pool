/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation schemes

An **approximation scheme** in the sense of Pietsch is a sequence `A 0 ⊆ A 1 ⊆ A 2 ⊆ ⋯` of
subsets of a real normed space `X` with

* `A 0 = {0}`,
* `c • a ∈ A n` for every real `c` and every `a ∈ A n`,
* `A m + A n ⊆ A (m + n)`.

The elements of `A n` are the "approximants of complexity `n`": polynomials of degree `< n`,
linear combinations of the first `n` elements of a basis, or linear combinations of at most
`n` elements of a dictionary.  The last example is not a linear subspace, which is why a
scheme consists of sets and not of submodules.

`A 0 = {0}` is part of the definition, as in Pietsch's paper.  It makes the error of
approximation from `A 0` equal to the norm, and hence every approximation space embed into
`X`.  Families indexed by a degree are fed in with a strict inequality ("degree `< n`"), so
that this condition holds without shifting indices.

The file provides the structure, its elementary consequences (the sets are nonempty and
closed under negation, differences and finite sums), the dyadic inclusions used by all
telescoping arguments, and two constructions: the preimage `A.comap ι` of a scheme under an
injective linear map and the image `A.map T` under a linear map.
-/

@[expose] public section

open scoped Pointwise

/-- An **approximation scheme** in the sense of Pietsch: an increasing sequence of sets
`A 0 ⊆ A 1 ⊆ ⋯` in a real normed space, starting with `A 0 = {0}`, closed under real
multiples, and with `A m + A n ⊆ A (m + n)`. -/
structure ApproximationScheme (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The set `A n` of approximants of complexity `n`. -/
  sets : ℕ → Set X
  /-- The only approximant of complexity `0` is `0`. -/
  sets_zero : sets 0 = {0}
  /-- The sets increase with the complexity. -/
  mono : Monotone sets
  /-- Each set is closed under real multiples. -/
  smul_mem : ∀ (c : ℝ) {n : ℕ} {a : X}, a ∈ sets n → c • a ∈ sets n
  /-- The sum of two approximants has at most the sum of their complexities. -/
  add_subset : ∀ m n, sets m + sets n ⊆ sets (m + n)

namespace ApproximationScheme

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A scheme is used as its sequence of sets `n ↦ A_n`. -/
instance : CoeFun (ApproximationScheme X) (fun _ => ℕ → Set X) := ⟨ApproximationScheme.sets⟩

variable (A : ApproximationScheme X)

/-- `A_0 = {0}`. -/
theorem coe_zero : A 0 = {0} := A.sets_zero

/-- Two schemes with the same sets are equal. -/
@[ext]
theorem ext {A B : ApproximationScheme X} (h : ∀ n, A n = B n) : A = B := by
  cases A; cases B; congr; funext n; exact h n

/-- `0` is an approximant of every complexity. -/
theorem zero_mem (n : ℕ) : (0 : X) ∈ A n :=
  A.mono (Nat.zero_le n) (by rw [A.coe_zero]; rfl)

/-- The sets of a scheme are nonempty.  This is the hypothesis under which
`Metric.infEDist` is finite, so the error of approximation is finite. -/
theorem nonempty (n : ℕ) : (A n).Nonempty := ⟨0, A.zero_mem n⟩

variable {A}

/-- The sets increase: `A_m ⊆ A_n` for `m ≤ n`. -/
theorem mem_of_le {m n : ℕ} (h : m ≤ n) {a : X} (ha : a ∈ A m) : a ∈ A n := A.mono h ha

/-- `a + b ∈ A_{m+n}` for `a ∈ A_m` and `b ∈ A_n`. -/
theorem add_mem {m n : ℕ} {a b : X} (ha : a ∈ A m) (hb : b ∈ A n) : a + b ∈ A (m + n) :=
  A.add_subset m n (Set.add_mem_add ha hb)

/-- `-a ∈ A_n` for `a ∈ A_n`. -/
theorem neg_mem {n : ℕ} {a : X} (ha : a ∈ A n) : -a ∈ A n := by
  simpa using A.smul_mem (-1) ha

/-- `a - b ∈ A_{m+n}` for `a ∈ A_m` and `b ∈ A_n`. -/
theorem sub_mem {m n : ℕ} {a b : X} (ha : a ∈ A m) (hb : b ∈ A n) : a - b ∈ A (m + n) := by
  simpa [sub_eq_add_neg] using add_mem ha (neg_mem hb)

/-- Two approximants of complexity `2 ^ k` add up to one of complexity `2 ^ (k + 1)`. -/
theorem add_mem_pow_succ {k : ℕ} {a b : X} (ha : a ∈ A (2 ^ k)) (hb : b ∈ A (2 ^ k)) :
    a + b ∈ A (2 ^ (k + 1)) := by
  have := add_mem ha hb
  rwa [← two_mul, ← pow_succ'] at this

/-- `a - b ∈ A_{2^(k+1)}` for `a, b ∈ A_{2^k}`. -/
theorem sub_mem_pow_succ {k : ℕ} {a b : X} (ha : a ∈ A (2 ^ k)) (hb : b ∈ A (2 ^ k)) :
    a - b ∈ A (2 ^ (k + 1)) := by
  have := sub_mem ha hb
  rwa [← two_mul, ← pow_succ'] at this

/-- The difference of consecutive dyadic approximants, `a ∈ A (2 ^ (k + 1))` and
`b ∈ A (2 ^ k)`, lies in `A (2 ^ (k + 2))`.  This is the inclusion that every telescoping
argument uses. -/
theorem sub_mem_pow_add_two {k : ℕ} {a b : X} (ha : a ∈ A (2 ^ (k + 1))) (hb : b ∈ A (2 ^ k)) :
    a - b ∈ A (2 ^ (k + 2)) :=
  mem_of_le (by rw [pow_succ 2 (k + 1), pow_succ 2 k]; omega) (sub_mem ha hb)

/-- A finite sum of approximants has at most the sum of the complexities. -/
theorem sum_mem {ι : Type*} (s : Finset ι) {f : ι → X} {n : ι → ℕ}
    (h : ∀ i ∈ s, f i ∈ A (n i)) : ∑ i ∈ s, f i ∈ A (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using A.zero_mem 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact add_mem (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Multiplying by a nonzero scalar maps `A n` onto itself. -/
theorem smul_set_eq {c : ℝ} (hc : c ≠ 0) (n : ℕ) : c • A n = A n := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact A.smul_mem c ha
  · intro a ha
    refine ⟨c⁻¹ • a, A.smul_mem _ ha, ?_⟩
    simp [smul_smul, hc]

variable (A)

/-- The union of all the sets of a scheme, as a real subspace.  It is closed under addition
because `A m + A n ⊆ A (m + n)`. -/
def iUnionSubmodule : Submodule ℝ X where
  carrier := ⋃ n, A n
  zero_mem' := Set.mem_iUnion.2 ⟨0, A.zero_mem 0⟩
  add_mem' := by
    rintro a b ⟨_, ⟨m, rfl⟩, ha⟩ ⟨_, ⟨n, rfl⟩, hb⟩
    exact Set.mem_iUnion.2 ⟨m + n, add_mem ha hb⟩
  smul_mem' := by
    rintro c a ⟨_, ⟨n, rfl⟩, ha⟩
    exact Set.mem_iUnion.2 ⟨n, A.smul_mem c ha⟩

/-- The submodule `iUnionSubmodule` has the carrier `⋃ n, A_n`. -/
@[simp]
theorem coe_iUnionSubmodule : (A.iUnionSubmodule : Set X) = ⋃ n, A n := rfl

/-- The **preimage of a scheme** under an injective linear map `ι : Y → X`: the sets
`ι ⁻¹' A n`.  Injectivity is what makes `ι ⁻¹' {0} = {0}`.  This is the scheme on a smaller
space `Y` (for instance `L_r ⊆ L_p`) induced by a scheme on `X`. -/
def comap (ι : Y →ₗ[ℝ] X) (hι : Function.Injective ι) : ApproximationScheme Y where
  sets n := ι ⁻¹' A n
  sets_zero := by
    ext y
    simp only [Set.mem_preimage, A.coe_zero, Set.mem_singleton_iff]
    constructor
    · intro h; exact hι (by rw [h, map_zero])
    · rintro rfl; exact map_zero ι
  mono _ _ h _ hy := A.mono h hy
  smul_mem c _ _ hy := by
    simp only [Set.mem_preimage, map_smul] at hy ⊢
    exact A.smul_mem c hy
  add_subset m n := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_preimage, map_add] at ha hb ⊢
    exact add_mem ha hb

/-- Membership in the preimage scheme: `y ∈ ι⁻¹(A_n)` iff `ι y ∈ A_n`. -/
@[simp]
theorem mem_comap {ι : Y →ₗ[ℝ] X} {hι : Function.Injective ι} {n : ℕ} {y : Y} :
    y ∈ A.comap ι hι n ↔ ι y ∈ A n := Iff.rfl

/-- The **image of a scheme** under a linear map `T : X → Y`: the sets `T '' A n`. -/
def map (T : X →ₗ[ℝ] Y) : ApproximationScheme Y where
  sets n := T '' A n
  sets_zero := by simp [A.coe_zero]
  mono _ _ h := Set.image_mono (A.mono h)
  smul_mem c _ _ := by
    rintro ⟨a, ha, rfl⟩
    exact ⟨c • a, A.smul_mem c ha, map_smul T c a⟩
  add_subset m n := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add T a b⟩

/-- Membership in the image scheme: `y ∈ T(A_n)` iff `y = T a` for some `a ∈ A_n`. -/
@[simp]
theorem mem_map {T : X →ₗ[ℝ] Y} {n : ℕ} {y : Y} : y ∈ A.map T n ↔ ∃ a ∈ A n, T a = y :=
  Iff.rfl

/-- `T a ∈ T(A_n)` for `a ∈ A_n`. -/
theorem mem_map_of_mem (T : X →ₗ[ℝ] Y) {n : ℕ} {a : X} (ha : a ∈ A n) : T a ∈ A.map T n :=
  ⟨a, ha, rfl⟩

/-- A scheme made of an increasing sequence of **linear subspaces** starting with `{0}`.  The
third axiom holds automatically, since `A m` and `A n` both lie in `A (m + n)`. -/
def ofSubmodules (A : ℕ → Submodule ℝ X) (h0 : A 0 = ⊥) (hA : Monotone A) :
    ApproximationScheme X where
  sets n := A n
  sets_zero := by rw [h0, Submodule.bot_coe]
  mono _ _ h := hA h
  smul_mem c _ _ ha := (A _).smul_mem c ha
  add_subset m n := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (A (m + n)).add_mem (hA (Nat.le_add_right m n) ha) (hA (Nat.le_add_left n m) hb)

/-- Membership in the scheme of an increasing sequence of subspaces. -/
@[simp]
theorem mem_ofSubmodules {A : ℕ → Submodule ℝ X} {h0 : A 0 = ⊥} {hA : Monotone A} {n : ℕ}
    {x : X} : x ∈ ofSubmodules A h0 hA n ↔ x ∈ A n := Iff.rfl

/-- The **dyadic scheme of an increasing sequence of subspaces** `V_0 ⊆ V_1 ⊆ ⋯`: `{0}` at
complexity `0` and `V_k`, `k = ⌊log₂ n⌋`, at complexity `n ≥ 1`, so that the level `V_k` is the
set of approximants of complexity `2^k`. Piecewise polynomials and splines on dyadic partitions
are schemes of this form. -/
def ofMonotoneSubmodules (V : ℕ → Submodule ℝ X) (hV : Monotone V) : ApproximationScheme X :=
  ofSubmodules (fun n => if n = 0 then ⊥ else V (Nat.log 2 n)) (by simp) (by
    intro a b hab
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      exact bot_le
    · have hb : b ≠ 0 := by omega
      simp only [ha, hb, ↓reduceIte]
      exact hV (Nat.log_mono_right hab))

/-- The dyadic scheme of a sequence of subspaces is `{0}` at complexity `0`. -/
theorem mem_ofMonotoneSubmodules_zero {V : ℕ → Submodule ℝ X} {hV : Monotone V} {x : X} :
    x ∈ ofMonotoneSubmodules V hV 0 ↔ x = 0 := by
  rw [ofMonotoneSubmodules, mem_ofSubmodules]
  simp

/-- The dyadic scheme of a sequence of subspaces is `V_⌊log₂ n⌋` at complexity `n ≥ 1`. -/
theorem mem_ofMonotoneSubmodules {V : ℕ → Submodule ℝ X} {hV : Monotone V} {n : ℕ}
    (hn : n ≠ 0) {x : X} : x ∈ ofMonotoneSubmodules V hV n ↔ x ∈ V (Nat.log 2 n) := by
  rw [ofMonotoneSubmodules, mem_ofSubmodules]
  simp only [hn, ↓reduceIte]

/-- The dyadic scheme of a sequence of subspaces is `V_k` at complexity `2^k`. -/
theorem mem_ofMonotoneSubmodules_two_pow {V : ℕ → Submodule ℝ X} {hV : Monotone V} {k : ℕ}
    {x : X} : x ∈ ofMonotoneSubmodules V hV (2 ^ k) ↔ x ∈ V k := by
  rw [mem_ofMonotoneSubmodules (pow_ne_zero k two_ne_zero), Nat.log_pow Nat.one_lt_two]

end ApproximationScheme
