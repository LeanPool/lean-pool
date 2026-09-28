/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.IntervalEval
/-!
# N-Dimensional Boxes for Global Optimization

This file provides the `Box` type for representing n-dimensional domains
as products of intervals, along with helper functions for branch-and-bound
optimization.

## Main definitions

* `Box` - A list of intervals representing an n-dimensional box
* `Box.toEnv` - Convert a box to an interval environment
* `Box.mem` - Membership: a point (list of reals) is in a box
* `Box.widestDim` - Find the dimension with the largest width (for splitting)
* `Box.split` - Split a box along a given dimension
* `Box.volume` - Product of interval widths (heuristic measure)

## Design

A `Box` is represented as `List IntervalRat`, where the i-th element is the
interval for the i-th variable. This allows boxes of any dimension.

For expressions with `n` variables (var 0 through var n-1), a box should
have at least `n` intervals. The conversion `Box.toEnv` returns `default`
for out-of-bounds indices.
-/

/-! ### Box type and basic operations -/

@[expose] public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-- An n-dimensional box as a list of intervals.
    The i-th element is the interval for variable i. -/
abbrev Box := List IntervalRat

/-- A point in ℝⁿ represented as a list of reals -/
abbrev Point := List ℝ

/-- A rational point in ℚⁿ -/
abbrev PointQ := List ℚ

namespace Box

/-- Create a one-dimensional box from a single interval. -/
def ofInterval (I : IntervalRat) : Box := [I]

/-- Convert a box to an interval environment.
    Returns `default` for out-of-bounds indices (i.e., the whole real line approximation). -/
def toEnv (B : Box) : IntervalEnv :=
  fun i => B.getD i default

/-- The dimension (number of intervals) of a box -/
def dim (B : Box) : ℕ := B.length

/-- Check if a point is in a box.
    A point is in a box if each coordinate is in the corresponding interval. -/
def mem (p : Point) (B : Box) : Prop :=
  ∃ (h : p.length = B.length), ∀ i : Fin B.length, p[i.val]'(by rw [h]; exact i.isLt) ∈
    B[i.val]'(by exact i.isLt)

/-- Membership for a real function (environment) in a box.
    This is the key notion for correctness: ρ ∈ B means ρ i ∈ B[i] for all i < B.length. -/
def envMem (ρ : Nat → ℝ) (B : Box) : Prop :=
  ∀ i : Fin B.length, ρ i.val ∈ B[i.val]'(by exact i.isLt)

/-- envMem implies the general IntervalEnv membership for toEnv
    NOTE: For indices beyond the box dimension, we use the default interval [0,0].
    This means expressions should only use variables 0..B.length-1 for correct results. -/
theorem envMem_toEnv (ρ : Nat → ℝ) (B : Box) (h : envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    LeanCert.Engine.envMem ρ (toEnv B) := by
  intro i
  unfold toEnv
  by_cases hi : i < B.length
  · simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD]
    exact h ⟨i, hi⟩
  · have hge : B.length ≤ i := not_lt.mp hi
    simp only [List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD]
    rw [IntervalRat.mem_default]
    exact hzero i hge

/-! ### Width and dimension selection -/

/-- Width of an interval -/
def intervalWidth (I : IntervalRat) : ℚ := I.hi - I.lo

/-- Get the width of each dimension -/
def widths (B : Box) : List ℚ := B.map intervalWidth

/-- Find the index of the maximum element in a list (returns 0 for empty list) -/
def maxIdx (xs : List ℚ) : Nat :=
  match xs with
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
    let restMax := maxIdx (y :: rest)
    if x ≥ (y :: rest).getD restMax 0 then 0 else restMax + 1

/-- Find the dimension with the widest interval (heuristic for splitting).
    Returns 0 if the box is empty. -/
def widestDim (B : Box) : Nat :=
  maxIdx (widths B)

/-- Alternative: find widest dimension with explicit fold -/
def widestDim' (B : Box) : Nat :=
  let indexed := B.zipIdx.map fun (I, i) => (i, intervalWidth I)
  match indexed.argmax (·.2) with
  | some (i, _) => i
  | none => 0

/-! ### Box splitting -/

/-- Split a box along a given dimension by bisecting that interval.
    Returns the original box if the dimension is out of bounds. -/
def split (B : Box) (dim : Nat) : Box × Box :=
  if h : dim < B.length then
    let I := B[dim]'h
    let (I₁, I₂) := I.bisect
    let B₁ := B.set dim I₁
    let B₂ := B.set dim I₂
    (B₁, B₂)
  else
    (B, B)

/-- Split along the widest dimension -/
def splitWidest (B : Box) : Box × Box :=
  split B (widestDim B)

/-- Splitting preserves the number of box coordinates. -/
theorem split_length_eq (B : Box) (d : Nat) :
    (split B d).1.length = B.length ∧ (split B d).2.length = B.length := by
  simp only [split]
  split_ifs with h
  · constructor <;> simp only [List.length_set]
  · exact ⟨rfl, rfl⟩

/-- The lower child of a split is a semantic sub-box of its parent. -/
theorem envMem_of_envMem_split (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    envMem ρ (split B d).1 → envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.1)).length := by
      simp only [List.length_set]
      exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_left hmem
    · exact hmem
  · exact h

/-- The upper child of a split is a semantic sub-box of its parent. -/
theorem envMem_of_envMem_split_right (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    envMem ρ (split B d).2 → envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.2)).length := by
      simp only [List.length_set]
      exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_right hmem
    · exact hmem
  · exact h

/-! ### Volume and size heuristics -/

/-- Volume of a box (product of widths).
    Returns 0 for empty box. -/
def volume (B : Box) : ℚ :=
  (widths B).foldl (· * ·) 1

/-- Maximum width across all dimensions -/
def maxWidth (B : Box) : ℚ :=
  (widths B).foldl max 0

/-- Check if a box is "small" (max width below threshold) -/
def isSmall (B : Box) (threshold : ℚ) : Bool :=
  maxWidth B ≤ threshold

/-! ### Box construction helpers -/

/-- Create a box from a list of (lo, hi) pairs -/
def ofPairs (pairs : List (ℚ × ℚ)) : Box :=
  pairs.filterMap fun (lo, hi) =>
    if h : lo ≤ hi then some ⟨lo, hi, h⟩ else none

/-- Create a unit box [0,1]ⁿ -/
def unit (n : Nat) : Box :=
  List.replicate n ⟨0, 1, by norm_num⟩

/-- Create a symmetric box [-1,1]ⁿ -/
def symmetric (n : Nat) : Box :=
  List.replicate n ⟨-1, 1, by norm_num⟩

/-- Create a box from bounds: [lo₀, hi₀] × ... × [loₙ₋₁, hiₙ₋₁] -/
def ofBounds (los his : List ℚ) (_h : los.length = his.length) : Box :=
  (los.zip his).filterMap fun (lo, hi) =>
    if hle : lo ≤ hi then some ⟨lo, hi, hle⟩ else none

/-! ### Membership lemmas -/

/-- If a point is in a box, its i-th coordinate is in the i-th interval -/
theorem coord_mem_of_mem (p : Point) (B : Box) (h : mem p B) (i : Fin B.length) :
    p[i.val]'(by obtain ⟨hlen, _⟩ := h; rw [hlen]; exact i.isLt) ∈ B[i.val]'(by exact i.isLt) := by
  obtain ⟨hlen, hmem⟩ := h
  exact hmem i

/-- After splitting, any point in the original box is in one of the halves. -/
theorem mem_split_cases (B : Box) (d : Nat) (hd : d < B.length)
    (p : Point) (hp : mem p B) :
    mem p (split B d).1 ∨ mem p (split B d).2 := by
  simp only [split, hd, ↓reduceDIte]
  obtain ⟨hp_len, hp_mem⟩ := hp
  have hp_d : p[d]'(by rw [hp_len]; exact hd) ∈ B[d]'hd := hp_mem ⟨d, hd⟩
  have hbisect := IntervalRat.mem_bisect_or hp_d
  cases hbisect with
  | inl hleft =>
    left
    have hlen1 : (B.set d (B[d].bisect.1)).length = B.length := List.length_set
    use (by rw [hlen1]; exact hp_len)
    intro ⟨i, hi⟩
    have hi_orig : i < B.length := by rw [← hlen1]; exact hi
    by_cases h_eq : i = d
    · -- i = d: use the bisection result
      simp only [h_eq, List.getElem_set_self]
      convert hleft using 2
    · -- i ≠ d: use original membership
      have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      have hp_i := hp_mem ⟨i, hi_orig⟩
      convert hp_i using 2
  | inr hright =>
    right
    have hlen2 : (B.set d (B[d].bisect.2)).length = B.length := List.length_set
    use (by rw [hlen2]; exact hp_len)
    intro ⟨i, hi⟩
    have hi_orig : i < B.length := by rw [← hlen2]; exact hi
    by_cases h_eq : i = d
    · simp only [h_eq, List.getElem_set_self]
      convert hright using 2
    · have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      have hp_i := hp_mem ⟨i, hi_orig⟩
      convert hp_i using 2

/-- Environment membership after splitting. -/
theorem envMem_split_cases (B : Box) (d : Nat) (hd : d < B.length)
    (ρ : Nat → ℝ) (hρ : envMem ρ B) :
    envMem ρ (split B d).1 ∨ envMem ρ (split B d).2 := by
  simp only [split, hd, ↓reduceDIte]
  have hρ_d : ρ d ∈ B[d]'hd := hρ ⟨d, hd⟩
  have hbisect := IntervalRat.mem_bisect_or hρ_d
  -- After bisection, ρ d is in either the left or right half
  cases hbisect with
  | inl hleft =>
    left
    intro ⟨i, hi⟩
    -- After B.set d I₁, length is preserved
    have hlen : (B.set d (B[d].bisect.1)).length = B.length := List.length_set
    have hi_orig : i < B.length := by rw [← hlen]; exact hi
    by_cases h_eq : i = d
    · -- i = d: use the bisection result
      simp only [h_eq, List.getElem_set_self]
      exact hleft
    · -- i ≠ d: use original membership
      have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      exact hρ ⟨i, hi_orig⟩
  | inr hright =>
    right
    intro ⟨i, hi⟩
    have hlen : (B.set d (B[d].bisect.2)).length = B.length := List.length_set
    have hi_orig : i < B.length := by rw [← hlen]; exact hi
    by_cases h_eq : i = d
    · simp only [h_eq, List.getElem_set_self]
      exact hright
    · have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      exact hρ ⟨i, hi_orig⟩

end Box

end LeanCert.Engine.Optimization
