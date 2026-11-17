/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import LeanPool.AaronsonAmbainis.Bridge.Fourier
public import LeanPool.AaronsonAmbainis.Row.Degree

/-!
# Closure properties of `HasDegreeLE`

`HasDegreeLE` is closed under constants, sums, scalar multiples, products (degrees add), powers
and finite products; the coordinate functions have degree at most `1`.
These are what makes `HasDegreeLE` a degree in the usual sense.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem hasDegreeLE_const (a : ℝ) (d : ℕ) : HasDegreeLE (fun _ : Cube ι => a) d := by
  exact Row.hasDegreeLE_const a d

omit [DecidableEq ι] in
theorem hasDegreeLE_add {f g : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g d) : HasDegreeLE (fun x => f x + g x) d := by
  exact Row.hasDegreeLE_add hf hg

omit [DecidableEq ι] in
theorem hasDegreeLE_smul (r : ℝ) {f : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d) :
    HasDegreeLE (fun x => r * f x) d := by
  exact Row.hasDegreeLE_const_mul r hf

omit [DecidableEq ι] in
theorem hasDegreeLE_sum {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {d : ℕ}
    (h : ∀ k ∈ s, HasDegreeLE (F k) d) : HasDegreeLE (fun x => ∑ k ∈ s, F k x) d := by
  exact Row.hasDegreeLE_sum s F h

omit [DecidableEq ι] in
theorem hasDegreeLE_chi (S : Finset ι) : HasDegreeLE (chi S) S.card := by
  exact Row.hasDegreeLE_chi S le_rfl

omit [Fintype ι] in
theorem card_symmDiff_le (S T : Finset ι) : (symmDiff S T).card ≤ S.card + T.card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
  intro i hi
  rw [Finset.mem_symmDiff] at hi
  rw [Finset.mem_union]
  rcases hi with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

omit [DecidableEq ι] in
/-- Degrees add under multiplication. -/
theorem hasDegreeLE_mul {f g : Cube ι → ℝ} {d e : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g e) : HasDegreeLE (fun x => f x * g x) (d + e) := by
  exact Row.hasDegreeLE_mul hf hg

omit [DecidableEq ι] in
theorem hasDegreeLE_pow {g : Cube ι → ℝ} {k : ℕ} (hg : HasDegreeLE g k) (m : ℕ) :
    HasDegreeLE (fun x => g x ^ m) (m * k) := by
  exact Row.hasDegreeLE_pow hg m

omit [DecidableEq ι] in
theorem hasDegreeLE_prod {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {k : α → ℕ}
    (h : ∀ a ∈ s, HasDegreeLE (F a) (k a)) :
    HasDegreeLE (fun x => ∏ a ∈ s, F a x) (∑ a ∈ s, k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDegreeLE_const (ι := ι) 1 0
  | insert a s ha ih =>
    have h2 : (fun x => ∏ a ∈ insert a s, F a x) = fun x => F a x * ∏ a ∈ s, F a x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [h2, Finset.sum_insert ha]
    exact hasDegreeLE_mul (h a (Finset.mem_insert_self a s))
      (ih (fun a' ha' => h a' (Finset.mem_insert_of_mem ha')))

omit [DecidableEq ι] in
/-- The `±1` coordinate function has degree at most `1`. -/
theorem hasDegreeLE_pm_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (-1 : ℝ) else 1) 1 := by
  classical
  exact dict_hasDegreeLE_one i

omit [DecidableEq ι] in
/-- The `0/1` coordinate function has degree at most `1`. -/
theorem hasDegreeLE_zo_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (1 : ℝ) else 0) 1 := by
  exact Row.hasDegreeLE_indicator i

end AaronsonAmbainis.Bridge
