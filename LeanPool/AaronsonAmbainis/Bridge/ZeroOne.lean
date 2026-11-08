/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Bridge.Basic

/-!
# `HasDegreeLE` with `0/1` monomials

`HasDegreeLE` is defined with the characters `∏_{i∈S} (-1)^{x_i}`. Theorem 1.7 of
arXiv:2410.19062 and Conjecture 6 of arXiv:0911.0996 speak of polynomials in the `0/1` variables.
The definition with the `0/1` monomials `∏_{i∈S} x_i` is equivalent (`hasDegreeLE_iff_01`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Monomial in the letters `φ (x i)`. -/
noncomputable def mon (φ : Bool → ℝ) (S : Finset ι) (x : Cube ι) : ℝ := ∏ i ∈ S, φ (x i)

/-- Degree at most `d` with respect to the monomials built from the letter `φ`. -/
def HasDegLE (φ : Bool → ℝ) (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * mon φ S x

/-- The analogue of `HasDegreeLE` with the `0/1` monomials `∏_{i∈S} x_i`. -/
def HasDegreeLE01 (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧
    ∀ x, f x = ∑ S, c S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)

omit [DecidableEq ι] in
theorem hasDegreeLE_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ HasDegLE (fun b => if b then (-1 : ℝ) else 1) f d :=
  Iff.rfl

omit [DecidableEq ι] in
theorem hasDegreeLE01_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE01 f d ↔ HasDegLE (fun b => if b then (1 : ℝ) else 0) f d :=
  Iff.rfl

/-- Expansion of a monomial after an affine change of letter `ψ = β φ + α`. -/
theorem mon_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α) (S : Finset ι)
    (x : Cube ι) :
    mon ψ S x
      = ∑ T : Finset ι, if T ⊆ S then β ^ T.card * α ^ (S \ T).card * mon φ T x else 0 := by
  have hpow : S.powerset = univ.filter (fun T => T ⊆ S) := by
    ext T
    simp [Finset.mem_powerset]
  unfold mon
  simp only [hψ]
  rw [Finset.prod_add, hpow, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  split_ifs with hT
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    ring
  · rfl

omit [DecidableEq ι] in
/-- An affine change of letter does not raise the degree. -/
theorem hasDegLE_of_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegLE ψ f d) : HasDegLE φ f d := by
  classical
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => ∑ S : Finset ι, if T ⊆ S then c S * (β ^ T.card * α ^ (S \ T).card) else 0,
    fun T hT => ?_, fun x => ?_⟩
  · refine Finset.sum_eq_zero (fun S _ => ?_)
    split_ifs with hTS
    · rw [hc S (lt_of_lt_of_le hT (Finset.card_le_card hTS)), zero_mul]
    · rfl
  · rw [hf x]
    simp only [mon_affine hψ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun S _ => ?_))
    split_ifs <;> ring

omit [DecidableEq ι] in
/-- `HasDegreeLE` (characters) is equivalent to the definition with `0/1` monomials. -/
theorem hasDegreeLE_iff_01 {f : Cube ι → ℝ} {d : ℕ} : HasDegreeLE f d ↔ HasDegreeLE01 f d := by
  classical
  rw [hasDegreeLE_iff_hasDegLE, hasDegreeLE01_iff_hasDegLE]
  constructor
  · -- `(-1)^b = (-2) * b + 1`
    exact hasDegLE_of_affine (α := 1) (β := -2) (fun b => by cases b <;> norm_num)
  · -- `b = (-1/2) * (-1)^b + 1/2`
    exact hasDegLE_of_affine (α := 1 / 2) (β := -1 / 2) (fun b => by cases b <;> norm_num)

end AaronsonAmbainis.Bridge
