/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Iteratedderivs -/


@[expose] public section

open  UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Pointwise


theorem upper_ne_int (x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0 := by
  intro h
  have h1 : 0 < (x : ℂ).im := by simpa using im_pos x
  simp [add_eq_zero_iff_eq_neg.mp h] at h1


theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  have hs : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  rw [iteratedDerivWithin_comp_add_const]
  change iteratedDerivWithin k (fun y : ℂ => 1 / y)
    ((d : ℂ) +ᵥ {z : ℂ | 0 < z.im}) (x + (d : ℂ)) = _
  have hmem : x + (d : ℂ) ∈ (d : ℂ) +ᵥ {z : ℂ | 0 < z.im} := by
    simpa only [vadd_eq_add, add_comm] using vadd_mem_vadd_set (a := (d : ℂ)) hx
  have h := iteratedDerivWithin_one_div k (hs.vadd (d : ℂ)) hmem
  have exponent : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
  simpa only [exponent, zpow_neg, zpow_natCast, one_div] using h

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx; simp_rw [sub_eq_add_neg]; simpa using aut_iter_deriv (-d : ℤ) k hx

theorem aut_contDiffOn (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d))
    {z : ℂ | 0 < z.im} := by
  simp only [one_div]
  apply ContDiffOn.inv
  · apply ContDiffOn.sub
    · apply contDiffOn_id
    apply contDiffOn_const
  intro x hx; simpa [sub_eq_add_neg] using upper_ne_int ⟨x, hx⟩ (-d)


theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) {z : ℂ | 0 < z.im})
      ((fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  have h1 :
    (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) =
      (fun z : ℂ => 1 / (z - d)) + fun z : ℂ => 1 / (z + d) := by rfl
  rw [h1]
  simp only [one_div, Pi.add_apply] at *
  rw [iteratedDerivWithin_add hx ?_]
  · have h2 := aut_iter_deriv d k hx
    have h3 := aut_iter_deriv' d k hx
    simp_all only [mem_ofPred_eq, one_div]
  · have h4 := aut_contDiffOn d k
    simp only [one_div] at h4
    apply h4
    exact hx
  · have h5 := aut_contDiffOn (-d) k
    simp only [Int.cast_neg, sub_neg_eq_add, one_div] at h5
    apply h5
    exact hx
  · exact IsOpen.uniqueDiffOn (isOpen_lt (by
    exact continuous_const) (by
    exact continuous_im))

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)




theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * m * s))
           {z : ℂ | 0 < z.im})
      (fun t => (2 * ↑π * Complex.I * m) ^ n * Complex.exp (2 * ↑π * Complex.I * m * t))
      {z : ℂ | 0 < z.im} := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen (isOpen_lt (by
    exact continuous_const) (by
    exact continuous_im)))
  exact fun x _ => congr_fun (iteratedDeriv_cexp_const_mul ..) x
