/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Finiteness of bounded Gaussian lattice sets

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- A Gaussian lattice disk of any real squared radius is finite. -/
theorem gaussianLatticeDisk_finite (radius : ℝ) :
    {x : GaussianInt | (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 < radius}.Finite := by
  classical
  let S := {x : GaussianInt | (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 < radius}
  obtain ⟨N, hN⟩ := exists_nat_ge (max radius 1)
  have hR : radius ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNo : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have bounds (x : GaussianInt) (hx : x ∈ S) :
      -(N : ℤ) ≤ x.re ∧ x.re ≤ N ∧ -(N : ℤ) ≤ x.im ∧ x.im ≤ N := by
    change (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 < radius at hx
    have hr : -(N : ℝ) ≤ (x.re : ℝ) := by
      nlinarith [sq_nonneg (x.im : ℝ), sq_nonneg ((x.re : ℝ) + N)]
    have hr' : (x.re : ℝ) ≤ (N : ℝ) := by
      nlinarith [sq_nonneg (x.im : ℝ), sq_nonneg ((x.re : ℝ) - N)]
    have hi : -(N : ℝ) ≤ (x.im : ℝ) := by
      nlinarith [sq_nonneg (x.re : ℝ), sq_nonneg ((x.im : ℝ) + N)]
    have hi' : (x.im : ℝ) ≤ (N : ℝ) := by
      nlinarith [sq_nonneg (x.re : ℝ), sq_nonneg ((x.im : ℝ) - N)]
    exact ⟨by exact_mod_cast hr, by exact_mod_cast hr',
      by exact_mod_cast hi, by exact_mod_cast hi'⟩
  let interval := Set.Icc (-(N : ℤ)) (N : ℤ)
  let : Finite interval := (Set.finite_Icc _ _).to_subtype
  let encode (x : S) : interval × interval :=
    (⟨x.1.re, (bounds x x.2).1, (bounds x x.2).2.1⟩,
      ⟨x.1.im, (bounds x x.2).2.2.1, (bounds x x.2).2.2.2⟩)
  let : Finite S := Finite.of_injective encode (by
    intro x y hxy
    apply Subtype.ext
    apply Zsqrtd.ext
    · exact congrArg (fun z => z.1.val) hxy
    · exact congrArg (fun z => z.2.val) hxy)
  exact Set.finite_coe_iff.mp (by infer_instance : Finite S)

end ApollonianSuperharmonic

end
