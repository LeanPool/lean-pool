/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-! # Signs and compact angular coordinates in the mixed embedding space -/

@[expose] public section

namespace NairTenenbaum

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable {K : Type*} [Field K]

/-- Real and complex polar coordinates for the archimedean embeddings. -/
noncomputable def mixedPolarCoordinates
    (σ : {w : InfinitePlace K // IsReal w} → Bool) (r : realSpace K)
    (a : {w : InfinitePlace K // IsComplex w} → ℝ) : mixedSpace K :=
  (fun w => if σ w then r w else -r w,
   fun w => (r w : ℂ) * Complex.exp (((2 * a w - 1) * Real.pi : ℝ) * Complex.I))

theorem exists_mixedPolarCoordinates (x : mixedSpace K) :
    ∃ σ : {w : InfinitePlace K // IsReal w} → Bool,
      ∃ a : {w : InfinitePlace K // IsComplex w} → ℝ,
        a ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧
        mixedPolarCoordinates σ (normAtAllPlaces x) a = x := by
  classical
  let σ : {w : InfinitePlace K // IsReal w} → Bool := fun w => decide (0 ≤ x.1 w)
  let a : {w : InfinitePlace K // IsComplex w} → ℝ :=
    fun w => (Complex.arg (x.2 w) / Real.pi + 1) / 2
  have ha : a ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    constructor <;> intro w
    · have H : -1 ≤ Complex.arg (x.2 w) / Real.pi :=
        (le_div_iff₀ Real.pi_pos).mpr (by linarith [Complex.neg_pi_lt_arg (x.2 w)])
      dsimp [a]
      linarith
    · have H : Complex.arg (x.2 w) / Real.pi ≤ 1 :=
        (div_le_iff₀ Real.pi_pos).mpr (by linarith [Complex.arg_le_pi (x.2 w)])
      dsimp [a]
      linarith
  refine ⟨σ, a, ha, ?_⟩
  apply Prod.ext
  · ext w
    change (if σ w then normAtAllPlaces x w else -normAtAllPlaces x w) = x.1 w
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
    by_cases hw : 0 ≤ x.1 w
    · simp [σ, hw, abs_of_nonneg hw]
    · simp [σ, hw, abs_of_neg (lt_of_not_ge hw)]
  · ext w
    change (normAtAllPlaces x w : ℂ) *
      Complex.exp (((2 * a w - 1) * Real.pi : ℝ) * Complex.I) = x.2 w
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.2]
    have HE : (2 * a w - 1) * Real.pi = Complex.arg (x.2 w) := by
      dsimp [a]
      field_simp
      ring
    rw [HE]
    exact Complex.norm_mul_exp_arg_mul_I (x.2 w)

end NairTenenbaum
