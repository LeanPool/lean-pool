/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.BooleanDegree
public import LeanPool.NoncommutativeAMGM.HarmonicExpansion

/-! # Replacing the total variable by the slice parameter -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

/-- The polynomial quotient of `(Z-k)ₜ-(s-k)ₜ` by `Z-s`. -/
noncomputable def booleanFallingQuotient (n k : ℕ) (s : ℝ) : ℕ → BooleanPolynomial n
  | 0 => 0
  | t + 1 => (totalVariable n - ((k + t : ℕ) : ℝ) • 1) *
      booleanFallingQuotient n k s t + falling (s - k) t • 1

theorem booleanFalling_substitution (n k t : ℕ) (s : ℝ) :
    booleanFalling n k t - falling (s - k) t • 1 =
      (totalVariable n - s • 1) * booleanFallingQuotient n k s t := by
  induction t with
  | zero => simp [booleanFallingQuotient]
  | succ t ih =>
    have hscalar : falling (s - k) (t + 1) • (1 : BooleanPolynomial n) =
        (s • 1 - ((k + t : ℕ) : ℝ) • 1) * (falling (s - k) t • 1) := by
      rw [falling_succ]
      simp only [Algebra.smul_def, mul_one, map_mul, map_sub, Nat.cast_add]
      push_cast
      ring
    rw [booleanFalling_succ, hscalar, booleanFallingQuotient]
    linear_combination (totalVariable n - ((k + t : ℕ) : ℝ) • 1) * ih

theorem booleanFalling_degree (n k t : ℕ) : BooleanDegreeLE (booleanFalling n k t) t := by
  induction t with
  | zero => simpa using booleanDegreeLE_one n
  | succ t ih =>
    rw [booleanFalling_succ]
    simpa [Nat.add_comm] using booleanDegreeLE_mul (booleanDegreeLE_total_sub n _) ih

theorem booleanFallingQuotient_degree (n k t : ℕ) (s : ℝ) :
    BooleanDegreeLE (booleanFallingQuotient n k s t) (t - 1) := by
  induction t with
  | zero => exact booleanDegreeLE_zero _ _
  | succ t ih =>
    cases t with
    | zero =>
      simp only [booleanFallingQuotient, mul_zero, falling_zero, one_smul, zero_add]
      exact booleanDegreeLE_one n
    | succ t =>
      apply booleanDegreeLE_add
      · exact booleanDegreeLE_mono
          (booleanDegreeLE_mul (booleanDegreeLE_total_sub n _) ih) (by omega)
      · exact booleanDegreeLE_smul _
          (booleanDegreeLE_mono (booleanDegreeLE_one n) (by omega))

/-- A degree-controlled change by a multiple of `Z-s` preserves the slice second moment. -/
theorem slice_square_eq_of_substitution {n d : ℕ} (s : ℝ) (f g q : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d)
    (hg : BooleanDegreeLE g d) (hq : BooleanDegreeLE q (d - 1))
    (hsub : f - g = (totalVariable n - s • 1) * q) :
    sliceFunctional n s (f ^ 2) = sliceFunctional n s (g ^ 2) := by
  have hprod : BooleanDegreeLE (q * (f + g)) (n - 1) := by
    apply booleanDegreeLE_mono (booleanDegreeLE_mul hq (booleanDegreeLE_add hf hg))
    omega
  have hz := slice_total_sub_mul hn s (q * (f + g)) hprod
  have he : f ^ 2 - g ^ 2 = (totalVariable n - s • 1) * (q * (f + g)) := by
    calc
      _ = (f - g) * (f + g) := by ring
      _ = _ := by rw [hsub]; ring
  rw [← he, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- The harmonic expansion with `Z` replaced by the real slice parameter. -/
noncomputable def harmonicSliceReplacement {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) : BooleanPolynomial n :=
  ∑ r ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (r + 1),
    falling (s - k) (r - k) • homogeneousPolynomial (h r k)

/-- The explicit quotient witnessing the difference from the harmonic replacement. -/
noncomputable def harmonicSliceQuotient {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) : BooleanPolynomial n :=
  ∑ r ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (r + 1),
    booleanFallingQuotient n k s (r - k) * homogeneousPolynomial (h r k)

theorem harmonicSliceReplacement_degree {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) :
    BooleanDegreeLE (harmonicSliceReplacement h d s) d := by
  apply booleanDegreeLE_sum
  intro r hr
  apply booleanDegreeLE_sum
  intro k hk
  apply booleanDegreeLE_smul
  apply booleanDegreeLE_mono (homogeneousPolynomial_degree _)
  have := Finset.mem_range.mp hr
  have := Finset.mem_range.mp hk
  omega

theorem harmonicSliceQuotient_degree {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) :
    BooleanDegreeLE (harmonicSliceQuotient h d s) (d - 1) := by
  apply booleanDegreeLE_sum
  intro r hr
  apply booleanDegreeLE_sum
  intro k hk
  by_cases he : r = k
  · subst r
    simp only [Nat.sub_self, booleanFallingQuotient, zero_mul]
    exact booleanDegreeLE_zero _ _
  · apply booleanDegreeLE_mono (booleanDegreeLE_mul
      (booleanFallingQuotient_degree n k (r - k) s) (homogeneousPolynomial_degree _))
    have := Finset.mem_range.mp hr
    have := Finset.mem_range.mp hk
    omega

theorem harmonicSliceReplacement_difference {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) :
    (∑ r ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (r + 1),
      booleanFalling n k (r - k) * homogeneousPolynomial (h r k)) -
        harmonicSliceReplacement h d s =
      (totalVariable n - s • 1) * harmonicSliceQuotient h d s := by
  rw [harmonicSliceReplacement, harmonicSliceQuotient, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (booleanFalling n k (r - k) - falling (s - k) (r - k) • 1) *
        homogeneousPolynomial (h r k) := by rw [sub_mul, smul_mul_assoc, one_mul]
    _ = _ := by rw [booleanFalling_substitution]; ring

/-- Constructive slice-second-moment preservation for the full harmonic expansion. -/
theorem exists_harmonic_slice_replacement {n d : ℕ} (s : ℝ) (f : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d) :
    ∃ h : (r k : ℕ) → HomogeneousSpace n k,
      (∀ r k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h r k))) ∧
      sliceFunctional n s (f ^ 2) =
        sliceFunctional n s ((harmonicSliceReplacement h d s) ^ 2) := by
  obtain ⟨h, hhar, he⟩ := boolean_harmonic_expansion f hf
  refine ⟨h, hhar, ?_⟩
  apply slice_square_eq_of_substitution s f _ (harmonicSliceQuotient h d s) hn hd hf
    (harmonicSliceReplacement_degree h d s) (harmonicSliceQuotient_degree h d s)
  conv_lhs => rw [he]
  exact harmonicSliceReplacement_difference h d s

/-- A single family of harmonic vectors works simultaneously for every real slice parameter. -/
theorem exists_uniform_harmonic_slice_replacement {n d : ℕ} (f : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d) :
    ∃ h : (r k : ℕ) → HomogeneousSpace n k,
      (∀ r k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h r k))) ∧
      ∀ s : ℝ, sliceFunctional n s (f ^ 2) =
        sliceFunctional n s ((harmonicSliceReplacement h d s) ^ 2) := by
  obtain ⟨h, hhar, he⟩ := boolean_harmonic_expansion f hf
  refine ⟨h, hhar, ?_⟩
  intro s
  apply slice_square_eq_of_substitution s f _ (harmonicSliceQuotient h d s) hn hd hf
    (harmonicSliceReplacement_degree h d s) (harmonicSliceQuotient_degree h d s)
  conv_lhs => rw [he]
  exact harmonicSliceReplacement_difference h d s

end NoncommutativeAMGM
