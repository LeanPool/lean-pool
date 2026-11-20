/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.HarmonicNorm
public import LeanPool.NoncommutativeAMGM.SliceSubstitution

/-! # The harmonic norm formula and positivity of the interpolated slice functional -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem homogeneousPolynomial_zero (n k : ℕ) :
    homogeneousPolynomial (0 : HomogeneousSpace n k) = 0 := by
  apply MonoidAlgebra.ext
  ext T
  simp [homogeneousPolynomial_coeff, homogeneousCoefficient]

theorem homogeneousPolynomial_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → HomogeneousSpace n k) :
    homogeneousPolynomial (∑ i ∈ s, c i) = ∑ i ∈ s, homogeneousPolynomial (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousPolynomial_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, homogeneousPolynomial_add, ih,
      Finset.sum_insert hi]

theorem homogeneous_harmonic_zero (n k : ℕ) :
    HarmonicCoefficients k (homogeneousCoefficient (0 : HomogeneousSpace n k)) := by
  cases k with
  | zero => intro R hR; omega
  | succ k => exact (homogeneousDown_eq_zero_iff _).mp (map_zero _)

theorem homogeneous_harmonic_smul {n k : ℕ} (a : ℝ) (c : HomogeneousSpace n k)
    (hc : HarmonicCoefficients k (homogeneousCoefficient c)) :
    HarmonicCoefficients k (homogeneousCoefficient (a • c)) := by
  cases k with
  | zero => intro R hR; omega
  | succ k =>
    apply (homogeneousDown_eq_zero_iff _).mp
    rw [map_smul, (homogeneousDown_eq_zero_iff c).mpr hc, smul_zero]

theorem homogeneous_harmonic_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → HomogeneousSpace n k)
    (hc : ∀ i ∈ s, HarmonicCoefficients k (homogeneousCoefficient (c i))) :
    HarmonicCoefficients k (homogeneousCoefficient (∑ i ∈ s, c i)) := by
  cases k with
  | zero => intro R hR; omega
  | succ k =>
    apply (homogeneousDown_eq_zero_iff _).mp
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact (homogeneousDown_eq_zero_iff (c i)).mpr (hc i hi)

/-- The coefficient vector of degree `k` after replacing `Z` by `s`. -/
noncomputable def harmonicSliceComponent {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) (k : ℕ) :
    HomogeneousSpace n k :=
  ∑ r ∈ Finset.range (d + 1), if k ≤ r then falling (s - k) (r - k) • h r k else 0

theorem harmonicSliceComponent_harmonic {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) (k : ℕ)
    (hhar : ∀ r k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h r k))) :
    HarmonicCoefficients k (homogeneousCoefficient (harmonicSliceComponent h d s k)) := by
  apply homogeneous_harmonic_sum
  intro r _
  split_ifs with hkr
  · exact homogeneous_harmonic_smul _ _ (hhar r k hkr)
  · exact homogeneous_harmonic_zero _ _

theorem harmonicSliceReplacement_eq_sum {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d : ℕ) (s : ℝ) :
    harmonicSliceReplacement h d s =
      ∑ k ∈ Finset.range (d + 1), homogeneousPolynomial (harmonicSliceComponent h d s k) := by
  classical
  simp only [harmonicSliceComponent, homogeneousPolynomial_sum]
  simp_rw [apply_ite (homogeneousPolynomial (n := n)), homogeneousPolynomial_smul,
    homogeneousPolynomial_zero]
  rw [Finset.sum_comm]
  unfold harmonicSliceReplacement
  apply Finset.sum_congr rfl
  intro r hr
  have hfilter : (Finset.range (d + 1)).filter (fun k ↦ k ≤ r) = Finset.range (r + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have := Finset.mem_range.mp hr
    omega
  rw [← Finset.sum_filter, hfilter]

/-- Equation (28) for the constructed harmonic replacement, simultaneously for every `s`. -/
theorem boolean_harmonic_norm_formula {n d : ℕ} (f : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d) :
    ∃ h : (r k : ℕ) → HomogeneousSpace n k,
      (∀ r k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h r k))) ∧
      ∀ s : ℝ, sliceFunctional n s (f ^ 2) =
        ∑ k ∈ Finset.range (d + 1),
          (falling s k * falling ((n : ℝ) - s) k / falling n (2 * k)) *
            ∑ S : HomogeneousIndex n k, (harmonicSliceComponent h d s k S) ^ 2 := by
  obtain ⟨h, hhar, he⟩ := exists_uniform_harmonic_slice_replacement f hn hd hf
  refine ⟨h, hhar, ?_⟩
  intro s
  rw [he s, harmonicSliceReplacement_eq_sum]
  exact slice_harmonic_sum_square s _ (fun k _ ↦ harmonicSliceComponent_harmonic h d s k hhar) hd

/-- Theorem 3.3: positivity on squares of degree at most `d` in the admissible slice interval. -/
theorem sliceFunctional_square_nonneg {n d : ℕ} (s : ℝ) (f : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d)
    (hs : (d : ℝ) - 1 ≤ s) (hns : (d : ℝ) - 1 ≤ (n : ℝ) - s) :
    0 ≤ sliceFunctional n s (f ^ 2) := by
  obtain ⟨h, _, he⟩ := boolean_harmonic_norm_formula f hn hd hf
  rw [he s]
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg
  · exact harmonic_weight_nonneg (by have := Finset.mem_range.mp hk; omega) hs hns
  · exact Finset.sum_nonneg (fun S _ ↦ sq_nonneg _)

end NoncommutativeAMGM
