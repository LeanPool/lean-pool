/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.HarmonicRaising

/-! # The falling-factorial harmonic expansion from Appendix C -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

/-- The Boolean polynomial `(Z-k)ₜ`. -/
noncomputable def booleanFalling (n k t : ℕ) : BooleanPolynomial n :=
  ∏ i ∈ Finset.range t, (totalVariable n - ((k + i : ℕ) : ℝ) • 1)

@[simp] theorem booleanFalling_zero (n k : ℕ) : booleanFalling n k 0 = 1 := by
  simp [booleanFalling]

theorem booleanFalling_succ (n k t : ℕ) :
    booleanFalling n k (t + 1) =
      (totalVariable n - ((k + t : ℕ) : ℝ) • 1) * booleanFalling n k t := by
  rw [booleanFalling, Finset.prod_range_succ, mul_comm]
  rfl

theorem booleanFalling_raise (n k r : ℕ) (hk : k ≤ r) :
    (totalVariable n - (r : ℝ) • 1) * booleanFalling n k (r - k) =
      booleanFalling n k (r + 1 - k) := by
  rw [show r + 1 - k = (r - k) + 1 by omega, booleanFalling_succ,
    Nat.add_sub_of_le hk]

/-- Every homogeneous polynomial is a sum of harmonic pieces raised by falling
factorials in `Z`. The pieces are fixed coefficient vectors, independent of the slice parameter. -/
theorem homogeneous_harmonic_expansion {n : ℕ} (r : ℕ) (c : HomogeneousSpace n r) :
    ∃ h : (k : ℕ) → HomogeneousSpace n k,
      (∀ k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h k))) ∧
      homogeneousPolynomial c = ∑ k ∈ Finset.range (r + 1),
        booleanFalling n k (r - k) * homogeneousPolynomial (h k) := by
  classical
  induction r with
  | zero =>
    let h : (k : ℕ) → HomogeneousSpace n k := Function.update (fun _ ↦ 0) 0 c
    refine ⟨h, ?_, ?_⟩
    · intro k hk S hS
      omega
    · simp [h]
  | succ r ih =>
    obtain ⟨v, q, hv, hc⟩ := homogeneous_harmonic_decomposition c
    obtain ⟨h, hh, hq⟩ := ih q
    let h' : (k : ℕ) → HomogeneousSpace n k := Function.update h (r + 1) v
    refine ⟨h', ?_, ?_⟩
    · intro k hk
      by_cases he : k = r + 1
      · subst k
        simpa [h'] using (homogeneousDown_eq_zero_iff v).mp hv
      · have hkr : k ≤ r := by omega
        simpa [h', he] using hh k hkr
    · have hlow : (∑ k ∈ Finset.range (r + 1),
          booleanFalling n k (r + 1 - k) * homogeneousPolynomial (h' k)) =
          (totalVariable n - (r : ℝ) • 1) * homogeneousPolynomial q := by
        rw [hq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkr : k ≤ r := by have := Finset.mem_range.mp hk; omega
        have he : k ≠ r + 1 := by omega
        simp only [h', Function.update_of_ne he]
        rw [← booleanFalling_raise n k r hkr]
        ring
      rw [Finset.sum_range_succ, hlow]
      simp only [h', Function.update_self, Nat.sub_self, booleanFalling_zero, one_mul]
      rw [hc, homogeneousPolynomial_add, homogeneousPolynomial_up]
      exact add_comm _ _

/-- The coefficient vector of a single homogeneous layer of a Boolean polynomial. -/
noncomputable def homogeneousComponent {n : ℕ} (f : BooleanPolynomial n) (r : ℕ) :
    HomogeneousSpace n r := WithLp.toLp 2 (fun S ↦ f.coeff (BooleanMonomial.ofFinset S.val))

theorem homogeneousComponent_coefficient {n : ℕ} (f : BooleanPolynomial n) (r : ℕ)
    (T : BooleanMonomial n) :
    homogeneousCoefficient (homogeneousComponent f r) T.toFinset =
      if T.toFinset.card = r then f.coeff T else 0 := by
  classical
  unfold homogeneousCoefficient
  split_ifs <;> rfl

theorem booleanPolynomial_eq_sum_homogeneous {n d : ℕ} (f : BooleanPolynomial n)
    (hf : BooleanDegreeLE f d) :
    f = ∑ r ∈ Finset.range (d + 1), homogeneousPolynomial (homogeneousComponent f r) := by
  classical
  apply MonoidAlgebra.ext
  ext T
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    homogeneousPolynomial_coeff, homogeneousComponent_coefficient]
  rw [Finset.sum_ite_eq]
  by_cases hT : T.toFinset.card ≤ d
  · simp [Finset.mem_range, hT]
  · have hz : f.coeff T = 0 := by
      by_contra hne
      exact hT (hf T hne)
    simp [hz]

/-- The complete falling-factorial harmonic expansion of an arbitrary Boolean polynomial.
Every harmonic coefficient vector here is independent of `s`. -/
theorem boolean_harmonic_expansion {n d : ℕ} (f : BooleanPolynomial n)
    (hf : BooleanDegreeLE f d) :
    ∃ h : (r k : ℕ) → HomogeneousSpace n k,
      (∀ r k, k ≤ r → HarmonicCoefficients k (homogeneousCoefficient (h r k))) ∧
      f = ∑ r ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (r + 1),
        booleanFalling n k (r - k) * homogeneousPolynomial (h r k) := by
  classical
  choose h hhar hpoly using fun r ↦
    homogeneous_harmonic_expansion r (homogeneousComponent f r)
  refine ⟨h, hhar, ?_⟩
  rw [booleanPolynomial_eq_sum_homogeneous f hf]
  apply Finset.sum_congr rfl
  intro r _
  exact hpoly r

end NoncommutativeAMGM
