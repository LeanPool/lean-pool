/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.AuxiliaryPolynomial.DegreeBound
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import LeanPool.CCDN.ForMathlib.MvPolynomial

/-! Bad-prime factors of integer polynomials, and the geometric bad-prime factor used by the
determinant method. A bad-prime factor `badPrimeFactor P` is zero for nonabsolute equations
and the exact finite exponential product over the primes above `stepanovThreshold` satisfying
the bad-reduction predicate `P` otherwise. For nonzero homogeneous equations the geometric
factor agrees with CCDN Definition 3.2.1. For affine equations its bad-prime predicate also
includes degree loss; this stronger convention is not identical to the literal printed
definition. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An absolutely irreducible integral polynomial has positive total degree. -/
lemma absolute_integer_polynomial_totalDegree_pos {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) :
    0 < f.totalDegree := by
  rw [← totalDegree_map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)).injective_int f]
  exact totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/-- The bad-prime factor of an integer polynomial `f` relative to a bad-reduction predicate
`P`: the product `primeSetFactor` of the primes `p > stepanovThreshold (deg f)` with `P f p`
when `f` is absolutely irreducible over `ℚ`, and `0` otherwise. The hypothesis `hP` gives the
finiteness of these primes for absolutely irreducible `f`. -/
def badPrimeFactor {σ : Type*} (P : MvPolynomial σ ℤ → ℕ → Prop)
    (hP : ∀ f : MvPolynomial σ ℤ, AbsolutelyIrreducible f →
      {p : ℕ | stepanovThreshold f.totalDegree < p ∧ P f p}.Finite)
    (f : MvPolynomial σ ℤ) : ℝ := by
  classical
  exact if h : AbsolutelyIrreducible f then
    primeSetFactor (hP f h).toFinset
  else 0

section BadPrimeFactor

variable {σ : Type*} {P Q : MvPolynomial σ ℤ → ℕ → Prop}
  {hP : ∀ f : MvPolynomial σ ℤ, AbsolutelyIrreducible f →
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ P f p}.Finite}
  {hQ : ∀ f : MvPolynomial σ ℤ, AbsolutelyIrreducible f →
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ Q f p}.Finite}

/-- The bad-prime factor `badPrimeFactor P hP f` is nonnegative. -/
lemma badPrimeFactor_nonneg (f : MvPolynomial σ ℤ) : 0 ≤ badPrimeFactor P hP f := by
  unfold badPrimeFactor
  split <;> positivity

/-- The bad-prime factor of an integral polynomial that is not absolutely irreducible is
zero. -/
lemma badPrimeFactor_eq_zero {f : MvPolynomial σ ℤ}
    (hf : ¬ AbsolutelyIrreducible f) :
    badPrimeFactor P hP f = 0 := by
  simp only [badPrimeFactor, dite_eq_right hf]

/-- For an absolutely irreducible equation of degree `d`, the bad-prime factor is the
`primeSetFactor` of any finite set listing exactly the bad primes above `27 d⁴`. -/
lemma badPrimeFactor_eq_primeSetFactor {d : ℕ} {f : MvPolynomial σ ℤ}
    (hf : AbsolutelyIrreducible f)
    (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ P f p) :
    badPrimeFactor P hP f = primeSetFactor bad := by
  classical
  unfold badPrimeFactor
  rw [dite_eq_left hf]
  congr 1
  ext p
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdegree, hbad]

/-- If the bad-reduction predicate `P` implies `Q` at `f`, then the bad-prime factor of `f`
for `P` is at most that for `Q`. -/
lemma badPrimeFactor_mono (f : MvPolynomial σ ℤ) (hPQ : ∀ p, P f p → Q f p) :
    badPrimeFactor P hP f ≤ badPrimeFactor Q hQ f := by
  classical
  by_cases hf : AbsolutelyIrreducible f
  · unfold badPrimeFactor
    rw [dite_eq_left hf, dite_eq_left hf]
    apply Real.exp_le_exp.mpr
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨hp.1, hPQ p hp.2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  · rw [badPrimeFactor_eq_zero hf, badPrimeFactor_eq_zero hf]

end BadPrimeFactor

/-- The geometric bad-prime factor: `badPrimeFactor` for `HypersurfaceBadReduction`, which
counts both failure of absolute irreducibility and degree loss modulo `p`. -/
def hypersurfaceBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ :=
  badPrimeFactor HypersurfaceBadReduction
    (fun f h => finite_fin_hypersurface_bad_primes f h
      (absolute_integer_polynomial_totalDegree_pos f h)) f

/-- The geometric bad-prime factor `hypersurfaceBadPrimeFactor f` is nonnegative. -/
lemma hypersurfaceBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ hypersurfaceBadPrimeFactor f :=
  badPrimeFactor_nonneg f

/-- The geometric bad-prime factor of an integral polynomial that is not absolutely
irreducible is zero. -/
lemma hypersurfaceBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬ AbsolutelyIrreducible f) :
    hypersurfaceBadPrimeFactor f = 0 :=
  badPrimeFactor_eq_zero hf

/-- For an absolutely irreducible integral polynomial of degree `d`, the geometric bad-prime
factor is the `primeSetFactor` of any finite set listing exactly the primes above
`stepanovThreshold d` at which `f` has geometric bad reduction. -/
lemma hypersurfaceBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f)
    (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    hypersurfaceBadPrimeFactor f = primeSetFactor bad :=
  badPrimeFactor_eq_primeSetFactor hf hdegree bad hbad

/-- The bad-prime factor satisfies the coefficient-height bound also
for nonabsolute equations, where the factor is zero by definition. -/
theorem hypersurfaceBadPrimeFactor_le_height {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    hypersurfaceBadPrimeFactor f ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  have hc : 0 < hypersurfaceHeightConstant (n + 1) :=
    zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
  by_cases hf : AbsolutelyIrreducible f
  · obtain ⟨bad, hbad, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge f hf
      (absolute_integer_polynomial_totalDegree_pos f hf) H hH hcoeff
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    calc
      _ ≤ Real.exp (Real.log (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1) :=
        Real.exp_le_exp.mpr hcharge
      _ = _ := by
        rw [show Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 =
          Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + (2 * mertensError + 1) by ring,
          Real.exp_add, Real.exp_log (by positivity)]
        ring
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    positivity

/-- The max-form of CCDN Corollary 3.2.3 for the defined factor itself. -/
theorem hypersurfaceBadPrimeFactor_le_max {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    hypersurfaceBadPrimeFactor f ≤
      (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
  have hh := hypersurfaceBadPrimeFactor_le_height f H hH hcoeff
  have h1 := le_max_left (Real.log H / (f.totalDegree : ℝ) ^ 2) (1 : ℝ)
  have h2 := le_max_right (Real.log H / (f.totalDegree : ℝ) ^ 2) (1 : ℝ)
  have hc : 0 ≤ Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1) :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2 h1) hc]

end
end CCDN
