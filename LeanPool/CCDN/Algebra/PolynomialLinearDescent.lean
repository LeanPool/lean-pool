/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Coefficientwise application of a linear map to multivariate polynomials, and
linear coefficient descent of a polynomial over a field extension: a nonzero
polynomial vanishing at base-field points has a nonzero base-field polynomial of no
larger degree vanishing at every one of those points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- Apply a linear coefficient map without changing any monomial. -/
def polynomialCoefficientLinear {R A B σ : Type*} [CommSemiring R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) : MvPolynomial σ A →ₗ[R] MvPolynomial σ B :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- Each coefficient of `polynomialCoefficientLinear φ f` is the image under `φ` of the
corresponding coefficient of `f`. -/
@[simp] lemma polynomialCoefficientLinear_coeff {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (f : MvPolynomial σ A) (e : σ →₀ ℕ) :
    (polynomialCoefficientLinear φ f).coeff e = φ (f.coeff e) := rfl

/-- Applying the linear map `φ` coefficientwise sends the constant `C a` to `C (φ a)`. -/
@[simp] lemma polynomialCoefficientLinear_C {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (a : A) :
    polynomialCoefficientLinear (σ := σ) φ (C a) = C (φ a) := by
  classical
  ext e
  simp only [polynomialCoefficientLinear_coeff, coeff_C]
  split_ifs <;> simp

/-- If `φ (a * θ b) = φ a * b` for a ring map `θ : B →+* A`, then applying `φ` coefficientwise
is linear over polynomials with coefficients in `B`: it sends `f * map θ g` to
`polynomialCoefficientLinear φ f * g`. -/
lemma polynomialCoefficientLinear_mul_compatible {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (θ : B →+* A)
    (hφ : ∀ a b, φ (a * θ b) = φ a * b)
    (f : MvPolynomial σ A) (g : MvPolynomial σ B) :
    polynomialCoefficientLinear φ (f * map θ g) =
      polynomialCoefficientLinear φ f * g := by
  classical
  ext e
  rw [polynomialCoefficientLinear_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_map, polynomialCoefficientLinear_coeff, hφ]

/-- For a field extension `L / K` and a `K`-linear functional `φ : L → K`, applying `φ`
coefficientwise is linear over polynomials with coefficients in `K`: it sends
`f * map (algebraMap K L) g` to `polynomialCoefficientLinear φ f * g`. -/
lemma polynomialCoefficientLinear_mul_map {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (φ : L →ₗ[K] K) (f : MvPolynomial σ L) (g : MvPolynomial σ K) :
    polynomialCoefficientLinear φ (f * map (algebraMap K L) g) =
      polynomialCoefficientLinear φ f * g := by
  apply polynomialCoefficientLinear_mul_compatible
  intro a b
  simpa only [Algebra.smul_def, smul_eq_mul, mul_comm, Algebra.algebraMap_self,
    RingHom.id_apply] using φ.map_smul b a

/-- Coefficient functionals send elements of an extended ideal into the
original ideal, for any variable type. -/
theorem polynomialCoefficientLinear_mem_scalar_extension {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ L)
    (hg : g ∈ I.map (map (algebraMap K L))) (φ : L →ₗ[K] K) :
    polynomialCoefficientLinear φ g ∈ I := by
  have hh : ∀ (ψ : L →ₗ[K] K) (r : MvPolynomial σ L),
      polynomialCoefficientLinear ψ (r * g) ∈ I := by
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      intro ψ r
      rw [polynomialCoefficientLinear_mul_map]
      exact I.mul_mem_left _ hf
    | zero =>
      intro ψ r
      rw [mul_zero, map_zero]
      exact I.zero_mem
    | add x y _ _ hx hy =>
      intro ψ r
      rw [mul_add, map_add]
      exact I.add_mem (hx ψ r) (hy ψ r)
    | smul a x _ hx =>
      intro ψ r
      simpa only [smul_eq_mul, mul_assoc] using hx ψ (r * a)
  simpa only [one_mul] using hh φ 1

/-- Applying a linear map coefficientwise does not increase the total degree. -/
lemma polynomialCoefficientLinear_totalDegree_le {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (f : MvPolynomial σ A) :
    (polynomialCoefficientLinear φ f).totalDegree ≤ f.totalDegree := by
  classical
  apply Finset.sup_le
  intro m hm
  apply le_totalDegree
  rw [mem_support_iff, polynomialCoefficientLinear_coeff] at hm
  rw [mem_support_iff]
  intro hz
  exact hm (by rw [hz, map_zero])

/-- For a field extension `K / k` and a `k`-linear functional `φ : K → k`, evaluating the
coefficientwise image of `f` under `φ` at a `k`-point `x` gives `φ` of the value of `f` at `x`. -/
lemma polynomialCoefficientLinear_eval {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (φ : K →ₗ[k] k) (f : MvPolynomial σ K) (x : σ → k) :
    eval x (polynomialCoefficientLinear φ f) = φ (eval (algebraMap k K ∘ x) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    have hX : (X j : MvPolynomial σ K) = map (algebraMap k K) (X j) := by simp
    rw [hX, polynomialCoefficientLinear_mul_map, map_X]
    simp only [map_mul, eval_X, hf, Function.comp_apply]
    rw [mul_comm _ (algebraMap k K (x j)), ← Algebra.smul_def, φ.map_smul, smul_eq_mul, mul_comm]

/-- Linear coefficient descent: for a field extension `K / k`, a nonzero polynomial `f` over `K`
has a nonzero polynomial over `k` of total degree at most that of `f` vanishing at every
`k`-point where `f` vanishes. -/
theorem exists_nonzero_polynomial_linear_descent {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    ∃ g : MvPolynomial (Fin n) k, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      ∀ x : Fin n → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  refine ⟨polynomialCoefficientLinear φ f, ?_,
    polynomialCoefficientLinear_totalDegree_le φ f, ?_⟩
  · intro he
    have hh := polynomialCoefficientLinear_coeff φ f m
    have hz : φ (f.coeff m) = 0 := by simpa [he] using hh.symm
    exact hφ hz
  · intro x hx
    rw [polynomialCoefficientLinear_eval, hx, map_zero]

end
end CCDN
