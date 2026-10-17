/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The determinant kernel of diagonal substitution

A form `A(u,v)s + B(u,v)w` of bidegree `(e,1)` is represented on the affine chart
`u = 1` by the polynomial pair `(A(1,X), B(1,X))`. Diagonal substitution becomes
`(A,B) ↦ A + X * B`, and multiplication by `uw - vs` becomes
`p ↦ (-X * p, p)`.

The identities here hold over every commutative ring. They include the fixed
quotient/kernel coordinates and the monomial identities underlying the
simultaneous triangularization in Section 5.1 of *Matrix Multiplication via
Auxiliary Separation and Polynomial Multiplication*.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

open Polynomial

variable {R : Type*} [CommRing R]

/-- Affine representatives of forms linear in the second pair of variables. -/
abbrev FormPair (R : Type*) [CommRing R] := R[X] × R[X]

/-- Substitute the first variable pair into the second variable pair. -/
def diagonal : FormPair R →ₗ[R] R[X] where
  toFun p := p.1 + X * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; ring
  map_smul' c p := by simp [smul_eq_C_mul]; ring

/-- Multiplication by `D = uw - vs` after putting `u = 1`. -/
def determinant : R[X] →ₗ[R] FormPair R where
  toFun p := (-X * p, p)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem diagonal_apply (p : FormPair R) : diagonal p = p.1 + X * p.2 := rfl

@[simp] theorem determinant_apply (p : R[X]) : determinant p = (-X * p, p) := rfl

theorem diagonal_determinant (p : R[X]) : diagonal (determinant p) = 0 := by
  simp [diagonal, determinant]

/-- The determinant factor can be recovered from the second component. -/
theorem determinant_injective : Function.Injective (determinant (R := R)) := by
  intro p q h
  exact congrArg Prod.snd h

/-- Vanishing after diagonal substitution is exactly divisibility by `uw - vs`. -/
theorem diagonal_eq_zero_iff (p : FormPair R) :
    diagonal p = 0 ↔ p = determinant p.2 := by
  constructor
  · intro h
    apply Prod.ext
    · change p.1 = -X * p.2
      have h' : p.1 + X * p.2 = 0 := h
      linear_combination h'
    · rfl
  · intro h
    rw [h]
    exact diagonal_determinant _

/-- The kernel parametrization does not require any field or domain hypothesis. -/
theorem mem_kernel_iff (p : FormPair R) :
    p ∈ LinearMap.ker diagonal ↔ ∃ q, determinant q = p := by
  rw [LinearMap.mem_ker, diagonal_eq_zero_iff]
  constructor
  · intro h
    exact ⟨p.2, h.symm⟩
  · rintro ⟨q, rfl⟩
    rfl

theorem kernel_eq_range : LinearMap.ker (diagonal (R := R)) = LinearMap.range determinant := by
  ext p
  exact mem_kernel_iff p

/-- A fixed linear complement to the determinant kernel on unrestricted polynomials. -/
def split : (R[X] × R[X]) ≃ₗ[R] FormPair R where
  toFun p := (p.1 - X * p.2, p.2)
  invFun p := (p.1 + X * p.2, p.2)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  map_add' p q := by
    apply Prod.ext <;> simp
    ring
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem split_apply (p : R[X] × R[X]) : split p = (p.1 - X * p.2, p.2) := rfl

@[simp] theorem split_symm_apply (p : FormPair R) : split.symm p = (diagonal p, p.2) := rfl

theorem diagonal_split (p : R[X] × R[X]) : diagonal (split p) = p.1 := by
  simp [split, diagonal]

theorem split_zero_left (q : R[X]) : split (0, q) = determinant q := by
  simp [split, determinant]

theorem diagonal_surjective : Function.Surjective (diagonal (R := R)) := by
  intro p
  exact ⟨(p, 0), by simp⟩

/-- The kernel is canonically isomorphic to one polynomial copy. -/
def kernelEquiv : R[X] ≃ₗ[R] LinearMap.ker (diagonal (R := R)) where
  toFun p := ⟨determinant p, by simp⟩
  invFun p := p.1.2
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    exact ((diagonal_eq_zero_iff p.1).mp p.2).symm
  map_add' p q := by apply Subtype.ext; exact map_add determinant p q
  map_smul' c p := by apply Subtype.ext; exact map_smul determinant c p

/-- Multiply both coefficients by a first-input polynomial. -/
def multiply (f : R[X]) : FormPair R →ₗ[R] FormPair R where
  toFun p := (f * p.1, f * p.2)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by apply Prod.ext <;> simp [smul_eq_C_mul] <;> ring

@[simp] theorem multiply_apply (f : R[X]) (p : FormPair R) :
    multiply f p = (f * p.1, f * p.2) := rfl

/-- The quotient action is ordinary polynomial multiplication. -/
theorem diagonal_multiply (f : R[X]) (p : FormPair R) :
    diagonal (multiply f p) = f * diagonal p := by
  simp [diagonal, multiply]
  ring

/-- The kernel action is ordinary polynomial multiplication with the same first input. -/
theorem multiply_determinant (f p : R[X]) :
    multiply f (determinant p) = determinant (f * p) := by
  apply Prod.ext <;> simp [multiply, determinant]
  ring

/-- Every first-input slice preserves the determinant kernel. -/
theorem multiply_mem_kernel (f : R[X]) {p : FormPair R}
    (hp : p ∈ LinearMap.ker diagonal) : multiply f p ∈ LinearMap.ker diagonal := by
  rw [LinearMap.mem_ker, diagonal_multiply, LinearMap.mem_ker.mp hp, mul_zero]

/-- Quotient and kernel coordinates transform simultaneously, with an unchanged first input. -/
theorem split_multiply (f : R[X]) (p : R[X] × R[X]) :
    multiply f (split p) = split (f * p.1, f * p.2) := by
  apply Prod.ext <;> simp [multiply, split]
  ring

/-- The ordinary quotient monomial `u^(e-j) v^j s`, with `j ≤ e`. -/
def quotientMonomial (j : ℕ) : FormPair R := (X ^ j, 0)

/-- The last quotient monomial `v^e w`. -/
def quotientTop (e : ℕ) : FormPair R := (0, X ^ e)

/-- The kernel monomial `(uw-vs) u^(e-1-j) v^j`, with `j < e`. -/
def kernelMonomial (j : ℕ) : FormPair R := determinant (X ^ j)

theorem diagonal_quotientMonomial (j : ℕ) :
    diagonal (quotientMonomial (R := R) j) = X ^ j := by
  simp [diagonal, quotientMonomial]

theorem diagonal_quotientTop (e : ℕ) :
    diagonal (quotientTop (R := R) e) = X ^ (e + 1) := by
  simp [diagonal, quotientTop, pow_succ, mul_comm]

theorem diagonal_kernelMonomial (j : ℕ) :
    diagonal (kernelMonomial (R := R) j) = 0 := by
  simp [kernelMonomial]

theorem multiply_quotientMonomial (i j : ℕ) :
    multiply (X ^ i) (quotientMonomial (R := R) j) = quotientMonomial (i + j) := by
  apply Prod.ext <;> simp [multiply, quotientMonomial, pow_add]

theorem multiply_kernelMonomial (i j : ℕ) :
    multiply (X ^ i) (kernelMonomial (R := R) j) = kernelMonomial (i + j) := by
  rw [kernelMonomial, multiply_determinant, ← pow_add, kernelMonomial]

/-- The sole cross term in a nonfinal first-input slice has coefficient one. -/
theorem multiply_quotientTop_cross (i e : ℕ) :
    multiply (X ^ i) (quotientTop (R := R) e) =
      quotientMonomial (i + e + 1) + kernelMonomial (i + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, quotientMonomial, kernelMonomial, determinant,
    pow_add, pow_succ]
  ring

/-- For the final first-input monomial the last quotient vector remains the last vector. -/
theorem multiply_quotientTop_last (d e : ℕ) :
    multiply (X ^ d) (quotientTop (R := R) e) = quotientTop (d + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, pow_add]

/-- The actual quotient vectors used at degree `e`: there are `e + 2` of them. -/
def quotientVector (e : ℕ) (j : Fin (e + 2)) : FormPair R :=
  if (j : ℕ) < e + 1 then quotientMonomial j else quotientTop e

/-- The actual kernel vectors used at degree `e`: there are `e` of them. -/
def kernelVector (_e : ℕ) (j : Fin _e) : FormPair R := kernelMonomial j

theorem diagonal_quotientVector (e : ℕ) (j : Fin (e + 2)) :
    diagonal (quotientVector (R := R) e j) = X ^ (j : ℕ) := by
  unfold quotientVector
  split_ifs with h
  · exact diagonal_quotientMonomial j
  · have hj : (j : ℕ) = e + 1 := by omega
    simpa [hj] using diagonal_quotientTop (R := R) e

theorem diagonal_kernelVector (e : ℕ) (j : Fin e) :
    diagonal (kernelVector (R := R) e j) = 0 := by
  exact diagonal_kernelMonomial j

/-- Ordinary quotient columns have no kernel correction in the adapted output basis. -/
theorem multiply_quotientVector_ordinary (d e i j : ℕ)
    (hi : i ≤ d) (hj : j ≤ e) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨j, by omega⟩) =
      quotientVector (d + e) ⟨i + j, by omega⟩ := by
  simp only [quotientVector, show j < e + 1 by omega,
    show i + j < d + e + 1 by omega, ↓reduceIte]
  exact multiply_quotientMonomial i j

/-- Nonfinal slices have exactly the quotient-top cross term described in Section 5.1. -/
theorem multiply_quotientVector_top_cross (d e i : ℕ) (hi : i < d) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨e + 1 + i, by omega⟩ +
        kernelVector (d + e) ⟨e + i, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte,
    show e + 1 + i < d + e + 1 by omega, kernelVector]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    multiply_quotientTop_cross (R := R) i e

/-- The final slice has no cross term. -/
theorem multiply_quotientVector_top_last (d e : ℕ) :
    multiply (X ^ d) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨d + e + 1, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte]
  exact multiply_quotientTop_last d e

/-- All kernel columns have the convolution indices of the smaller branch. -/
theorem multiply_kernelVector (d e i j : ℕ) (hi : i ≤ d) (hj : j < e) :
    multiply (X ^ i) (kernelVector (R := R) e ⟨j, hj⟩) =
      kernelVector (d + e) ⟨i + j, by omega⟩ := by
  exact multiply_kernelMonomial i j


/-- Distinct bounded powers of `X` are independent even when the coefficient ring
has zero divisors. -/
theorem monomials_linearIndependent (n : ℕ) :
    LinearIndependent R (fun i : Fin n => (X : R[X]) ^ (i : ℕ)) := by
  have h := (Polynomial.degreeLT.basis R n).linearIndependent.map'
    (Polynomial.degreeLT R n).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  simpa only [Function.comp_def, Submodule.subtype_apply, Polynomial.degreeLT.basis_val] using h

/-- The quotient vectors followed by the kernel vectors are linearly independent.
This establishes nonsingularity of the simultaneous change of coordinates,
without any genericity assumption on the first input. -/
theorem adaptedVectors_linearIndependent (e : ℕ) :
    LinearIndependent R (Sum.elim (quotientVector (R := R) e) (kernelVector e)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : ∑ i : Fin (e + 2), c (Sum.inl i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg (diagonal (R := R)) hc
    simpa only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
      Sum.elim_inl, Sum.elim_inr, diagonal_quotientVector, diagonal_kernelVector,
      smul_zero, Finset.sum_const_zero, add_zero, map_zero] using h
  have cq : ∀ i : Fin (e + 2), c (Sum.inl i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) (e + 2))) _ hq
  have hk : ∑ i : Fin e, c (Sum.inr i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg Prod.snd hc
    simpa only [Fintype.sum_sum_type, Prod.snd_add, Prod.snd_sum, Prod.snd_smul,
      Sum.elim_inl, Sum.elim_inr, cq, zero_smul, Finset.sum_const_zero, zero_add,
      kernelVector, kernelMonomial, determinant_apply, Prod.snd_zero, Prod.smul_mk] using h
  have ck : ∀ i : Fin e, c (Sum.inr i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) e)) _ hk
  exact Sum.rec cq ck

end MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

end

end MatrixMultiplicationAllFields
