/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Degree bounds for the binary determinant relation

The polynomial identity `A + X * B = 0` forces one extra degree of cancellation:
if `A` has degree less than `e + 1`, then `B` has degree less than `e`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantBounds

open Polynomial

variable {R : Type*} [CommRing R]

/-- A degree bound on the first component of a diagonal relation bounds the
second component by one degree less. -/
theorem degree_lt_of_diagonal_eq_zero {e : ℕ} {A B : R[X]}
    (hA : A.degree < (e + 1 : ℕ)) (h : A + X * B = 0) :
    B.degree < e := by
  rw [degree_lt_iff_coeff_zero] at hA ⊢
  intro n hn
  have hc := congrArg (fun p : R[X] => p.coeff (n + 1)) h
  simpa only [coeff_add, coeff_X_mul, hA (n + 1) (by omega),
    zero_add, coeff_zero] using hc

/-- Multiplication by `-X` increases the strict degree bound by at most one. -/
theorem degree_neg_X_mul_lt {e : ℕ} {q : R[X]} (hq : q.degree < e) :
    (-(X * q) : R[X]).degree < (e + 1 : ℕ) := by
  rw [degree_lt_iff_coeff_zero] at hq ⊢
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [coeff_neg, Nat.succ_eq_add_one, coeff_X_mul]
  exact neg_eq_zero.mpr (hq k (by omega))

/-- The determinant generator preserves the two component degree bounds. -/
theorem determinant_degree_bounds {e : ℕ} {q : R[X]} (hq : q.degree < e) :
    (-(X * q) : R[X]).degree < (e + 1 : ℕ) ∧ q.degree < (e + 1 : ℕ) := by
  refine ⟨degree_neg_X_mul_lt hq, hq.trans_le ?_⟩
  exact_mod_cast Nat.le_succ e

/-- Pairs representing forms of bidegree `(e, 1)`. -/
abbrev BoundedPair (R : Type*) [CommRing R] (e : ℕ) :=
  degreeLT R (e + 1) × degreeLT R (e + 1)

/-- Diagonal substitution on the space with the prescribed degree bounds. -/
def diagonal (e : ℕ) : BoundedPair R e →ₗ[R] R[X] where
  toFun p := (p.1 : R[X]) + X * (p.2 : R[X])
  map_add' p q := by simp [mul_add]; ring
  map_smul' c p := by simp [smul_eq_C_mul]; ring

/-- The first component of multiplication by `uw-vs`. -/
def negativeShift (e : ℕ) : degreeLT R e →ₗ[R] degreeLT R (e + 1) :=
  ((LinearMap.mulLeft R (-X : R[X])).domRestrict (degreeLT R e)).codRestrict
    (degreeLT R (e + 1)) (fun q => mem_degreeLT.mpr <| by
      simpa only [LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, neg_mul] using
        degree_neg_X_mul_lt (mem_degreeLT.mp q.2))

/-- Increase the allowed degree bound by one. -/
def widen (e : ℕ) : degreeLT R e →ₗ[R] degreeLT R (e + 1) :=
  Submodule.inclusion (degreeLT_mono (Nat.le_succ e))

@[simp] theorem widen_coe (e : ℕ) (q : degreeLT R e) :
    (widen e q : R[X]) = (q : R[X]) :=
  Submodule.coe_inclusion _ q

/-- Multiplication by `uw-vs` lands in the bounded pair space. -/
def determinant (e : ℕ) : degreeLT R e →ₗ[R] BoundedPair R e where
  toFun q := (negativeShift e q, widen e q)
  map_add' p q := Prod.ext (map_add (negativeShift e) p q) (map_add (widen e) p q)
  map_smul' c p := Prod.ext (map_smul (negativeShift e) c p) (map_smul (widen e) c p)

@[simp] theorem diagonal_apply (e : ℕ) (p : BoundedPair R e) :
    diagonal e p = (p.1 : R[X]) + X * (p.2 : R[X]) := rfl

@[simp] theorem determinant_fst (e : ℕ) (q : degreeLT R e) :
    ((determinant e q).1 : R[X]) = -X * (q : R[X]) := rfl

@[simp] theorem determinant_snd (e : ℕ) (q : degreeLT R e) :
    ((determinant (R := R) e q).2 : R[X]) = (q : R[X]) := by
  change (widen e q : R[X]) = (q : R[X])
  exact widen_coe e q

theorem diagonal_determinant (e : ℕ) (q : degreeLT R e) :
    diagonal e (determinant e q) = 0 := by
  simp only [diagonal_apply, determinant_fst, determinant_snd, neg_mul, neg_add_cancel]

/-- The determinant map with codomain restricted to the diagonal kernel. -/
def toKernel (e : ℕ) : degreeLT R e →ₗ[R] LinearMap.ker (diagonal (R := R) e) :=
  (determinant (R := R) e).codRestrict _ fun q => diagonal_determinant e q

@[simp] theorem toKernel_coe (e : ℕ) (q : degreeLT R e) :
    (toKernel e q : BoundedPair R e) = determinant e q := rfl

theorem toKernel_bijective (e : ℕ) : Function.Bijective (toKernel (R := R) e) := by
  constructor
  · intro p q h
    apply Subtype.ext
    have hc := congrArg (fun z : LinearMap.ker (diagonal (R := R) e) =>
      (z.1.2 : R[X])) h
    simpa only [toKernel_coe, determinant_snd] using hc
  · rintro ⟨p, hp⟩
    let q : degreeLT R e := ⟨(p.2 : R[X]), mem_degreeLT.mpr <|
      degree_lt_of_diagonal_eq_zero (mem_degreeLT.mp p.1.2) hp⟩
    refine ⟨q, Subtype.ext ?_⟩
    change determinant (R := R) e q = p
    apply Prod.ext
    · apply Subtype.ext
      rw [determinant_fst]
      have h : (p.1 : R[X]) + X * (p.2 : R[X]) = 0 := hp
      simpa only [q, neg_mul] using (eq_neg_of_add_eq_zero_left h).symm
    · apply Subtype.ext
      exact determinant_snd e q

/-- The bounded determinant kernel has exactly the degree-`< e` polynomials
as its parameters, including at `e = 0`. -/
def kernelEquiv (e : ℕ) : degreeLT R e ≃ₗ[R] LinearMap.ker (diagonal (R := R) e) :=
  LinearEquiv.ofBijective (toKernel e) (toKernel_bijective e)

/-- The finite determinant kernel has dimension `e`. -/
theorem finrank_kernel (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (LinearMap.ker (diagonal (R := K) e)) = e := by
  rw [← (kernelEquiv (R := K) e).finrank_eq]
  simpa using Module.finrank_eq_card_basis (degreeLT.basis K e)

/-- The diagonal has the next larger degree bound. -/
theorem degree_diagonal_lt (e : ℕ) (p : BoundedPair R e) :
    (diagonal e p).degree < (e + 2 : ℕ) := by
  change ((p.1 : R[X]) + X * (p.2 : R[X])).degree < ((e + 2 : ℕ) : WithBot ℕ)
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · refine (mem_degreeLT.mp p.1.2).trans_le ?_
    exact_mod_cast (show e + 1 ≤ e + 2 by omega)
  · simpa only [degree_neg, Nat.add_assoc] using
      degree_neg_X_mul_lt (mem_degreeLT.mp p.2.2)

/-- Diagonal substitution with both the domain and codomain degree bounded. -/
def diagonalToDegreeLT (e : ℕ) : BoundedPair R e →ₗ[R] degreeLT R (e + 2) :=
  (diagonal e).codRestrict _ fun p => mem_degreeLT.mpr (degree_diagonal_lt e p)

@[simp] theorem diagonalToDegreeLT_coe (e : ℕ) (p : BoundedPair R e) :
    (diagonalToDegreeLT e p : R[X]) = diagonal e p := rfl

/-- Removing the constant coefficient lowers the strict degree bound by one. -/
theorem degree_divX_lt {e : ℕ} {p : R[X]} (hp : p.degree < (e + 1 : ℕ)) :
    p.divX.degree < e := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro n hn
  rw [coeff_divX]
  exact hp (n + 1) (by omega)

/-- Every polynomial of the output degree is a diagonal restriction of a
bounded pair. -/
theorem diagonalToDegreeLT_surjective (e : ℕ) :
    Function.Surjective (diagonalToDegreeLT (R := R) e) := by
  intro p
  let A : degreeLT R (e + 1) := ⟨C ((p : R[X]).coeff 0), mem_degreeLT.mpr <|
    degree_C_lt.trans_le (by exact_mod_cast (show 1 ≤ e + 1 by omega))⟩
  let B : degreeLT R (e + 1) := ⟨(p : R[X]).divX, mem_degreeLT.mpr <|
    degree_divX_lt (by simpa only [Nat.add_assoc] using mem_degreeLT.mp p.2)⟩
  refine ⟨(A, B), ?_⟩
  apply Subtype.ext
  change C ((p : R[X]).coeff 0) + X * (p : R[X]).divX = (p : R[X])
  simpa only [add_comm] using X_mul_divX_add (p : R[X])

@[simp] theorem ker_diagonalToDegreeLT (e : ℕ) :
    LinearMap.ker (diagonalToDegreeLT (R := R) e) = LinearMap.ker (diagonal e) := by
  ext p
  simp only [LinearMap.mem_ker]
  exact Subtype.val_inj.symm

end MatrixMultiplication.AuxiliarySeparation.DeterminantBounds

end

end MatrixMultiplicationAllFields
