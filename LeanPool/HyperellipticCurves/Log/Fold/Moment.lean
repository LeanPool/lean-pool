/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspFold
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The moment system and its Cramer data

The master congruence of the cuspidal fold (`ChabautyColeman.cuspMoment_congruence`) pins the
reduced supports `A_j` down by linear equations: writing `q := d_j(-z)` for the node
polynomial, the congruence says that `A_j·q` has vanishing odd coefficients `z^1, …, z^(2g-1)`
(`ChabautyColeman.coeff_mul_comp_neg_X_eq_zero` — the even coefficients cancel identically,
the odd ones appear doubled, so characteristic `≠ 2` extracts them). These `g` equations in the
`g` unknown lower coefficients of the monic `A_j` form the **moment system**
(`ChabautyColeman.momentMatrix`, `ChabautyColeman.momentRhs`), and Cramer's rule — in the
integral direction that needs no invertibility (`ChabautyColeman.det_smul_eq_cramer_of_mulVec`)
— gives the uniqueness clause `ChabautyColeman.eq_of_det_momentMatrix_ne_zero` (consumed
at the mirror endpoint). This realizes parts (2) and (3) of the blueprint's
`thm:cusp-moment` in the invertibility-free form the chain induction spends; the
nonvanishing certificates for the atoms are the subject of the certificate cluster.

## Main statements

* `ChabautyColeman.coeff_mul_comp_neg_X_eq_zero`: the odd coefficients of `p(z)·q(-z)` below
  `n` vanish when `z^n ∣ p(z)·q(-z) - p(-z)·q(z)` and `2 ≠ 0` (`thm:cusp-moment` (2)).
* `ChabautyColeman.momentMatrix_mulVec`: the coefficient vector of `A` solves the moment
  system.
* `ChabautyColeman.det_smul_eq_cramer_of_mulVec`: the invertibility-free Cramer direction
  feeding uniqueness (`ChabautyColeman.eq_of_det_momentMatrix_ne_zero`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Coefficients of `p(-X)`, and the moment system -/

section CoeffCompNegX

variable {R : Type*} [CommRing R]

/-- The coefficients of `p(-X)`: the sign alternates. -/
theorem coeff_comp_neg_X (p : R[X]) (n : ℕ) : (p.comp (-X)).coeff n = (-1) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, hp, hq, coeff_add, mul_add]
  | monomial k a =>
    rw [monomial_comp, neg_pow (X : R[X]) k,
      show ((-1 : R[X]) ^ k) = C ((-1) ^ k) by rw [map_pow, map_neg, map_one],
      mul_left_comm, coeff_C_mul, C_mul_X_pow_eq_monomial]
    rcases eq_or_ne k n with rfl | hkn
    · rfl
    · simp [coeff_monomial, hkn]

/-- **The moment system, generic form**: if `z^n` divides the symmetrized product
`p(z)·q(-z) - p(-z)·q(z)` and `2 ≠ 0`, then the odd coefficients of `p(z)·q(-z)` below `n`
all vanish (`thm:cusp-moment` (2): the even ones cancel identically, the odd ones doubly). -/
theorem coeff_mul_comp_neg_X_eq_zero [NoZeroDivisors R] {p q : R[X]} (h2 : (2 : R) ≠ 0)
    {n : ℕ} (hdvd : X ^ n ∣ p * q.comp (-X) - p.comp (-X) * q)
    {k : ℕ} (hk : Odd k) (hkn : k < n) :
    (p * q.comp (-X)).coeff k = 0 := by
  have h0 := X_pow_dvd_iff.mp hdvd k hkn
  have h1 : p.comp (-X) * q = (p * q.comp (-X)).comp (-X) := by rw [mul_comp, comp_neg_X_comp_neg_X]
  rw [coeff_sub, h1, coeff_comp_neg_X, hk.neg_one_pow, sub_eq_zero] at h0
  have h3 : (2 : R) * (p * q.comp (-X)).coeff k = 0 := by linear_combination h0
  exact (mul_eq_zero.mp h3).resolve_left h2

end CoeffCompNegX

/-! ### The moment matrix and its Cramer data -/

section MomentMatrix

variable {R : Type*} [CommRing R] {g : ℕ} {A q : R[X]}

/-- **The moment matrix** of a node polynomial value `q = d(-z)`: row `i` extracts the odd
coefficient `z^(2i+1)`, column `m` is shifted by `X^m` — so `M·(coeffs of A) = coeff of A·q`
row by row. Its entries are the elementary symmetric values `e_(G-(2i+1)+m)` of the node
multiset (`thm:cusp-moment` (3)). -/
noncomputable def momentMatrix (g : ℕ) (q : R[X]) : Matrix (Fin g) (Fin g) R :=
  Matrix.of fun i m ↦ (q * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)

/-- The right-hand side of the moment system: the negated monic column `m = g`. -/
noncomputable def momentRhs (g : ℕ) (q : R[X]) : Fin g → R :=
  fun i ↦ -((q * X ^ g).coeff (2 * (i : ℕ) + 1))

theorem momentMatrix_apply (i m : Fin g) :
    momentMatrix g q i m = (q * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1) := rfl

theorem momentRhs_apply (i : Fin g) :
    momentRhs g q i = -((q * X ^ g).coeff (2 * (i : ℕ) + 1)) := rfl

/-- A product coefficient, split along the coefficients of a bounded-degree left factor. -/
theorem coeff_mul_eq_sum_coeff_mul_X_pow (hA : A.natDegree ≤ g) (k : ℕ) :
    (A * q).coeff k = ∑ m ∈ Finset.range (g + 1), A.coeff m * (q * X ^ m).coeff k := by
  conv_lhs => rw [A.as_sum_range' (g + 1) (by lia), Finset.sum_mul]
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, mul_comm (X ^ m) q, coeff_C_mul]

/-- **The fold state solves the moment system**: a monic `A` of degree `g` whose product
with `q` has vanishing odd coefficients `z^1, …, z^(2g-1)` gives a solution vector of the
moment linear system. -/
theorem momentMatrix_mulVec (hA : A.Monic) (hAdeg : A.natDegree = g)
    (hsys : ∀ i : Fin g, (A * q).coeff (2 * (i : ℕ) + 1) = 0) :
    (momentMatrix g q).mulVec (fun m ↦ A.coeff (m : ℕ)) = momentRhs g q := by
  funext i
  have hcg : A.coeff g = 1 := hAdeg ▸ hA.coeff_natDegree
  have h1 := coeff_mul_eq_sum_coeff_mul_X_pow (q := q) hAdeg.le (2 * (i : ℕ) + 1)
  rw [hsys i, Finset.sum_range_succ, hcg, one_mul] at h1
  have h2 : ∑ m : Fin g, A.coeff (m : ℕ) * (q * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)
      = ∑ m ∈ Finset.range g, A.coeff m * (q * X ^ m).coeff (2 * (i : ℕ) + 1) :=
    Fin.sum_univ_eq_sum_range (fun m ↦ A.coeff m * (q * X ^ m).coeff (2 * (i : ℕ) + 1)) g
  calc (momentMatrix g q).mulVec (fun m ↦ A.coeff (m : ℕ)) i
      = ∑ m : Fin g, (q * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1) * A.coeff (m : ℕ) := rfl
    _ = ∑ m ∈ Finset.range g, A.coeff m * (q * X ^ m).coeff (2 * (i : ℕ) + 1) := by
        rw [← h2]
        exact Finset.sum_congr rfl fun m _ ↦ mul_comm _ _
    _ = momentRhs g q i := by
        rw [momentRhs_apply]
        linear_combination -h1

/-- **Cramer's identity for a solution vector** (no invertibility needed): a solution of
`M·x = b` satisfies `det M • x = cramer M b`. -/
theorem det_smul_eq_cramer_of_mulVec {n : Type*} [DecidableEq n] [Fintype n]
    {M : Matrix n n R} {x b : n → R} (h : M.mulVec x = b) :
    M.det • x = M.cramer b := by
  calc M.det • x = (M.det • (1 : Matrix n n R)).mulVec x := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = M.adjugate.mulVec (M.mulVec x) := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    _ = M.cramer b := by rw [h, Matrix.cramer_eq_adjugate_mulVec]

end MomentMatrix

end ChabautyColeman

end
