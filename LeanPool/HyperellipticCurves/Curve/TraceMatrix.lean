/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.TraceDiff
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The trace matrix is invertible

The Hankel matrix `C_ij = -λ_u(X^(i+j)·s)` of the trace-form differential
(`ChabautyColeman.traceMat`), assembled into a matrix
(`ChabautyColeman.traceMatrix`) and shown to be invertible over a domain
(`ChabautyColeman.det_traceMatrix_ne_zero`).

It is the Gram matrix, in the monomial basis of `A[X]/u`, of the residue pairing
`(p, q) ↦ -λ_u(p·q·s)`. That pairing is nondegenerate whenever `s` is a unit modulo `u`: if
`p` has nonzero residue then so does `p·s`, and a nonzero residue is detected by some `X^m`
with `m < deg u` (`Polynomial.exists_topCoeffMod_ne_zero` — choose `m` making the degree
exactly `deg u - 1`, so that no reduction happens and the top coefficient is a leading
coefficient).

This is the *basis* half of `thm:omega-prime-global` clause (c): the constant matrix `A = C(0)`
of the trace-form route is the trace matrix of the `τ`-datum, whose Bézout cofactor is a unit
modulo `u_τ`, so `A` is invertible and the differentials it combines form a basis. The explicit
numerators `P_l = ½·∑_j ((A⁻¹)_{lj}·xʲ)` are `ChabautyColeman.tracePoly`, with their linear
independence (`ChabautyColeman.sum_smul_tracePoly_ne_zero`); they are disk-independent, which is
what lets one annihilating differential serve every residue disk of `thm:main-count`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Matrix

open scoped Matrix

variable {A : Type*} [CommRing A] {u s : A[X]}

/-- The trace form as a matrix in the monomial basis of `A[X]/u`: the Hankel matrix
`C_ij = -λ_u(X^(i+j)·s)`. -/
noncomputable def traceMatrix (u s : A[X]) : Matrix (Fin u.natDegree) (Fin u.natDegree) A :=
  Matrix.of fun i j ↦ traceMat u s i j

@[simp] theorem traceMatrix_apply (i j : Fin u.natDegree) :
    traceMatrix u s i j = traceMat u s i j :=
  rfl

theorem sum_mul_traceMatrix (v : Fin u.natDegree → A) (m : Fin u.natDegree) :
    ∑ i, v i * traceMatrix u s i m
      = -topCoeffMod u (X ^ (m : ℕ) * (∑ i : Fin u.natDegree, C (v i) * X ^ (i : ℕ)) * s) := by
  have hexp : X ^ (m : ℕ) * (∑ i : Fin u.natDegree, C (v i) * X ^ (i : ℕ)) * s
      = ∑ i : Fin u.natDegree, C (v i) * (X ^ ((i : ℕ) + m) * s) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hexp, topCoeffMod_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [topCoeffMod_C_mul, traceMatrix_apply, traceMat]
    ring

/-- The Hankel matrix is symmetric: its entries depend only on `i + j`. -/
theorem traceMatrix_comm (i j : Fin u.natDegree) :
    traceMatrix u s i j = traceMatrix u s j i := by
  rw [traceMatrix_apply, traceMatrix_apply, traceMat, traceMat, add_comm]

/-- The core of nondegeneracy: a vector orthogonal to every column is zero. Read as
polynomials, `∑ᵢ vᵢ Xⁱ` has residue `0` modulo `u` because `s` is a unit there and every
`λ_u(X^m·p·s)` vanishes (`exists_topCoeffMod_ne_zero`). -/
theorem eq_zero_of_sum_mul_traceMatrix [Nontrivial A] (hu : u.Monic) (hs : IsCoprime u s)
    {v : Fin u.natDegree → A} (hv : ∀ m, ∑ i, v i * traceMatrix u s i m = 0) : v = 0 := by
  set p : A[X] := ∑ i : Fin u.natDegree, C (v i) * X ^ (i : ℕ) with hp
  have hzero (m : Fin u.natDegree) : topCoeffMod u (X ^ (m : ℕ) * (p * s)) = 0 := by
    have h := hv m
    rwa [sum_mul_traceMatrix v m, neg_eq_zero, mul_assoc] at h
  have hps : (p * s) %ₘ u = 0 := by
    by_contra h0
    obtain ⟨m, hm, hne⟩ := exists_topCoeffMod_ne_zero hu h0
    exact hne (hzero ⟨m, hm⟩)
  have hpdvd : u ∣ p := hs.dvd_of_dvd_mul_right ((modByMonic_eq_zero_iff_dvd hu).mp hps)
  have hpdeg : p.degree < u.degree := by
    rw [degree_eq_natDegree hu.ne_zero]
    exact degree_sum_fin_lt v
  have hp0 : p = 0 := by
    rw [← (modByMonic_eq_self_iff hu).mpr hpdeg, (modByMonic_eq_zero_iff_dvd hu).mpr hpdvd]
  funext i
  simpa [hp, coeff_C_mul, coeff_X_pow, Finset.sum_ite_eq' Finset.univ i, Fin.val_eq_val] using
    congrArg (fun q ↦ Polynomial.coeff q (i : ℕ)) hp0

/-- **The trace matrix is nondegenerate**, hence invertible over a domain. It is the Gram
matrix of the residue pairing `(p, q) ↦ -λ_u(p·q·s)` on `A[X]/u`, and that pairing is
nondegenerate whenever `s` is a unit there. -/
theorem det_traceMatrix_ne_zero [IsDomain A] (hu : u.Monic) (hs : IsCoprime u s) :
    (traceMatrix u s).det ≠ 0 := by
  refine Matrix.nondegenerate_iff_det_ne_zero.mp
    (Matrix.nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero.mpr
      ⟨fun v hv ↦ eq_zero_of_sum_mul_traceMatrix hu hs fun m ↦ congrFun hv m,
        fun w hw ↦ eq_zero_of_sum_mul_traceMatrix hu hs fun m ↦ ?_⟩)
  have h : ∑ i, traceMatrix u s m i * w i = 0 := congrFun hw m
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, traceMatrix_comm]

end Matrix

section TracePoly

open scoped Matrix

variable {K : Type*} [Field K] {u s : K[X]}

/-- **The trace-form numerator polynomials** (the explicit numerators of
`thm:omega-prime-global` clause (c)): `P_l = ½·∑_j ((A⁻¹)_{lj}·xʲ)` with `A` the trace
matrix of the datum `(u, s)`. By the trace-form identity these are the numerators of the
basis differentials `ω′_l`, independently of the residue disk. -/
noncomputable def tracePoly (u s : K[X]) (l : Fin u.natDegree) : K[X] :=
  (2⁻¹ : K) • ∑ j : Fin u.natDegree, C ((traceMatrix u s)⁻¹ l j) * X ^ (j : ℕ)

theorem degree_tracePoly_lt (l : Fin u.natDegree) :
    (tracePoly u s l).degree < u.natDegree :=
  (degree_smul_le _ _).trans_lt (degree_sum_fin_lt _)

/-- The doubled trace-form numerator is the inverse-trace-matrix combination itself. -/
theorem two_smul_tracePoly [NeZero (2 : K)] (l : Fin u.natDegree) :
    (2 : K) • tracePoly u s l
      = ∑ j : Fin u.natDegree, C ((traceMatrix u s)⁻¹ l j) * X ^ (j : ℕ) := by
  rw [tracePoly, smul_smul, mul_inv_cancel₀ (two_ne_zero (α := K)), one_smul]

/-- A coordinate-vector combination of the trace-form numerators, read off the
inverse-trace-matrix image of the coordinate vector. -/
theorem sum_smul_tracePoly (cs : Fin u.natDegree → K) :
    ∑ l, cs l • tracePoly u s l
      = (2⁻¹ : K) • ∑ j : Fin u.natDegree,
          C ((cs ᵥ* (traceMatrix u s)⁻¹) j) * X ^ (j : ℕ) := by
  simp only [tracePoly, Finset.smul_sum, smul_eq_C_mul, map_mul, Matrix.vecMul, dotProduct,
    map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

/-- **The trace-form numerators are linearly independent** (the basis half of
`thm:omega-prime-global` clause (c)): a nonzero coordinate vector gives a nonzero
polynomial, because the trace matrix is invertible
(`ChabautyColeman.det_traceMatrix_ne_zero`). -/
theorem sum_smul_tracePoly_ne_zero [NeZero (2 : K)] (hu : u.Monic) (hs : IsCoprime u s)
    {cs : Fin u.natDegree → K} (hcs : cs ≠ 0) :
    ∑ l, cs l • tracePoly u s l ≠ 0 := by
  intro h0
  set A := traceMatrix u s
  rw [sum_smul_tracePoly] at h0
  have hsum := (smul_eq_zero.mp h0).resolve_left (inv_ne_zero (two_ne_zero (α := K)))
  have hw : cs ᵥ* A⁻¹ = 0 := by
    funext j
    have := congrArg (fun q ↦ Polynomial.coeff q (j : ℕ)) hsum
    simpa [coeff_C_mul, coeff_X_pow, Finset.sum_ite_eq' Finset.univ j,
      Fin.val_eq_val] using this
  have hdet : IsUnit A.det := (det_traceMatrix_ne_zero hu hs).isUnit
  refine hcs ?_
  have h := congrArg (· ᵥ* A) hw
  rwa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hdet, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h

end TracePoly

end ChabautyColeman

end
