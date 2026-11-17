/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspChain
public import LeanPool.HyperellipticCurves.Log.Witness.TupleSeed

/-!
# Base state and step conditions of the cuspidal fold

The chain lemmas of `LeanPool.HyperellipticCurves.Log.Fold.CuspChain` consume one composition
condition per
fold step; this file produces them, together with the base state (`def:cusp-fold`,
`def:centre-fold`):

* `ChabautyColeman.isCuspState_base`: the Mumford datum interpolating the parametrized cusp
  points `(tᵢ², tᵢ^N)` (via the tuple machinery of
  `LeanPool.HyperellipticCurves.Log.Witness.TupleSeed`),
  together with the support `A₀ = ∏(z - tᵢ)`, satisfies the fold invariants — the only
  hypothesis is injectivity of the nodes `tᵢ²`.
* `ChabautyColeman.cuspStep_cond_of_generic`: at a disjoint step (`A(±t) ≠ 0`), the
  field-division scalar `H = (t^N - V(t²))/U(t²)` satisfies the composition condition.
* `ChabautyColeman.cuspStep_cond_of_double`: at the doubling step, the condition follows from
  the second-order interpolation (value and derivative of the composed square root at the
  node), by the square-factor criterion `Polynomial.X_sub_C_sq_dvd_iff`.
* `ChabautyColeman.cuspStep_cond_base`, `ChabautyColeman.exists_cuspStep_H`: the doubling
  condition instantiated at the base state — the initial step of the fold doubles a node of
  the base support — with the tangency identity as a certificate, solved by the explicit
  derivative-form scalar `H₀ = ((2g+1)t^(2g) - 2t·V₀'(t²))/(2t·U₀'(t²))`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Conditions

variable {F : Type*} [Field F] {g : ℕ} {U V A Vc : F[X]} {t : F}

/-- The state's `U`-value at a parametrized node, through the `U`–`A` identity. -/
theorem IsCuspState.eval_sq (hs : IsCuspState g U V A) (t : F) :
    U.eval (t ^ 2) = (-1) ^ g * (A.eval t * A.eval (-t)) := by
  simpa [eval_comp] using congrArg (eval t) hs.comp_sq

/-- **The generic composition condition** (`def:centre-fold`, disjoint step): when the
disjointness values `A(±t)` are nonzero, the field-division scalar
`H = (t^N - V(t²))/U(t²)` satisfies the composition condition of the fold step. -/
theorem cuspStep_cond_of_generic (hs : IsCuspState g U V A) (hAt : A.eval t ≠ 0)
    (hAmt : A.eval (-t) ≠ 0) :
    A * (X - C t) ∣ X ^ (2 * g + 1)
      - (V + C ((t ^ (2 * g + 1) - V.eval (t ^ 2)) / U.eval (t ^ 2)) * U).comp (X ^ 2) := by
  have hU0 : U.eval (t ^ 2) ≠ 0 := by
    rw [hs.eval_sq]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hAt hAmt)
  refine cuspCompose_dvd hs.dvd_lift ?_ ?_ hAt
  · rw [add_sub_cancel_left, mul_comp, C_comp]
    have hAU : A ∣ U.comp (X ^ 2) := ⟨(-1) ^ g * A.comp (-X), by rw [hs.comp_sq]; ring⟩
    exact hAU.mul_left _
  · rw [eval_add, eval_mul, eval_C, div_mul_cancel₀ _ hU0]
    ring

/-- **The doubling composition condition** (`def:centre-fold`, the single doubling step), in
certificate form: if the support factors as `A = B·(z - t)` with `B(t) ≠ 0` and the composed
square root is tangent at the node — value and derivative conditions — then the composition
condition holds. -/
theorem cuspStep_cond_of_double {B : F[X]} (hdvd : A ∣ X ^ (2 * g + 1) - V.comp (X ^ 2))
    (hVcV : A ∣ (Vc - V).comp (X ^ 2)) (hA : A = B * (X - C t)) (hBt : B.eval t ≠ 0)
    (hint : Vc.eval (t ^ 2) = t ^ (2 * g + 1))
    (hder : ((2 * g + 1 : ℕ) : F) * t ^ (2 * g) = 2 * t * Vc.derivative.eval (t ^ 2)) :
    A * (X - C t) ∣ X ^ (2 * g + 1) - Vc.comp (X ^ 2) := by
  rw [hA, mul_assoc, ← sq]
  have hBdvd : B ∣ A := hA ▸ dvd_mul_right B _
  refine ((isCoprime_X_sub_C_of_eval_ne_zero hBt).pow_right).mul_dvd ?_ ?_
  · have h1 : X ^ (2 * g + 1) - Vc.comp (X ^ 2)
        = (X ^ (2 * g + 1) - V.comp (X ^ 2)) - (Vc - V).comp (X ^ 2) := by
      rw [sub_comp]
      ring
    rw [h1]
    exact (hBdvd.trans hdvd).sub (hBdvd.trans hVcV)
  · refine X_sub_C_sq_dvd_iff.mpr ⟨?_, ?_⟩
    · rw [eval_sub, eval_pow, eval_X, eval_comp, eval_pow, eval_X, hint, sub_self]
    · simp only [derivative_sub, derivative_X_pow, derivative_comp, eval_sub, eval_mul,
        eval_C, eval_pow, eval_X, eval_comp]
      push_cast
      push_cast at hder
      linear_combination hder

end Conditions

section Base

variable {F : Type*} [Field F] {g : ℕ} {t : Fin g → F}

/-- **The base state of the cuspidal fold** (`def:cusp-fold`): the Mumford datum
interpolating the parametrized points `(tᵢ², tᵢ^N)` on the cusp, together with the support
`A₀ = ∏(z - tᵢ)`, satisfies the fold invariants. -/
theorem isCuspState_base (hinj : Function.Injective fun i ↦ t i ^ 2) :
    IsCuspState g (tupleU fun i ↦ t i ^ 2)
      (tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1)) (tupleU t) := by
  have htinj : Function.Injective t := fun i j hij ↦ hinj (by simp only [hij])
  have hcurve i : (t i ^ (2 * g + 1)) ^ 2 = (X ^ (2 * g + 1) : F[X]).eval (t i ^ 2) := by
    rw [eval_pow, eval_X]
    ring
  refine ⟨monic_tupleU _, natDegree_tupleU _, ?_, ?_, monic_tupleU _, natDegree_tupleU _,
    ?_, ?_⟩
  · exact ⟨tupleW (X ^ (2 * g + 1)) (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1),
      tupleV_sq_sub hinj hcurve⟩
  · exact degree_tupleV_lt.trans_eq
      (by rw [degree_eq_natDegree (monic_tupleU _).ne_zero, natDegree_tupleU])
  · refine tupleU_dvd htinj fun i ↦ ?_
    rw [eval_sub, eval_pow, eval_X, eval_comp, eval_pow, eval_X, eval_tupleV hinj, sub_self]
  · simp only [tupleU_eq_prod]
    rw [prod_comp, prod_comp]
    simp only [sub_comp, X_comp, C_comp]
    rw [show (∏ i, (-X - C (t i)) : F[X]) = ∏ i, (-1) * (X + C (t i)) from
        Finset.prod_congr rfl fun i _ ↦ by ring,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsq : ((-1 : F[X]) ^ g) * ((-1) ^ g) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨g, rfl⟩
    rw [show ((-1) ^ g * ((∏ i, (X - C (t i))) * ((-1) ^ g * ∏ i, (X + C (t i)))) : F[X])
        = ((-1) ^ g * (-1) ^ g) * ((∏ i, (X - C (t i))) * ∏ i, (X + C (t i))) by ring,
      hsq, one_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [map_pow]
    ring

/-- **The doubling composition condition at the base** (`def:centre-fold`, the single
doubling step, on the cusp): at any node of the base state, a scalar `H₀` satisfying the
tangency identity makes the composition condition of the doubling fold step hold. -/
theorem cuspStep_cond_base (hinj : Function.Injective fun i ↦ t i ^ 2) (i : Fin g)
    {H₀ : F}
    (hH : ((2 * g + 1 : ℕ) : F) * t i ^ (2 * g)
      = 2 * t i
        * ((tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1)).derivative.eval (t i ^ 2)
          + H₀ * (tupleU fun i ↦ t i ^ 2).derivative.eval (t i ^ 2))) :
    tupleU t * (X - C (t i)) ∣ X ^ (2 * g + 1)
      - ((tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1))
        + C H₀ * tupleU fun i ↦ t i ^ 2).comp (X ^ 2) := by
  have htinj : Function.Injective t := fun a b hab ↦ hinj (by simp only [hab])
  have hbase := isCuspState_base hinj
  have hU0 : (tupleU fun i ↦ t i ^ 2).eval (t i ^ 2) = 0 := by
    simpa using eval_tupleU_self (fun j ↦ t j ^ 2) i
  have hV0 : (tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1)).eval (t i ^ 2)
      = t i ^ (2 * g + 1) := by
    simpa using eval_tupleV (y := fun j ↦ t j ^ (2 * g + 1)) hinj i
  refine cuspStep_cond_of_double (B := nodeLag t i) (V := tupleV (fun i ↦ t i ^ 2)
    fun i ↦ t i ^ (2 * g + 1)) hbase.dvd_lift ?_ ?_ ?_ ?_ ?_
  · rw [add_sub_cancel_left, mul_comp, C_comp]
    have hAU : tupleU t ∣ (tupleU fun i ↦ t i ^ 2).comp (X ^ 2) :=
      ⟨(-1) ^ g * (tupleU t).comp (-X), by rw [hbase.comp_sq]; ring⟩
    exact hAU.mul_left _
  · rw [tupleU_eq_prod, Fintype.prod_eq_mul_prod_compl i (fun j ↦ (X : F[X]) - C (t j)),
      mul_comm, nodeLag_eq_prod]
  · rw [eval_nodeLag_self]
    exact nodeDiff_ne_zero htinj i
  · rw [eval_add, eval_mul, eval_C, hU0, mul_zero, add_zero, hV0]
  · rw [derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
    exact hH

/-- The tangency identity has a solution whenever the node is away from `0` and
Weierstrass points: the explicit derivative-form doubling scalar. -/
theorem exists_cuspStep_H (h2 : (2 : F) ≠ 0)
    (hinj : Function.Injective fun i ↦ t i ^ 2) (i : Fin g) (hti : t i ≠ 0) :
    ∃ H₀ : F, ((2 * g + 1 : ℕ) : F) * t i ^ (2 * g)
      = 2 * t i
        * ((tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1)).derivative.eval (t i ^ 2)
          + H₀ * (tupleU fun i ↦ t i ^ 2).derivative.eval (t i ^ 2)) := by
  have hU' : (tupleU fun i ↦ t i ^ 2).derivative.eval (t i ^ 2) ≠ 0 := by
    have h1 : (tupleU fun i ↦ t i ^ 2).derivative.eval (t i ^ 2)
        = nodeDiff (fun i ↦ t i ^ 2) i := by
      simpa using derivative_tupleU_eval (fun j ↦ t j ^ 2) i
    rw [h1]
    exact nodeDiff_ne_zero hinj i
  refine ⟨(((2 * g + 1 : ℕ) : F) * t i ^ (2 * g)
      - 2 * t i
        * (tupleV (fun i ↦ t i ^ 2) fun i ↦ t i ^ (2 * g + 1)).derivative.eval (t i ^ 2))
    / (2 * t i * (tupleU fun i ↦ t i ^ 2).derivative.eval (t i ^ 2)), ?_⟩
  field_simp
  ring

end Base

end ChabautyColeman

end
