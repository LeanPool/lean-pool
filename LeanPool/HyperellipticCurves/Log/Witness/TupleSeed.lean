/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Witness.TupleDatum

/-!
# The Mumford datum of a tuple of curve points is a center seed

Over a field, the denominator-cleared data of `LeanPool.HyperellipticCurves.Log.Witness.TupleDatum`
are the
honest data of the Mumford datum interpolating a tuple of points of the curve `y² = f(x)`
with distinct `x`-coordinates and nonzero `y`-coordinates: `ChabautyColeman.tupleV` is the
interpolant and `ChabautyColeman.tupleW` its cofactor, with the node denominator
`ChabautyColeman.nodeDen` controlling injectivity of the tuple and the interpolation
identities (`ChabautyColeman.eval_tupleV`, `ChabautyColeman.tupleV_sq_sub`).

This is the datum layer consumed by the `τ`-pack construction
(`ChabautyColeman.TauData.exists_of_hasGoodCenter`,
`LeanPool.HyperellipticCurves.Log.Ftau.TauExists`) and by
the infinity family (`LeanPool.HyperellipticCurves.Log.Witness.InfinityFamily`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Field

variable {K : Type*} [Field K] {m : ℕ} {f : K[X]} {x y : Fin m → K}

theorem nodeDiff_ne_zero (hx : Function.Injective x) (i : Fin m) : nodeDiff x i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hj ↦
    sub_ne_zero.mpr fun he ↦ (Finset.mem_compl.mp hj) (Finset.mem_singleton.mpr (hx he).symm)

theorem nodeDen_ne_zero (hx : Function.Injective x) : nodeDen x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ ↦ nodeDiff_ne_zero hx i

/-- A polynomial vanishing at all the nodes is divisible by the nodal polynomial. -/
theorem tupleU_dvd (hx : Function.Injective x) {p : K[X]} (h : ∀ i, p.eval (x i) = 0) :
    tupleU x ∣ p :=
  Fintype.prod_dvd_of_coprime
    (fun _ _ hij ↦ isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun he ↦ hij (hx he))))
    fun i ↦ dvd_iff_isRoot.mpr (h i)

theorem isCoprime_tupleU {p : K[X]} (h : ∀ i, p.eval (x i) ≠ 0) : IsCoprime (tupleU x) p := by
  rw [tupleU_eq_prod]
  exact IsCoprime.prod_left fun i _ ↦ (isCoprime_X_sub_C_of_eval_ne_zero (h i)).symm

/-- The Mumford `v`-part interpolating the tuple. -/
noncomputable def tupleV (x y : Fin m → K) : K[X] := C (nodeDen x)⁻¹ * tupleInterp x y

/-- The cofactor of the Mumford datum interpolating the tuple. -/
noncomputable def tupleW (f : K[X]) (x y : Fin m → K) : K[X] :=
  C ((nodeDen x) ^ 2)⁻¹ * tupleWNum f x y

theorem eval_tupleV (hx : Function.Injective x) (i : Fin m) : (tupleV x y).eval (x i) = y i := by
  have hD : (nodeDen x : K) ≠ 0 := nodeDen_ne_zero hx
  rw [tupleV, eval_mul, eval_C, eval_tupleInterp]
  field_simp

theorem degree_tupleV_lt : (tupleV x y).degree < (tupleU x).degree := by
  rw [degree_eq_natDegree (monic_tupleU x).ne_zero, natDegree_tupleU, tupleV, ← smul_eq_C_mul]
  exact (degree_smul_le _ _).trans_lt (degree_tupleInterp_lt x y)

/-- **Reduction commutes with interpolation**: a polynomial of degree below the nodal degree
that interpolates lifts of given values maps to the canonical interpolant of the values
themselves. -/
theorem map_eq_tupleV {O : Type*} [CommRing O] (φ : O →+* K) {a₀ b₀ : Fin m → O} {v : O[X]}
    (hxinj : Function.Injective fun i ↦ φ (a₀ i)) (hvdeg : v.degree < (tupleU a₀).degree)
    (hveq : ∀ i, v.eval (a₀ i) = b₀ i) :
    v.map φ = tupleV (fun i ↦ φ (a₀ i)) fun i ↦ φ (b₀ i) := by
  classical
  have hvm : (v.map φ).degree < (tupleU fun i ↦ φ (a₀ i)).degree :=
    calc (v.map φ).degree ≤ v.degree := degree_map_le
      _ < (tupleU a₀).degree := hvdeg
      _ = ((tupleU a₀).map φ).degree := ((monic_tupleU a₀).degree_map φ).symm
      _ = (tupleU fun i ↦ φ (a₀ i)).degree := by rw [map_tupleU]
  rcases eq_or_ne (v.map φ - tupleV (fun i ↦ φ (a₀ i)) fun i ↦ φ (b₀ i)) 0 with h0 | h0
  · exact sub_eq_zero.mp h0
  refine sub_eq_zero.mp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (Finset.image (fun i ↦ φ (a₀ i)) Finset.univ) (fun c hc ↦ ?_) ?_)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    rw [eval_sub, eval_tupleV hxinj, eval_map_apply, hveq, sub_self]
  · have h := natDegree_lt_natDegree h0
      ((degree_sub_le _ _).trans_lt (max_lt hvm degree_tupleV_lt))
    rw [natDegree_tupleU] at h
    rwa [Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]

/-- The tuple datum is a Mumford datum: the cleared numerator identity. -/
theorem tupleInterp_sq_sub (hx : Function.Injective x)
    (hcurve : ∀ i, y i ^ 2 = f.eval (x i)) :
    tupleInterp x y ^ 2 - C (nodeDen x ^ 2) * f = tupleU x * tupleWNum f x y := by
  obtain ⟨k, hk⟩ := tupleU_dvd hx (p := tupleInterp x y ^ 2 - C (nodeDen x ^ 2) * f) fun i ↦ by
    simp only [eval_sub, eval_pow, eval_mul, eval_C, eval_tupleInterp, ← hcurve]
    ring
  rw [tupleWNum, hk, mul_divByMonic_cancel_left _ (monic_tupleU x)]

theorem tupleV_sq_sub (hx : Function.Injective x) (hcurve : ∀ i, y i ^ 2 = f.eval (x i)) :
    tupleV x y ^ 2 - f = tupleU x * tupleW f x y := by
  have hD : (nodeDen x : K) ≠ 0 := nodeDen_ne_zero hx
  have h := tupleInterp_sq_sub hx hcurve
  have hinv : (C ((nodeDen x ^ 2)⁻¹) : K[X]) * C (nodeDen x ^ 2) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 hD), C_1]
  have hsq : (C ((nodeDen x)⁻¹) : K[X]) ^ 2 = C ((nodeDen x ^ 2)⁻¹) := by rw [← C_pow, ← inv_pow]
  rw [tupleV, tupleW]
  linear_combination (C ((nodeDen x ^ 2)⁻¹) : K[X]) * h + tupleInterp x y ^ 2 * hsq + f * hinv

end Field

end ChabautyColeman

end
