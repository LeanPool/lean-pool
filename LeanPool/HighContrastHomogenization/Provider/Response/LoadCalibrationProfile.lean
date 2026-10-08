/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationLoads

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationProfile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The individual load bounds and the profile factor

The boxed display of the response-load calibration:

    (L_t^±)² ≤ 4√θ,     Λ_t^± ≤ √5 θ^{1/4},     K_t ≤ β^{1/2}κ_t^{1/4},

and the signed-load display,

    |𝐌₀^{1/2}x^±|² ≤ 4β√θ.

The individual load bounds follow from the exact sum of `LoadCalibrationLoads`
because both summands are nonnegative — each is a quadratic form of the
positive block `Ê_t`.  The `Λ` bound adds the pairing `p·q^± = 1`, which holds
because `p·q = e·e = 1` and both `g₀ - h` and `h - g₀` are skew.  The `K_t` bound is the upper
canonical comparison
`Ê_t ≤ β√κ_t 𝐌₀` read as a relative size, and the signed-load
bound is the lower one `β⁻¹𝐌₀ ≤ Ê_t` read at `x^±`.

Throughout, `|𝐌₀^{1/2}x|²` is the quadratic form `x ⬝ 𝐌₀ x`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Elementary facts about the canonical metric block -/

/-- The canonical metric block `𝐌₀ = diag(m₀, m₀⁻¹)` is positive definite. -/
theorem posDef_metricBlock {m0 : Mat d} (hm0 : m0.PosDef) :
    (Matrix.fromBlocks m0 0 0 m0⁻¹ : FullBlockMat d).PosDef := by
  rw [← schurBlock_zero]
  exact posDef_schurBlock hm0 hm0

/-- A quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem quadratic_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (x : n → ℝ) : 0 ≤ x ⬝ᵥ A *ᵥ x := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- The congruence of a positive semidefinite matrix has nonnegative quadratic
forms. -/
theorem quadratic_conj_nonneg {Et G0 Ehat : FullBlockMat d} (hEt : Et.PosSemidef)
    (hEhat : Ehat = G0ᴴ * Et * G0) (x : FullBlockVec d) : 0 ≤ x ⬝ᵥ Ehat *ᵥ x := by
  rw [hEhat, Initialization.quad_conj]
  exact quadratic_nonneg hEt _

/-- A nonnegative number below a square root bound. -/
theorem le_sqrt_of_sq_le {x c : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ c) : x ≤ Real.sqrt c := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hx] at this

/-! ## The pairing of the signed loads -/

variable {S SStar K r B m g0 h m0 : Mat d} {Et Ehat G0 M0 : FullBlockMat d} {e p q : Vec d}

/-- **The load pairing is one**: `p·q^± = 1`, because
`p·q = e·e = 1` and the shift is by a skew matrix. -/
theorem dotProduct_signed_load {W : Mat d} (hm : m.PosDef) (hW : Wᴴ = -W)
    (hp : p = matSqrt m⁻¹ *ᵥ e) (hq : q = matSqrt m *ᵥ e) (he : e ⬝ᵥ e = 1) :
    p ⬝ᵥ (q + W *ᵥ p) = 1 := by
  rw [dotProduct_add, dotProduct_mulVec_of_skew hW, add_zero, hp, hq,
    dotProduct_load_pair hm, he]

/-- Both `g₀ - h` and `h - g₀` are skew when `g₀` and `h` are. -/
theorem skew_sub {A C : Mat d} (hA : Aᴴ = -A) (hC : Cᴴ = -C) : (A - C)ᴴ = -(A - C) := by
  rw [Matrix.conjTranspose_sub, hA, hC]
  abel

/-! ## The individual load bounds -/

/-- **`(L_t^-)² ≤ 4√θ`**, from the exact sum and nonnegativity
of the other summand. -/
theorem load_sq_neg_le (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEtpd : Et.PosDef) (hEt : Et = schurBlock S SStar K)
    (hG0 : G0 = fullBlockShear g0) (hEhat : Ehat = G0ᴴ * Et * G0)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ))
    (hB : B = S + rᴴ * SStar⁻¹ * r) (hmdef : m = matGeomMean B SStar)
    (hp : p = matSqrt m⁻¹ *ᵥ e) (hq : q = matSqrt m *ᵥ e) (he : e ⬝ᵥ e = 1)
    {theta : ℝ} (htheta : 0 < theta) (hBle : B ≤ theta • SStar) :
    Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) ≤
      4 * Real.sqrt theta := by
  have hsum := load_sum_le hS hStar hEt hG0 hEhat hr hh hB hmdef hp hq he htheta hBle
  have hpos := quadratic_conj_nonneg hEtpd.posSemidef hEhat
    (Sum.elim p (q + (h - g0) *ᵥ p))
  linarith only [hsum, hpos]

/-- **`(L_t^+)² ≤ 4√θ`**. -/
theorem load_sq_pos_le (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEtpd : Et.PosDef) (hEt : Et = schurBlock S SStar K)
    (hG0 : G0 = fullBlockShear g0) (hEhat : Ehat = G0ᴴ * Et * G0)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ))
    (hB : B = S + rᴴ * SStar⁻¹ * r) (hmdef : m = matGeomMean B SStar)
    (hp : p = matSqrt m⁻¹ *ᵥ e) (hq : q = matSqrt m *ᵥ e) (he : e ⬝ᵥ e = 1)
    {theta : ℝ} (htheta : 0 < theta) (hBle : B ≤ theta • SStar) :
    Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) ≤
      4 * Real.sqrt theta := by
  have hsum := load_sum_le hS hStar hEt hG0 hEhat hr hh hB hmdef hp hq he htheta hBle
  have hpos := quadratic_conj_nonneg hEtpd.posSemidef hEhat
    (Sum.elim (-p) (q + (g0 - h) *ᵥ p))
  linarith only [hsum, hpos]

/-! ## The recentered profile factor -/

/-- **`Λ_t^± ≤ √5 θ^{1/4}`**.  The printed `Λ` is
`((L_t^±)² + |p·q^±|)^{1/2}`; with the pairing equal to one and `θ ≥ 1` the
square is at most `5√θ`. -/
theorem lambda_le {Lsq Lam theta : ℝ} (hLam : 0 ≤ Lam) (htheta : 1 ≤ theta)
    (hLamsq : Lam ^ 2 = Lsq + 1) (hLsq : Lsq ≤ 4 * Real.sqrt theta) :
    Lam ≤ Real.sqrt 5 * Real.sqrt (Real.sqrt theta) := by
  have hs1 : 1 ≤ Real.sqrt theta := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt htheta
  have hsq : Lam ^ 2 ≤ 5 * Real.sqrt theta := by
    rw [hLamsq]
    linarith only [hLsq, hs1]
  have h := le_sqrt_of_sq_le hLam hsq
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)] at h

/-- **`K_t ≤ β^{1/2}κ_t^{1/4}`** (, proof).  The printed
`K_t` is `|𝐌₀^{-1/2}Ê_t𝐌₀^{-1/2}|^{1/2}`, i.e. the square root of the relative
size of `Ê_t` against `𝐌₀`. -/
theorem profile_factor_le {Kt beta kappa : ℝ} (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (hEhatPsd : Ehat.PosSemidef)
    (hKt : 0 ≤ Kt) (hKtsq : Kt ^ 2 = relSize Ehat M0) (hbeta : 0 ≤ beta)
    (hup : Ehat ≤ (beta * Real.sqrt kappa) • M0) :
    Kt ≤ Real.sqrt beta * Real.sqrt (Real.sqrt kappa) := by
  have hM0pd : M0.PosDef := by rw [hM0]; exact posDef_metricBlock hm0
  have hrel : relSize Ehat M0 ≤ beta * Real.sqrt kappa :=
    (relSize_le_iff hEhatPsd hM0pd (mul_nonneg hbeta (Real.sqrt_nonneg kappa))).mpr hup
  have hsq : Kt ^ 2 ≤ beta * Real.sqrt kappa := by rw [hKtsq]; exact hrel
  have h := le_sqrt_of_sq_le hKt hsq
  rwa [Real.sqrt_mul hbeta] at h

/-- The response skew coordinate `h = ½(K - Kᵗ)` is skew. -/
theorem skew_half_sub (K : Mat d) : ((2 : ℝ)⁻¹ • (K - Kᴴ))ᴴ = -((2 : ℝ)⁻¹ • (K - Kᴴ)) := by
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg]

/-! ## The signed loads in the canonical metric -/

/-- **`|𝐌₀^{1/2}x|² ≤ β (L)²`**: the lower canonical
comparison read at a signed profile vector. -/
theorem metric_load_le_smul {beta : ℝ} (hbeta : 0 < beta)
    (hlow : beta⁻¹ • M0 ≤ Ehat) (x : FullBlockVec d) :
    x ⬝ᵥ M0 *ᵥ x ≤ beta * (x ⬝ᵥ Ehat *ᵥ x) := by
  have h := Initialization.dotProduct_mulVec_le_of_le hlow x
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  have hb : beta⁻¹ * (x ⬝ᵥ M0 *ᵥ x) ≤ x ⬝ᵥ Ehat *ᵥ x := h
  have := mul_le_mul_of_nonneg_left hb hbeta.le
  rwa [← mul_assoc, mul_inv_cancel₀ hbeta.ne', one_mul] at this

/-- **`|𝐌₀^{1/2}x^±|² ≤ 4β√θ`**, the boxed display. -/
theorem metric_signed_load_le {beta theta : ℝ} (hbeta : 0 < beta)
    (hlow : beta⁻¹ • M0 ≤ Ehat) {x : FullBlockVec d}
    (hx : x ⬝ᵥ Ehat *ᵥ x ≤ 4 * Real.sqrt theta) :
    x ⬝ᵥ M0 *ᵥ x ≤ 4 * beta * Real.sqrt theta := by
  have h := metric_load_le_smul hbeta hlow x
  nlinarith only [h, hx, hbeta]

end

end Response
end HighContrast
end HCPolySupport
