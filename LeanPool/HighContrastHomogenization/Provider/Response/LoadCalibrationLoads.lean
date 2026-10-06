/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationMetric
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationTheta

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationLoads

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The exact energy sum of the two signed loads

The boxed display of the response-load calibration:

    (L_t^-)² + (L_t^+)² = 4 eᵗ(m^{1/2}S_*^{-1}m^{1/2}) e ≤ 4√θ,

with `L_t^∓ = |Ê_t^{1/2}x^∓|`, `Ê_t = 𝐆₀ᵗE_t𝐆₀`, and the two signed profile
vectors `x^- = (-p, q^-)`, `x^+ = (p, q^+)`, `q^∓ = q ± (g₀ - h)p`,
`p = m^{-1/2}e`, `q = m^{1/2}e`, `m = B # S_*`.

The proof is the printed one, through the skew-recentered blocks and the
coefficient transpose.  Recentering by `𝐆₀` replaces
`q^∓` by `q ∓ hp`, so the Schur factorization gives

    (L_t^-)² = ⟨Sp, p⟩ + ⟨S_*⁻¹(q + rp), q + rp⟩,
    (L_t^+)² = ⟨Sp, p⟩ + ⟨S_*⁻¹(q - rp), q - rp⟩,

whose sum is `2⟨Bp, p⟩ + 2⟨S_*⁻¹q, q⟩` because the two cross terms cancel and
`⟨S_*⁻¹rp, rp⟩ = ⟨rᵗS_*⁻¹r p, p⟩`.  The Riccati characterization of the metric
geometric mean gives `mS_*⁻¹m = B`, so both summands equal
`eᵗ(m^{1/2}S_*^{-1}m^{1/2})e` and the sum is four times it.

For the bound, the printed proof passes through the eigenvalues of
`S_*^{-1/2}mS_*^{-1/2}`.  The route here is the equivalent Loewner one, which
needs no spectral theory: joint monotonicity and homogeneity of the geometric
mean turn `B ≤ θS_*` into `m = B # S_* ≤ (θS_*) # S_* = √θ S_*`, and inverting
and conjugating by `m^{1/2}` turns that into
`m^{1/2}S_*^{-1}m^{1/2} ≤ √θ I`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Square roots against the matrix -/

/-- `m^{-1/2}m = m^{1/2}`. -/
theorem matSqrt_inv_mul_eq {m : Mat d} (hm : m.PosDef) :
    matSqrt m⁻¹ * m = matSqrt m := by
  have hsq : matSqrt m * matSqrt m = m := (matSqrt_spec hm.posSemidef).2
  calc matSqrt m⁻¹ * m = matSqrt m⁻¹ * (matSqrt m * matSqrt m) := by rw [hsq]
    _ = (matSqrt m⁻¹ * matSqrt m) * matSqrt m := by noncomm_ring
    _ = matSqrt m := by rw [matSqrt_inv_mul_matSqrt hm, Matrix.one_mul]

/-- `m m^{-1/2} = m^{1/2}`. -/
theorem mul_matSqrt_inv_eq {m : Mat d} (hm : m.PosDef) :
    m * matSqrt m⁻¹ = matSqrt m := by
  have hsq : matSqrt m * matSqrt m = m := (matSqrt_spec hm.posSemidef).2
  calc m * matSqrt m⁻¹ = (matSqrt m * matSqrt m) * matSqrt m⁻¹ := by rw [hsq]
    _ = matSqrt m * (matSqrt m * matSqrt m⁻¹) := by noncomm_ring
    _ = matSqrt m := by rw [matSqrt_mul_matSqrt_inv hm, Matrix.mul_one]

/-- `m^{1/2}m⁻¹m^{1/2} = I`. -/
theorem matSqrt_mul_inv_mul_matSqrt {m : Mat d} (hm : m.PosDef) :
    matSqrt m * m⁻¹ * matSqrt m = 1 := by
  calc matSqrt m * m⁻¹ * matSqrt m
      = matSqrt m * (matSqrt m⁻¹ * matSqrt m⁻¹) * matSqrt m := by
        rw [matSqrt_inv_mul_self hm]
    _ = (matSqrt m * matSqrt m⁻¹) * (matSqrt m⁻¹ * matSqrt m) := by noncomm_ring
    _ = 1 := by
        rw [matSqrt_mul_matSqrt_inv hm, matSqrt_inv_mul_matSqrt hm, Matrix.one_mul]

/-- The dilation of a positive definite matrix inverts scalarwise. -/
theorem inv_smul_posDef {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA), mul_inv_cancel₀ hc.ne', one_smul]

/-! ## The two signed loads -/

variable {S SStar K r B m g0 h : Mat d} {Et Ehat G0 : FullBlockMat d} {e p q : Vec d}

/-- The response block `B = S + rᵗS_*⁻¹r` is positive definite. -/
theorem posDef_responseBlock (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r) : B.PosDef := by
  rw [hB]
  exact hS.add_posSemidef (hStar.inv.posSemidef.conjTranspose_mul_mul_same r)

/-- **The negative load in Schur coordinates**.  Recentering by
`𝐆₀` replaces `q^-` by `q - hp`, and the Schur factorization then produces
`q + rp` in the second slot. -/
theorem load_sq_neg (hEt : Et = schurBlock S SStar K) (hG0 : G0 = fullBlockShear g0)
    (hEhat : Ehat = G0ᴴ * Et * G0) (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ))
    (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ)) :
    Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) =
      p ⬝ᵥ S *ᵥ p + (q + r *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q + r *ᵥ p) := by
  have hsum : h *ᵥ p + r *ᵥ p = K *ᵥ p := by
    rw [hh, hr, ← Matrix.add_mulVec]
    congr 1
    module
  have hshift : g0 *ᵥ (-p) + (q + (g0 - h) *ᵥ p) = q - h *ᵥ p := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_neg]
    abel
  have hslot : (q - h *ᵥ p) - K *ᵥ (-p) = q + r *ᵥ p := by
    rw [Matrix.mulVec_neg, ← hsum]
    abel
  rw [hEhat, Initialization.quad_conj, hG0, fullBlockShear_mulVec, hshift, hEt,
    quadratic_schurBlock, hslot, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct,
    neg_neg]

/-- **The positive load in Schur coordinates**, through the Riccati
characterization of the matrix geometric mean. -/
theorem load_sq_pos (hEt : Et = schurBlock S SStar K) (hG0 : G0 = fullBlockShear g0)
    (hEhat : Ehat = G0ᴴ * Et * G0) (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ))
    (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ)) :
    Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) =
      p ⬝ᵥ S *ᵥ p + (q - r *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q - r *ᵥ p) := by
  have hsum : h *ᵥ p + r *ᵥ p = K *ᵥ p := by
    rw [hh, hr, ← Matrix.add_mulVec]
    congr 1
    module
  have hshift : g0 *ᵥ p + (q + (h - g0) *ᵥ p) = q + h *ᵥ p := by
    rw [Matrix.sub_mulVec]
    abel
  have hslot : (q + h *ᵥ p) - K *ᵥ p = q - r *ᵥ p := by
    rw [← hsum]
    abel
  rw [hEhat, Initialization.quad_conj, hG0, fullBlockShear_mulVec, hshift, hEt,
    quadratic_schurBlock, hslot]

/-! ## The exact sum -/

/-- **The exact energy sum**:
`(L_t^-)² + (L_t^+)² = 4 eᵗ(m^{1/2}S_*^{-1}m^{1/2})e`. -/
theorem load_sum_eq (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEt : Et = schurBlock S SStar K) (hG0 : G0 = fullBlockShear g0)
    (hEhat : Ehat = G0ᴴ * Et * G0) (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ))
    (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ)) (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hmdef : m = matGeomMean B SStar) (hp : p = matSqrt m⁻¹ *ᵥ e)
    (hq : q = matSqrt m *ᵥ e) :
    Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) +
        Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) =
      4 * (e ⬝ᵥ (matSqrt m * SStar⁻¹ * matSqrt m) *ᵥ e) := by
  have hBpd : B.PosDef := posDef_responseBlock hS hStar hB
  have hm : m.PosDef := by rw [hmdef]; exact posDef_matGeomMean hBpd hStar
  have hric : m * SStar⁻¹ * m = B := by
    rw [hmdef, matGeomMean_comm hBpd hStar]
    exact matGeomMean_riccati hStar hBpd
  have hsymmInv : (matSqrt m⁻¹)ᴴ = matSqrt m⁻¹ := conjTranspose_matSqrt hm.inv.posSemidef
  have hsymmSqrt : (matSqrt m)ᴴ = matSqrt m := conjTranspose_matSqrt hm.posSemidef
  have hkey : matSqrt m⁻¹ * (m * SStar⁻¹ * m) * matSqrt m⁻¹ =
      matSqrt m * SStar⁻¹ * matSqrt m := by
    calc matSqrt m⁻¹ * (m * SStar⁻¹ * m) * matSqrt m⁻¹
        = (matSqrt m⁻¹ * m) * SStar⁻¹ * (m * matSqrt m⁻¹) := by noncomm_ring
      _ = matSqrt m * SStar⁻¹ * matSqrt m := by
          rw [matSqrt_inv_mul_eq hm, mul_matSqrt_inv_eq hm]
  have hBterm : p ⬝ᵥ B *ᵥ p = e ⬝ᵥ (matSqrt m * SStar⁻¹ * matSqrt m) *ᵥ e := by
    have hconj := Initialization.quad_conj (matSqrt m⁻¹) B e
    rw [hsymmInv] at hconj
    rw [hp, ← hconj, ← hric, hkey]
  have hQterm : q ⬝ᵥ SStar⁻¹ *ᵥ q = e ⬝ᵥ (matSqrt m * SStar⁻¹ * matSqrt m) *ᵥ e := by
    have hconj := Initialization.quad_conj (matSqrt m) SStar⁻¹ e
    rw [hsymmSqrt] at hconj
    rw [hq, ← hconj]
  have hpol := polarization SStar⁻¹ q (r *ᵥ p)
  have hcross : (r *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r *ᵥ p) = p ⬝ᵥ (rᴴ * SStar⁻¹ * r) *ᵥ p :=
    (Initialization.quad_conj r SStar⁻¹ p).symm
  have hsplit : p ⬝ᵥ B *ᵥ p = p ⬝ᵥ S *ᵥ p + p ⬝ᵥ (rᴴ * SStar⁻¹ * r) *ᵥ p := by
    rw [hB, Matrix.add_mulVec, dotProduct_add]
  rw [load_sq_neg hEt hG0 hEhat hr hh, load_sq_pos hEt hG0 hEhat hr hh]
  linarith only [hpol, hcross, hsplit, hBterm, hQterm]

/-! ## The bound by the response ratio -/

/-- **`m ≤ √θ S_*`** from `B ≤ θ S_*`, by joint monotonicity and homogeneity of
the metric geometric mean. -/
theorem geomMean_le_sqrt_smul (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r) (hmdef : m = matGeomMean B SStar) {theta : ℝ}
    (htheta : 0 < theta) (hBle : B ≤ theta • SStar) :
    m ≤ Real.sqrt theta • SStar := by
  have hBpd : B.PosDef := posDef_responseBlock hS hStar hB
  have hmono := matGeomMean_mono hBpd (posDef_smul hStar htheta) hStar hStar hBle le_rfl
  have hrw : matGeomMean (theta • SStar) SStar = Real.sqrt theta • SStar := by
    have hs := matGeomMean_smul (A := SStar) (B := SStar) hStar hStar htheta one_pos
    rw [one_smul, matGeomMean_self hStar, mul_one] at hs
    exact hs
  rw [hrw] at hmono
  rw [hmdef]
  exact hmono

/-- **`m^{1/2}S_*^{-1}m^{1/2} ≤ √θ I`**. -/
theorem normalized_le_sqrt_smul_one {SStar m : Mat d} (hStar : SStar.PosDef)
    (hm : m.PosDef) {theta : ℝ} (htheta : 0 < theta)
    (hmle : m ≤ Real.sqrt theta • SStar) :
    matSqrt m * SStar⁻¹ * matSqrt m ≤ Real.sqrt theta • (1 : Mat d) := by
  have hspos : 0 < Real.sqrt theta := Real.sqrt_pos.mpr htheta
  have hinv := inv_le_inv_of_le hm (posDef_smul hStar hspos) hmle
  rw [inv_smul_posDef hStar hspos] at hinv
  have hconj := conj_le_conj' (C := matSqrt m) (conjTranspose_matSqrt hm.posSemidef) hinv
  rw [Matrix.mul_smul, Matrix.smul_mul, matSqrt_mul_inv_mul_matSqrt hm] at hconj
  exact le_of_smul_inv_le hspos hconj

/-- **The exact sum and its bound**, the boxed display: for a
unit vector `e` the two signed loads have energy sum
`4 eᵗ(m^{1/2}S_*^{-1}m^{1/2})e`, and that is at most `4√θ`. -/
theorem load_sum_le (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEt : Et = schurBlock S SStar K) (hG0 : G0 = fullBlockShear g0)
    (hEhat : Ehat = G0ᴴ * Et * G0) (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ))
    (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ)) (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hmdef : m = matGeomMean B SStar) (hp : p = matSqrt m⁻¹ *ᵥ e)
    (hq : q = matSqrt m *ᵥ e) (he : e ⬝ᵥ e = 1) {theta : ℝ} (htheta : 0 < theta)
    (hBle : B ≤ theta • SStar) :
    Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) +
        Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) ≤
      4 * Real.sqrt theta := by
  have hBpd : B.PosDef := posDef_responseBlock hS hStar hB
  have hm : m.PosDef := by rw [hmdef]; exact posDef_matGeomMean hBpd hStar
  have hN := normalized_le_sqrt_smul_one hStar hm htheta
    (geomMean_le_sqrt_smul hS hStar hB hmdef htheta hBle)
  have hq' := Initialization.dotProduct_mulVec_le_of_le hN e
  have hval : e ⬝ᵥ (Real.sqrt theta • (1 : Mat d)) *ᵥ e = Real.sqrt theta := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, he,
      mul_one]
  rw [hval] at hq'
  rw [load_sum_eq hS hStar hEt hG0 hEhat hr hh hB hmdef hp hq]
  linarith only [hq']

end

end Response
end HighContrast
end HCPolySupport
