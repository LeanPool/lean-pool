/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCalibrationAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenteringEstimate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The generic centering estimate

The closed Schur form of the centering pairing, at the calibrated loads of
the response metric, is second order in the contrast defect: the calibration
defect is the `B⁻¹`-quadratic of `(B−1)e`, the symmetric-skew terms cancel to
their quadratic remainder, and the diagonal-gap term pairs against the
deviation vector.  The hypotheses are the normalized diagonal gap, the
symmetric-skew bound, and their two trace forms; the conclusion holds with
the dimension-only constant `6d + 8`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Almost-parallelogram bound for a positive semidefinite quadratic. -/
private theorem quad_add_le {M : Mat d} (hM : M.PosSemidef) (x y : Vec d) :
    (x + y) ⬝ᵥ M *ᵥ (x + y) ≤
      2 * (x ⬝ᵥ M *ᵥ x) + 2 * (y ⬝ᵥ M *ᵥ y) := by
  have hswap : y ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ y := by
    rw [dotProduct_comm, mulVec_dotProduct_symm hM.isHermitian.eq]
  have hminus : 0 ≤ (x - y) ⬝ᵥ M *ᵥ (x - y) := by
    have := hM.dotProduct_mulVec_nonneg (x - y)
    simpa using this
  have hexp₁ : (x + y) ⬝ᵥ M *ᵥ (x + y) =
      x ⬝ᵥ M *ᵥ x + 2 * (x ⬝ᵥ M *ᵥ y) + y ⬝ᵥ M *ᵥ y := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hswap]
    ring
  have hexp₂ : (x - y) ⬝ᵥ M *ᵥ (x - y) =
      x ⬝ᵥ M *ᵥ x - 2 * (x ⬝ᵥ M *ᵥ y) + y ⬝ᵥ M *ᵥ y := by
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hswap]
    ring
  rw [hexp₂] at hminus
  rw [hexp₁]
  linarith only [hminus]


private theorem calibration_load_and_trace_bounds
    {S SStar κ : Mat d} (hStar : SStar.PosDef)
    (hκ : κᴴ = κ)
    {eps : ℝ} (heps0 : 0 ≤ eps)
    (horder : SStar ≤ S)
    (hgapM : S - SStar ≤ eps • SStar)
    (hskewM : κ * SStar⁻¹ * κ ≤ (eps ^ 2 / 4) • SStar)
    (htrGap : Matrix.trace ((S - SStar) * SStar⁻¹) ≤ eps)
    (htrSkew : Matrix.trace (κ * SStar⁻¹ * κ * SStar⁻¹) ≤
      (d : ℝ) * eps ^ 2 / 4)
    (e : Vec d) (he : e ⬝ᵥ e = 1)
    (hb : (S + κ * SStar⁻¹ * κ).PosDef)
    (hbStar : SStar ≤ (S + κ * SStar⁻¹ * κ))
    (hm : (matGeomMean (S + κ * SStar⁻¹ * κ) SStar).PosDef)
    (hStarInvHerm : (SStar⁻¹)ᴴ = SStar⁻¹)
    (hBge : (1 : Mat d) ≤ (calibrationB (S + κ * SStar⁻¹ * κ) SStar))
    (hBinvle : (calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ ≤ (1 : Mat d))
    : ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar) *ᵥ e) = 1) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) = e ⬝ᵥ (calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
      e) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) = e ⬝ᵥ (calibrationB (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤ 1) ∧
    (0 ≤ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ∧
    (∀ x : Vec d, x ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ x =
      (κ *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ x)) ∧
    (∀ x y : Vec d, x ⬝ᵥ SStar⁻¹ *ᵥ y = y ⬝ᵥ SStar⁻¹ *ᵥ x) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (S - SStar) *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤ eps * ((matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹
      *ᵥ e))) ∧
    (0 ≤ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (S - SStar) *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ∧
    (((κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ≤ eps ^ 2 / 4 * ((matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ∧
    (0 ≤ ((κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))) ∧
    (((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1).PosSemidef) ∧
    (e ⬝ᵥ ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) *ᵥ e = ((matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ
      e)) - 1) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) = (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
      e) ⬝ᵥ (S + κ * SStar⁻¹ * κ) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ∧
    ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (S + κ * SStar⁻¹ * κ) *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) = ((matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹
      *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (S - SStar) *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((κ *ᵥ (matSqrt (matGeomMean (S
      + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)))) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) ≤ 1 + eps + eps ^ 2 / 4) ∧
    (Matrix.trace ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) ≤ eps + (d : ℝ) * eps ^ 2 / 4)
    := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set B : Mat d := calibrationB b SStar with hBdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set gp : ℝ := p ⬝ᵥ (S - SStar) *ᵥ p with hgp
  set Rk : ℝ := (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) with hRkdef
  have hpair : p ⬝ᵥ r = 1 := by
    rw [hpdef, hrdef, calibration_pair hb hStar e, he]
  have ha1B : a1 = e ⬝ᵥ B⁻¹ *ᵥ e := by
    rw [ha1, hpdef, hBdef]
    exact calibration_energy_p hb hStar e
  have ha2B : a2 = e ⬝ᵥ B *ᵥ e := by
    rw [ha2, hrdef, hBdef]
    exact calibration_energy_r hb hStar e
  have ha1le : a1 ≤ 1 := by
    rw [ha1B]
    have h := Initialization.dotProduct_mulVec_le_of_le hBinvle e
    rwa [Matrix.one_mulVec, he] at h
  have ha1nn : 0 ≤ a1 := by
    rw [ha1]
    have := hStar.posSemidef.dotProduct_mulVec_nonneg p
    simpa using this
  -- transports for the skew quadratic at `p`
  have hkq : ∀ x : Vec d, x ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ x =
      (κ *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ x) := by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← mulVec_dotProduct_symm hκ]
  have hMswap : ∀ x y : Vec d, x ⬝ᵥ SStar⁻¹ *ᵥ y = y ⬝ᵥ SStar⁻¹ *ᵥ x := by
    intro x y
    rw [dotProduct_comm]
    exact mulVec_dotProduct_symm hStarInvHerm y x
  -- gap and skew bounds at the loads
  have hgapP : gp ≤ eps * a1 := by
    rw [hgp]
    have h := Initialization.dotProduct_mulVec_le_of_le hgapM p
    rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← ha1] at h
  have hgapNN : 0 ≤ gp := by
    rw [hgp]
    have hpsd : (S - SStar).PosSemidef := Matrix.le_iff.mp horder
    have := hpsd.dotProduct_mulVec_nonneg p
    simpa using this
  have hRkle : Rk ≤ eps ^ 2 / 4 * a1 := by
    rw [hRkdef, ← hkq]
    have h := Initialization.dotProduct_mulVec_le_of_le hskewM p
    rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← ha1] at h
  have hRkNN : 0 ≤ Rk := by
    rw [hRkdef]
    have := hStar.inv.posSemidef.dotProduct_mulVec_nonneg (κ *ᵥ p)
    simpa using this
  -- the calibration defect `T = B − 1`
  set T : Mat d := B - 1 with hTdef
  have hTpsd : T.PosSemidef := by
    rw [hTdef]
    exact Matrix.le_iff.mp hBge
  have heTe : e ⬝ᵥ T *ᵥ e = a2 - 1 := by
    rw [hTdef, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, he,
      ← ha2B]
  -- `e·Be = p·bp`, hence the bound on `a2`
  have ha2b : a2 = p ⬝ᵥ b *ᵥ p := by
    rw [ha2B, hBdef, calibrationB]
    have hherm : (matSqrt (matGeomMean b SStar)⁻¹)ᴴ =
        matSqrt (matGeomMean b SStar)⁻¹ :=
      conjTranspose_matSqrt hm.inv.posSemidef
    have hquad := Initialization.quad_conj (matSqrt (matGeomMean b SStar)⁻¹) b e
    rw [hherm] at hquad
    rw [hquad, ← hpdef]
  have hbp : p ⬝ᵥ b *ᵥ p = a1 + gp + Rk := by
    rw [hbdef, Matrix.add_mulVec, dotProduct_add, hkq, ← hRkdef]
    have hsplit : p ⬝ᵥ S *ᵥ p = a1 + gp := by
      rw [ha1, hgp, Matrix.sub_mulVec, dotProduct_sub]
      ring
    rw [hsplit]
  have ha2le : a2 ≤ 1 + eps + eps ^ 2 / 4 := by
    rw [ha2b, hbp]
    have h1 : gp ≤ eps := le_trans hgapP
      (by nlinarith only [ha1le, heps0])
    have h2 : Rk ≤ eps ^ 2 / 4 := le_trans hRkle
      (by nlinarith only [ha1le, heps0])
    linarith only [ha1le, h1, h2]
  -- the trace of the calibration defect
  have htrT : Matrix.trace T ≤ eps + (d : ℝ) * eps ^ 2 / 4 := by
    have htrB : Matrix.trace B =
        Matrix.trace (b * (matGeomMean b SStar)⁻¹) := by
      rw [hBdef, calibrationB, Matrix.trace_mul_cycle]
      rw [show matSqrt (matGeomMean b SStar)⁻¹ *
            matSqrt (matGeomMean b SStar)⁻¹ * b =
            (matGeomMean b SStar)⁻¹ * b from by
          rw [(matSqrt_spec hm.inv.posSemidef).2]]
      rw [Matrix.trace_mul_comm]
    have hminv : (matGeomMean b SStar)⁻¹ ≤ SStar⁻¹ :=
      HCPolySupport.HighContrast.inv_le_inv_of_le hStar hm
        (sStar_le_metric hb hStar hbStar)
    have hmono : Matrix.trace (b * (matGeomMean b SStar)⁻¹) ≤
        Matrix.trace (b * SStar⁻¹) :=
      PortableHistory.trace_mul_le_trace_mul hb.posSemidef hminv
    have hone : Matrix.trace ((SStar : Mat d) * SStar⁻¹) = (d : ℝ) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
        Matrix.trace_one]
      simp [Fintype.card_fin]
    have hsplitS : S * SStar⁻¹ =
        SStar * SStar⁻¹ + (S - SStar) * SStar⁻¹ := by
      rw [← Matrix.add_mul]
      congr 1
      abel
    have hbtrace : Matrix.trace (b * SStar⁻¹) =
        (d : ℝ) + Matrix.trace ((S - SStar) * SStar⁻¹) +
          Matrix.trace (κ * SStar⁻¹ * κ * SStar⁻¹) := by
      rw [hbdef, Matrix.add_mul, Matrix.trace_add, hsplitS,
        Matrix.trace_add, hone]
    have htrTB : Matrix.trace T = Matrix.trace B - (d : ℝ) := by
      rw [hTdef, Matrix.trace_sub, Matrix.trace_one]
      simp [Fintype.card_fin]
    have hchain := le_trans hmono (le_of_eq hbtrace)
    rw [htrTB, htrB]
    linarith only [hchain, htrGap, htrSkew]
  exact ⟨hpair, ha1B, ha2B, ha1le, ha1nn, hkq, hMswap, hgapP, hgapNN, hRkle, hRkNN, hTpsd, heTe,
    ha2b, hbp, ha2le, htrT⟩

private theorem squared_gap_matrix_bound
    {S SStar : Mat d} (hStar : SStar.PosDef)
    {eps : ℝ} (heps0 : 0 ≤ eps)
    (horder : SStar ≤ S)
    (hgapM : S - SStar ≤ eps • SStar)
    : ((S - SStar) * SStar⁻¹ * (S - SStar) ≤ (eps ^ 2) • SStar) := by
  classical
  have hΔ2 : (S - SStar) * SStar⁻¹ * (S - SStar) ≤ (eps ^ 2) • SStar := by
    set C : Mat d := matSqrt SStar⁻¹ with hCdef
    have hCherm : Cᴴ = C := conjTranspose_matSqrt hStar.inv.posSemidef
    have hCC : C * C = SStar⁻¹ := (matSqrt_spec hStar.inv.posSemidef).2
    have hC1 : C * SStar * C = 1 := by
      rw [hCdef]
      exact matSqrt_inv_conj_self hStar
    set D : Mat d := matSqrt SStar with hDdef
    have hDherm : Dᴴ = D := conjTranspose_matSqrt hStar.posSemidef
    have hDC : D * C = 1 := by
      rw [hDdef, hCdef]
      exact matSqrt_mul_matSqrt_inv hStar
    have hCD : C * D = 1 := by
      rw [hDdef, hCdef]
      exact matSqrt_inv_mul_matSqrt hStar
    have hT'le : Cᴴ * (S - SStar) * C ≤ Cᴴ * (eps • SStar) * C :=
      conj_le_conj C hgapM
    have hT'le' : C * (S - SStar) * C ≤ eps • (1 : Mat d) := by
      rw [hCherm] at hT'le
      calc
        C * (S - SStar) * C ≤ C * (eps • SStar) * C := hT'le
        _ = eps • (C * SStar * C) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = eps • (1 : Mat d) := by rw [hC1]
    have hT'psd : (C * (S - SStar) * C).PosSemidef := by
      have hΔpsd : (S - SStar).PosSemidef := Matrix.le_iff.mp horder
      have h := hΔpsd.conjTranspose_mul_mul_same C
      rwa [hCherm] at h
    have hsq := psd_sq_le_smul hT'psd hT'le'
    have hsqEq : (C * (S - SStar) * C) * (C * (S - SStar) * C) =
        C * ((S - SStar) * SStar⁻¹ * (S - SStar)) * C := by
      calc
        (C * (S - SStar) * C) * (C * (S - SStar) * C) =
            C * (S - SStar) * (C * C) * (S - SStar) * C := by
          noncomm_ring
        _ = C * ((S - SStar) * SStar⁻¹ * (S - SStar)) * C := by
          rw [hCC]
          noncomm_ring
    rw [hsqEq] at hsq
    have hconjD := conj_le_conj D hsq
    rw [hDherm] at hconjD
    have hleft : D * (C * ((S - SStar) * SStar⁻¹ * (S - SStar)) * C) * D =
        (S - SStar) * SStar⁻¹ * (S - SStar) := by
      calc
        D * (C * ((S - SStar) * SStar⁻¹ * (S - SStar)) * C) * D =
            (D * C) * ((S - SStar) * SStar⁻¹ * (S - SStar)) * (C * D) := by
          noncomm_ring
        _ = (S - SStar) * SStar⁻¹ * (S - SStar) := by
          rw [hDC, hCD, Matrix.one_mul, Matrix.mul_one]
    have hright : D * (eps • (C * (S - SStar) * C)) * D =
        eps • (S - SStar) := by
      calc
        D * (eps • (C * (S - SStar) * C)) * D =
            eps • (D * (C * (S - SStar) * C) * D) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = eps • ((D * C) * (S - SStar) * (C * D)) := by
          congr 1
          noncomm_ring
        _ = eps • (S - SStar) := by
          rw [hDC, hCD, Matrix.one_mul, Matrix.mul_one]
    rw [hleft, hright] at hconjD
    calc
      (S - SStar) * SStar⁻¹ * (S - SStar) ≤ eps • (S - SStar) := hconjD
      _ ≤ eps • (eps • SStar) := by
        exact smul_le_smul_of_nonneg_left hgapM heps0
      _ = (eps ^ 2) • SStar := by
        rw [smul_smul]
        ring_nf
  exact hΔ2

private theorem calibration_bracket_quadratic_bound
    {S SStar κ : Mat d}
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (e : Vec d) (he : e ⬝ᵥ e = 1)
    (hBpd : (calibrationB (S + κ * SStar⁻¹ * κ) SStar).PosDef)
    (hBinvle : (calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ ≤ (1 : Mat d))
    (hpair : (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S
      + κ * SStar⁻¹ * κ) SStar) *ᵥ e) = 1)
    (ha1B : ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) = e ⬝ᵥ (calibrationB (S + κ * SStar⁻¹ * κ)
      SStar)⁻¹ *ᵥ e)
    (ha2B : ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) = e ⬝ᵥ (calibrationB (S + κ * SStar⁻¹ * κ)
      SStar) *ᵥ e)
    (hTpsd : ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1).PosSemidef)
    (heTe : e ⬝ᵥ ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) *ᵥ e = ((matSqrt (matGeomMean (S
      + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ)
      SStar) *ᵥ e)) - 1)
    (ha2le : ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) ≤ 1 + eps + eps ^ 2 / 4)
    (htrT : Matrix.trace ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) ≤ eps + (d : ℝ) * eps ^ 2
      / 4)
    : ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) * (calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ =
      1) ∧
    ((calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ * (calibrationB (S + κ * SStar⁻¹ * κ) SStar) = 1)
      ∧
    (((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) * (calibrationB (S + κ * SStar⁻¹ * κ)
      SStar)⁻¹ * ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) = (calibrationB (S + κ * SStar⁻¹
      * κ) SStar) + (calibrationB (S + κ * SStar⁻¹ * κ) SStar)⁻¹ - (2 : ℝ) • (1 : Mat d)) ∧
    ((((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)
      *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2 * ((matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ *
      κ) SStar) *ᵥ e))) = (((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) *ᵥ e) ⬝ᵥ (calibrationB
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ (((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) *ᵥ e)) ∧
    (0 ≤ (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2
      * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar) *ᵥ e)))) ∧
    ((((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)
      *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2 * ((matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ *
      κ) SStar) *ᵥ e))) ≤ Matrix.trace ((calibrationB (S + κ * SStar⁻¹ * κ) SStar) - 1) *
      (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 1)) ∧
    ((((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)
      *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2 * ((matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ *
      κ) SStar) *ᵥ e))) ≤ 2 * (1 + (d : ℝ)) * eps ^ 2) := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set B : Mat d := calibrationB b SStar with hBdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set T : Mat d := B - 1 with hTdef
  set bracket : ℝ := a1 + a2 - 2 * (p ⬝ᵥ r) with hbracketdef
  have hB1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hBpd)
  have hB2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hBpd)
  have hfact : T * B⁻¹ * T = B + B⁻¹ - (2 : ℝ) • (1 : Mat d) := by
    have htwo : (2 : ℝ) • (1 : Mat d) = 1 + 1 := by
      rw [two_smul]
    rw [hTdef, htwo]
    calc
      (B - 1) * B⁻¹ * (B - 1) = (B * B⁻¹ - 1 * B⁻¹) * (B - 1) := by
        rw [Matrix.sub_mul]
      _ = (1 - B⁻¹) * (B - 1) := by
        rw [hB1, Matrix.one_mul]
      _ = 1 * B - 1 * 1 - (B⁻¹ * B - B⁻¹ * 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      _ = B + B⁻¹ - (1 + 1) := by
        rw [hB2, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
        abel
  have hbracketEq : bracket = (T *ᵥ e) ⬝ᵥ B⁻¹ *ᵥ (T *ᵥ e) := by
    have hquad := Initialization.quad_conj T B⁻¹ e
    rw [hTpsd.isHermitian.eq] at hquad
    rw [← hquad, hfact, hbracketdef, hpair, ha1B, ha2B]
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, he,
      smul_eq_mul]
    ring
  have hbracketNN : 0 ≤ bracket := by
    rw [hbracketEq]
    have := hBpd.inv.posSemidef.dotProduct_mulVec_nonneg (T *ᵥ e)
    simpa using this
  have hbracket_le : bracket ≤ Matrix.trace T * (a2 - 1) := by
    have hstep1 : (T *ᵥ e) ⬝ᵥ B⁻¹ *ᵥ (T *ᵥ e) ≤ (T *ᵥ e) ⬝ᵥ (T *ᵥ e) := by
      have h := Initialization.dotProduct_mulVec_le_of_le hBinvle (T *ᵥ e)
      rwa [Matrix.one_mulVec] at h
    have hstep2 : (T *ᵥ e) ⬝ᵥ (T *ᵥ e) = e ⬝ᵥ (T * T) *ᵥ e := by
      rw [mulVec_dotProduct_symm hTpsd.isHermitian.eq,
        Matrix.mulVec_mulVec]
    have hTle : T ≤ Matrix.trace T • (1 : Mat d) :=
      psd_le_smul_one hTpsd fun x => psd_quad_le_trace hTpsd x
    have hstep3 : e ⬝ᵥ (T * T) *ᵥ e ≤ Matrix.trace T * (e ⬝ᵥ T *ᵥ e) := by
      have h := Initialization.dotProduct_mulVec_le_of_le
        (psd_sq_le_smul hTpsd hTle) e
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    rw [hbracketEq, ← heTe]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  have hbracket_eps : bracket ≤ 2 * (1 + (d : ℝ)) * eps ^ 2 := by
    have heTele : a2 - 1 ≤ eps + eps ^ 2 / 4 := by linarith only [ha2le]
    have heTenn : 0 ≤ a2 - 1 := by
      rw [← heTe]
      have := hTpsd.dotProduct_mulVec_nonneg e
      simpa using this
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hchain := le_trans hbracket_le
      (mul_le_mul htrT heTele heTenn
        (by nlinarith only [heps0, hd0, sq_nonneg eps]))
    have hle1 : 0 ≤ 1 - eps := by linarith only [heps1]
    have h3 : 0 ≤ eps ^ 2 * (1 - eps) := mul_nonneg (sq_nonneg eps) hle1
    have h4 : 0 ≤ eps ^ 3 * (1 - eps) :=
      mul_nonneg (pow_nonneg heps0 3) hle1
    have hd3 : 0 ≤ (d : ℝ) * (eps ^ 2 * (1 - eps)) := mul_nonneg hd0 h3
    have hd4 : 0 ≤ (d : ℝ) * (eps ^ 3 * (1 - eps)) := mul_nonneg hd0 h4
    nlinarith only [hchain, h3, h4, hd3, hd4, heps0, hd0, sq_nonneg eps]
  -- the deviation quadratic
  exact ⟨hB1, hB2, hfact, hbracketEq, hbracketNN, hbracket_le, hbracket_eps⟩

private theorem centering_gap_and_skew_pairing_bounds
    {S SStar κ : Mat d} (hStar : SStar.PosDef)
    {eps : ℝ} (heps0 : 0 ≤ eps)
    (hskewM : κ * SStar⁻¹ * κ ≤ (eps ^ 2 / 4) • SStar)
    (e : Vec d)
    (hStarInvHerm : (SStar⁻¹)ᴴ = SStar⁻¹)
    (hδqNN : 0 ≤ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) -
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))
    (hΔp2 : ((S - SStar) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹
      *ᵥ ((S - SStar) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤
      eps ^ 2 * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
        (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))
    (hkq : ∀ x : Vec d, x ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ x =
      (κ *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ x))
    : (|(((S - SStar) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ ((SStar⁻¹
      *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S
      + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
      e)))| ≤ eps ^ 2 / 2 * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + (1 / 2) * (((SStar⁻¹ *ᵥ
      ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))
      ⬝ᵥ SStar *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))) ∧
    (|(((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ κ *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)
      *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))| ≤ eps / 2 * (((SStar⁻¹ *ᵥ ((matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar
      *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)))) := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set W : Vec d := r + κ *ᵥ p with hWdef
  set u : Vec d := SStar⁻¹ *ᵥ W with hudef
  set δ : Vec d := u - p with hδdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set A5 : ℝ := ((S - SStar) *ᵥ p) ⬝ᵥ δ with hA5
  set A6 : ℝ := δ ⬝ᵥ κ *ᵥ δ with hA6
  have hA5abs : |A5| ≤ eps ^ 2 / 2 * a1 + (1 / 2) * (δ ⬝ᵥ SStar *ᵥ δ) := by
    have hcanδ : SStar⁻¹ *ᵥ (SStar *ᵥ δ) = δ := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    have hcross : (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p)) ⬝ᵥ SStar *ᵥ δ = A5 := by
      rw [mulVec_dotProduct_symm hStarInvHerm, hcanδ, hA5]
    have hcancel : SStar *ᵥ (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p)) =
        (S - SStar) *ᵥ p := by
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    have hself : (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p)) ⬝ᵥ SStar *ᵥ
        (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p)) =
        ((S - SStar) *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) := by
      rw [hcancel, mulVec_dotProduct_symm hStarInvHerm]
    have hcrossδ : δ ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p)) =
        A5 := by
      rw [hcancel, hA5, dotProduct_comm]
    have hyoung : ∀ s : ℝ, s ^ 2 = 1 →
        2 * s * A5 ≤ ((S - SStar) *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) +
          δ ⬝ᵥ SStar *ᵥ δ := by
      intro s hs
      have hquad : 0 ≤ (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) - s • δ) ⬝ᵥ SStar *ᵥ
          (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) - s • δ) := by
        have := hStar.posSemidef.dotProduct_mulVec_nonneg
          (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) - s • δ)
        simpa using this
      have hexp : (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) - s • δ) ⬝ᵥ SStar *ᵥ
          (SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) - s • δ) =
          ((S - SStar) *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) -
            2 * s * A5 + s ^ 2 * (δ ⬝ᵥ SStar *ᵥ δ) := by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
          sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [hself, hcross, hcrossδ]
        ring
      rw [hexp, hs, one_mul] at hquad
      linarith only [hquad]
    have hplus := hyoung 1 (by norm_num)
    have hminus := hyoung (-1) (by norm_num)
    rw [abs_le]
    constructor
    · nlinarith only [hminus, hΔp2]
    · nlinarith only [hplus, hΔp2]
  -- the skew-pairing bound
  have hA6abs : |A6| ≤ eps / 2 * (δ ⬝ᵥ SStar *ᵥ δ) := by
    have hcs := dotProduct_sq_le_quad_mul_quad hStar δ (κ *ᵥ δ)
    have hκδ : (κ *ᵥ δ) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ δ) ≤
        eps ^ 2 / 4 * (δ ⬝ᵥ SStar *ᵥ δ) := by
      rw [← hkq δ]
      have h := Initialization.dotProduct_mulVec_le_of_le hskewM δ
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    have hA6sq : A6 ^ 2 ≤ (eps / 2 * (δ ⬝ᵥ SStar *ᵥ δ)) ^ 2 := by
      have hδκ : δ ⬝ᵥ (κ *ᵥ δ) = A6 := by rw [hA6]
      have h1 : A6 ^ 2 ≤ (δ ⬝ᵥ SStar *ᵥ δ) *
          ((κ *ᵥ δ) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ δ)) := by
        rw [← hδκ]
        exact hcs
      nlinarith only [h1, mul_le_mul_of_nonneg_left hκδ hδqNN, hδqNN,
        sq_nonneg (δ ⬝ᵥ SStar *ᵥ δ), heps0]
    have habs := Real.sqrt_le_sqrt hA6sq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq
      (by positivity : (0 : ℝ) ≤ eps / 2 * (δ ⬝ᵥ SStar *ᵥ δ))] at habs
  -- the closed-form identity
  exact ⟨hA5abs, hA6abs⟩

private theorem calibrated_deviation_quadratic_bound
    {S SStar κ : Mat d} (hStar : SStar.PosDef)
    (e : Vec d)
    (hStarInvHerm : (SStar⁻¹)ᴴ = SStar⁻¹)
    : (SStar *ᵥ (SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) = ((matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
      e))) ∧
    (((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)) = (SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) -
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + SStar⁻¹ *ᵥ (κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ∧
    ((SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) - (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar) *ᵥ e) - (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) =
      (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2
      * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar) *ᵥ e)))) ∧
    ((SStar⁻¹ *ᵥ (κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ⬝ᵥ SStar *ᵥ
      (SStar⁻¹ *ᵥ (κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) =
      ((κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ
        (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))) ∧
    (((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ)
      SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤ 2 * (((matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹
      *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2 * ((matSqrt (matGeomMean (S + κ *
      SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e))) + 2
      * ((κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))) ∧
    (0 ≤ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) + κ *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar *ᵥ ((SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ)
      SStar) *ᵥ e) + κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) - (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set W : Vec d := r + κ *ᵥ p with hWdef
  set u : Vec d := SStar⁻¹ *ᵥ W with hudef
  set δ : Vec d := u - p with hδdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set Rk : ℝ := (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) with hRkdef
  set bracket : ℝ := a1 + a2 - 2 * (p ⬝ᵥ r) with hbracketdef
  have hSu : SStar *ᵥ u = W := by
    rw [hudef, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
      Matrix.one_mulVec]
  have hδsplit : δ = (SStar⁻¹ *ᵥ r - p) + SStar⁻¹ *ᵥ (κ *ᵥ p) := by
    rw [hδdef, hudef, hWdef, Matrix.mulVec_add]
    abel
  have hvq : (SStar⁻¹ *ᵥ r - p) ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ r - p) = bracket := by
    have hcancel : SStar *ᵥ (SStar⁻¹ *ᵥ r) = r := by
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    have hcross : (SStar⁻¹ *ᵥ r) ⬝ᵥ SStar *ᵥ p = p ⬝ᵥ r := by
      rw [mulVec_dotProduct_symm hStarInvHerm, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec, dotProduct_comm]
    have hself : (SStar⁻¹ *ᵥ r) ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ r) = a2 := by
      rw [hcancel, mulVec_dotProduct_symm hStarInvHerm, ← ha2]
    have hcross₂ : p ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ r) = p ⬝ᵥ r := by
      rw [hcancel]
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hself, hcross, hcross₂, ← ha1, hbracketdef]
    ring
  have hzq : (SStar⁻¹ *ᵥ (κ *ᵥ p)) ⬝ᵥ SStar *ᵥ (SStar⁻¹ *ᵥ (κ *ᵥ p)) =
      Rk := by
    have hcancel : SStar *ᵥ (SStar⁻¹ *ᵥ (κ *ᵥ p)) = κ *ᵥ p := by
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    rw [hcancel, mulVec_dotProduct_symm hStarInvHerm, ← hRkdef]
  have hδq : δ ⬝ᵥ SStar *ᵥ δ ≤ 2 * bracket + 2 * Rk := by
    rw [hδsplit]
    have h := quad_add_le hStar.posSemidef (SStar⁻¹ *ᵥ r - p)
      (SStar⁻¹ *ᵥ (κ *ᵥ p))
    rwa [hvq, hzq] at h
  have hδqNN : 0 ≤ δ ⬝ᵥ SStar *ᵥ δ := by
    have := hStar.posSemidef.dotProduct_mulVec_nonneg δ
    simpa using this
  -- the gap-pairing bound
  exact ⟨hSu, hδsplit, hvq, hzq, hδq, hδqNN⟩
/-- **The generic centering estimate.**  `κ` is the symmetric skew coordinate;
the primal pairing consumes it as stated and the adjoint pairing at `−κ`. -/
theorem centering_generic_estimate
    {S SStar κ : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hκ : κᴴ = κ)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (horder : SStar ≤ S)
    (hgapM : S - SStar ≤ eps • SStar)
    (hskewM : κ * SStar⁻¹ * κ ≤ (eps ^ 2 / 4) • SStar)
    (htrGap : Matrix.trace ((S - SStar) * SStar⁻¹) ≤ eps)
    (htrSkew : Matrix.trace (κ * SStar⁻¹ * κ * SStar⁻¹) ≤
      (d : ℝ) * eps ^ 2 / 4)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    |(matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ S *ᵥ
        (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
          κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ
        SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) -
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ
        (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) -
      (SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) ⬝ᵥ
        κ *ᵥ (SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e))) -
      (S *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ
        (SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))| ≤
      (6 * (d : ℝ) + 8) * eps ^ 2 := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  have hκpsd : (κ * SStar⁻¹ * κ).PosSemidef := by
    have h := hStar.inv.posSemidef.conjTranspose_mul_mul_same κ
    rwa [hκ] at h
  have hb : b.PosDef := hS.add_posSemidef hκpsd
  have hSb : S ≤ b := by
    refine Initialization.le_of_dotProduct_mulVec_le hS.isHermitian hb.isHermitian
      fun x => ?_
    rw [hbdef, Matrix.add_mulVec, dotProduct_add]
    have h := hκpsd.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at h
    linarith only [h]
  have hbStar : SStar ≤ b := le_trans horder hSb
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hStarInvHerm : (SStar⁻¹)ᴴ = SStar⁻¹ := hStar.inv.isHermitian
  have hStarHerm : SStarᴴ = SStar := hStar.isHermitian
  have hΔherm : (S - SStar)ᴴ = S - SStar := by
    rw [Matrix.conjTranspose_sub, hS.isHermitian.eq, hStarHerm]
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set W : Vec d := r + κ *ᵥ p with hWdef
  set u : Vec d := SStar⁻¹ *ᵥ W with hudef
  set δ : Vec d := u - p with hδdef
  set B : Mat d := calibrationB b SStar with hBdef
  have hBpd : B.PosDef := calibrationB_posDef hb hStar
  have hBge : (1 : Mat d) ≤ B := one_le_calibrationB hb hStar hbStar
  have hBinvle : B⁻¹ ≤ (1 : Mat d) := calibrationB_inv_le_one hb hStar hbStar
  -- scalar abbreviations
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set gp : ℝ := p ⬝ᵥ (S - SStar) *ᵥ p with hgp
  set Rk : ℝ := (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) with hRkdef
  set g1 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) with hg1
  set A5 : ℝ := ((S - SStar) *ᵥ p) ⬝ᵥ δ with hA5
  set A6 : ℝ := δ ⬝ᵥ κ *ᵥ δ with hA6
  set T : Mat d := B - 1 with hTdef
  obtain ⟨hpair, ha1B, ha2B, ha1le, ha1nn, hkq, hMswap, hgapP, hgapNN, hRkle, hRkNN, hTpsd, heTe,
    ha2b, hbp, ha2le, htrT⟩ :=
    calibration_load_and_trace_bounds hStar hκ heps0
      horder hgapM hskewM htrGap htrSkew e he hb hbStar hm hStarInvHerm hBge hBinvle
  have htrTNN : 0 ≤ Matrix.trace T := hTpsd.trace_nonneg
  -- the bracket
  set bracket : ℝ := a1 + a2 - 2 * (p ⬝ᵥ r) with hbracketdef
  obtain ⟨hB1, hB2, hfact, hbracketEq, hbracketNN, hbracket_le, hbracket_eps⟩ :=
    calibration_bracket_quadratic_bound heps0 heps1
      e he hBpd hBinvle hpair ha1B ha2B hTpsd heTe ha2le htrT
  obtain ⟨hSu, hδsplit, hvq, hzq, hδq, hδqNN⟩ :=
    calibrated_deviation_quadratic_bound hStar e hStarInvHerm
  have hΔ2 :=
    squared_gap_matrix_bound hStar heps0 horder hgapM
  have hΔp2 : ((S - SStar) *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) ≤
      eps ^ 2 * a1 := by
    have htrans : ((S - SStar) *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ ((S - SStar) *ᵥ p) =
        p ⬝ᵥ ((S - SStar) * SStar⁻¹ * (S - SStar)) *ᵥ p := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← mulVec_dotProduct_symm hΔherm]
    have h := Initialization.dotProduct_mulVec_le_of_le hΔ2 p
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← ha1] at h
    rw [htrans]
    exact h
  obtain ⟨hA5abs, hA6abs⟩ :=
    centering_gap_and_skew_pairing_bounds hStar
      heps0 hskewM e hStarInvHerm hδqNN hΔp2 hkq
  set CF : ℝ := p ⬝ᵥ S *ᵥ p + W ⬝ᵥ SStar⁻¹ *ᵥ W - p ⬝ᵥ r -
      u ⬝ᵥ κ *ᵥ u - (S *ᵥ p) ⬝ᵥ u with hCFdef
  have hWq : W ⬝ᵥ SStar⁻¹ *ᵥ W = a2 + 2 * g1 + Rk := by
    have hswapg : (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ r = g1 := by
      rw [hg1]
      exact hMswap _ _
    rw [hWdef]
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [← ha2, ← hg1, ← hRkdef, hswapg]
    ring
  have hSp_split : p ⬝ᵥ S *ᵥ p = a1 + gp := by
    rw [ha1, hgp, Matrix.sub_mulVec, dotProduct_sub]
    ring
  have hpu : p ⬝ᵥ κ *ᵥ u = g1 + Rk := by
    have h1 : p ⬝ᵥ κ *ᵥ u = (κ *ᵥ p) ⬝ᵥ u := by
      rw [← mulVec_dotProduct_symm hκ]
    have h2 : (κ *ᵥ p) ⬝ᵥ u = (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ r +
        (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) := by
      rw [hudef, hWdef, Matrix.mulVec_add, dotProduct_add]
    have hswapg : (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ r = g1 := by
      rw [hg1]
      exact hMswap _ _
    rw [h1, h2, hswapg, ← hRkdef]
  have huκu : u ⬝ᵥ κ *ᵥ u = A6 + 2 * (g1 + Rk) - p ⬝ᵥ κ *ᵥ p := by
    have hδexp : A6 = u ⬝ᵥ κ *ᵥ u - 2 * (p ⬝ᵥ κ *ᵥ u) +
        p ⬝ᵥ κ *ᵥ p := by
      have hswapu : u ⬝ᵥ κ *ᵥ p = p ⬝ᵥ κ *ᵥ u := by
        rw [← mulVec_dotProduct_symm hκ, dotProduct_comm]
      rw [hA6, hδdef]
      simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
      rw [hswapu]
      ring
    rw [hδexp, hpu]
    ring
  have hSpu : (S *ᵥ p) ⬝ᵥ u = p ⬝ᵥ r + p ⬝ᵥ κ *ᵥ p + gp + A5 := by
    have hsplit : (S *ᵥ p) ⬝ᵥ u = (SStar *ᵥ p) ⬝ᵥ u +
        ((S - SStar) *ᵥ p) ⬝ᵥ u := by
      rw [← add_dotProduct, ← Matrix.add_mulVec]
      congr 2
      abel
    have hfirst : (SStar *ᵥ p) ⬝ᵥ u = p ⬝ᵥ r + p ⬝ᵥ κ *ᵥ p := by
      rw [mulVec_dotProduct_symm hStarHerm, hSu, dotProduct_add]
    have hsecond : ((S - SStar) *ᵥ p) ⬝ᵥ u = gp + A5 := by
      have hup : ((S - SStar) *ᵥ p) ⬝ᵥ p = gp := by
        rw [hgp, dotProduct_comm]
      have hδu : ((S - SStar) *ᵥ p) ⬝ᵥ u =
          ((S - SStar) *ᵥ p) ⬝ᵥ p + ((S - SStar) *ᵥ p) ⬝ᵥ δ := by
        rw [hδdef, dotProduct_sub]
        ring
      rw [hδu, hup, ← hA5]
    rw [hsplit, hfirst, hsecond]
    ring
  have hCFeq : CF = bracket - Rk - A5 - A6 := by
    rw [hCFdef, hWq, hSp_split, huκu, hSpu, hbracketdef]
    ring
  -- final assembly
  have hRkle' : Rk ≤ eps ^ 2 / 4 := le_trans hRkle
    (by nlinarith only [ha1le, heps0])
  have hδqle : δ ⬝ᵥ SStar *ᵥ δ ≤ 2 * bracket + 2 * Rk := hδq
  have hA5le : |A5| ≤ eps ^ 2 / 2 + bracket + Rk := by
    have h1 : eps ^ 2 / 2 * a1 ≤ eps ^ 2 / 2 := by
      nlinarith only [ha1le, heps0, ha1nn]
    calc
      |A5| ≤ eps ^ 2 / 2 * a1 + (1 / 2) * (δ ⬝ᵥ SStar *ᵥ δ) := hA5abs
      _ ≤ eps ^ 2 / 2 + (1 / 2) * (2 * bracket + 2 * Rk) := by
        have := mul_le_mul_of_nonneg_left hδqle
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith only [h1, this]
      _ = eps ^ 2 / 2 + bracket + Rk := by ring
  have hA6le : |A6| ≤ bracket + Rk := by
    calc
      |A6| ≤ eps / 2 * (δ ⬝ᵥ SStar *ᵥ δ) := hA6abs
      _ ≤ eps / 2 * (2 * bracket + 2 * Rk) :=
        mul_le_mul_of_nonneg_left hδqle (by positivity)
      _ ≤ bracket + Rk := by
        nlinarith only [heps1, heps0, hbracketNN, hRkNN]
  have hCFabs : |CF| ≤ 3 * bracket + 3 * Rk + eps ^ 2 / 2 := by
    rw [hCFeq]
    have h1 : |bracket - Rk - A5 - A6| ≤ bracket + Rk + |A5| + |A6| := by
      rw [abs_le]
      constructor
      · nlinarith only [hbracketNN, hRkNN, le_abs_self A5, le_abs_self A6,
          neg_abs_le A5, neg_abs_le A6]
      · nlinarith only [hbracketNN, hRkNN, le_abs_self A5, le_abs_self A6,
          neg_abs_le A5, neg_abs_le A6]
    calc
      |bracket - Rk - A5 - A6| ≤ bracket + Rk + |A5| + |A6| := h1
      _ ≤ 3 * bracket + 3 * Rk + eps ^ 2 / 2 := by
        linarith only [hA5le, hA6le]
  have hfinal : |CF| ≤ (6 * (d : ℝ) + 8) * eps ^ 2 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    calc
      |CF| ≤ 3 * bracket + 3 * Rk + eps ^ 2 / 2 := hCFabs
      _ ≤ 3 * (2 * (1 + (d : ℝ)) * eps ^ 2) + 3 * (eps ^ 2 / 4) +
          eps ^ 2 / 2 := by
        linarith only [hbracket_eps, hRkle']
      _ ≤ (6 * (d : ℝ) + 8) * eps ^ 2 := by
        nlinarith only [heps0, hd0, sq_nonneg eps]
  -- the goal is `|CF|` after folding the abbreviations
  exact hfinal

end

end HCPolySupport.HighContrast.Quenched
