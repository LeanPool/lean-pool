/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringEstimate

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenterMagnitude

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The center magnitudes

Both components of the annealed center at the calibrated loads — the closed
Schur forms of the annealed mean gradient and mean flux — are second order
in the smallness parameter: the mean gradient is the deviation vector `δ` of
the centering estimate, and the mean flux is the calibration bracket
deviation plus a skew-small correction.  This is the printed
`|M₀^{1/2}𝔼[(∇v)_{□}]|² ≤ C(Θ̂−1)²` display, feeding the row cap at the
profile centers.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem quad_add_le' {M : Mat d} (hM : M.PosSemidef) (x y : Vec d) :
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

private theorem calibrated_flux_gap_quadratic_bound
    {S SStar κ : Mat d} (hStar : SStar.PosDef)
    {eps : ℝ}
    (e : Vec d)
    (hStarHerm : SStarᴴ = SStar)
    (hΔp2 : ((S - SStar) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹
      *ᵥ ((S - SStar) *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤
      eps ^ 2 * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
        (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)))
    : (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) - SStar *ᵥ (matSqrt (matGeomMean
      (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ *
      κ) SStar) *ᵥ e) - SStar *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) =
      (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
      (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ * SStar⁻¹
      * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e)) - 2
      * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar) *ᵥ e)))) ∧
    (∀ x y : Vec d,
      (x - y) ⬝ᵥ SStar⁻¹ *ᵥ (x - y) ≤
        2 * (x ⬝ᵥ SStar⁻¹ *ᵥ x) + 2 * (y ⬝ᵥ SStar⁻¹ *ᵥ y)) ∧
    (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) - S *ᵥ (matSqrt (matGeomMean (S + κ
      * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ SStar⁻¹ *ᵥ ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ)
      SStar) *ᵥ e) - S *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ≤
      2 * (((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt
        (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) + ((matSqrt (matGeomMean (S + κ *
        SStar⁻¹ * κ) SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)
        *ᵥ e)) - 2 * ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ (matSqrt
        (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e))) + 2 * (eps ^ 2 * ((matSqrt (matGeomMean
        (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ *
        κ) SStar)⁻¹ *ᵥ e)))) := by
  classical
  set b : Mat d := S + κ * SStar⁻¹ * κ with hbdef
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set bracket : ℝ := a1 + a2 - 2 * (p ⬝ᵥ r) with hbracketdef
  have hvq2 : (r - SStar *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r - SStar *ᵥ p) = bracket := by
    have hcancel : SStar⁻¹ *ᵥ (SStar *ᵥ p) = p := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hcancel]
    have h1 : (SStar *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ r = p ⬝ᵥ r := by
      rw [mulVec_dotProduct_symm hStarHerm, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
        Matrix.one_mulVec]
    have h2 : (SStar *ᵥ p) ⬝ᵥ p = a1 := by
      rw [mulVec_dotProduct_symm hStarHerm, ← ha1]
    have h3 : r ⬝ᵥ p = p ⬝ᵥ r := dotProduct_comm r p
    rw [h1, h2, h3, ← ha2, hbracketdef]
    ring
  have hquadsub : ∀ x y : Vec d,
      (x - y) ⬝ᵥ SStar⁻¹ *ᵥ (x - y) ≤
        2 * (x ⬝ᵥ SStar⁻¹ *ᵥ x) + 2 * (y ⬝ᵥ SStar⁻¹ *ᵥ y) := by
    intro x y
    have h := quad_add_le' hStar.inv.posSemidef x (-y)
    rw [show x + -y = x - y from by abel] at h
    have hneg : (-y) ⬝ᵥ SStar⁻¹ *ᵥ (-y) = y ⬝ᵥ SStar⁻¹ *ᵥ y := by
      rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
    rwa [hneg] at h
  have hqx : (r - S *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r - S *ᵥ p) ≤
      2 * bracket + 2 * (eps ^ 2 * a1) := by
    have hsplit : r - S *ᵥ p = (r - SStar *ᵥ p) - (S - SStar) *ᵥ p := by
      rw [Matrix.sub_mulVec]
      abel
    rw [hsplit]
    refine le_trans (hquadsub _ _) ?_
    rw [hvq2]
    linarith only [hΔp2]
  exact ⟨hvq2, hquadsub, hqx⟩
/-- **The center magnitudes.**  At the calibrated loads, both components of
the annealed center — the closed Schur forms of the mean gradient and mean
flux — are second order in `ε`, in the natural `σ*`-metrics. -/
theorem centering_center_quads_le
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
    ((-(matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
        SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
          κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
            e))) ⬝ᵥ
      SStar *ᵥ
        (-(matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
          SStar⁻¹ *ᵥ
            (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
              κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
                e))) ≤ 5 * (1 + (d : ℝ)) * eps ^ 2) ∧
    (((1 - κ * SStar⁻¹) *ᵥ
        (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) -
        (S + κ * SStar⁻¹ * κ) *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) ⬝ᵥ
      SStar⁻¹ *ᵥ
        ((1 - κ * SStar⁻¹) *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) -
          (S + κ * SStar⁻¹ * κ) *ᵥ
            (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
              e)) ≤ 24 * (1 + (d : ℝ)) * eps ^ 2) := by
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
    have h := quad_add_le' hStar.posSemidef (SStar⁻¹ *ᵥ r - p)
      (SStar⁻¹ *ᵥ (κ *ᵥ p))
    rwa [hvq, hzq] at h
  have hδqNN : 0 ≤ δ ⬝ᵥ SStar *ᵥ δ := by
    have := hStar.posSemidef.dotProduct_mulVec_nonneg δ
    simpa using this
  -- the gap-pairing bound
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
  -- the second center component in load form
  have hXm1 : -p + SStar⁻¹ *ᵥ W = δ := by
    rw [hδdef, hudef]
    abel
  have hmm1 : ∀ v : Vec d, (κ * SStar⁻¹) *ᵥ v = κ *ᵥ (SStar⁻¹ *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec]
  have hmm2 : ∀ v : Vec d,
      (κ * SStar⁻¹ * κ) *ᵥ v = κ *ᵥ (SStar⁻¹ *ᵥ (κ *ᵥ v)) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hXm2 : (1 - κ * SStar⁻¹) *ᵥ r - b *ᵥ p = (r - S *ᵥ p) - κ *ᵥ u := by
    rw [hudef, hWdef, hbdef]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
      hmm1 r, hmm2 p, Matrix.mulVec_add, Matrix.mulVec_add]
    abel
  -- the first conclusion
  have hconc1 : δ ⬝ᵥ SStar *ᵥ δ ≤ 5 * (1 + (d : ℝ)) * eps ^ 2 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h1 : Rk ≤ eps ^ 2 / 4 := by
      nlinarith only [hRkle, ha1le, heps0, sq_nonneg eps]
    nlinarith only [hδq, hbracket_eps, h1, hd0, sq_nonneg eps]
  -- the second conclusion
  obtain ⟨hvq2, hquadsub, hqx⟩ :=
    calibrated_flux_gap_quadratic_bound hStar e
      hStarHerm hΔp2
  have hutrans : u ⬝ᵥ SStar *ᵥ u = W ⬝ᵥ SStar⁻¹ *ᵥ W := by
    rw [hSu]
    rw [hudef, mulVec_dotProduct_symm hStarInvHerm]
  have hWq : W ⬝ᵥ SStar⁻¹ *ᵥ W ≤ 2 * a2 + 2 * Rk := by
    rw [hWdef]
    have h := quad_add_le' hStar.inv.posSemidef r (κ *ᵥ p)
    rwa [← ha2, ← hRkdef] at h
  have hqy : (κ *ᵥ u) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ u) ≤
      eps ^ 2 / 4 * (2 * a2 + 2 * Rk) := by
    have h1 : (κ *ᵥ u) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ u) =
        u ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ u := (hkq u).symm
    have h2 := Initialization.dotProduct_mulVec_le_of_le hskewM u
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h2
    rw [h1]
    refine le_trans h2 ?_
    rw [hutrans]
    have hnn : (0 : ℝ) ≤ eps ^ 2 / 4 := by positivity
    exact mul_le_mul_of_nonneg_left hWq hnn
  have hconc2 : ((r - S *ᵥ p) - κ *ᵥ u) ⬝ᵥ SStar⁻¹ *ᵥ
      ((r - S *ᵥ p) - κ *ᵥ u) ≤ 24 * (1 + (d : ℝ)) * eps ^ 2 := by
    refine le_trans (hquadsub _ _) ?_
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hRk1 : Rk ≤ eps ^ 2 / 4 := by
      nlinarith only [hRkle, ha1le, heps0, sq_nonneg eps]
    have ha2b1 : a2 ≤ 3 := by nlinarith only [ha2le, heps1, heps0]
    have hq1 : (r - S *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r - S *ᵥ p) ≤
        2 * bracket + 2 * eps ^ 2 := by
      refine le_trans hqx ?_
      have hprod : 0 ≤ eps ^ 2 * (1 - a1) :=
        mul_nonneg (sq_nonneg eps) (by linarith only [ha1le])
      nlinarith only [hprod]
    have hq2 : (κ *ᵥ u) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ u) ≤ 2 * eps ^ 2 := by
      refine le_trans hqy ?_
      have hRk14 : Rk ≤ 1 / 4 := by
        nlinarith only [hRk1, heps1, heps0, sq_nonneg eps]
      have hp1 : 0 ≤ eps ^ 2 * (3 - a2) :=
        mul_nonneg (sq_nonneg eps) (by linarith only [ha2b1])
      have hp2 : 0 ≤ eps ^ 2 * (1 / 4 - Rk) :=
        mul_nonneg (sq_nonneg eps) (by linarith only [hRk14])
      nlinarith only [hp1, hp2, sq_nonneg eps]
    nlinarith only [hq1, hq2, hbracket_eps, hd0, sq_nonneg eps]
  -- assemble at the load spellings
  constructor
  · rw [show -(matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
        SStar⁻¹ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
          κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e)) =
        δ from by rw [← hXm1]]
    exact hconc1
  · rw [show (1 - κ * SStar⁻¹) *ᵥ
        (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e) -
        (S + κ * SStar⁻¹ * κ) *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) =
        (r - S *ᵥ p) - κ *ᵥ u from by rw [← hXm2]]
    exact hconc2

end

end HCPolySupport.HighContrast.Quenched
