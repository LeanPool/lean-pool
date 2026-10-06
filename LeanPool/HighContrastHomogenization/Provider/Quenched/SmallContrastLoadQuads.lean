/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenterSchur
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCalibrationAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastLoadQuads

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The calibrated load quadratics

The two Schur-form quadratics of the recentered terminal mean at the
calibrated load pair `(-p, r)` (and its adjoint mirror `(p, r)`) are bounded
by the absolute constant `7` under the smallness pack, and the skew-shifted
load pairings are exactly one.  These are the only load-dependent factors of
the weak-cap majorant, so the weak value becomes uniform over unit
directions.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem quad_two_add {M : Mat d} (hM : M.PosSemidef) (x y : Vec d) :
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

/-- **The two hatted load quadratics are at most `7`.** -/
theorem calibrated_load_quads_le {S SStar κ : Mat d}
    (hS : S.PosDef) (hStar : SStar.PosDef) (hκ : κᴴ = κ)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (horder : SStar ≤ S)
    (hgapM : S - SStar ≤ eps • SStar)
    (hskewM : κ * SStar⁻¹ * κ ≤ (eps ^ 2 / 4) • SStar)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ
        S *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
          κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
            e)) ⬝ᵥ
        SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e +
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
              e)) ≤ 7) ∧
    ((matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) ⬝ᵥ
        S *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ e) +
      (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e -
          κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
            e)) ⬝ᵥ
        SStar⁻¹ *ᵥ
          (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar) *ᵥ e -
            κ *ᵥ (matSqrt (matGeomMean (S + κ * SStar⁻¹ * κ) SStar)⁻¹ *ᵥ
              e)) ≤ 7) := by
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
  set B : Mat d := calibrationB b SStar with hBdef
  have hBge : (1 : Mat d) ≤ B := one_le_calibrationB hb hStar hbStar
  have hBinvle : B⁻¹ ≤ (1 : Mat d) := calibrationB_inv_le_one hb hStar hbStar
  set p : Vec d := matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e with hpdef
  set r : Vec d := matSqrt (matGeomMean b SStar) *ᵥ e with hrdef
  set a1 : ℝ := p ⬝ᵥ SStar *ᵥ p with ha1
  set a2 : ℝ := r ⬝ᵥ SStar⁻¹ *ᵥ r with ha2
  set gp : ℝ := p ⬝ᵥ (S - SStar) *ᵥ p with hgp
  set Rk : ℝ := (κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ p) with hRkdef
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
  have hkq : ∀ x : Vec d, x ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ x =
      (κ *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (κ *ᵥ x) := by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← mulVec_dotProduct_symm hκ]
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
  have ha2b : a2 = p ⬝ᵥ b *ᵥ p := by
    rw [ha2B, hBdef, calibrationB]
    have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
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
  have hgp1 : gp ≤ eps := le_trans hgapP
    (by nlinarith only [ha1le, heps0])
  have hRk1 : Rk ≤ eps ^ 2 / 4 := le_trans hRkle
    (by nlinarith only [ha1le, heps0])
  have heps2 : eps ^ 2 ≤ 1 := by nlinarith only [heps0, heps1]
  have ha2le : a2 ≤ 9 / 4 := by
    rw [ha2b, hbp]
    linarith only [ha1le, hgp1, hRk1, heps1, heps2]
  have ha2nn : 0 ≤ a2 := by
    rw [ha2]
    have := hStar.inv.posSemidef.dotProduct_mulVec_nonneg r
    simpa using this
  have hSquad : p ⬝ᵥ S *ᵥ p ≤ 2 := by
    have hsplit : p ⬝ᵥ S *ᵥ p = a1 + gp := by
      rw [ha1, hgp, Matrix.sub_mulVec, dotProduct_sub]
      ring
    rw [hsplit]
    linarith only [ha1le, hgp1, heps1]
  have hplus : (r + κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r + κ *ᵥ p) ≤ 5 := by
    have h := quad_two_add hStar.inv.posSemidef r (κ *ᵥ p)
    rw [← ha2, ← hRkdef] at h
    refine le_trans h ?_
    linarith only [ha2le, hRk1, heps2]
  have hminus : (r - κ *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (r - κ *ᵥ p) ≤ 5 := by
    have h := quad_two_add hStar.inv.posSemidef r (-(κ *ᵥ p))
    have hnegquad : (-(κ *ᵥ p)) ⬝ᵥ SStar⁻¹ *ᵥ (-(κ *ᵥ p)) = Rk := by
      rw [hRkdef, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct,
        neg_neg]
    rw [← sub_eq_add_neg, hnegquad, ← ha2] at h
    refine le_trans h ?_
    linarith only [ha2le, hRk1, heps2]
  exact ⟨by linarith only [hSquad, hplus],
    by linarith only [hSquad, hminus]⟩

/-- **The skew-shifted load pairings are exactly one.** -/
theorem calibrated_pair_skew_abs {b SStar : Mat d}
    (hb : b.PosDef) (hStar : SStar.PosDef)
    {h0 : Mat d} (hh0 : IsSkewMat h0)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    |(matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ
        (matSqrt (matGeomMean b SStar) *ᵥ e -
          h0 *ᵥ (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e))| = 1 ∧
    |(matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ
        (matSqrt (matGeomMean b SStar) *ᵥ e +
          h0 *ᵥ (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e))| = 1 := by
  have hgstar : h0ᴴ = -h0 := by
    rwa [conjTranspose_eq_transpose']
  have hpair : (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ
      (matSqrt (matGeomMean b SStar) *ᵥ e) = 1 := by
    rw [calibration_pair hb hStar e, he]
  have hzero : (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ
      (h0 *ᵥ (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e)) = 0 :=
    Response.dotProduct_mulVec_of_skew hgstar _
  constructor
  · rw [dotProduct_sub, hpair, hzero, sub_zero, abs_one]
  · rw [dotProduct_add, hpair, hzero, add_zero, abs_one]

/-- **The recentered hatted mean quadratic in closed Schur form.** -/
theorem hatMean_blockQuad_eq [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (t : ℤ) {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    (x y : Vec d) :
    blockVecDot ((x, y) : BlockVec d)
        (blockMatVecMul
          (Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t))
          ((x, y) : BlockVec d)) =
      x ⬝ᵥ S *ᵥ x +
        (y - Response.responseSymmetric K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ
          (y - Response.responseSymmetric K *ᵥ x) := by
  have hE2 : toFullBlockMat
      (Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t)) =
      schurBlock S SStar (Response.responseSymmetric K) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock
      (Response.responseSkew K) hform
    rwa [Response.sub_responseSkew K] at h
  have hvec : toFullBlockVec ((x, y) : BlockVec d) = Sum.elim x y := by
    funext α
    cases α <;> rfl
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, hE2, hvec,
    Response.quadratic_schurBlock]

end

end HCPolySupport.HighContrast.Quenched
