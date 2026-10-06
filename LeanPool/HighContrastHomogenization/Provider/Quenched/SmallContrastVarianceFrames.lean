/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSchurExtraction
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecenteredSharp
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringSmallness
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDilation
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSymmetricSkew
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastVarianceFrames

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frame inputs of the variance split

The two frame-sensitive scalar inputs of the abstract variance split,
discharged at the recentered means: the terminal recentered mean is within
factor four of its sharp, and the lower-scale recentered sharp gap is
first order in the hatted contrast defect, both against the terminal
frame.  The recentering is at the lower scale's response skew, so the
symmetric parts are controlled by the smallness packs and the skew
difference by the good quadratics.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem schurBlock_herm {S SStar K : Mat d}
    (hS : Sᴴ = S) (hStar : SStarᴴ = SStar) :
    (schurBlock S SStar K)ᴴ = schurBlock S SStar K := by
  rw [schurBlock, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    Matrix.fromBlocks_conjTranspose]
  have hStarInv : (SStar⁻¹)ᴴ = SStar⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hStar]
  rw [hS, hStarInv]
  have h0 : (0 : Mat d)ᴴ = 0 := Matrix.conjTranspose_zero
  rw [h0]
  noncomm_ring

private theorem full_le_of_pair_quads {A B : FullBlockMat d}
    (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : ∀ x y : Vec d, Sum.elim x y ⬝ᵥ A *ᵥ Sum.elim x y ≤
      Sum.elim x y ⬝ᵥ B *ᵥ Sum.elim x y) : A ≤ B := by
  refine Initialization.le_of_dotProduct_mulVec_le hA hB fun v => ?_
  have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
    funext α
    cases α <;> rfl
  rw [hv]
  exact h _ _

private theorem quad_smul_full (c : ℝ) (B : FullBlockMat d) (v : BlockCoord d → ℝ) :
    v ⬝ᵥ (c • B) *ᵥ v = c * (v ⬝ᵥ B *ᵥ v) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

private theorem quad_split_two {M : Mat d} (hM : M.PosSemidef) (a b : Vec d) :
    (a + b) ⬝ᵥ M *ᵥ (a + b) ≤
      2 * (a ⬝ᵥ M *ᵥ a) + 2 * (b ⬝ᵥ M *ᵥ b) := by
  have hswap : b ⬝ᵥ M *ᵥ a = a ⬝ᵥ M *ᵥ b := by
    rw [dotProduct_comm]
    exact mulVec_dotProduct_symm hM.isHermitian.eq a b
  have hminus : 0 ≤ (a - b) ⬝ᵥ M *ᵥ (a - b) := by
    have := hM.dotProduct_mulVec_nonneg (a - b)
    simpa using this
  have hexp₁ : (a + b) ⬝ᵥ M *ᵥ (a + b) =
      a ⬝ᵥ M *ᵥ a + 2 * (a ⬝ᵥ M *ᵥ b) + b ⬝ᵥ M *ᵥ b := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hswap]
    ring
  have hexp₂ : (a - b) ⬝ᵥ M *ᵥ (a - b) =
      a ⬝ᵥ M *ᵥ a - 2 * (a ⬝ᵥ M *ᵥ b) + b ⬝ᵥ M *ᵥ b := by
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hswap]
    ring
  rw [hexp₂] at hminus
  rw [hexp₁]
  linarith only [hminus]

private theorem starInv_le_smul_inv {S SStar : Mat d}
    (hS : S.PosDef) (hStar : SStar.PosDef) {eps : ℝ} (heps0 : 0 ≤ eps)
    (hgap : S - SStar ≤ eps • SStar) :
    SStar⁻¹ ≤ (1 + eps) • S⁻¹ := by
  have hSle : S ≤ (1 + eps) • SStar := by
    have h := add_le_add_right hgap SStar
    have hh : SStar + (S - SStar) = S := by abel
    rw [hh] at h
    rw [add_smul, one_smul]
    exact h
  have hsmulpd : ((1 + eps) • SStar).PosDef :=
    hStar.smul (by linarith only [heps0])
  have hinv := inv_le_inv_of_le hS hsmulpd hSle
  rw [inv_smul_posDef hStar (by linarith only [heps0])] at hinv
  have h := smul_le_smul_of_nonneg_left hinv
    (by linarith only [heps0] : (0 : ℝ) ≤ 1 + eps)
  rwa [smul_smul, mul_inv_cancel₀ (by linarith only [heps0]), one_smul]
    at h

/-- **The terminal recentered sharp comparison** with constant four. -/
theorem hatted_sharp_inverse_bound
    {Sp SStarp Kp : Mat d} (hSp : Sp.PosDef) (hStarp : SStarp.PosDef)
    {epsp : ℝ} (hposp : 0 ≤ epsp) (hepsp1 : epsp ≤ 1)
    (hgapMp : Sp - SStarp ≤ epsp • SStarp)
    (hskewMp : Response.responseSymmetric Kp * SStarp⁻¹ *
      Response.responseSymmetric Kp ≤ (epsp ^ 2 / 4) • SStarp)
    (h0 : Mat d) (hh0 : IsSkewMat h0) :
    schurBlock Sp SStarp (Kp - h0) ≤
      (4 : ℝ) • fullBlockSharp (schurBlock Sp SStarp (Kp - h0)) := by
  have hSpherm : Spᴴ = Sp := hSp.isHermitian
  have hStarherm : SStarpᴴ = SStarp := hStarp.isHermitian
  rw [fullBlockSharp_schurBlock hSp hStarp]
  refine full_le_of_pair_quads
    (schurBlock_herm hSpherm hStarherm) ?_ ?_
  · rw [Matrix.conjTranspose_smul, star_trivial]
    congr 1
    exact schurBlock_herm hStarherm hSpherm
  intro x y
  rw [quad_smul_full, Response.quadratic_schurBlock, Response.quadratic_schurBlock]
  -- the symmetric part of the shifted skew
  have hsym2 : (Kp - h0) + (Kp - h0)ᴴ =
      (2 : ℝ) • Response.responseSymmetric Kp := by
    have hh0star : h0ᴴ = -h0 := by
      rwa [conjTranspose_eq_transpose']
    rw [Matrix.conjTranspose_sub, hh0star, Response.two_smul_responseSymmetric]
    abel
  have hBdecomp : y - (Kp - h0) *ᵥ x =
      (y - (-(Kp - h0)ᴴ) *ᵥ x) -
        ((2 : ℝ) • Response.responseSymmetric Kp) *ᵥ x := by
    rw [← hsym2]
    rw [Matrix.neg_mulVec, Matrix.add_mulVec]
    abel
  set B : Vec d := y - (-(Kp - h0)ᴴ) *ᵥ x with hBdef
  set Cx : Vec d := ((2 : ℝ) • Response.responseSymmetric Kp) *ᵥ x with hCxdef
  -- quadratic pieces
  have hCq : Cx ⬝ᵥ SStarp⁻¹ *ᵥ Cx ≤ epsp ^ 2 * (x ⬝ᵥ SStarp *ᵥ x) := by
    have hks : (Response.responseSymmetric Kp)ᴴ = Response.responseSymmetric Kp :=
      Response.responseSymmetric_isHermitian Kp
    have hkq : x ⬝ᵥ (Response.responseSymmetric Kp * SStarp⁻¹ *
        Response.responseSymmetric Kp) *ᵥ x =
        (Response.responseSymmetric Kp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
          (Response.responseSymmetric Kp *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← mulVec_dotProduct_symm hks]
    have h := Initialization.dotProduct_mulVec_le_of_le hskewMp x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hkq] at h
    have hCx2 : Cx = (2 : ℝ) • (Response.responseSymmetric Kp *ᵥ x) := by
      rw [hCxdef, Matrix.smul_mulVec]
    rw [hCx2]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    linarith only [h]
  have hSq : x ⬝ᵥ Sp *ᵥ x ≤ (1 + epsp) * (x ⬝ᵥ SStarp *ᵥ x) := by
    have h := Initialization.dotProduct_mulVec_le_of_le hgapMp x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    linarith only [h]
  have hBq : B ⬝ᵥ SStarp⁻¹ *ᵥ B ≤
      (1 + epsp) * (B ⬝ᵥ Sp⁻¹ *ᵥ B) := by
    have hinv := starInv_le_smul_inv hSp hStarp hposp hgapMp
    have h := Initialization.dotProduct_mulVec_le_of_le hinv B
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  have hsplitq : (y - (Kp - h0) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
      (y - (Kp - h0) *ᵥ x) ≤
      2 * (B ⬝ᵥ SStarp⁻¹ *ᵥ B) + 2 * (Cx ⬝ᵥ SStarp⁻¹ *ᵥ Cx) := by
    have hBC : y - (Kp - h0) *ᵥ x = B + (-Cx) := by
      rw [hBdef, hCxdef, ← sub_eq_add_neg]
      exact hBdecomp
    rw [hBC]
    have h := quad_split_two hStarp.inv.posSemidef B (-Cx)
    have hnegq : (-Cx) ⬝ᵥ SStarp⁻¹ *ᵥ (-Cx) = Cx ⬝ᵥ SStarp⁻¹ *ᵥ Cx := by
      rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
    rwa [hnegq] at h
  -- nonnegativity of the pieces
  have hxq0 : 0 ≤ x ⬝ᵥ SStarp *ᵥ x := by
    have := hStarp.posSemidef.dotProduct_mulVec_nonneg x
    simpa using this
  have hBq0 : 0 ≤ B ⬝ᵥ Sp⁻¹ *ᵥ B := by
    have := hSp.inv.posSemidef.dotProduct_mulVec_nonneg B
    simpa using this
  have heps2 : epsp ^ 2 ≤ 1 := by nlinarith only [hposp, hepsp1]
  have hp1 : (1 + epsp) * (x ⬝ᵥ SStarp *ᵥ x) ≤
      2 * (x ⬝ᵥ SStarp *ᵥ x) := by
    nlinarith only [hxq0, hepsp1]
  have hp2 : epsp ^ 2 * (x ⬝ᵥ SStarp *ᵥ x) ≤ x ⬝ᵥ SStarp *ᵥ x := by
    nlinarith only [hxq0, heps2]
  have hp3 : (1 + epsp) * (B ⬝ᵥ Sp⁻¹ *ᵥ B) ≤
      2 * (B ⬝ᵥ Sp⁻¹ *ᵥ B) := by
    nlinarith only [hBq0, hepsp1]
  linarith only [hSq, hsplitq, hBq, hCq, hp1, hp2, hp3]

private theorem inverse_gap_quadratic_bound
    {Sj SStarj : Mat d} (hSj : Sj.PosDef) (hStarj : SStarj.PosDef)
    {epsj : ℝ} (hposj : 0 ≤ epsj) (horderj : SStarj ≤ Sj)
    (hgapMj : Sj - SStarj ≤ epsj • SStarj) (κ : Mat d) (x y : Vec d) :
    (y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x) -
      (y + κ *ᵥ x) ⬝ᵥ Sj⁻¹ *ᵥ (y + κ *ᵥ x) ≤
      epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) := by
  classical
  have hinvj : SStarj⁻¹ ≤ (1 + epsj) • Sj⁻¹ :=
    starInv_le_smul_inv hSj hStarj hposj hgapMj
  have hSjinvle : Sj⁻¹ ≤ SStarj⁻¹ :=
    inv_le_inv_of_le hStarj hSj horderj
  have hdiffq : (y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x) -
      (y + κ *ᵥ x) ⬝ᵥ Sj⁻¹ *ᵥ (y + κ *ᵥ x) ≤
      epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) := by
    have hd : SStarj⁻¹ - Sj⁻¹ ≤ epsj • SStarj⁻¹ := by
      have h1 : SStarj⁻¹ - Sj⁻¹ ≤ (1 + epsj) • Sj⁻¹ - Sj⁻¹ :=
        sub_le_sub_right hinvj _
      have h2 : (1 + epsj) • Sj⁻¹ - Sj⁻¹ = epsj • Sj⁻¹ := by
        rw [add_smul, one_smul]
        abel
      rw [h2] at h1
      refine h1.trans ?_
      exact smul_le_smul_of_nonneg_left hSjinvle hposj
    have h := Initialization.dotProduct_mulVec_le_of_le hd (y + κ *ᵥ x)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    exact h
  exact hdiffq

/-- **The lower-scale recentered sharp gap** is first order in the
smallness parameter against the terminal frame. -/
theorem hatted_sharp_gap_bound
    {Sj SStarj : Mat d} (hSj : Sj.PosDef) (hStarj : SStarj.PosDef)
    {epsj : ℝ} (hposj : 0 ≤ epsj) (hepsj1 : epsj ≤ 1)
    (horderj : SStarj ≤ Sj)
    (hgapMj : Sj - SStarj ≤ epsj • SStarj)
    {κ : Mat d} (hκ : κᴴ = κ)
    (hskewMj : κ * SStarj⁻¹ * κ ≤ (epsj ^ 2 / 4) • SStarj)
    {Sp SStarp Khatp : Mat d} (hSp : Sp.PosDef) (hStarp : SStarp.PosDef)
    (horderp : SStarp ≤ Sp)
    (hstarcross : SStarj ≤ SStarp)
    (hdilquad : ∀ y : Vec d,
      y ⬝ᵥ SStarj⁻¹ *ᵥ y ≤ 2 * (y ⬝ᵥ SStarp⁻¹ *ᵥ y))
    (hKhat : ∀ x : Vec d,
      (Khatp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (Khatp *ᵥ x) ≤ x ⬝ᵥ Sp *ᵥ x) :
    schurBlock Sj SStarj κ - fullBlockSharp (schurBlock Sj SStarj κ) ≤
      (36 * epsj) • schurBlock Sp SStarp Khatp := by
  have hSjherm : Sjᴴ = Sj := hSj.isHermitian
  have hStarjherm : SStarjᴴ = SStarj := hStarj.isHermitian
  have hSpherm : Spᴴ = Sp := hSp.isHermitian
  have hStarpherm : SStarpᴴ = SStarp := hStarp.isHermitian
  rw [fullBlockSharp_schurBlock hSj hStarj]
  have hsharpherm : (schurBlock SStarj Sj (-κᴴ))ᴴ =
      schurBlock SStarj Sj (-κᴴ) := schurBlock_herm hStarjherm hSjherm
  refine full_le_of_pair_quads ?_ ?_ ?_
  · rw [Matrix.conjTranspose_sub, schurBlock_herm hSjherm hStarjherm,
      hsharpherm]
  · rw [Matrix.conjTranspose_smul, star_trivial]
    congr 1
    exact schurBlock_herm hSpherm hStarpherm
  intro x y
  -- unfold the three quadratics
  have hsub : Sum.elim x y ⬝ᵥ
      (schurBlock Sj SStarj κ - schurBlock SStarj Sj (-κᴴ)) *ᵥ
        Sum.elim x y =
      Sum.elim x y ⬝ᵥ schurBlock Sj SStarj κ *ᵥ Sum.elim x y -
        Sum.elim x y ⬝ᵥ schurBlock SStarj Sj (-κᴴ) *ᵥ Sum.elim x y := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [hsub, quad_smul_full, Response.quadratic_schurBlock,
    Response.quadratic_schurBlock, Response.quadratic_schurBlock]
  -- the reversed slot
  have hslotB : y - -κᴴ *ᵥ x = y + κ *ᵥ x := by
    rw [hκ, Matrix.neg_mulVec, sub_neg_eq_add]
  rw [hslotB]
  -- atoms
  set X : ℝ := x ⬝ᵥ SStarj *ᵥ x with hXdef
  set Yq : ℝ := y ⬝ᵥ SStarj⁻¹ *ᵥ y with hYdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have := hStarj.posSemidef.dotProduct_mulVec_nonneg x
    simpa using this
  have hYq0 : 0 ≤ Yq := by
    rw [hYdef]
    have := hStarj.inv.posSemidef.dotProduct_mulVec_nonneg y
    simpa using this
  -- the gap of the sigma part
  have hgapq : x ⬝ᵥ Sj *ᵥ x - X ≤ epsj * X := by
    have h := Initialization.dotProduct_mulVec_le_of_le hgapMj x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← hXdef] at h
    exact h
  -- the skew quadratic
  have hκq : (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) ≤ epsj ^ 2 / 4 * X := by
    have hkq : x ⬝ᵥ (κ * SStarj⁻¹ * κ) *ᵥ x =
        (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← mulVec_dotProduct_symm hκ]
    have h := Initialization.dotProduct_mulVec_le_of_le hskewMj x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hkq,
      ← hXdef] at h
    exact h
  -- the cross term
  set c : ℝ := (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ y with hcdef
  have hstarinvherm : (SStarj⁻¹)ᴴ = SStarj⁻¹ := hStarj.inv.isHermitian
  have hswapgen : ∀ a b : Vec d,
      a ⬝ᵥ SStarj⁻¹ *ᵥ b = b ⬝ᵥ SStarj⁻¹ *ᵥ a := fun a b => by
    rw [dotProduct_comm]
    exact mulVec_dotProduct_symm hstarinvherm b a
  have hexpA : (y - κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y - κ *ᵥ x) =
      Yq - 2 * c + (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) := by
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hswapgen y (κ *ᵥ x), ← hYdef, ← hcdef]
    ring
  have hexpB : (y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x) =
      Yq + 2 * c + (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hswapgen y (κ *ᵥ x), ← hYdef, ← hcdef]
    ring
  -- the Cauchy--Schwarz bound on the cross term
  have hc2 : c ^ 2 ≤ ((κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x)) * Yq := by
    have hw : SStarj *ᵥ (SStarj⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStarj),
        Matrix.one_mulVec]
    have h := dotProduct_sq_le_quad_mul_quad hStarj.inv (κ *ᵥ x)
      (SStarj⁻¹ *ᵥ y)
    have hcoll : (SStarj⁻¹ *ᵥ y) ⬝ᵥ (SStarj⁻¹)⁻¹ *ᵥ (SStarj⁻¹ *ᵥ y) =
        Yq := by
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStarj),
        hw, mulVec_dotProduct_symm hstarinvherm y y, ← hYdef]
    rw [hcoll] at h
    rw [← hcdef] at h
    exact h
  have hc2' : c ^ 2 ≤ epsj ^ 2 / 4 * X * Yq := by
    have hstep := mul_le_mul_of_nonneg_right hκq hYq0
    exact le_trans hc2 hstep
  have hsq : (4 * c) ^ 2 ≤ (epsj * X + epsj * Yq) ^ 2 := by
    nlinarith only [hc2', sq_nonneg (epsj * X - epsj * Yq)]
  have hS0 : 0 ≤ epsj * X + epsj * Yq := by
    have h1 := mul_nonneg hposj hX0
    have h2 := mul_nonneg hposj hYq0
    linarith only [h1, h2]
  have habs4 : |4 * c| ≤ epsj * X + epsj * Yq := by
    have h1 : Real.sqrt ((4 * c) ^ 2) ≤
        Real.sqrt ((epsj * X + epsj * Yq) ^ 2) := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hS0] at h1
  have hcross4 : -(4 * c) ≤ epsj * X + epsj * Yq := by
    have h2 := neg_abs_le (4 * c)
    linarith only [habs4, h2]
  have habs2 : |2 * c| ≤ (epsj * X + epsj * Yq) / 2 := by
    have h4 : |(4 : ℝ) * c| = 2 * |2 * c| := by
      rw [show (4 : ℝ) * c = 2 * (2 * c) by ring, abs_mul]
      norm_num
    linarith only [habs4, h4]
  have hepsc2 : epsj * (2 * c) ≤ epsj * X + epsj * Yq := by
    have h1 : 2 * c ≤ |2 * c| := le_abs_self _
    have h2 : epsj * (2 * c) ≤ epsj * |2 * c| :=
      mul_le_mul_of_nonneg_left h1 hposj
    have h3 : epsj * |2 * c| ≤ 1 * |2 * c| :=
      mul_le_mul_of_nonneg_right hepsj1 (abs_nonneg _)
    have h4 : (0 : ℝ) ≤ epsj * X + epsj * Yq := hS0
    linarith only [h2, h3, habs2, h4]
  -- the inverse-gap correction
  have hdiffq := inverse_gap_quadratic_bound hSj hStarj hposj horderj hgapMj κ x y
  -- the frame comparison
  set Fpq : ℝ := x ⬝ᵥ Sp *ᵥ x +
    (y - Khatp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (y - Khatp *ᵥ x) with hFpqdef
  have hFpq0 : 0 ≤ Fpq := by
    rw [hFpqdef]
    have h1 := hSp.posSemidef.dotProduct_mulVec_nonneg x
    have h2 := hStarp.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - Khatp *ᵥ x)
    simp only [star_trivial] at h1 h2
    linarith only [h1, h2]
  have hX2 : X ≤ Fpq := by
    have h1 := Initialization.dotProduct_mulVec_le_of_le hstarcross x
    have h2 := Initialization.dotProduct_mulVec_le_of_le horderp x
    have h3 := hStarp.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - Khatp *ᵥ x)
    simp only [star_trivial] at h3
    rw [hXdef, hFpqdef]
    linarith only [h1, h2, h3]
  have hY2 : Yq ≤ 8 * Fpq := by
    have h1 := hdilquad y
    have hyp : y ⬝ᵥ SStarp⁻¹ *ᵥ y ≤
        2 * ((y - Khatp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (y - Khatp *ᵥ x)) +
          2 * ((Khatp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (Khatp *ᵥ x)) := by
      have hdecomp : y = (y - Khatp *ᵥ x) + Khatp *ᵥ x := by abel
      have h := quad_split_two hStarp.inv.posSemidef
        (y - Khatp *ᵥ x) (Khatp *ᵥ x)
      calc y ⬝ᵥ SStarp⁻¹ *ᵥ y =
          ((y - Khatp *ᵥ x) + Khatp *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
            ((y - Khatp *ᵥ x) + Khatp *ᵥ x) := by rw [← hdecomp]
        _ ≤ _ := h
    have h2 := hKhat x
    have h3 := hSp.posSemidef.dotProduct_mulVec_nonneg x
    have h4 := hStarp.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - Khatp *ᵥ x)
    simp only [star_trivial] at h3 h4
    rw [← hYdef] at h1
    rw [hFpqdef]
    linarith only [h1, hyp, h2, h3, h4]
  -- products
  have haX : epsj * X ≤ epsj * Fpq :=
    mul_le_mul_of_nonneg_left hX2 hposj
  have haY : epsj * Yq ≤ 8 * (epsj * Fpq) := by
    have h := mul_le_mul_of_nonneg_left hY2 hposj
    calc epsj * Yq ≤ epsj * (8 * Fpq) := h
      _ = 8 * (epsj * Fpq) := by ring
  have haB : epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) ≤
      epsj * Yq + epsj * (2 * c) + epsj * (epsj ^ 2 / 4 * X) := by
    have h : epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) ≤
        epsj * (Yq + 2 * c + epsj ^ 2 / 4 * X) := by
      refine mul_le_mul_of_nonneg_left ?_ hposj
      rw [hexpB]
      linarith only [hκq]
    calc epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) ≤
        epsj * (Yq + 2 * c + epsj ^ 2 / 4 * X) := h
      _ = epsj * Yq + epsj * (2 * c) + epsj * (epsj ^ 2 / 4 * X) := by
        ring
  have hεX2 : epsj * (epsj ^ 2 / 4 * X) ≤ epsj * X := by
    have heps2 : epsj ^ 2 / 4 ≤ 1 := by nlinarith only [hposj, hepsj1]
    have h : epsj ^ 2 / 4 * X ≤ X := by nlinarith only [heps2, hX0]
    exact mul_le_mul_of_nonneg_left h hposj
  have hεFpq0 : 0 ≤ epsj * Fpq := mul_nonneg hposj hFpq0
  have hfinal : x ⬝ᵥ Sj *ᵥ x +
      (y - κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y - κ *ᵥ x) -
      (X + (y + κ *ᵥ x) ⬝ᵥ Sj⁻¹ *ᵥ (y + κ *ᵥ x)) ≤
      36 * epsj * Fpq := by
    have hkey : -((y + κ *ᵥ x) ⬝ᵥ Sj⁻¹ *ᵥ (y + κ *ᵥ x)) ≤
        -((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) +
          epsj * ((y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x)) := by
      linarith only [hdiffq]
    have hBqStar : (y + κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y + κ *ᵥ x) =
        Yq + 2 * c + (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) := hexpB
    have hAqe : (y - κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (y - κ *ᵥ x) =
        Yq - 2 * c + (κ *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ (κ *ᵥ x) := hexpA
    rw [hAqe]
    rw [hBqStar] at hkey haB
    linarith only [hgapq, hkey, haB, hεX2, hcross4, hepsc2, haX, haY,
      hεFpq0]
  exact hfinal

end

end HCPolySupport.HighContrast.Quenched
