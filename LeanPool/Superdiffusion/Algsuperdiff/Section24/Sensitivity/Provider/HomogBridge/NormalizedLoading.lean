/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.Superdiffusion.Support.Book.Ch02.Theorems.Quadraticity

/-!
# NormalizedLoading

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `sigma0`-loaded scalar response is one of the normalized block responses

The homogenization error `mathcal E_{s,p,q}(cu_m; a, a0)` of ABK26, Definition
`d.mathcal.E`, is built from the *doubled* local responses
  `bfJ(z + cu_l, bfA_0^{-1/2} e, bfA_0^{1/2} e; a)`,  `e in R^{2d}`, `|e| = 1`,

whereas the subadditivity display opening the proof of
`l.J.sensitivity.no.conditions` uses the *scalar* responses `J(z +
cu_{-h}, sigma0^{-1/2} e, sigma0^{1/2} e; a)` with `e in R^d`.

This module supplies the exact passage between the two.  For `a0 = sigma0 I`
one has `kappa0 = 0`, hence `bfA_0 = diag(sigma0, sigma0^{-1})` and, for a unit
vector `e in R^d`, the doubled unit probe
  `E := (e / sqrt 2, - e / sqrt 2) in R^{2d}`,  `|E| = 1`,

produces `bfA_0^{-1/2} E = (c sigma0^{-1/2} e, -c sigma0^{1/2} e)` and
`bfA_0^{1/2} E = (c sigma0^{1/2} e, -c sigma0^{-1/2} e)` with `c = 2^{-1/2}`.
CoarseGraining's scalar splitting of the doubled response then collapses the
adjoint half-sum completely: the `a`-transpose summand is evaluated at the zero
loading, and the `a`-summand carries the loading `(sqrt 2 sigma0^{-1/2} e, sqrt
2 sigma0^{1/2} e)`, whose quadratic homogeneity contributes exactly the factor
`2` that cancels the `1/2`.  Consequently
  `J(R, sigma0^{-1/2} e, sigma0^{1/2} e; a)
     = bfJ(R, bfA_0^{-1/2} E, bfA_0^{1/2} E; a)`

is a *member* of the value set whose supremum is the one-cube `max_{|e| = 1}`,
and the supremum bound follows.  Nothing here is an inequality of ellipticity
type; the only quantitative input is the unconditional boundedness of the
normalized block-response value set proved in CoarseGraining.

The normalization is stated through `blockVecDot P (bfA_0 P) = 1`, which is
CoarseGraining's representation-free spelling of `|bfA_0^{1/2} P| = 1`; it is
what lets us avoid ever computing the matrix square root `bfA_0^{1/2}`
explicitly.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The doubled probe attached to a unit vector `e` and a positive scalar
background `sigma0`: `P = (c sigma0^{-1/2} e, -c sigma0^{1/2} e)` with
`c = 2^{-1/2}`. -/
def scalarLoadingProbe (σ0 : ℝ) (e : Vec d) : BlockVec d :=
  ((Real.sqrt 2)⁻¹ • ((Real.sqrt σ0)⁻¹ • e),
    (-(Real.sqrt 2)⁻¹) • (Real.sqrt σ0 • e))

/-- The image of `scalarLoadingProbe` under the constant block matrix of
`sigma0 I`, namely `bfA_0^{1/2} E = (c sigma0^{1/2} e, -c sigma0^{-1/2} e)`. -/
def scalarLoadingCoProbe (σ0 : ℝ) (e : Vec d) : BlockVec d :=
  ((Real.sqrt 2)⁻¹ • (Real.sqrt σ0 • e),
    (-(Real.sqrt 2)⁻¹) • ((Real.sqrt σ0)⁻¹ • e))

private theorem sqrt_two_inv_mul_sqrt_two_inv :
    ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [h]

/-- The constant block matrix of `sigma0 I` maps the probe to the co-probe. -/
private theorem blockMatVecMul_constantBlockMatrix_scalarLoadingProbe
    {σ0 : ℝ} (hσ0 : 0 < σ0) (e : Vec d) :
    blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0))
        (scalarLoadingProbe σ0 e) =
      scalarLoadingCoProbe σ0 e := by
  have hs : (0 : ℝ) < Real.sqrt σ0 := Real.sqrt_pos.mpr hσ0
  have hss : Real.sqrt σ0 * Real.sqrt σ0 = σ0 := Real.mul_self_sqrt hσ0.le
  have hkey : σ0 * ((Real.sqrt 2)⁻¹ * (Real.sqrt σ0)⁻¹) =
      (Real.sqrt 2)⁻¹ * Real.sqrt σ0 := by
    field_simp
    linarith [hss]
  have hkey' : σ0⁻¹ * (-(Real.sqrt 2)⁻¹ * Real.sqrt σ0) =
      -(Real.sqrt 2)⁻¹ * (Real.sqrt σ0)⁻¹ := by
    field_simp
    linarith [hss]
  have hzeroMat : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x
    funext i
    simp [matVecMul]
  rw [constantBlockMatrix_scalarMatrix hσ0]
  simp only [scalarLoadingProbe, scalarLoadingCoProbe, blockMatVecMul,
    matVecMul_scalarMatrix, hzeroMat, add_zero, zero_add, smul_smul,
    Prod.mk.injEq]
  exact ⟨by rw [hkey], by rw [hkey']⟩

/-- The probe is normalized: its `bfA_0`-quadratic form is `1`, which is
CoarseGraining's representation-free spelling of `|bfA_0^{1/2} P| = 1`. -/
private theorem blockVecDot_scalarLoadingProbe
    {σ0 : ℝ} (hσ0 : 0 < σ0) {e : Vec d} (he : vecNorm e = 1) :
    blockVecDot (scalarLoadingProbe σ0 e) (scalarLoadingCoProbe σ0 e) = 1 := by
  have hs : (0 : ℝ) < Real.sqrt σ0 := Real.sqrt_pos.mpr hσ0
  have hs2 : (Real.sqrt 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hee : vecDot e e = 1 := by
    have hsq := vecNorm_sq_eq_vecNormSq e
    rw [he] at hsq
    simpa [vecNormSq] using hsq.symm
  simp only [scalarLoadingProbe, scalarLoadingCoProbe, blockVecDot,
    vecDot_smul_left, vecDot_smul_right, hee]
  field_simp
  linarith [h2]

/-- The doubled response at the normalized probe is exactly the scalar
`sigma0`-loaded response. -/
private theorem doubledResponseJ_scalarLoadingProbe_eq_responseJ
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (σ0 : ℝ) (e : Vec d) :
    doubledResponseJ (cubeDomain R) (F.coeffOn R)
        (scalarLoadingProbe σ0 e) (scalarLoadingCoProbe σ0 e) =
      responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) := by
  simp only [scalarLoadingProbe, scalarLoadingCoProbe]
  set c : ℝ := (Real.sqrt 2)⁻¹ with hc
  set p : Vec d := (Real.sqrt σ0)⁻¹ • e with hp
  set q : Vec d := Real.sqrt σ0 • e with hq
  have hsplit :=
    (doubledResponseTheory (cubeDomain R)
      (F.coeffOn R)).doubledResponseJ_eq_scalar (c • p) ((-c) • p) ((-c) • q) (c • q)
  have hsub1 : c • p - (-c) • p = (2 * c) • p := by
    rw [← sub_smul]
    congr 1
    ring
  have hsub2 : c • q - (-c) • q = (2 * c) • q := by
    rw [← sub_smul]
    congr 1
    ring
  have hadd1 : (-c) • p + c • p = (0 : Vec d) := by
    rw [← add_smul]
    simp
  have hadd2 : c • q + (-c) • q = (0 : Vec d) := by
    rw [← add_smul]
    simp
  have hzeroResp :
      responseJ (cubeDomain R) (F.coeffOn R).transpose (0 : Vec d) (0 : Vec d) = 0 := by
    have hz := responseJ_smul (U := cubeDomain R) (a := (F.coeffOn R).transpose)
      (0 : ℝ) (0 : Vec d) (0 : Vec d)
    simpa using hz
  have hhomog :
      responseJ (cubeDomain R) (F.coeffOn R) ((2 * c) • p) ((2 * c) • q) =
        (2 * c) ^ 2 * responseJ (cubeDomain R) (F.coeffOn R) p q :=
    responseJ_smul (U := cubeDomain R) (a := F.coeffOn R) (2 * c) p q
  have hcc : (2 * c) ^ 2 = 2 := by
    have h2 := sqrt_two_inv_mul_sqrt_two_inv
    simp only [hc]
    nlinarith [h2]
  rw [hsplit, hsub1, hsub2, hadd1, hadd2, hzeroResp, hhomog, hcc]
  ring

/-- **The local passage from the scalar `sigma0`-loading to the normalized block
response.**  For a positive scalar background `sigma0` and a unit vector `e` in
`R^d`, the scalar response with loading `(sigma0^{-1/2} e, sigma0^{1/2} e)` on a
triadic cube is bounded by the normalized block-response maximum of that cube,
i.e. by the one-cube building block of `mathcal E_{s,p,q}( .; a, sigma0)`. -/
theorem responseJ_scalarLoading_le_normalizedBlockResponseMax
    (F : TriadicCoeffFamily d) (R : TriadicCube d) {σ0 : ℝ} (hσ0 : 0 < σ0)
    {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤
      Book.Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) := by
  classical
  have hmap := blockMatVecMul_constantBlockMatrix_scalarLoadingProbe (d := d) hσ0 e
  have hquad :
      blockVecDot (scalarLoadingProbe σ0 e)
        (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0))
          (scalarLoadingProbe σ0 e)) = 1 := by
    rw [hmap]
    exact blockVecDot_scalarLoadingProbe hσ0 he
  have hmem0 :=
    normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
      R F (isEllipticMatrix_scalarMatrix hσ0) (scalarLoadingProbe σ0 e) hquad
  rw [hmap, doubledResponseJ_scalarLoadingProbe_eq_responseJ F R σ0 e] at hmem0
  unfold Book.Ch02.normalizedBlockResponseMax
  exact le_csSup
    (normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := F) (Q := R) (R := R) (k := R.scale)
      (scalarMatrix (d := d) σ0) (by simp [descendantsAtScale_self]))
    hmem0

end

end Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge
