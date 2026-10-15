/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.Comparator
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.Superdiffusion.Support.Book.Ch02.Theorems.Quadraticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VecGauge

/-!
# BlockResponse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.bfJ.general`: the block response at the isotropic comparator, in scalar `J`

ABK26, (the itemized property `e.bfJ.general`) and its use in the first
display of the proof of `p.mathcalE.annular.decomp` (with the transpose
remark):

```
bfJ(U, (p,q), (q*,p*); a) = 1/2 J(U, p-p*, q*-q; a) + 1/2 J(U, p*+p, q*+q; a^t) .
```

The identity itself is **proved upstream and unconditional**: it is
CoarseGraining's `Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum`,
the public accessor of the doubled-response theory available for every `CoeffOn
U`.  What this module supplies is the *conversion the manuscript actually
performs with it*: the normalized block-response maximum over the
`2d`-dimensional full-block unit sphere, which is the inner quantity of
`d.mathcal.E`, is bounded by the sum of the scalar maxima at the loads
`(sigma0^{-1/2} e, sigma0^{1/2} e)` for the field and for its transpose.

## The mechanism, and why the constant is `1`

For `a0 = sigma0 I` one has `bfA_0 = diag(sigma0 I, sigma0^{-1} I)`, so a member
of the normalized value set is `bfJ(U, P, bfA_0 P)` with the representation-free
normalization `<P, bfA_0 P> = 1`, i.e. `sigma0 |p|^2 + sigma0^{-1} |q|^2 = 1`
for `P = (p, q)`.  The splitting identity evaluates it at

```
u := p - sigma0^{-1} q ,   v := p + sigma0^{-1} q ,
bfJ = 1/2 J(a, u, sigma0 u) + 1/2 J(a^t, v, sigma0 v) ,
```

and both scalar loads are of the manuscript's shape
`(sigma0^{-1/2} f, sigma0^{1/2} f)` with `f = sigma0^{1/2} u` resp.
`g = sigma0^{1/2} v`.  Quadratic homogeneity of `J` in the load pair turns them
into `|f|^2` resp. `|g|^2` times the value at a unit direction, and the
normalization gives exactly

```
sigma0 |u|^2 + sigma0 |v|^2 = 2 (sigma0 |p|^2 + sigma0^{-1} |q|^2) = 2 ,
```

so each half-weight is at most `1`: the conversion holds with constant `1`, well
inside the manuscript's `C`.

## What is proved

* `responseJ_scalarLoad_le_of_unit_bound` -- the homogeneity step.
* `normalizedBlockResponseMax_scalarMatrix_le` -- the one-cube conversion.
* `maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le` -- the same over
  a whole descendant family, which is the shape the `(infinity,2)` scale sum
  reads.
* `responseJ_transpose_scalarLoading_le_normalizedBlockResponseMax` -- the
  reverse inequality for the transposed field, the mirror of the proved Section
  2.4 bound for the field itself; in particular the transposed scalar value set
  is bounded above, so a caller may form its supremum.
* `..._isotropicComparator_le` -- the conversions in the Section 3/4 spelling
  (`Observable.isotropicComparatorMatrix`, `Observable.inverseSqrtLoad`,
  `Observable.sqrtLoad`), i.e. literally the manuscript's
  `J(., sigmaBar^{-1/2} e, sigmaBar^{1/2} e)`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Euclidean bookkeeping on `Vec d` -/

private theorem vecNormSq_nonneg (x : Vec d) : 0 ≤ vecNormSq x := by
  rw [← vecNorm_sq_eq_vecNormSq]
  exact sq_nonneg _

private theorem vecNormSq_smul (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  simp only [vecNormSq, vecDot_smul_left, vecDot_smul_right]
  ring

private theorem vecNormSq_add (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  simp only [vecNormSq, vecDot_add_left, vecDot_add_right]
  rw [vecDot_comm y x]
  ring

private theorem vecNormSq_sub (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq x - 2 * vecDot x y + vecNormSq y := by
  have hsub : x - y = x + (-1 : ℝ) • y := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hsub, vecNormSq_add, vecDot_smul_right, vecNormSq_smul]
  ring

private theorem vecNorm_eq_sqrt_vecNormSq (x : Vec d) :
    vecNorm x = Real.sqrt (vecNormSq x) := by
  rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg x)]

private theorem eq_zero_of_vecNorm_eq_zero {x : Vec d} (hx : vecNorm x = 0) :
    x = 0 := by
  have hsq : vecNormSq x = 0 := by
    rw [← vecNorm_sq_eq_vecNormSq, hx]
    norm_num
  have hsum : ∑ i, x i * x i = 0 := hsq
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), x i * x i = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum
    intro i _
    exact mul_self_nonneg (x i)
  funext i
  have hi : x i * x i = 0 := hterm i (Finset.mem_univ i)
  have := mul_self_eq_zero.mp hi
  simpa using this

private theorem exists_vecNorm_eq_one [NeZero d] :
    ∃ e : Vec d, vecNorm e = 1 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
  have hsq : vecNormSq (Pi.single (⟨0, hd⟩ : Fin d) 1) = 1 := by
    have := vecDot_single_left (⟨0, hd⟩ : Fin d) (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ))
    rw [vecNormSq, this]
    simp
  rw [vecNorm_eq_sqrt_vecNormSq, hsq, Real.sqrt_one]

/-! ## The homogeneity step -/

/-- **Quadratic homogeneity at the scalar loading.**  If the response at every
*unit* load pair `(sigma0^{-1/2} e, sigma0^{1/2} e)` is at most `B`, then at the
general pair `(u, sigma0 u)` -- which is that shape at the vector
`sigma0^{1/2} u` -- it is at most `sigma0 |u|^2 B`. -/
theorem responseJ_scalarLoad_le_of_unit_bound {U : Domain d} (a : CoeffOn U)
    {σ0 : ℝ} (hσ0 : 0 < σ0) {B : ℝ}
    (hB : ∀ e : Vec d, vecNorm e = 1 →
      responseJ U a ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤ B)
    (u : Vec d) :
    responseJ U a u (σ0 • u) ≤ σ0 * vecNormSq u * B := by
  have hs : (0 : ℝ) < Real.sqrt σ0 := Real.sqrt_pos.mpr hσ0
  have hss : Real.sqrt σ0 * Real.sqrt σ0 = σ0 := Real.mul_self_sqrt hσ0.le
  set s : ℝ := Real.sqrt σ0 with hsdef
  set f : Vec d := s • u with hfdef
  have hfu : (s : ℝ)⁻¹ • f = u := by
    rw [hfdef, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
  have hfs : s • f = σ0 • u := by
    rw [hfdef, smul_smul, hss]
  set c : ℝ := vecNorm f with hcdef
  have hc0 : 0 ≤ c := vecNorm_nonneg f
  have hcsq : c ^ 2 = σ0 * vecNormSq u := by
    rw [hcdef, vecNorm_sq_eq_vecNormSq, hfdef, vecNormSq_smul, hsdef, sq]
    rw [hss]
  rcases eq_or_lt_of_le hc0 with hczero | hcpos
  · have hf0 : f = 0 := eq_zero_of_vecNorm_eq_zero hczero.symm
    have hu0 : u = 0 := by rw [← hfu, hf0, smul_zero]
    have hJ0 : responseJ U a u (σ0 • u) = 0 := by
      have hz := responseJ_smul (U := U) (a := a) (0 : ℝ) (0 : Vec d) (0 : Vec d)
      rw [hu0, smul_zero]
      simpa using hz
    have hrhs : σ0 * vecNormSq u * B = 0 := by
      have : c ^ 2 = 0 := by rw [← hczero]; norm_num
      rw [hcsq] at this
      rw [this, zero_mul]
    rw [hJ0, hrhs]
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    set eu : Vec d := c⁻¹ • f with heudef
    have heu : vecNorm eu = 1 := by
      rw [heudef, Algsuperdiff.Section5.Support.vecNorm_smul,
        abs_of_pos (inv_pos.mpr hcpos), ← hcdef,
        inv_mul_cancel₀ hcne]
    have hu : u = c • ((s : ℝ)⁻¹ • eu) := by
      rw [heudef, smul_smul, smul_smul, show c * s⁻¹ * c⁻¹ = s⁻¹ by field_simp]
      exact hfu.symm
    have hsu : σ0 • u = c • (s • eu) := by
      rw [heudef, smul_smul, smul_smul, show c * s * c⁻¹ = s by field_simp]
      exact hfs.symm
    have hhom : responseJ U a u (σ0 • u)
        = c ^ 2 * responseJ U a ((s : ℝ)⁻¹ • eu) (s • eu) := by
      have hq := responseJ_smul (U := U) (a := a) c ((s : ℝ)⁻¹ • eu) (s • eu)
      rw [← hu, ← hsu] at hq
      exact hq
    rw [hhom, ← hcsq]
    exact mul_le_mul_of_nonneg_left (hB eu heu) (sq_nonneg c)

/-! ## The block-load structure at an isotropic background -/

private theorem ofFullBlockVec_mulVec (M : FullBlockMat d) (P : BlockVec d) :
    ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) =
      blockMatVecMul (ofFullBlockMat M) P := by
  have h := toFullBlockVec_blockMatVecMul (ofFullBlockMat M) P
  rw [toFullBlockMat_ofFullBlockMat] at h
  rw [← h, ofFullBlockVec_toFullBlockVec]

/-- The two structural facts about a normalized block probe: its co-load is the
image under the constant block matrix, and its quadratic normalization is `1`.
Both are representation free -- the matrix square root never has to be
computed. -/
theorem blockProbe_of_mem_valueSet {a0 : Mat d} {lam Lam : ℝ}
    (ha0 : IsEllipticMatrix lam Lam a0) {e : FullBlockVec d}
    (he : Ch02.fullBlockVecNormSq e = 1) :
    ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e) =
        blockMatVecMul (constantBlockMatrix a0)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)) ∧
      blockVecDot (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (blockMatVecMul (constantBlockMatrix a0)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))) = 1 := by
  classical
  set M : FullBlockMat d := Ch02.constantFullBlockMatrix a0 with hMdef
  set S : FullBlockMat d := Ch02.constantFullBlockMatrixSqrt a0 with hSdef
  have hMpos : M.PosDef := by
    rw [hMdef]
    exact constantFullBlockMatrix_posDef_of_isEllipticMatrix (a0 := a0) ha0
  have hSunit : IsUnit S := by
    rw [hSdef, Ch02.constantFullBlockMatrixSqrt, ← hMdef]
    simpa using (CFC.isUnit_sqrt_iff M).2 hMpos.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det (A := S)).mp hSunit
  have hSS : S * S = M := by
    have hsq : S ^ 2 = M := by
      rw [hSdef, Ch02.constantFullBlockMatrixSqrt, ← hMdef]
      simpa using CFC.sq_sqrt M hMpos.posSemidef.nonneg
    rwa [pow_two] at hsq
  set P : BlockVec d := ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)
    with hPdef
  have htoP : toFullBlockVec P = Matrix.mulVec S⁻¹ e := by
    rw [hPdef, toFullBlockVec_ofFullBlockVec, Ch02.constantFullBlockMatrixInvSqrt, hSdef]
  have hMS : M * S⁻¹ = S := by
    rw [← hSS, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.mul_one]
  have hSSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hco : blockMatVecMul (constantBlockMatrix a0) P =
      ofFullBlockVec (Matrix.mulVec S e) := by
    have hofM : ofFullBlockMat M = constantBlockMatrix a0 := by
      rw [hMdef, Ch02.constantFullBlockMatrix, ofFullBlockMat_toFullBlockMat]
    calc blockMatVecMul (constantBlockMatrix a0) P
        = ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) := by
          rw [ofFullBlockVec_mulVec, hofM]
      _ = ofFullBlockVec (Matrix.mulVec M (Matrix.mulVec S⁻¹ e)) := by rw [htoP]
      _ = ofFullBlockVec (Matrix.mulVec (M * S⁻¹) e) := by
          rw [Matrix.mulVec_mulVec]
      _ = ofFullBlockVec (Matrix.mulVec S e) := by rw [hMS]
  refine ⟨hco.symm, ?_⟩
  have hnorm :=
    fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq (a0 := a0) ha0 P
  rw [htoP, ← hSdef, Matrix.mulVec_mulVec, hSSinv] at hnorm
  rw [← hnorm, Matrix.one_mulVec]
  exact he

/-! ## The conversion -/

/-- **`e.bfJ.general`, in the form the manuscript uses it**.

At the isotropic background `sigma0 I`, the normalized block-response maximum of
one cube -- the maximum of the *doubled* response over the `2d`-dimensional unit
sphere, i.e. the inner quantity of `d.mathcal.E` -- is bounded by the sum of two
scalar bounds: one for the field `a` and one for its transpose `a^t`, each taken
over the scalar loads `(sigma0^{-1/2} e, sigma0^{1/2} e)` with `|e| = 1`.

The constant is `1`; the manuscript's display carries a `C(d)`. -/
theorem normalizedBlockResponseMax_scalarMatrix_le [NeZero d]
    (F : TriadicCoeffFamily d) (R : TriadicCube d) {σ0 : ℝ} (hσ0 : 0 < σ0)
    {Jf Jt : ℝ}
    (hfld : ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤ Jf)
    (htrn : ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R).transpose
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤ Jt) :
    normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) ≤ Jf + Jt := by
  classical
  obtain ⟨e0, he0⟩ := exists_vecNorm_eq_one (d := d)
  have hJf0 : 0 ≤ Jf :=
    le_trans (responseJ_nonneg (cubeDomain R) (F.coeffOn R) _ _) (hfld e0 he0)
  have hJt0 : 0 ≤ Jt :=
    le_trans (responseJ_nonneg (cubeDomain R) (F.coeffOn R).transpose _ _) (htrn e0 he0)
  have ha0 : IsEllipticMatrix σ0 σ0 (scalarMatrix (d := d) σ0) :=
    isEllipticMatrix_scalarMatrix hσ0
  refine Real.sSup_le ?_ (by linarith only [hJf0, hJt0])
  rintro x ⟨e, he, rfl⟩
  set P : BlockVec d :=
    ofFullBlockVec
      (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) σ0)) e) with hPdef
  obtain ⟨hco, hquad⟩ := blockProbe_of_mem_valueSet (a0 := scalarMatrix (d := d) σ0) ha0 he
  have hblock : blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) P =
      (σ0 • P.1, σ0⁻¹ • P.2) := by
    rw [constantBlockMatrix_scalarMatrix hσ0]
    have hz : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
      intro x
      funext i
      simp [matVecMul]
    simp only [blockMatVecMul, matVecMul_scalarMatrix, hz, add_zero, zero_add]
  rw [hco, hblock]
  have hquad' : σ0 * vecNormSq P.1 + σ0⁻¹ * vecNormSq P.2 = 1 := by
    rw [hblock] at hquad
    simpa [blockVecDot, vecNormSq, vecDot_smul_right] using hquad
  set p : Vec d := P.1 with hpdef
  set q : Vec d := P.2 with hqdef
  set u : Vec d := p - σ0⁻¹ • q with hudef
  set v : Vec d := p + σ0⁻¹ • q with hvdef
  have hσ0ne : σ0 ≠ 0 := ne_of_gt hσ0
  have hu : σ0 • p - q = σ0 • u := by
    rw [hudef, smul_sub, smul_smul, mul_inv_cancel₀ hσ0ne, one_smul]
  have hv : σ0 • p + q = σ0 • v := by
    rw [hvdef, smul_add, smul_smul, mul_inv_cancel₀ hσ0ne, one_smul]
  have hvcomm : σ0⁻¹ • q + p = v := by
    rw [hvdef, add_comm]
  have hsplit :
      doubledResponseJ (cubeDomain R) (F.coeffOn R) P (σ0 • P.1, σ0⁻¹ • P.2)
        = (1 / 2 : ℝ) * responseJ (cubeDomain R) (F.coeffOn R) u (σ0 • u)
          + (1 / 2 : ℝ) * responseJ (cubeDomain R) (F.coeffOn R).transpose v (σ0 • v) := by
    have hP : P = (p, q) := rfl
    rw [hP]
    rw [doubledResponseJ_eq_half_responseJ_adjoint_sum (cubeDomain R) (F.coeffOn R)
      p (σ0⁻¹ • q) q (σ0 • p)]
    rw [← hudef, hu, hvcomm, hv]
  rw [hsplit]
  have hbf := responseJ_scalarLoad_le_of_unit_bound (F.coeffOn R) hσ0 hfld u
  have hbt := responseJ_scalarLoad_le_of_unit_bound (F.coeffOn R).transpose hσ0 htrn v
  have hbudget : σ0 * vecNormSq u + σ0 * vecNormSq v = 2 := by
    rw [hudef, hvdef, vecNormSq_sub, vecNormSq_add, vecNormSq_smul]
    have hσ0sq : σ0 * (σ0⁻¹ ^ 2 * vecNormSq q) = σ0⁻¹ * vecNormSq q := by
      field_simp
    have hexpand :
        σ0 * (vecNormSq p - 2 * vecDot p (σ0⁻¹ • q) + σ0⁻¹ ^ 2 * vecNormSq q)
          + σ0 * (vecNormSq p + 2 * vecDot p (σ0⁻¹ • q) + σ0⁻¹ ^ 2 * vecNormSq q)
          = 2 * (σ0 * vecNormSq p + σ0 * (σ0⁻¹ ^ 2 * vecNormSq q)) := by ring
    rw [hexpand, hσ0sq, hquad']
    norm_num
  have hu0 : 0 ≤ σ0 * vecNormSq u := mul_nonneg hσ0.le (vecNormSq_nonneg u)
  have hv0 : 0 ≤ σ0 * vecNormSq v := mul_nonneg hσ0.le (vecNormSq_nonneg v)
  have h1 : (1 / 2 : ℝ) * (σ0 * vecNormSq u * Jf) ≤ Jf := by
    have hcoef : (1 / 2 : ℝ) * (σ0 * vecNormSq u) ≤ 1 := by
      linarith only [hbudget, hv0]
    calc (1 / 2 : ℝ) * (σ0 * vecNormSq u * Jf)
        = ((1 / 2 : ℝ) * (σ0 * vecNormSq u)) * Jf := by ring
      _ ≤ 1 * Jf := mul_le_mul_of_nonneg_right hcoef hJf0
      _ = Jf := one_mul _
  have h2 : (1 / 2 : ℝ) * (σ0 * vecNormSq v * Jt) ≤ Jt := by
    have hcoef : (1 / 2 : ℝ) * (σ0 * vecNormSq v) ≤ 1 := by
      linarith only [hbudget, hu0]
    calc (1 / 2 : ℝ) * (σ0 * vecNormSq v * Jt)
        = ((1 / 2 : ℝ) * (σ0 * vecNormSq v)) * Jt := by ring
      _ ≤ 1 * Jt := mul_le_mul_of_nonneg_right hcoef hJt0
      _ = Jt := one_mul _
  have hstep1 : (1 / 2 : ℝ) * responseJ (cubeDomain R) (F.coeffOn R) u (σ0 • u)
      ≤ (1 / 2 : ℝ) * (σ0 * vecNormSq u * Jf) :=
    mul_le_mul_of_nonneg_left hbf (by norm_num)
  have hstep2 : (1 / 2 : ℝ) * responseJ (cubeDomain R) (F.coeffOn R).transpose v (σ0 • v)
      ≤ (1 / 2 : ℝ) * (σ0 * vecNormSq v * Jt) :=
    mul_le_mul_of_nonneg_left hbt (by norm_num)
  linarith only [hstep1, hstep2, h1, h2]

/-- **The conversion over a whole descendant family.**  This is the shape the
`(infinity,2)` scale sum of `mathcal E_{s,infinity,2}` reads at one scale. -/
theorem maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le [NeZero d]
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    {σ0 : ℝ} (hσ0 : 0 < σ0) {Jf Jt : ℝ}
    (hfld : ∀ R ∈ descendantsAtScale Q k, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤ Jf)
    (htrn : ∀ R ∈ descendantsAtScale Q k, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R).transpose
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤ Jt) :
    maxDescendantNormalizedBlockResponseAtScale Q k F (scalarMatrix (d := d) σ0)
      ≤ Jf + Jt := by
  classical
  unfold Ch02.maxDescendantNormalizedBlockResponseAtScale
  refine finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  exact normalizedBlockResponseMax_scalarMatrix_le F R hσ0 (hfld R hR) (htrn R hR)

/-! ## The mirror bound for the transposed field

The `a`-side of the reverse inequality is proved in the Section 2.4 bridge
(`responseJ_scalarLoading_le_normalizedBlockResponseMax`), whose doubled probe
is `(e/sqrt 2, -e/sqrt 2)` in the normalized coordinates.  Flipping that sign
selects the *adjoint* summand of the same splitting identity, which gives the
transpose analogue below.  Together with the conversion above, the block
maximum and the two scalar maxima control each other, so the transposed scalar
value set is bounded above -- which is what lets a caller form its supremum at
all. -/

/-- The normalized block probe used for the transposed annular response. -/
def transposeProbe (σ0 : ℝ) (e : Vec d) : BlockVec d :=
  ((Real.sqrt 2)⁻¹ • ((Real.sqrt σ0)⁻¹ • e), (Real.sqrt 2)⁻¹ • (Real.sqrt σ0 • e))

private theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith only [h]

private theorem blockMatVecMul_transposeProbe {σ0 : ℝ} (hσ0 : 0 < σ0) (e : Vec d) :
    blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) (transposeProbe σ0 e) =
      ((transposeProbe σ0 e).2, (transposeProbe σ0 e).1) := by
  have hs : (0 : ℝ) < Real.sqrt σ0 := Real.sqrt_pos.mpr hσ0
  have hss : Real.sqrt σ0 * Real.sqrt σ0 = σ0 := Real.mul_self_sqrt hσ0.le
  have hz : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x
    funext i
    simp [matVecMul]
  have h1 : σ0 * ((Real.sqrt 2)⁻¹ * (Real.sqrt σ0)⁻¹)
      = (Real.sqrt 2)⁻¹ * Real.sqrt σ0 := by
    field_simp
    linarith only [hss]
  have h2 : σ0⁻¹ * ((Real.sqrt 2)⁻¹ * Real.sqrt σ0)
      = (Real.sqrt 2)⁻¹ * (Real.sqrt σ0)⁻¹ := by
    field_simp
    linarith only [hss]
  rw [constantBlockMatrix_scalarMatrix hσ0]
  simp only [transposeProbe, blockMatVecMul, matVecMul_scalarMatrix, hz, add_zero,
    zero_add, smul_smul, Prod.mk.injEq]
  exact ⟨by rw [h1], by rw [h2]⟩

private theorem blockVecDot_transposeProbe {σ0 : ℝ} (hσ0 : 0 < σ0) {e : Vec d}
    (he : vecNorm e = 1) :
    blockVecDot (transposeProbe σ0 e) ((transposeProbe σ0 e).2, (transposeProbe σ0 e).1)
      = 1 := by
  have hs : (0 : ℝ) < Real.sqrt σ0 := Real.sqrt_pos.mpr hσ0
  have hee : vecDot e e = 1 := by
    have hsq := vecNorm_sq_eq_vecNormSq e
    rw [he] at hsq
    simpa [vecNormSq] using hsq.symm
  have h2 : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 := sqrt_two_inv_sq
  simp only [transposeProbe, blockVecDot, vecDot_smul_left, vecDot_smul_right, hee]
  field_simp
  linarith only [h2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sq_sqrt hσ0.le, Real.mul_self_sqrt hσ0.le]

private theorem doubledResponseJ_transposeProbe (F : TriadicCoeffFamily d)
    (R : TriadicCube d) (σ0 : ℝ) (e : Vec d) :
    doubledResponseJ (cubeDomain R) (F.coeffOn R) (transposeProbe σ0 e)
        ((transposeProbe σ0 e).2, (transposeProbe σ0 e).1) =
      responseJ (cubeDomain R) (F.coeffOn R).transpose
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) := by
  set c : ℝ := (Real.sqrt 2)⁻¹ with hc
  set y1 : Vec d := (Real.sqrt σ0)⁻¹ • e with hy1
  set y2 : Vec d := Real.sqrt σ0 • e with hy2
  have hgoal : doubledResponseJ (cubeDomain R) (F.coeffOn R) (transposeProbe σ0 e)
      ((transposeProbe σ0 e).2, (transposeProbe σ0 e).1)
      = doubledResponseJ (cubeDomain R) (F.coeffOn R) (c • y1, c • y2) (c • y2, c • y1) := rfl
  have hsplit := doubledResponseJ_eq_half_responseJ_adjoint_sum (cubeDomain R)
    (F.coeffOn R) (c • y1) (c • y1) (c • y2) (c • y2)
  have hzero1 : c • y1 - c • y1 = (0 : Vec d) := by simp
  have hzero2 : c • y2 - c • y2 = (0 : Vec d) := by simp
  have hadd1 : c • y1 + c • y1 = (2 * c) • y1 := by
    rw [← add_smul]
    congr 1
    ring
  have hadd2 : c • y2 + c • y2 = (2 * c) • y2 := by
    rw [← add_smul]
    congr 1
    ring
  have hzeroResp :
      responseJ (cubeDomain R) (F.coeffOn R) (0 : Vec d) (0 : Vec d) = 0 := by
    have hz := responseJ_smul (U := cubeDomain R) (a := F.coeffOn R)
      (0 : ℝ) (0 : Vec d) (0 : Vec d)
    simpa using hz
  have hhomog :
      responseJ (cubeDomain R) (F.coeffOn R).transpose ((2 * c) • y1) ((2 * c) • y2)
        = (2 * c) ^ 2 * responseJ (cubeDomain R) (F.coeffOn R).transpose y1 y2 :=
    responseJ_smul (U := cubeDomain R) (a := (F.coeffOn R).transpose) (2 * c) y1 y2
  have hcc : (2 * c) ^ 2 = 2 := by
    have h2 := sqrt_two_inv_sq
    have : c * c = 1 / 2 := h2
    nlinarith [this]
  rw [hgoal, hsplit, hzero1, hzero2, hadd1, hadd2, hzeroResp, hhomog, hcc]
  ring

/-- **The mirror of the Section 2.4 scalar-loading bound, for the transposed
field.**  The transposed scalar response at the normalized loading is one of the
normalized block-response values, hence at most the block maximum.  In
particular the transposed value set is bounded above. -/
theorem responseJ_transpose_scalarLoading_le_normalizedBlockResponseMax
    (F : TriadicCoeffFamily d) (R : TriadicCube d) {σ0 : ℝ} (hσ0 : 0 < σ0)
    {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain R) (F.coeffOn R).transpose
        ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)
      ≤ normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) := by
  classical
  have hmap := blockMatVecMul_transposeProbe (d := d) hσ0 e
  have hquad :
      blockVecDot (transposeProbe σ0 e)
        (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0))
          (transposeProbe σ0 e)) = 1 := by
    rw [hmap]
    exact blockVecDot_transposeProbe hσ0 he
  have hmem :=
    normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
      R F (isEllipticMatrix_scalarMatrix hσ0) (transposeProbe σ0 e) hquad
  rw [hmap, doubledResponseJ_transposeProbe F R σ0 e] at hmem
  unfold Ch02.normalizedBlockResponseMax
  exact le_csSup
    (normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := F) (Q := R) (R := R) (k := R.scale)
      (scalarMatrix (d := d) σ0) (by simp [descendantsAtScale_self]))
    hmem

/-! ## The Section 3/4 spelling -/

/-- The one-cube conversion at the Section 3 comparator literal
`sigma Id`, with the loads written as the Section 3 observables
`sigma^{-1/2} e` and `sigma^{1/2} e`. -/
theorem normalizedBlockResponseMax_isotropicComparator_le [NeZero d]
    (F : TriadicCoeffFamily d) (R : TriadicCube d)
    (sigma : Observable.PositiveScalar) {Jf Jt : ℝ}
    (hfld : ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R)
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jf)
    (htrn : ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R).transpose
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jt) :
    normalizedBlockResponseMax R F (Observable.isotropicComparatorMatrix sigma)
      ≤ Jf + Jt :=
  normalizedBlockResponseMax_scalarMatrix_le F R sigma.2 hfld htrn

/-- The descendant-family conversion at the Section 3 comparator literal. -/
theorem maxDescendantNormalizedBlockResponseAtScale_isotropicComparator_le [NeZero d]
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (sigma : Observable.PositiveScalar) {Jf Jt : ℝ}
    (hfld : ∀ R ∈ descendantsAtScale Q k, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R)
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jf)
    (htrn : ∀ R ∈ descendantsAtScale Q k, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain R) (F.coeffOn R).transpose
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jt) :
    maxDescendantNormalizedBlockResponseAtScale Q k F
        (Observable.isotropicComparatorMatrix sigma)
      ≤ Jf + Jt :=
  maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le F Q hk sigma.2 hfld htrn

end

end Algsuperdiff.Section4.Provider.Annular
