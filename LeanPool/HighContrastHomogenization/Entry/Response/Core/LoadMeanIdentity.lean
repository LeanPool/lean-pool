/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Transfer.ResponseContractionParameters

/-!
# High-contrast homogenization: Entry.Response.Core.LoadMeanIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response load and mean identity

This file proves the mean identity and the load/mean bounds `e.response.load.and.mean` of the
decomposition of
`adapted_response_core`: it shows the block mean `respM0` is symmetric, positive definite and
self-inverse under multiplication, expands the associated quadratic form under block scaling and
under a Loewner bound, and combines these into the response load-and-mean estimate
`response_load_and_mean`. The supporting matrix identities — the block-matrix-vector product under
scaling, the transpose of the full block matrix, and the quadratic-form symmetry and expansion
lemmas — are proved along the way.
-/

section
/-!
## R1 decomposition, part 3: the mean identity and the load/mean bounds

The two parts of the decomposition of R1
`adapted_response_core`: the mean identity and the load/mean bounds.
-/

open HCPolySupport.HighContrast (CoeffSpace blockScale matSqrt matSqrt_spec)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The mean identity -/

/-! ## The load/mean bounds -/

/-! ### Helpers for the load/mean bounds

The block-algebra lemmas the proof of `response_load_and_mean` rests on.  They are `private`
and local to this file; four of them (`respM0_qform_eq_sum_vecDot`,
`respM0_isSymm_of_metric_posDef`,
`respM0_blockPosDef_of_metric_posDef`, `blockSqrt_qform`) repeat the public declarations
`respM0_qform_split_canonicalMetric` and `blockSqrt_qform_blockVecDot` of
`HCPoly/Entry/Response/Core/SourceLoadBound.lean` and `respM0_isSymm_of_canonicalMetric_posDef` and
`respM0_blockPosDef_of_canonicalMetric_posDef` of
`HCPoly/Entry/Response/Core/AnnealedMeanDrift.lean`. -/

private theorem responseLoadMean_matVecMul_step (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

private theorem qform_of_loewner {A B : BlockMat d} (h : BlockMatLoewnerLE A B)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) ≤ blockVecDot X (blockMatVecMul B X) := by
  have h1 := h X
  linarith only [h1]

private theorem blockMatVecMul_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockScale c A) X = c • blockMatVecMul A X := by
  refine Prod.ext ?_ ?_ <;>
    · funext i
      simp [blockScale, blockMatVecMul, responseLoadMean_matVecMul_step, Matrix.smul_mulVec]

private theorem blockScale_qform (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X)
      = c * blockVecDot X (blockMatVecMul A X) := by
  rw [blockMatVecMul_blockScale, blockVecDot_smul_right]

private theorem blockCongr_isSymm (G : BlockMat d) {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) : IsSymmetricBlockMat (blockCongr G A) := by
  rw [blockCongr]
  refine isSymmetricBlockMat_of_isSymm ?_
  show ((toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G)ᵀ
    = (toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (isSymm_toFullBlockMat hA).eq, Matrix.mul_assoc]

private theorem qform_symm {A : BlockMat d} (hA : IsSymmetricBlockMat A) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul A Y) = blockVecDot Y (blockMatVecMul A X) := by
  have hS : (toFullBlockMat A)ᵀ = toFullBlockMat A := (isSymm_toFullBlockMat hA).eq
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]

private theorem qform_expand {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (U V : BlockVec d) (c : ℝ) :
    blockVecDot (U + c • V) (blockMatVecMul A (U + c • V))
      = blockVecDot U (blockMatVecMul A U) + 2 * c * blockVecDot V (blockMatVecMul A U)
        + c ^ 2 * blockVecDot V (blockMatVecMul A V) := by
  have hsym := qform_symm hA U V
  simp only [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
    blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right, hsym]
  ring

private theorem qform_add_le {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (h0 : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul A X)) (U V : BlockVec d) :
    blockVecDot (U + V) (blockMatVecMul A (U + V))
      ≤ 2 * blockVecDot U (blockMatVecMul A U) + 2 * blockVecDot V (blockMatVecMul A V) := by
  have h1 := qform_expand hA U V 1
  have h2 := qform_expand hA U V (-1)
  have h3 := h0 (U + (-1 : ℝ) • V)
  rw [one_smul] at h1
  norm_num at h1 h2 h3
  linarith only [h1, h2, h3]

/-! ### `M_0` and the swap -/

/-- `M_0^{-1} = diag(m^{-1}, m)`. -/
@[expose]
public noncomputable def respM0inv (F : BlockMat d) : BlockMat d :=
  ⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩

private theorem respM0_qform_eq_sum_vecDot (F : BlockMat d) (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (respM0 F) Y) =
      vecDot Y.1 (matVecMul (explicitCanonicalMetric F) Y.1) +
        vecDot Y.2 (matVecMul (explicitCanonicalMetric F)⁻¹ Y.2) := by
  simp [respM0, blockVecDot, blockMatVecMul, matVecMul, vecDot]

private theorem respM0_isSymm_of_metric_posDef {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    IsSymmetricBlockMat (respM0 F) := by
  intro α β
  have h1 := hm.isHermitian
  have h2 := hm.inv.isHermitian
  cases α with
  | inl i => cases β with
    | inl j =>
        show (explicitCanonicalMetric F) i j = (explicitCanonicalMetric F) j i
        simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
          (congrFun (congrFun h1 i) j).symm
    | inr j => rfl
  | inr i => cases β with
    | inl j => rfl
    | inr j =>
        show (explicitCanonicalMetric F)⁻¹ i j = (explicitCanonicalMetric F)⁻¹ j i
        simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
          (congrFun (congrFun h2 i) j).symm

private theorem respM0_qform_nonneg {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    (X : BlockVec d) : 0 ≤ blockVecDot X (blockMatVecMul (respM0 F) X) := by
  rw [respM0_qform_eq_sum_vecDot]
  have h1 : 0 ≤ vecDot X.1 (matVecMul (explicitCanonicalMetric F) X.1) := by
    simpa only [star_trivial] using! hm.posSemidef.dotProduct_mulVec_nonneg X.1
  have h2 : 0 ≤ vecDot X.2 (matVecMul (explicitCanonicalMetric F)⁻¹ X.2) := by
    simpa only [star_trivial] using! hm.inv.posSemidef.dotProduct_mulVec_nonneg X.2
  linarith only [h1, h2]

private theorem respM0_blockPosDef_of_metric_posDef {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    Book.Ch02.BlockPosDef (respM0 F) := by
  intro X hX
  rw [respM0_qform_eq_sum_vecDot]
  have h1 : 0 ≤ vecDot X.1 (matVecMul (explicitCanonicalMetric F) X.1) := by
    simpa only [star_trivial] using! hm.posSemidef.dotProduct_mulVec_nonneg X.1
  have h2 : 0 ≤ vecDot X.2 (matVecMul (explicitCanonicalMetric F)⁻¹ X.2) := by
    simpa only [star_trivial] using! hm.inv.posSemidef.dotProduct_mulVec_nonneg X.2
  have hsplit : X.1 ≠ 0 ∨ X.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX (Prod.ext hcon.1 hcon.2)
  rcases hsplit with h | h
  · have hv := hm.dotProduct_mulVec_pos h
    simp only [star_trivial] at hv
    have hv' : 0 < vecDot X.1 (matVecMul (explicitCanonicalMetric F) X.1) := hv
    linarith only [h1, h2, hv']
  · have hv := hm.inv.dotProduct_mulVec_pos h
    simp only [star_trivial] at hv
    have hv' : 0 < vecDot X.2 (matVecMul (explicitCanonicalMetric F)⁻¹ X.2) := hv
    linarith only [h1, h2, hv']

theorem respM0_full_posDef {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    (toFullBlockMat (respM0 F)).PosDef :=
  posDef_toFullBlockMat (respM0_isSymm_of_metric_posDef hm) (respM0_blockPosDef_of_metric_posDef hm)

/-- `M_0^{1/2}` is a genuine square root of `M_0` on the quadratic forms. -/
private theorem blockSqrt_qform {A : BlockMat d} (hA : (toFullBlockMat A).PosSemidef)
    (Y : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSqrt A) Y) (blockMatVecMul (blockSqrt A) Y) =
      blockVecDot Y (blockMatVecMul A Y) := by
  obtain ⟨hS, hSS⟩ := matSqrt_spec hA
  have hfull : toFullBlockMat (blockSqrt A) = matSqrt (toFullBlockMat A) := by
    simp only [blockSqrt, toFullBlockMat_ofFullBlockMat]
  have hT : (matSqrt (toFullBlockMat A))ᵀ = matSqrt (toFullBlockMat A) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hS.isHermitian.eq
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, hfull]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT,
    Matrix.mulVec_mulVec, hSS]
  exact dotProduct_comm _ _

/-- `M_0 M_0^{-1} = I`. -/
private theorem respM0_mul_inv {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    (W : BlockVec d) :
    blockMatVecMul (respM0 F) (blockMatVecMul (respM0inv F) W) = W := by
  have hu : IsUnit (explicitCanonicalMetric F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hm.isUnit
  simp [respM0, respM0inv, blockMatVecMul, responseLoadMean_matVecMul_step, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu]

/-- `𝐑 M_0 𝐑 = M_0^{-1}` on quadratic forms. -/
private theorem swap_qform (F : BlockMat d) (W : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSwap d) W)
        (blockMatVecMul (respM0 F) (blockMatVecMul (blockSwap d) W))
      = blockVecDot W (blockMatVecMul (respM0inv F) W) := by
  simp [blockSwap, Book.Ch02.blockR, respM0, respM0inv, blockMatVecMul, blockVecDot,
    responseLoadMean_matVecMul_step]
  ring

/-! ### The operator inequality `Ê M_0^{-1} Ê ≤ λ Ê` -/

/-- If `0 ≤ A` and `A ≤ λ M` with `M` invertible, then `x · A M^{-1} A x ≤ λ x · A x`:
take `V = x - λ^{-1} M^{-1} A x` in `0 ≤ V · A V`. -/
private theorem responseLoadMean_core {M0 Ah M0i : BlockMat d} {lam : ℝ} (hlam : 0 < lam)
    (hsym : IsSymmetricBlockMat Ah)
    (hA0 : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul Ah X))
    (hup : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul Ah X)
      ≤ lam * blockVecDot X (blockMatVecMul M0 X))
    (hinv : ∀ W : BlockVec d, blockMatVecMul M0 (blockMatVecMul M0i W) = W)
    (x : BlockVec d) :
    blockVecDot (blockMatVecMul Ah x) (blockMatVecMul M0i (blockMatVecMul Ah x))
      ≤ lam * blockVecDot x (blockMatVecMul Ah x) := by
  set w := blockMatVecMul Ah x with hw
  set y := blockMatVecMul M0i w with hy
  have hMy : blockMatVecMul M0 y = w := hinv w
  have hZ : blockVecDot w y = blockVecDot y (blockMatVecMul Ah x) := by
    rw [← hw, blockVecDot_comm]
  have hyy : blockVecDot y (blockMatVecMul Ah y) ≤ lam * blockVecDot y w := by
    have h := hup y
    rwa [hMy] at h
  have hexp := qform_expand hsym x y (-lam⁻¹)
  have h0 := hA0 (x + (-lam⁻¹) • y)
  rw [hexp] at h0
  rw [← hw, ← hZ] at h0
  -- `h0 : 0 ≤ x·Ax + 2(-1/λ)(w·y) + (1/λ)^2 (y·Ay)`
  have hZ' : blockVecDot y w = blockVecDot w y := blockVecDot_comm _ _
  have hsq : (0 : ℝ) ≤ (-lam⁻¹) ^ 2 := sq_nonneg _
  have hmul : (-lam⁻¹) ^ 2 * blockVecDot y (blockMatVecMul Ah y)
      ≤ (-lam⁻¹) ^ 2 * (lam * blockVecDot y w) := by
    exact mul_le_mul_of_nonneg_left hyy hsq
  have hid : (-lam⁻¹) ^ 2 * lam = lam⁻¹ := by
    field_simp
  have hstep : (-lam⁻¹) ^ 2 * (lam * blockVecDot y w) = lam⁻¹ * blockVecDot w y := by
    rw [← mul_assoc, hid, hZ']
  have hkey : 0 ≤ blockVecDot x (blockMatVecMul Ah x) - lam⁻¹ * blockVecDot w y := by
    have := hmul.trans_eq hstep
    linarith only [h0, this]
  have hfin := mul_le_mul_of_nonneg_left hkey hlam.le
  have harith : lam * (blockVecDot x (blockMatVecMul Ah x) - lam⁻¹ * blockVecDot w y)
      = lam * blockVecDot x (blockMatVecMul Ah x) - blockVecDot w y := by
    field_simp
  rw [mul_zero] at hfin
  rw [harith] at hfin
  -- goal is `blockVecDot w y ≤ lam * blockVecDot x (blockMatVecMul Ah x)`
  linarith only [hfin]

/-! ### The two bounds for one sign -/

private theorem load_and_mean_aux {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {Eh : BlockMat d} (hsym : IsSymmetricBlockMat Eh) {Cc lam : ℝ} (hCc : 0 < Cc)
    (hlam : 0 < lam)
    (hlow : BlockMatLoewnerLE (blockScale Cc⁻¹ (respM0 F)) Eh)
    (hup : BlockMatLoewnerLE Eh (blockScale lam (respM0 F)))
    (x : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) x)
        (blockMatVecMul (blockSqrt (respM0 F)) x)
        ≤ Cc * blockVecDot x (blockMatVecMul Eh x) ∧
      blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (blockResponseMean Eh x))
        (blockMatVecMul (blockSqrt (respM0 F)) (blockResponseMean Eh x))
        ≤ (2 * Cc + 2 * lam) * blockVecDot x (blockMatVecMul Eh x) := by
  have hM0psd := (respM0_full_posDef hm).posSemidef
  have hM0sym := respM0_isSymm_of_metric_posDef hm
  have hM00 := respM0_qform_nonneg hm
  have hlow' : ∀ X : BlockVec d, Cc⁻¹ * blockVecDot X (blockMatVecMul (respM0 F) X)
      ≤ blockVecDot X (blockMatVecMul Eh X) := by
    intro X
    have h := qform_of_loewner hlow X
    rwa [blockScale_qform] at h
  have hup' : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul Eh X)
      ≤ lam * blockVecDot X (blockMatVecMul (respM0 F) X) := by
    intro X
    have h := qform_of_loewner hup X
    rwa [blockScale_qform] at h
  have hE0 : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul Eh X) := fun X =>
    le_trans (mul_nonneg (inv_nonneg.mpr hCc.le) (hM00 X)) (hlow' X)
  have hload : blockVecDot x (blockMatVecMul (respM0 F) x)
      ≤ Cc * blockVecDot x (blockMatVecMul Eh x) := by
    have h := mul_le_mul_of_nonneg_left (hlow' x) hCc.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hCc), one_mul] at h
  refine ⟨?_, ?_⟩
  · rw [blockSqrt_qform hM0psd]
    exact hload
  · rw [blockSqrt_qform hM0psd, blockResponseMean]
    have hadd := qform_add_le hM0sym hM00 x
      (blockMatVecMul (blockSwap d) (blockMatVecMul Eh x))
    have hswap := swap_qform F (blockMatVecMul Eh x)
    have hcore := responseLoadMean_core (M0 := respM0 F) (M0i := respM0inv F) hlam hsym hE0 hup'
      (respM0_mul_inv hm) x
    linarith only [hadd, hswap, hcore, hload]

/-! ## The load/mean bounds -/

/-- **The load/mean bounds** `e.response.load.and.mean`:
`|M_0^{1/2}x^±|^2 <= C kappa_s^{1/2}` and `|M_0^{1/2}Y^±|^2 <= C kappa_s`.

Route, as printed.  Write `Q_A(X) = X · A X`, `x = x^±`, `Ê = Ê_t^±`, `w = Ê x`.

* `M_0^{1/2}` is a square root on quadratic forms (`blockSqrt_qform`), so both printed
  left-hand sides are `Q_{M_0}(x)` and `Q_{M_0}(Y)`.
* The **load bound** is the lower calibrated block alone: `C_c^{-1}M_0 <= Ê` gives
  `Q_{M_0}(x) <= C_c Q_Ê(x) = C_c (L^±)^2`, and `(L^±)^2 = 2E[J_t^±] + 2 <= 2C_e kappa_s^{1/2} + 2`
  is the energy-defect bound (`RespEnergyDefect`).
* For the **mean bound**, `Y = (I + R Ê)x` is `blockResponseMean`, i.e. `respYMinus`/`respYPlus`
  by definition, so
  `Q_{M_0}(Y) <= 2 Q_{M_0}(x) + 2 Q_{M_0}(R w)`.  Since `R M_0 R = M_0^{-1}`
  (`swap_qform`: both sides are `p·m p + q·m^{-1}q` with the two components exchanged),
  `Q_{M_0}(R w) = w · M_0^{-1} w`, and the operator inequality
  `Ê M_0^{-1} Ê <= C kappa_t^{1/2} Ê` of the printed proof is `responseLoadMean_core`: with
  `lam = C_c kappa_t^{1/2}` from the upper calibrated block, `0 <= (x - lam^{-1}M_0^{-1}w)·Ê
  (x - lam^{-1}M_0^{-1}w)` expands to `w·M_0^{-1}w <= lam Q_Ê(x)`.  No square root and no
  Cauchy-Schwarz is needed.
* The two are combined with `1 <= kappa_t <= kappa_s` (`response_imbalance_comparison`):
  `Q_{M_0}(Y) <= (2C_c + 2C_c kappa_t^{1/2})(2(C_e+1)kappa_s^{1/2})
  <= (4C_c kappa_s^{1/2})(2(C_e+1)kappa_s^{1/2}) = 8C_c(C_e+1)kappa_s`.

The constant is `C = 8 C_c (C_e + 1)`.

The statement carries the two premises `_hε : ε ∈ Set.Ioc 0 S.eps0` and
`_hσ : σ ∈ Set.Ioc 0 ε`, as do the other results of the decomposition.  They are needed for
the same reason: without them `S.one_le_B0` is unavailable, hence `1 ≤ B`, hence
`j_* < s` (`jStar_lt_s_of_raw`), hence `E_t ≤ E_s` and the comparison `kappa_t ≤ kappa_s`
are unavailable -- and the printed mean bound is `C kappa_s`, not
`C kappa_t^{1/2} kappa_s^{1/2}`, so the comparison is genuinely needed.  R1 carries both
premises, and the application passes `hε hσε`, which are in scope there. -/
theorem response_load_and_mean (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) (Cc Ce : ℝ) (_hCc : 0 < Cc) (_hCe : 0 < Ce) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ e : Vec d, vecDot e e = 1 →
          RespEnergyDefect Ce P jStar F s t e → RespLoadMean C P jStar F s t e := by
  refine ⟨8 * Cc * (Ce + 1), by positivity, ?_⟩
  intro ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw hcal e he hed
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  obtain ⟨hk1, hkts, -, -, -⟩ :=
    response_imbalance_comparison d _hd γ _hγ S _hS ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ
      Kg Src B jStar F s t raw
  -- scalars
  have hkt0 : (0 : ℝ) ≤ respKappa P jStar F t := le_trans zero_le_one hk1
  have hks1 : (1 : ℝ) ≤ respKappa P jStar F s := le_trans hk1 hkts
  have hq1 : (1 : ℝ) ≤ Real.sqrt (respKappa P jStar F s) := by
    simpa using Real.sqrt_le_sqrt hks1
  have hqq : Real.sqrt (respKappa P jStar F s) * Real.sqrt (respKappa P jStar F s)
      = respKappa P jStar F s := Real.mul_self_sqrt (by linarith only [hks1])
  have hqt0 : (0 : ℝ) ≤ Real.sqrt (respKappa P jStar F t) := Real.sqrt_nonneg _
  have hqts : Real.sqrt (respKappa P jStar F t) ≤ Real.sqrt (respKappa P jStar F s) :=
    Real.sqrt_le_sqrt hkts
  have hlam : 0 < Cc * Real.sqrt (respKappa P jStar F t) :=
    mul_pos _hCc (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hk1))
  -- the symmetric calibrated blocks
  have hEsym : IsSymmetricBlockMat (respMean P jStar F t) :=
    isSymmetricBlockMat_annealedBlock P _
  have hEm : IsSymmetricBlockMat (respEhatMinus P jStar F t) :=
    blockCongr_isSymm _ hEsym
  have hEp : IsSymmetricBlockMat (respEhatPlus P jStar F t) :=
    blockCongr_isSymm _ hEm
  obtain ⟨hlowm, hlowp, hupm, hupp, -, -⟩ := hcal
  obtain ⟨hJ0m, hJ0p, hJeqm, hJeqp, hJlem, hJlep, -, -, -, -⟩ := hed
  -- the two load identities
  have hLm : respLsqMinus P jStar F t e = 2 * respEJMinus P jStar F t e + 2 := by
    rw [hJeqm]; ring
  have hLp : respLsqPlus P jStar F t e = 2 * respEJPlus P jStar F t e + 2 := by
    rw [hJeqp]; ring
  have hLm0 : (0 : ℝ) ≤ respLsqMinus P jStar F t e := by rw [hLm]; linarith only [hJ0m]
  have hLp0 : (0 : ℝ) ≤ respLsqPlus P jStar F t e := by rw [hLp]; linarith only [hJ0p]
  have hLmu : respLsqMinus P jStar F t e
      ≤ 2 * (Ce + 1) * Real.sqrt (respKappa P jStar F s) := by
    rw [hLm]; linarith only [hJlem, hq1]
  have hLpu : respLsqPlus P jStar F t e
      ≤ 2 * (Ce + 1) * Real.sqrt (respKappa P jStar F s) := by
    rw [hLp]; linarith only [hJlep, hq1]
  -- the two block bounds
  obtain ⟨hxm, hym⟩ := load_and_mean_aux hm hEm _hCc hlam hlowm hupm
    (respxMinus P jStar F t e)
  obtain ⟨hxp, hyp⟩ := load_and_mean_aux hm hEp _hCc hlam hlowp hupp
    (respxPlus P jStar F t e)
  have hfac1 : 2 * Cc + 2 * (Cc * Real.sqrt (respKappa P jStar F t))
      ≤ 4 * Cc * Real.sqrt (respKappa P jStar F s) := by
    have ht : Cc * Real.sqrt (respKappa P jStar F t)
        ≤ Cc * Real.sqrt (respKappa P jStar F s) :=
      mul_le_mul_of_nonneg_left hqts _hCc.le
    have hs : Cc * 1 ≤ Cc * Real.sqrt (respKappa P jStar F s) :=
      mul_le_mul_of_nonneg_left hq1 _hCc.le
    linarith only [ht, hs]
  have hfac0 : (0 : ℝ) ≤ 4 * Cc * Real.sqrt (respKappa P jStar F s) :=
    mul_nonneg (by linarith only [_hCc] : (0:ℝ) ≤ 4 * Cc) (Real.sqrt_nonneg _)
  have hprod0 : ∀ q k : ℝ, q * q = k →
      (4 * Cc * q) * (2 * (Ce + 1) * q) = 8 * Cc * (Ce + 1) * k := by
    intro q k h
    rw [← h]; ring
  have hprod := hprod0 _ _ hqq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : respLsqMinus P jStar F t e ≤ 2 * (Ce + 1) * Real.sqrt (respKappa P jStar F s) :=
      hLmu
    have hle' : Cc * respLsqMinus P jStar F t e
        ≤ Cc * (2 * (Ce + 1) * Real.sqrt (respKappa P jStar F s)) :=
      mul_le_mul_of_nonneg_left hle _hCc.le
    have hX : 0 ≤ Cc * (Ce + 1) * Real.sqrt (respKappa P jStar F s) :=
      mul_nonneg (mul_nonneg _hCc.le (by linarith only [_hCe])) (Real.sqrt_nonneg _)
    have : Cc * respLsqMinus P jStar F t e
        ≤ 8 * Cc * (Ce + 1) * Real.sqrt (respKappa P jStar F s) := by
      linarith only [hle', hX]
    exact le_trans hxm this
  · have hle' : Cc * respLsqPlus P jStar F t e
        ≤ Cc * (2 * (Ce + 1) * Real.sqrt (respKappa P jStar F s)) :=
      mul_le_mul_of_nonneg_left hLpu _hCc.le
    have hX : 0 ≤ Cc * (Ce + 1) * Real.sqrt (respKappa P jStar F s) :=
      mul_nonneg (mul_nonneg _hCc.le (by linarith only [_hCe])) (Real.sqrt_nonneg _)
    have : Cc * respLsqPlus P jStar F t e
        ≤ 8 * Cc * (Ce + 1) * Real.sqrt (respKappa P jStar F s) := by
      linarith only [hle', hX]
    exact le_trans hxp this
  · refine le_trans hym (le_trans ?_ (le_of_eq hprod))
    exact mul_le_mul hfac1 hLmu hLm0 hfac0
  · refine le_trans hyp (le_trans ?_ (le_of_eq hprod))
    exact mul_le_mul hfac1 hLpu hLp0 hfac0

end HCPolySupport.HighContrast.Multiscale
end
