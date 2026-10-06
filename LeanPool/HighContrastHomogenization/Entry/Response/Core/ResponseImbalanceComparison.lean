/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SkewShearCongruence
public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss

/-!
# High-contrast homogenization: Entry.Response.Core.ResponseImbalanceComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response-imbalance comparison

This file proves the response-imbalance comparison and the matrix facts behind the
calibrated-blocks estimate `e.response.calibrated.blocks`: the calibration bundle `RespCalibrated`
bounds the canonical mean, the geometric mean, and the two centred energies `Ehat^∓` of the
recentred coefficients above and below, in terms of the determinant ratio and the canonical
imbalance. It shows the calibration bundle is preserved under congruence of the canonical mean,
that the response correction `g` is skew, and that the swapped conjugate block is positive
definite, and combines these facts into the comparison between the response imbalance and the
calibration bounds. It also records that the source load `L_s^±` is a sum of squares against
nonnegative weights, hence nonnegative, and the error-row arithmetic of the cutoff estimate
`e.response.cutoff.estimate`.
-/

section
open HCPolySupport.HighContrast (CoeffSpace isUnit_det_lowerRight matSqrt matSqrt_spec
  schurSigma)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-! ## The imbalance comparison -/

/-- **The imbalance comparison** `e.response.imbalance.comparison`:
`1 <= kappa_t <= kappa_s <= r^2 kappa_t` with `1 <= r = det E_s / det E_t < e^{d sigma}`.
(`1 <= r` is `det E_t <= det E_s`, which follows from `E_t <= E_s`; it is the implicit
side condition of the printed display.)

The first inequality is `Analysis.one_le_det_adaptedMean` together with the primal-adjoint
order `Analysis.adaptedMean_swapConj_le` (`e.matrix.annealed.sharp.order`,
`e.matrix.annealed.sharp.order`); the middle
one is subadditivity `Annealed.adaptedMean_antitone` and the eigenvalue-product argument of
`e.response.imbalance.comparison`; the last is `raw.det`, since
`detIncrement P q s t = log det E_s - log det E_t` by definition.

Premises `hε`, `hσ`: without them `1 ≤ B` and `jStar ≤ s` are unavailable. -/
theorem response_imbalance_comparison (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ)
    (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    1 ≤ respKappa P jStar F t ∧
      respKappa P jStar F t ≤ respKappa P jStar F s ∧
      respKappa P jStar F s ≤ respRatio P jStar F s t ^ 2 * respKappa P jStar F t ∧
      1 ≤ respRatio P jStar F s t ∧
      respRatio P jStar F s t < Real.exp ((d : ℝ) * σ) := by
  have := _raw.prob
  let : NeZero d := ⟨by omega⟩
  have hjs : (jStar : ℤ) < s :=
    jStar_lt_s_of_raw d _hd γ _hγ S ε σ Cglob Cprof Csrc Bresp hε hσ H P E Ψ Kg Src B jStar F
      s t _raw
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  have hEs : (toFullBlockMat (respMean P jStar F s)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm s
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hsS : IsSymmetricBlockMat (respMean P jStar F s) :=
    isSymmetricBlockMat_annealedBlock P _
  have hsT : IsSymmetricBlockMat (respMean P jStar F t) :=
    isSymmetricBlockMat_annealedBlock P _
  have hbS : Book.Ch02.BlockPosDef (respMean P jStar F s) := blockPosDef_of_full hEs
  have hbT : Book.Ch02.BlockPosDef (respMean P jStar F t) := blockPosDef_of_full hEt
  have hts : toFullBlockMat (respMean P jStar F t) ≤ toFullBlockMat (respMean P jStar F s) :=
    Analysis.matrixOrder_of_blockMatLoewnerLE hEt.isHermitian hEs.isHermitian
      (Annealed.adaptedMean_antitone d _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
        (explicitCanonicalMetric F) hm s t (le_of_lt hjs) (le_of_lt _raw.hst))
  obtain ⟨hr1, hEsr⟩ := le_detRatio_smul_of_le hEt hEs hts
  have hrpos : 0 < respRatio P jStar F s t := lt_of_lt_of_le zero_lt_one hr1
  -- conjunct 1
  have hswapT : toFullBlockMat (blockSwap d) * (toFullBlockMat (respMean P jStar F t))⁻¹ *
      toFullBlockMat (blockSwap d) ≤ toFullBlockMat (respMean P jStar F t) := by
    have h := Analysis.matrixOrder_of_blockMatLoewnerLE (Analysis.swapConj_posDef hEt).isHermitian hEt.isHermitian
      (Analysis.adaptedMean_swapConj_le _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
        (explicitCanonicalMetric F) hm t)
    rwa [toFullBlockMat_ofFullBlockMat] at h
  have hk1 : 1 ≤ respKappa P jStar F t := one_le_canonicalImbalance _hd hsT hbT hswapT
  -- conjunct 2
  have hk2 : respKappa P jStar F t ≤ respKappa P jStar F s :=
    canonicalImbalance_mono hsT hbT hsS hbS hts
  -- conjunct 3
  have hktnn : (0 : ℝ) ≤ respKappa P jStar F t := le_trans zero_le_one hk1
  have hinv : (toFullBlockMat (respMean P jStar F t))⁻¹
      ≤ respRatio P jStar F s t • (toFullBlockMat (respMean P jStar F s))⁻¹ := by
    have h := inv_le_inv_of_le hEs (posDef_smul hrpos hEt) hEsr
    rw [inv_smul_of_isUnit (ne_of_gt hrpos) ((Matrix.isUnit_iff_isUnit_det _).mp hEt.isUnit)] at h
    have h2 := smul_le_smul_left (le_of_lt hrpos) h
    rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul] at h2
  have hRt : (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (swap_hermitian d).eq
  have hRconj : toFullBlockMat (blockSwap d) * (toFullBlockMat (respMean P jStar F t))⁻¹ *
        toFullBlockMat (blockSwap d)
      ≤ respRatio P jStar F s t • (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (respMean P jStar F s))⁻¹ * toFullBlockMat (blockSwap d)) := by
    have h := Analysis.matrix_congr_le hinv (toFullBlockMat (blockSwap d))
    rw [hRt] at h
    rwa [Matrix.mul_smul, Matrix.smul_mul] at h
  have hk3 : respKappa P jStar F s ≤ respRatio P jStar F s t ^ 2 * respKappa P jStar F t := by
    refine imbalance_le_of_le hEs (mul_nonneg (sq_nonneg _) hktnn) ?_
    have hkt := le_of_imbalance_le hEt (le_refl (respKappa P jStar F t))
    have step1 := hEsr.trans (smul_le_smul_left (le_of_lt hrpos) hkt)
    have step2 := smul_le_smul_left (le_of_lt hrpos) (smul_le_smul_left hktnn hRconj)
    have hchain := step1.trans step2
    have heq : respRatio P jStar F s t • (respKappa P jStar F t •
          (respRatio P jStar F s t • (toFullBlockMat (blockSwap d) *
            (toFullBlockMat (respMean P jStar F s))⁻¹ * toFullBlockMat (blockSwap d))))
        = (respRatio P jStar F s t ^ 2 * respKappa P jStar F t) •
          (toFullBlockMat (blockSwap d) * (toFullBlockMat (respMean P jStar F s))⁻¹ *
            toFullBlockMat (blockSwap d)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rwa [heq] at hchain
  -- conjunct 5
  have hds : (1 : ℝ) ≤ (toFullBlockMat (respMean P jStar F s)).det :=
    Analysis.one_le_det_adaptedMean _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm s
  have hdt : (1 : ℝ) ≤ (toFullBlockMat (respMean P jStar F t)).det :=
    Analysis.one_le_det_adaptedMean _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hdiv : Real.log (respRatio P jStar F s t)
      = Real.log ((toFullBlockMat (respMean P jStar F s)).det)
        - Real.log ((toFullBlockMat (respMean P jStar F t)).det) := by
    simp only [respRatio]
    exact Real.log_div (ne_of_gt (by linarith only [hds])) (ne_of_gt (by linarith only [hdt]))
  have hloss : detIncrement P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t
      = Real.log (respRatio P jStar F s t) := by
    rw [hdiv]; rfl
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hdetraw := _raw.det
  rw [hloss] at hdetraw
  have hlogr : Real.log (respRatio P jStar F s t) < (d : ℝ) * σ := by
    have h := mul_lt_mul_of_pos_left hdetraw hdpos
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hdpos), one_mul] at h
  exact ⟨hk1, hk2, hk3, hr1, (Real.log_lt_iff_lt_exp hrpos).mp hlogr⟩

/-! ## Helpers for the calibrated-blocks estimate

New `private` lemmas proved for `e.response.calibrated.blocks`.
They are inserted here, immediately above `response_calibrated_blocks`, so that its body can
cite them.

The route they implement: the Riccati sandwich `M(E) ≤ E ≤ 𝔡(E)^{1/2}M(E)` (`p.response.transfer`),
the self-duality `𝐑M(F)⁻¹𝐑 = M(F)` and the congruence `G^t M(F) G = M_0` , and
the two-sided comparison of canonical means that carries the cost `√(r(1+ξ)/(1-ξ))`. -/

/-- The swap conjugate of a positive definite full block is positive definite. -/
theorem respCalib_swapConj_posDef {A : FullBlockMat d} (hA : A.PosDef) :
    (toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d)).PosDef := by
  have h := Analysis.swapConj_posDef (F := ofFullBlockMat A)
    (by simpa only [toFullBlockMat_ofFullBlockMat] using hA)
  simpa only [toFullBlockMat_ofFullBlockMat] using h

/-- Conjugation by the swap block is monotone. -/
private theorem respCalib_swapConj_mono {A B : FullBlockMat d} (h : A ≤ B) :
    toFullBlockMat (blockSwap d) * A * toFullBlockMat (blockSwap d) ≤
      toFullBlockMat (blockSwap d) * B * toFullBlockMat (blockSwap d) := by
  have hR : (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (swap_hermitian d).eq
  have hc := Analysis.matrix_congr_le h (toFullBlockMat (blockSwap d))
  rwa [hR] at hc

/-- `A # B ≤ A` whenever `B ≤ A`: the left half of the Riccati sandwich
`M(E) ≤ E ≤ 𝔡(E)^{1/2}M(E)` (`p.response.transfer`), applied with `B = E^♯ ≤ E`. -/
theorem respCalib_geoMean_le_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (h : B ≤ A) :
    GeometricMean.geoMean A B ≤ A := by
  have hm := GeometricMean.geoMean_mono_right hA hB hA h
  rwa [GeometricMean.geoMean_self hA] at hm

/-- `A ≤ c • B` implies `A ≤ √c • (A # B)`: the right half of the Riccati sandwich
(`p.response.transfer`).  Indeed `A = A # A ≤ A # (c • B) = √c • (A # B)`. -/
theorem respCalib_le_sqrt_smul_geoMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 0 < c)
    (h : A ≤ c • B) : A ≤ Real.sqrt c • GeometricMean.geoMean A B := by
  have h1 : GeometricMean.geoMean A A ≤ GeometricMean.geoMean A (c • B) :=
    GeometricMean.geoMean_mono_right hA hA (posDef_smul hc hB) h
  rw [GeometricMean.geoMean_self hA] at h1
  have h2 : GeometricMean.geoMean A (c • B) = Real.sqrt c • GeometricMean.geoMean A B := by
    have hs := GeometricMean.geoMean_smul hA hB (a := 1) (b := c) one_pos hc
    rwa [one_smul, one_mul] at hs
  rwa [h2] at h1

/-- Two-sided comparison of canonical means: `A ≤ a • F` and `F ≤ b • A` give
`M(A) ≤ √(ab) • M(F)`.  This is the congruence cost `√(r(1+ξ)/(1-ξ))` of
`p.response.transfer`: the first argument of the geometric mean is monotone and
the second, `𝐑·⁻¹𝐑`, is antitone, so a two-sided comparison is what the mean consumes. -/
theorem respCalib_canonicalMean_le {A F : FullBlockMat d}
    (hA : A.PosDef) (hF : F.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : A ≤ a • F) (h2 : F ≤ b • A) :
    GeometricMean.geoMean A (toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d)) ≤
      Real.sqrt (a * b) •
        GeometricMean.geoMean F
          (toFullBlockMat (blockSwap d) * F⁻¹ * toFullBlockMat (blockSwap d)) := by
  have hRA := respCalib_swapConj_posDef hA
  have hRF := respCalib_swapConj_posDef hF
  have hinv : A⁻¹ ≤ b • F⁻¹ := by
    have hstep := inv_le_inv_of_le hF (posDef_smul hb hA) h2
    rw [inv_smul_of_isUnit hb.ne' (GeometricMean.isUnit_det_of_posDef hA)] at hstep
    have hscal := smul_le_smul_left (c := b) hb.le hstep
    rwa [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] at hscal
  have hconj : toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d) ≤
      b • (toFullBlockMat (blockSwap d) * F⁻¹ * toFullBlockMat (blockSwap d)) := by
    have hc := respCalib_swapConj_mono hinv
    rwa [Matrix.mul_smul, Matrix.smul_mul] at hc
  have hmono := GeometricMean.geoMean_mono hA (posDef_smul ha hF) hRA
    (posDef_smul hb hRF) h1 hconj
  rwa [GeometricMean.geoMean_smul hF hRF ha hb] at hmono

/-- If `A ≤ B` are positive definite then `B ≤ (det B / det A) • A`.  With `A = E_t` and
`B = E_s` this is the comparison `E_s ≤ r E_t` of `e.response.calibrated.blocks`, `r` being the
determinant ratio of `p.response.transfer`: conjugating by `E_t^{-1/2}` turns `E_t ≤ E_s` into `1
≤ X` with
`det X = r`, and every eigenvalue of such an `X` is at most `det X`. -/
theorem respCalib_le_detRatio_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (h : A ≤ B) :
    B ≤ (B.det / A.det) • A := by
  have hP : (matSqrt A).PosDef := HCPolySupport.HighContrast.posDef_matSqrt hA
  have hPP : matSqrt A * matSqrt A = A := (matSqrt_spec hA.posSemidef).2
  have hPh : (matSqrt A)ᴴ = matSqrt A := HCPolySupport.HighContrast.conjTranspose_matSqrt hA.posSemidef
  have hPih : ((matSqrt A)⁻¹)ᴴ = (matSqrt A)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hPh]
  obtain ⟨hPR, hRP⟩ := GeometricMean.sqrtCancel hA
  rw [HCPolySupport.HighContrast.matSqrt_inv hA] at hPR hRP
  have hX : ((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹).PosDef := GeometricMean.posDef_conj_of_posDef hB hP.inv
  have h1X : (1 : Matrix ι ι ℝ) ≤ (matSqrt A)⁻¹ * B * (matSqrt A)⁻¹ := by
    have hc := HCPolySupport.HighContrast.conj_le_conj' hPih h
    have hl : (matSqrt A)⁻¹ * A * (matSqrt A)⁻¹ = 1 := by
      calc (matSqrt A)⁻¹ * A * (matSqrt A)⁻¹
          = (matSqrt A)⁻¹ * (matSqrt A * matSqrt A) * (matSqrt A)⁻¹ := by rw [hPP]
        _ = ((matSqrt A)⁻¹ * matSqrt A) * (matSqrt A * (matSqrt A)⁻¹) := by noncomm_ring
        _ = 1 := by rw [hRP, hPR, Matrix.one_mul]
    rwa [hl] at hc
  have hdetP : (matSqrt A).det * (matSqrt A).det = A.det := by
    rw [← Matrix.det_mul, hPP]
  have hdetPi : ((matSqrt A)⁻¹).det = ((matSqrt A).det)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← Matrix.det_mul, hPR, Matrix.det_one]
  have hAne : A.det ≠ 0 := hA.det_pos.ne'
  have hPne : (matSqrt A).det ≠ 0 := hP.det_pos.ne'
  have hdetX : ((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹).det = B.det / A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetPi, ← hdetP]
    field_simp
  have hXle := le_det_smul_one_of_one_le hX h1X
  have hc2 := HCPolySupport.HighContrast.conj_le_conj' hPh hXle
  have hl2 : matSqrt A * ((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹) * matSqrt A = B := by
    calc matSqrt A * ((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹) * matSqrt A
        = (matSqrt A * (matSqrt A)⁻¹) * B * ((matSqrt A)⁻¹ * matSqrt A) := by noncomm_ring
      _ = B := by rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]
  have hr2 : matSqrt A *
      (((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹).det • (1 : Matrix ι ι ℝ)) * matSqrt A
      = ((matSqrt A)⁻¹ * B * (matSqrt A)⁻¹).det • A := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP]
  rw [hl2, hr2, hdetX] at hc2
  exact hc2

/-! ### Block-algebra helpers. -/

/-- The swap block `𝐑` in `fromBlocks` form (`e.physical.endpoint.norm`). -/
private theorem respCalib_swap_full (d : ℕ) :
    toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
  rw [toFullBlockMat_eq_fromBlocks]; rfl

/-- The shear `G = ((Id, 0), (g, Id))` in `fromBlocks` form
(`p.response.transfer`). -/
private theorem respCalib_respG_full (F : BlockMat d) :
    toFullBlockMat (respG F) = Matrix.fromBlocks (1 : Mat d) 0 (respg F) 1 := by
  rw [toFullBlockMat_eq_fromBlocks]; rfl

/-- `D = diag(Id, -Id)` in `fromBlocks` form (`p.response.transfer`). -/
private theorem respCalib_blockD_full (d : ℕ) :
    toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
  rw [toFullBlockMat_eq_fromBlocks]; rfl

/-- `M_0 = diag(m, m⁻¹)` in `fromBlocks` form (`p.response.transfer`). -/
private theorem respCalib_respM0_full (F : BlockMat d) :
    toFullBlockMat (respM0 F)
      = Matrix.fromBlocks (explicitCanonicalMetric F) 0 0 (explicitCanonicalMetric F)⁻¹ := by
  rw [toFullBlockMat_eq_fromBlocks]; rfl

/-- CG block positivity from positivity of the full `2d`-by-`2d` representation. -/
private theorem respCalib_blockPosDef_of_full {M : FullBlockMat d} (hp : M.PosDef) :
    Book.Ch02.BlockPosDef (ofFullBlockMat M) := by
  intro X hX
  have hn : toFullBlockVec X ≠ 0 := by
    intro h
    apply hX
    have hz := congrArg ofFullBlockVec h
    simpa only [ofFullBlockVec_toFullBlockVec] using! hz
  simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, star_trivial] using hp.dotProduct_mulVec_pos hn

/-- The canonical mean is the geometric mean of `F` and `F# = 𝐑F⁻¹𝐑` in the full carrier. -/
theorem respCalib_canonicalMean_full (F : BlockMat d) :
    toFullBlockMat (canonicalMean F)
      = GeometricMean.geoMean (toFullBlockMat F)
          (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)) := by
  simp only [canonicalMean, toFullBlockMat_ofFullBlockMat]

/-- `m(F)` is the inverse of the lower-right block of the canonical mean `M(F)`. -/
private theorem respCalib_explicitCanonicalMetric_eq (F : BlockMat d) :
    explicitCanonicalMetric F = (canonicalMean F).lowerRight⁻¹ := by
  unfold explicitCanonicalMetric canonicalMean GeometricMean.geoMean
  congr 2
  simp only [Matrix.mul_assoc]

/-- Abstract self-duality: the geometric-mean solution of the Riccati equation satisfies
`M R M = R`. -/
private theorem respCalib_selfDual_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A R M : Matrix ι ι ℝ} (hA : A.PosDef) (hM : M.PosDef)
    (hNpos : (R * M⁻¹ * R).PosDef) (hRR : R * R = 1)
    (hric : M * A⁻¹ * M = R * A⁻¹ * R)
    (hMeq : GeometricMean.geoMean A (R * A⁻¹ * R) = M) :
    M * R * M = R := by
  have hMM := Matrix.nonsing_inv_mul M (GeometricMean.isUnit_det_of_posDef hM)
  have hMM' := Matrix.mul_nonsing_inv M (GeometricMean.isUnit_det_of_posDef hM)
  have hkey : (R * M⁻¹ * R) * A⁻¹ * (R * M⁻¹ * R) = R * A⁻¹ * R := by
    have hmid : M⁻¹ * (R * A⁻¹ * R) * M⁻¹ = A⁻¹ := by
      rw [← hric]
      calc M⁻¹ * (M * A⁻¹ * M) * M⁻¹ = (M⁻¹ * M) * A⁻¹ * (M * M⁻¹) := by noncomm_ring
        _ = A⁻¹ := by rw [hMM, hMM', Matrix.one_mul, Matrix.mul_one]
    calc (R * M⁻¹ * R) * A⁻¹ * (R * M⁻¹ * R)
        = R * (M⁻¹ * (R * A⁻¹ * R) * M⁻¹) * R := by noncomm_ring
      _ = R * A⁻¹ * R := by rw [hmid]
  have hself : R * M⁻¹ * R = M := by
    have hg := GeometricMean.eq_geoMean_of_riccati hA hNpos hkey
    rwa [hMeq] at hg
  have hinv : M⁻¹ = R * M * R := by
    have h := congrArg (fun X : Matrix ι ι ℝ => R * X * R) hself
    have hl : R * (R * M⁻¹ * R) * R = M⁻¹ := by
      calc R * (R * M⁻¹ * R) * R = (R * R) * M⁻¹ * (R * R) := by noncomm_ring
        _ = M⁻¹ := by rw [hRR, Matrix.one_mul, Matrix.mul_one]
    rw [hl] at h
    exact h
  have h1 : M * (R * M * R) = 1 := by
    rw [← hinv]; exact hMM'
  calc M * R * M = (M * R * M) * (R * R) := by rw [hRR, Matrix.mul_one]
    _ = (M * (R * M * R)) * R := by noncomm_ring
    _ = R := by rw [h1, Matrix.one_mul]

/-- Self-duality of the canonical mean, `M(F) 𝐑 M(F) = 𝐑` (`p.response.transfer`). -/
private theorem respCalib_canonicalMean_selfDual {F : BlockMat d}
    (hA : (toFullBlockMat F).PosDef) :
    toFullBlockMat (canonicalMean F) * toFullBlockMat (blockSwap d) *
        toFullBlockMat (canonicalMean F) = toFullBlockMat (blockSwap d) := by
  have hB := respCalib_swapConj_posDef hA
  have hM : (toFullBlockMat (canonicalMean F)).PosDef := by
    rw [respCalib_canonicalMean_full]; exact GeometricMean.geoMeanPosDef hA hB
  have hric : toFullBlockMat (canonicalMean F) * (toFullBlockMat F)⁻¹ *
      toFullBlockMat (canonicalMean F) =
      toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) := by
    rw [respCalib_canonicalMean_full]; exact GeometricMean.geoMean_riccati hA hB
  exact respCalib_selfDual_mul hA hM (respCalib_swapConj_posDef hM)
    (Analysis.toFullBlockMat_blockSwap_mul_self d) hric (respCalib_canonicalMean_full F).symm

/-- Auxiliary: `D U + L D = 0` with `D` invertible gives `D⁻¹L = -(U D⁻¹)`. -/
private theorem respCalib_skew_aux {n : Type*} [Fintype n] [DecidableEq n]
    {D L U : Matrix n n ℝ} (hDu : IsUnit D.det) (hid : D * U + L * D = 0) :
    D⁻¹ * L = -(U * D⁻¹) := by
  have hDR := Matrix.mul_nonsing_inv _ hDu
  have hDL := Matrix.nonsing_inv_mul _ hDu
  have hkey2 : L * D = -(D * U) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hid
  calc D⁻¹ * L = D⁻¹ * L * (D * D⁻¹) := by rw [hDR, Matrix.mul_one]
    _ = D⁻¹ * (L * D) * D⁻¹ := by noncomm_ring
    _ = D⁻¹ * (-(D * U)) * D⁻¹ := by rw [hkey2]
    _ = -((D⁻¹ * D) * (U * D⁻¹)) := by noncomm_ring
    _ = -(U * D⁻¹) := by rw [hDL, Matrix.one_mul]

/-- `M(F)` is positive definite (`p.response.transfer`). -/
private theorem respCalib_canonicalMean_posDef {F : BlockMat d} (hA : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (canonicalMean F)).PosDef := by
  rw [respCalib_canonicalMean_full]
  exact GeometricMean.geoMeanPosDef hA (respCalib_swapConj_posDef hA)

/-- `M(F)` is a symmetric doubled block. -/
private theorem respCalib_canonicalMean_isSymm {F : BlockMat d}
    (hA : (toFullBlockMat F).PosDef) : IsSymmetricBlockMat (canonicalMean F) :=
  (Analysis.toFullBlockMat_isHermitian_iff _).1 (respCalib_canonicalMean_posDef hA).isHermitian

/-- CG block positivity of `M(F)`, the form `schur_cancel` and `isUnit_det_lowerRight` need. -/
private theorem respCalib_canonicalMean_blockPosDef {F : BlockMat d}
    (hA : (toFullBlockMat F).PosDef) : Book.Ch02.BlockPosDef (canonicalMean F) := by
  simpa only [ofFullBlockMat_toFullBlockMat] using
    respCalib_blockPosDef_of_full (respCalib_canonicalMean_posDef hA)

/-- `g = k(M(F))` is skew (`p.response.transfer`): self-duality of `M(F)` forces
`M_{22}M_{12} + M_{21}M_{22} = 0`, which is exactly `gᵀ = -g`. -/
theorem respCalib_respg_isSkew {F : BlockMat d} (hA : (toFullBlockMat F).PosDef) :
    (respg F)ᵀ = -(respg F) := by
  have hsymm := respCalib_canonicalMean_isSymm hA
  have hp := respCalib_canonicalMean_blockPosDef hA
  have hDu : IsUnit (canonicalMean F).lowerRight.det := isUnit_det_lowerRight hp
  have hUR : (canonicalMean F).upperRight = ((canonicalMean F).lowerLeft)ᵀ := by
    ext i j
    simpa [blockMatEntry] using hsymm (Sum.inl i) (Sum.inr j)
  have hLRt : ((canonicalMean F).lowerRight)ᵀ = (canonicalMean F).lowerRight := by
    ext i j
    simpa [blockMatEntry] using hsymm (Sum.inr j) (Sum.inr i)
  have hsd := respCalib_canonicalMean_selfDual hA
  rw [toFullBlockMat_eq_fromBlocks (canonicalMean F), respCalib_swap_full, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hsd
  simp only [mul_zero, mul_one, zero_add, add_zero] at hsd
  have hid := (Matrix.fromBlocks_inj.mp hsd).2.2.2
  show (-((canonicalMean F).lowerRight⁻¹ * (canonicalMean F).lowerLeft))ᵀ
      = -(-((canonicalMean F).lowerRight⁻¹ * (canonicalMean F).lowerLeft))
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hLRt, neg_neg,
    ← hUR]
  exact (respCalib_skew_aux hDu hid).symm

/-- The shear congruence `G^t M(F) G` is block diagonal (`p.response.transfer`). -/
private theorem respCalib_shear_congr {F : BlockMat d} (hA : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (respG F))ᵀ * toFullBlockMat (canonicalMean F) * toFullBlockMat (respG F)
      = Matrix.fromBlocks (schurSigma (canonicalMean F)) 0 0 (canonicalMean F).lowerRight := by
  have hsymm := respCalib_canonicalMean_isSymm hA
  have hp := respCalib_canonicalMean_blockPosDef hA
  obtain ⟨h1, h2⟩ := schur_cancel hsymm hp
  have h2' : (respg F)ᵀ * (canonicalMean F).lowerRight = -(canonicalMean F).upperRight := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! h2
  have h1' : (canonicalMean F).lowerRight * respg F = -(canonicalMean F).lowerLeft := h1
  have hsig : schurSigma (canonicalMean F)
      = (canonicalMean F).upperLeft + (canonicalMean F).upperRight * respg F := by
    show (canonicalMean F).upperLeft -
        ((respg F)ᵀ * (canonicalMean F).lowerRight) * respg F = _
    rw [h2', neg_mul, sub_neg_eq_add]
  rw [respCalib_respG_full, toFullBlockMat_eq_fromBlocks (canonicalMean F), Matrix.fromBlocks_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · simp only [one_mul, mul_one]
    rw [hsig, h2']
    have hL : (canonicalMean F).lowerLeft = -((canonicalMean F).lowerRight * respg F) := by
      rw [h1', neg_neg]
    rw [hL, Matrix.mul_neg, ← Matrix.mul_assoc, h2']
    simp only [neg_mul, neg_neg, add_neg_cancel, zero_mul, add_zero]
  · simp only [one_mul, mul_one, mul_zero, zero_add]
    rw [h2', add_neg_cancel]
  · simp only [one_mul, mul_one, zero_mul, zero_add]
    rw [h1', add_neg_cancel]
  · simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add]

/-- Abstract congruence of a self-dual matrix by a shear that fixes `R`. -/
private theorem respCalib_congr_selfDual_aux {n : Type*} [Fintype n] [DecidableEq n]
    {G M R : Matrix n n ℝ} (hGRGt : G * R * Gᵀ = R) (hGtRG : Gᵀ * R * G = R)
    (hsd : M * R * M = R) :
    (Gᵀ * M * G) * R * (Gᵀ * M * G) = R := by
  calc (Gᵀ * M * G) * R * (Gᵀ * M * G) = Gᵀ * (M * (G * R * Gᵀ) * M) * G := by noncomm_ring
    _ = Gᵀ * (M * R * M) * G := by rw [hGRGt]
    _ = Gᵀ * R * G := by rw [hsd]
    _ = R := hGtRG

/-- The Schur complement of `M(F)` is the inverse of its lower-right block: the content of
the self-duality `(m, m, g)` of `p.response.transfer`. -/
private theorem respCalib_sigma_mul_lowerRight {F : BlockMat d} (hA : (toFullBlockMat F).PosDef) :
    schurSigma (canonicalMean F) * (canonicalMean F).lowerRight = 1 := by
  have hskew := respCalib_respg_isSkew hA
  have hG := respCalib_respG_full F
  have hR := respCalib_swap_full d
  have hGt : (toFullBlockMat (respG F))ᵀ = Matrix.fromBlocks 1 (-(respg F)) 0 1 := by
    rw [hG, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero, hskew]
  have hGRGt : toFullBlockMat (respG F) * toFullBlockMat (blockSwap d) *
      (toFullBlockMat (respG F))ᵀ = toFullBlockMat (blockSwap d) := by
    rw [hGt, hG, hR, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hGtRG : (toFullBlockMat (respG F))ᵀ * toFullBlockMat (blockSwap d) *
      toFullBlockMat (respG F) = toFullBlockMat (blockSwap d) := by
    rw [hGt, hG, hR, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hPRP := respCalib_congr_selfDual_aux hGRGt hGtRG (respCalib_canonicalMean_selfDual hA)
  rw [respCalib_shear_congr hA, hR, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hPRP
  simp only [mul_zero, mul_one, zero_mul, zero_add, add_zero] at hPRP
  exact (Matrix.fromBlocks_inj.mp hPRP).2.1

/-- `G^t M(F) G = M_0` (`p.response.transfer`). -/
theorem respCalib_congr_canonicalMean {F : BlockMat d} (hA : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (respG F))ᵀ * toFullBlockMat (canonicalMean F) * toFullBlockMat (respG F)
      = toFullBlockMat (respM0 F) := by
  have hp := respCalib_canonicalMean_blockPosDef hA
  have hs := respCalib_sigma_mul_lowerRight hA
  have hinv : (canonicalMean F).lowerRight⁻¹ = schurSigma (canonicalMean F) :=
    Matrix.inv_eq_left_inv hs
  rw [respCalib_shear_congr hA, respCalib_respM0_full, respCalib_explicitCanonicalMetric_eq, hinv,
    Matrix.inv_eq_right_inv hs]

/-- `D` commutes with `M_0` (`p.response.transfer`). -/
theorem respCalib_blockD_congr_respM0 (F : BlockMat d) :
    (toFullBlockMat (blockD d))ᵀ * toFullBlockMat (respM0 F) * toFullBlockMat (blockD d)
      = toFullBlockMat (respM0 F) := by
  rw [respCalib_blockD_full, respCalib_respM0_full, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- `Ehat_u^- = G^t E_u G` in the full carrier (`p.response.transfer`). -/
theorem respCalib_ehatMinus_full (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (u : ℤ) :
    toFullBlockMat (respEhatMinus P jStar F u)
      = (toFullBlockMat (respG F))ᵀ * toFullBlockMat (respMean P jStar F u) *
        toFullBlockMat (respG F) := by
  simp only [respEhatMinus, blockCongr, toFullBlockMat_ofFullBlockMat]

/-- `Ehat_u^+ = D Ehat_u^- D` in the full carrier (`p.response.transfer`). -/
theorem respCalib_ehatPlus_full (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (u : ℤ) :
    toFullBlockMat (respEhatPlus P jStar F u)
      = (toFullBlockMat (blockD d))ᵀ * toFullBlockMat (respEhatMinus P jStar F u) *
        toFullBlockMat (blockD d) := by
  simp only [respEhatPlus, blockAdjoint, blockCongr, toFullBlockMat_ofFullBlockMat]

/-- Upper half of `e.response.calibrated.blocks` in abstract form: `A ≤ k • N`, `N ≤ c • N_F`
and `G^t N_F G = M_0` give `G^t A G ≤ (C k) • M_0` for any `c ≤ C`
(`e.response.calibrated.blocks`). -/
theorem respCalib_upper {n : Type*} [Fintype n] [DecidableEq n]
    {A N NF Gf M0 : Matrix n n ℝ} {k c C : ℝ}
    (hM0 : M0.PosSemidef) (hGM : Gfᵀ * NF * Gf = M0)
    (hk : 0 ≤ k) (hcC : c ≤ C)
    (h1 : A ≤ k • N) (h2 : N ≤ c • NF) :
    Gfᵀ * A * Gf ≤ (C * k) • M0 := by
  have hstep : A ≤ (k * c) • NF := by
    refine h1.trans ?_
    have hs := smul_le_smul_left hk h2
    rwa [smul_smul] at hs
  have hcongr := Analysis.matrix_congr_le hstep Gf
  rw [Matrix.mul_smul, Matrix.smul_mul, hGM] at hcongr
  refine hcongr.trans (smul_le_smul_psd hM0 ?_)
  calc k * c = c * k := mul_comm k c
    _ ≤ C * k := mul_le_mul_of_nonneg_right hcC hk

/-- Lower half of `e.response.calibrated.blocks` in abstract form: `N_F ≤ c • N`, `N ≤ A`
and `G^t N_F G = M_0` give `C⁻¹ • M_0 ≤ G^t A G` for any `c ≤ C`
(`e.response.calibrated.blocks`). -/
theorem respCalib_lower {n : Type*} [Fintype n] [DecidableEq n]
    {A N NF Gf M0 : Matrix n n ℝ} {c C : ℝ}
    (hN : N.PosSemidef) (hGM : Gfᵀ * NF * Gf = M0)
    (hC : 0 < C) (hcC : c ≤ C)
    (h1 : NF ≤ c • N) (h2 : N ≤ A) :
    C⁻¹ • M0 ≤ Gfᵀ * A * Gf := by
  have hGN : (Gfᵀ * N * Gf).PosSemidef := by
    have hx := hN.conjTranspose_mul_mul_same Gf
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hx
  have hstep : M0 ≤ c • (Gfᵀ * N * Gf) := by
    have hcg := Analysis.matrix_congr_le h1 Gf
    rw [Matrix.mul_smul, Matrix.smul_mul, hGM] at hcg
    exact hcg
  calc C⁻¹ • M0 ≤ C⁻¹ • (c • (Gfᵀ * N * Gf)) :=
        smul_le_smul_left (by positivity) hstep
    _ = (C⁻¹ * c) • (Gfᵀ * N * Gf) := by rw [smul_smul]
    _ ≤ (1 : ℝ) • (Gfᵀ * N * Gf) := by
        refine smul_le_smul_psd hGN ?_
        rw [inv_mul_eq_div]
        exact (div_le_one hC).mpr hcC
    _ = Gfᵀ * N * Gf := one_smul _ _
    _ ≤ Gfᵀ * A * Gf := Analysis.matrix_congr_le h2 Gf

/-! ## The calibrated-blocks estimate -/

-- The two range premises are bound as `_hε`, `_hσ` inside the statement `∀`: the hypotheses
-- themselves are unchanged and the proof `intro`s and uses them, but the binder *names* do not
-- occur in the statement's own type, so `linter.unusedVariables` would fire under
-- `-DwarningAsError=true`.  Underscore-prefixed instead of suppressing the linter.

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Nonnegativity of the source load and the cutoff error-row arithmetic

The source load `L_s^±` of `p.response.transfer` is a weighted sum of squares against
nonnegative weights, hence nonnegative.  The cutoff estimate `e.response.cutoff.estimate`
collects its three error rows and the cutoff pairing term under one constant by elementary
arithmetic, using only that every scalar in sight is nonnegative.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The source load `L_s` is nonnegative: it is a sum over scales of a nonnegative weight
`3 ^ (-(3/2) n)` times a cell average of a squared sum of square roots. -/
theorem zero_le_respSourceLoad {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    0 ≤ respSourceLoad P jStar F s b Y := by
  unfold respSourceLoad
  exact tsum_nonneg fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun z _ => sq_nonneg _))

/-- `L_s^-` is nonnegative, being the source load of the recentred coefficient `a_-`. -/
theorem zero_le_respLsMinus {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) :
    0 ≤ respLsMinus P jStar F s t e := by
  unfold respLsMinus
  exact zero_le_respSourceLoad P jStar F s (respCoeffMinus F) (respYMinus P jStar F t e)

/-- `L_s^+` is nonnegative, being the source load of the adjoint recentred coefficient `a_+`. -/
theorem zero_le_respLsPlus {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) :
    0 ≤ respLsPlus P jStar F s t e := by
  unfold respLsPlus
  exact zero_le_respSourceLoad P jStar F s (respCoeffPlus F) (respYPlus P jStar F t e)

end

end HCPolySupport.HighContrast.Multiscale
end
