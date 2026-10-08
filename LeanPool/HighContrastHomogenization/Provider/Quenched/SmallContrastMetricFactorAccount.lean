/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMetricFactorTau
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMetricFactorAccount

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two metric factors of the sharp weak value, at the recentered reference

`weakValueBoundSharpIsotropyAt` carries two metric factors, both at the recentering
skew `h_0 = h_rsp(K_t)` of the terminal adapted mean:

* `K_{M,F_2}` at the inflated reference `F_2 = c_F 𝐄`;
* `K_{M,E_t}` at the terminal adapted mean itself.

This file bounds both by *reference data only* — no generation, no source
moment — once the reference has been recentered so that its canonical shear
vanishes (`SmallContrastCanonRecenter.canonicalShear_recentered_eq_zero`,
the normalization of Section 2.5 of HC) and the terminal mean is two-sidedly
comparable with the reference:

  `E_t ≤ c_F 𝐄`   (the entry envelope)     and   `𝐄 ≤ κ E_t`  (the entry
  comparability).

Under the recentering the canonical metric block of the reference *is* the
split metric `M_0 = diag(m(𝐄), m(𝐄)^{-1})`, so the balance chain
`M(𝐄) ≤ 𝐄 ≤ 𝔡(𝐄)^{1/2} M(𝐄)` turns the two comparabilities into a two-sided
comparison of `E_t` with `M_0`, which is exactly the input of
`responseSkew_quad_le_of_sandwich`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The trivial shear congruence is the identity. -/
theorem skewBlockCongr_zero (A : BlockMat d) : Response.skewBlockCongr 0 A = A := by
  apply toFullBlockMat_injective
  rw [Response.toFullBlockMat_skewBlockCongr, fullBlockShear_zero,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- The metric-factor value: the reference imbalance times the shear
distortion of the response skew, all under the square root. -/
@[expose]
def metricFactorValue (E : BlockMat d) (cF kap : ℝ) : ℝ :=
  Real.sqrt (cF * Real.sqrt (kappaRef E) *
    (2 + 2 * (kap * (cF * Real.sqrt (kappaRef E)))))

theorem metricFactorValue_nonneg (E : BlockMat d) (cF kap : ℝ) :
    0 ≤ metricFactorValue E cF kap := Real.sqrt_nonneg _

/-- **Both metric factors of the sharp weak value, at the recentered
reference.**  The bound depends only on the reference `𝐄` (through its
imbalance `κ_𝐄`), the envelope constant `c_F`, and the comparability constant
`κ` — never on the generation. -/
theorem diagonalWeakMetricFactor_recentered_le {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {A : BlockMat d} {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hform : toFullBlockMat A = schurBlock S SStar K)
    {cF kap : ℝ} (hcF : 0 ≤ cF) (hkap : 0 ≤ kap)
    (henv : BlockMatLoewnerLE A (blockScale cF E))
    (hcomp : BlockMatLoewnerLE E (blockScale kap A)) :
    Response.diagonalWeakMetricFactor (canonicalMetric E)
        (Response.skewBlockCongr (Response.responseSkew K) (blockScale cF E)) ≤
      metricFactorValue E cF kap ∧
    Response.diagonalWeakMetricFactor (canonicalMetric E)
        (Response.skewBlockCongr (Response.responseSkew K) A) ≤
      metricFactorValue E cF kap := by
  classical
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hm : (canonicalMetric E).PosDef := posDef_canonMetric hEfull
  have hMsym : IsSymmetricBlockMat
      (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) :=
    Response.isSymmetricBlockMat_diagonalMetric hm
  have hMpd : BlockPosDef (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) :=
    Response.blockPosDef_diagonalMetric hm
  -- the recentered reference has the split metric as its canonical block
  have hM0eq : canonicalBlock E =
      blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹ := by
    rw [canonicalBlock_eq_skewBlockCongr hEfull, hrec, neg_zero,
      skewBlockCongr_zero]
  -- the sharp order, flattened, and the balance chain
  have hsharpfull : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E := by
    have hsym : IsSymmetricBlockMat (blockSharp E) := by
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_blockSharp]
      exact (posDef_fullBlockSharp hEfull).posSemidef
    have h := (blockMatLoewnerLE_iff_le hsym hE).mp hsharp
    rwa [toFullBlockMat_blockSharp] at h
  obtain ⟨-, hMle, hbal⟩ := canonBalance hEfull hsharpfull
  have hkapE : Real.sqrt (kappaRef E) =
      Real.sqrt (canonImbalance (toFullBlockMat E)) := by
    rw [kappaRef_eq_canonImbalance hE hEpd]
  have hkapE0 : 0 ≤ Real.sqrt (kappaRef E) := Real.sqrt_nonneg _
  -- `M_0 ≤ 𝐄` and `𝐄 ≤ κ_𝐄^{1/2} M_0`
  have hM0leE : BlockMatLoewnerLE
      (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) E := by
    refine blockMatLoewnerLE_of_le ?_
    rw [← hM0eq, canonicalBlock, toFullBlockMat_ofFullBlockMat]
    exact hMle
  have hEleM0 : BlockMatLoewnerLE E
      (blockScale (Real.sqrt (kappaRef E))
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, ← hM0eq, canonicalBlock,
      toFullBlockMat_ofFullBlockMat, hkapE]
    exact hbal
  -- the two-sided comparison of `A` with the split metric
  have hupA : BlockMatLoewnerLE A
      (blockScale (cF * Real.sqrt (kappaRef E))
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) := by
    have hstep : BlockMatLoewnerLE (blockScale cF E)
        (blockScale cF
          (blockScale (Real.sqrt (kappaRef E))
            (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹))) :=
      blockMatLoewnerLE_blockScale_of_le hcF hEleM0
    have hcollapse : blockScale cF
        (blockScale (Real.sqrt (kappaRef E))
          (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) =
        blockScale (cF * Real.sqrt (kappaRef E))
          (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) := by
      unfold blockScale
      simp only [smul_smul]
    rw [hcollapse] at hstep
    exact fun X => le_trans (henv X) (hstep X)
  have hlowA : BlockMatLoewnerLE
      (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)
      (blockScale kap A) := fun X => le_trans (hM0leE X) (hcomp X)
  -- the shear size of the response skew
  have hC0 : 0 ≤ cF * Real.sqrt (kappaRef E) := mul_nonneg hcF hkapE0
  have htau := responseSkew_quad_le_of_sandwich hm hS hform hC0 hkap
    hupA hlowA
  have htau' : ∀ x : Vec d,
      vecDot (matVecMul (Response.responseSkew K - canonicalShear E) x)
          (matVecMul (canonicalMetric E)⁻¹
            (matVecMul (Response.responseSkew K - canonicalShear E) x)) ≤
        Real.sqrt (kap * (cF * Real.sqrt (kappaRef E))) ^ 2 *
          vecDot x (matVecMul (canonicalMetric E) x) := by
    intro x
    rw [hrec, sub_zero]
    exact htau x
  -- the reference factor
  have hbound := blockSize_skewBlockCongr_reference_le hE hEpd hsharp
    (Response.responseSkew K) hcF htau'
  have hsqtau : Real.sqrt (kap * (cF * Real.sqrt (kappaRef E))) ^ 2 =
      kap * (cF * Real.sqrt (kappaRef E)) :=
    Real.sq_sqrt (mul_nonneg hkap hC0)
  rw [hsqtau] at hbound
  set B : ℝ := cF * Real.sqrt (kappaRef E) *
    (2 + 2 * (kap * (cF * Real.sqrt (kappaRef E)))) with hB
  have hB0 : 0 ≤ B := by
    have h2 : (0 : ℝ) ≤ 2 + 2 * (kap * (cF * Real.sqrt (kappaRef E))) := by
      have := mul_nonneg hkap hC0
      linarith only [this]
    exact mul_nonneg hC0 h2
  refine ⟨?_, ?_⟩
  · rw [Response.diagonalWeakMetricFactor_eq, metricFactorValue, ← hB]
    exact Real.sqrt_le_sqrt hbound
  · -- the mean factor is dominated by the reference factor through the envelope
    rw [Response.diagonalWeakMetricFactor_eq, metricFactorValue, ← hB]
    refine Real.sqrt_le_sqrt ?_
    have hApd : (toFullBlockMat A).PosDef := by
      rw [hform]
      exact posDef_schurBlock hS hStar
    have hAsym : IsSymmetricBlockMat A :=
      isSymmetricBlockMat_of_posSemidef hApd.posSemidef
    have hnumsym : IsSymmetricBlockMat (Response.skewBlockCongr (Response.responseSkew K) A) :=
      Response.isSymmetricBlockMat_skewBlockCongr hAsym
    have hnumps :
        (toFullBlockMat (Response.skewBlockCongr (Response.responseSkew K) A)).PosSemidef := by
      rw [Response.toFullBlockMat_skewBlockCongr]
      exact hApd.posSemidef.conjTranspose_mul_mul_same
        (fullBlockShear (Response.responseSkew K))
    have hstep : BlockMatLoewnerLE (Response.skewBlockCongr (Response.responseSkew K) A)
        (Response.skewBlockCongr (Response.responseSkew K) (blockScale cF E)) :=
      (Response.skewBlockCongr_loewner_iff _ _ _).mpr henv
    have hrefle := blockMatLoewnerLE_skewBlockCongr_reference hE hEpd hsharp
      (Response.responseSkew K) hcF htau'
    rw [hsqtau, ← hB] at hrefle
    exact Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hnumsym hnumps hMsym
      hMpd hB0 (fun X => le_trans (hstep X) (hrefle X))

end

end HCPolySupport.HighContrast.Quenched
