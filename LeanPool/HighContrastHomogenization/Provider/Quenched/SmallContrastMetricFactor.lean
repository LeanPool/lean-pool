/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCanonRecenter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitBlock
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMetricFactor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak-norm metric factor of the small-contrast estimate

The weak value of the small-contrast one-step estimate carries the metric
factor

  `K_{M,F} = |M_0^{-1/2} F M_0^{-1/2}|^{1/2}`,   `M_0 = diag(m_0, m_0^{-1})`,

at `F` the recentered reference `G_{h_0}^t (c 𝐄) G_{h_0}` and at `F` the
recentered terminal adapted mean.  This file bounds the first one by data of
the reference alone — the printed `M_0` is built from the reference, so the
factor must not grow with the generation.

The route is the canonical factorization `M(𝐄) = G_{-g(𝐄)}^t M_0 G_{-g(𝐄)}`
at `m_0 = m(𝐄)` (`e.scale.selection.canonical.metric`) together with the
two-sided bound `𝐄 ≤ 𝔡(𝐄)^{1/2} M(𝐄)` between a positive block and its
canonical metric: the two shears compose, so the whole factor is the imbalance
times the distortion of the
single shear `h_0 - g(𝐄)`, and that distortion is quadratic in the size
`τ` of `m^{-1/2}(h_0 - g(𝐄))m^{-1/2}`.

The `g(𝐄)` half of the shear is removed once and for all by the recentering
of `SmallContrastCanonRecenter` (`canonicalShear_recentered_eq_zero`), which
is the normalization of Section 2.5 of HC; the remaining `h_0` half is the
response skew of the terminal mean, controlled in
`SmallContrastMetricFactorTau`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Two elementary quadratic-form facts -/

private theorem vecDot_matVecMul_eq (Q : Mat d) (x y : Vec d) :
    vecDot x (matVecMul Q y) = x ⬝ᵥ Q *ᵥ y := rfl

/-- The parallelogram bound for a positive semidefinite quadratic form. -/
private theorem quad_add_le_two {Q : Mat d} (hQ : Q.PosSemidef) (a b : Vec d) :
    vecDot (a + b) (matVecMul Q (a + b)) ≤
      2 * vecDot a (matVecMul Q a) + 2 * vecDot b (matVecMul Q b) := by
  have hkey : 0 ≤ (a - b) ⬝ᵥ Q *ᵥ (a - b) := by
    have h := hQ.dotProduct_mulVec_nonneg (a - b)
    simpa only [star_trivial] using h
  have hs : (a - b) ⬝ᵥ Q *ᵥ (a - b) =
      a ⬝ᵥ Q *ᵥ a - a ⬝ᵥ Q *ᵥ b - b ⬝ᵥ Q *ᵥ a + b ⬝ᵥ Q *ᵥ b := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have ha : (a + b) ⬝ᵥ Q *ᵥ (a + b) =
      a ⬝ᵥ Q *ᵥ a + a ⬝ᵥ Q *ᵥ b + b ⬝ᵥ Q *ᵥ a + b ⬝ᵥ Q *ᵥ b := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    ring
  rw [vecDot_matVecMul_eq, vecDot_matVecMul_eq, vecDot_matVecMul_eq, ha]
  rw [hs] at hkey
  linarith only [hkey]

/-- Dilations compose. -/
private theorem blockScale_blockScale (c c' : ℝ) (A : BlockMat d) :
    blockScale c (blockScale c' A) = blockScale (c * c') A := by
  unfold blockScale
  simp only [smul_smul]

/-! ## Shears compose -/

/-- **Shear congruences compose additively.** -/
theorem skewBlockCongr_skewBlockCongr (a b : Mat d) (A : BlockMat d) :
    Response.skewBlockCongr a (Response.skewBlockCongr b A) =
      Response.skewBlockCongr (b + a) A := by
  apply toFullBlockMat_injective
  rw [Response.toFullBlockMat_skewBlockCongr, Response.toFullBlockMat_skewBlockCongr,
    Response.toFullBlockMat_skewBlockCongr, ← fullBlockShear_mul]
  rw [Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## The shear distortion of the split metric -/

/-- **The distortion of the split metric under a shear.**  If the shear `h` has
`m`-normalized size at most `τ`, the shear congruence of `M_0 = diag(m,m^{-1})`
is at most `(2 + 2τ²) M_0`.  This is the only place the shear enters the metric
factor. -/
theorem blockMatLoewnerLE_skewBlockCongr_diagonalMetric {m h : Mat d}
    (hm : m.PosDef) {tau : ℝ}
    (htau : ∀ x : Vec d,
      vecDot (matVecMul h x) (matVecMul m⁻¹ (matVecMul h x)) ≤
        tau ^ 2 * vecDot x (matVecMul m x)) :
    BlockMatLoewnerLE (Response.skewBlockCongr h (blockDiag m m⁻¹))
      (blockScale (2 + 2 * tau ^ 2) (blockDiag m m⁻¹)) := by
  have hminv : (m⁻¹).PosDef := hm.inv
  rintro ⟨x, y⟩
  rw [Response.blockQuadratic_skewBlockCongr, blockVecDot_blockMatVecMul_blockScale]
  have hL : blockVecDot ((x, matVecMul h x + y) : BlockVec d)
      (blockMatVecMul (blockDiag m m⁻¹)
        ((x, matVecMul h x + y) : BlockVec d)) =
      vecDot x (matVecMul m x) +
        vecDot (matVecMul h x + y) (matVecMul m⁻¹ (matVecMul h x + y)) :=
    Response.metricBlockNormSq_eq m _
  have hR : blockVecDot ((x, y) : BlockVec d)
      (blockMatVecMul (blockDiag m m⁻¹) ((x, y) : BlockVec d)) =
      vecDot x (matVecMul m x) + vecDot y (matVecMul m⁻¹ y) :=
    Response.metricBlockNormSq_eq m _
  rw [hL, hR]
  have hA : 0 ≤ vecDot x (matVecMul m x) := by
    rw [vecDot_matVecMul_eq]
    simpa only [star_trivial] using hm.posSemidef.dotProduct_mulVec_nonneg x
  have hB : 0 ≤ vecDot y (matVecMul m⁻¹ y) := by
    rw [vecDot_matVecMul_eq]
    simpa only [star_trivial] using hminv.posSemidef.dotProduct_mulVec_nonneg y
  have hpar := quad_add_le_two hminv.posSemidef (matVecMul h x) y
  have hht := htau x
  have hsq : 0 ≤ tau ^ 2 := sq_nonneg tau
  nlinarith only [hA, hB, hpar, hht, hsq]

/-! ## The metric factor at the reference -/

/-- **The reference metric factor, squared.**  With the adapted-cube metric
`m_0 = m(𝐄)` — the canonical metric of the reference — the `M_0`-size of the
recentered dilated reference is at most `c · κ_𝐄^{1/2} · (2 + 2τ²)`, where `τ`
bounds the `m_0`-normalized size of the *total* shear `h - g(𝐄)`.

The generation never appears: the bound is reference data times the shear
distortion. -/
theorem blockMatLoewnerLE_skewBlockCongr_reference {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (h : Mat d) {c : ℝ} (hc : 0 ≤ c) {tau : ℝ}
    (htau : ∀ x : Vec d,
      vecDot (matVecMul (h - canonicalShear E) x)
          (matVecMul (canonicalMetric E)⁻¹
            (matVecMul (h - canonicalShear E) x)) ≤
        tau ^ 2 * vecDot x (matVecMul (canonicalMetric E) x)) :
    BlockMatLoewnerLE (Response.skewBlockCongr h (blockScale c E))
      (blockScale (c * Real.sqrt (kappaRef E) * (2 + 2 * tau ^ 2))
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) := by
  classical
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hm : (canonicalMetric E).PosDef := posDef_canonMetric hEfull
  have hMsym : IsSymmetricBlockMat
      (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) :=
    Response.isSymmetricBlockMat_diagonalMetric hm
  have hMpd : BlockPosDef (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) :=
    Response.blockPosDef_diagonalMetric hm
  -- the reference's sharp order, flattened
  have hsharpfull : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E := by
    have hsym : IsSymmetricBlockMat (blockSharp E) := by
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_blockSharp]
      exact (posDef_fullBlockSharp hEfull).posSemidef
    have h := (blockMatLoewnerLE_iff_le hsym hE).mp hsharp
    rwa [toFullBlockMat_blockSharp] at h
  obtain ⟨-, -, hbal⟩ := canonBalance hEfull hsharpfull
  have hkap : Real.sqrt (kappaRef E) =
      Real.sqrt (canonImbalance (toFullBlockMat E)) := by
    rw [kappaRef_eq_canonImbalance hE hEpd]
  have hkap0 : 0 ≤ Real.sqrt (kappaRef E) := Real.sqrt_nonneg _
  -- `𝐄 ≤ κ^{1/2} M(𝐄)`, structurally
  have hEle : BlockMatLoewnerLE E
      (blockScale (Real.sqrt (kappaRef E)) (canonicalBlock E)) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, canonicalBlock, toFullBlockMat_ofFullBlockMat,
      hkap]
    exact hbal
  -- dilate, then shear
  have hstep1 : BlockMatLoewnerLE (blockScale c E)
      (blockScale c (blockScale (Real.sqrt (kappaRef E)) (canonicalBlock E))) :=
    blockMatLoewnerLE_blockScale_of_le hc hEle
  have hstep2 : BlockMatLoewnerLE (Response.skewBlockCongr h (blockScale c E))
      (Response.skewBlockCongr h
        (blockScale c
          (blockScale (Real.sqrt (kappaRef E)) (canonicalBlock E)))) :=
    (Response.skewBlockCongr_loewner_iff h _ _).mpr hstep1
  -- the canonical block is a sheared split metric; the shears compose
  have hcanon : Response.skewBlockCongr h (canonicalBlock E) =
      Response.skewBlockCongr (h - canonicalShear E)
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) := by
    rw [canonicalBlock_eq_skewBlockCongr hEfull, skewBlockCongr_skewBlockCongr]
    congr 1
    abel
  have hrewrite : Response.skewBlockCongr h
      (blockScale c (blockScale (Real.sqrt (kappaRef E)) (canonicalBlock E))) =
      blockScale (c * Real.sqrt (kappaRef E))
        (Response.skewBlockCongr (h - canonicalShear E)
          (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) := by
    rw [Response.blockScale_skewBlockCongr, Response.blockScale_skewBlockCongr, hcanon,
      blockScale_blockScale]
  rw [hrewrite] at hstep2
  -- the shear distortion
  have hdist := blockMatLoewnerLE_skewBlockCongr_diagonalMetric hm htau
  have hstep3 : BlockMatLoewnerLE
      (blockScale (c * Real.sqrt (kappaRef E))
        (Response.skewBlockCongr (h - canonicalShear E)
          (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)))
      (blockScale (c * Real.sqrt (kappaRef E))
        (blockScale (2 + 2 * tau ^ 2)
          (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹))) :=
    blockMatLoewnerLE_blockScale_of_le (mul_nonneg hc hkap0) hdist
  have hcollapse : blockScale (c * Real.sqrt (kappaRef E))
      (blockScale (2 + 2 * tau ^ 2)
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹)) =
      blockScale (c * Real.sqrt (kappaRef E) * (2 + 2 * tau ^ 2))
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) :=
    blockScale_blockScale _ _ _
  rw [← hcollapse]
  exact fun X => le_trans (hstep2 X) (hstep3 X)

/-- **The reference metric factor, squared.**  With the adapted-cube metric
`m_0 = m(𝐄)` the `M_0`-size of the recentered dilated reference is at most
`c · κ_𝐄^{1/2} · (2 + 2τ²)`.  The generation never appears. -/
theorem blockSize_skewBlockCongr_reference_le {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (h : Mat d) {c : ℝ} (hc : 0 ≤ c) {tau : ℝ}
    (htau : ∀ x : Vec d,
      vecDot (matVecMul (h - canonicalShear E) x)
          (matVecMul (canonicalMetric E)⁻¹
            (matVecMul (h - canonicalShear E) x)) ≤
        tau ^ 2 * vecDot x (matVecMul (canonicalMetric E) x)) :
    blockSize (Response.skewBlockCongr h (blockScale c E))
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) ≤
      c * Real.sqrt (kappaRef E) * (2 + 2 * tau ^ 2) := by
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hm : (canonicalMetric E).PosDef := posDef_canonMetric hEfull
  have hkap0 : 0 ≤ Real.sqrt (kappaRef E) := Real.sqrt_nonneg _
  have hnumsym : IsSymmetricBlockMat (Response.skewBlockCongr h (blockScale c E)) :=
    Response.isSymmetricBlockMat_skewBlockCongr (isSymmetricBlockMat_blockScale c hE)
  have hnumps : (toFullBlockMat (Response.skewBlockCongr h (blockScale c E))).PosSemidef := by
    rw [Response.toFullBlockMat_skewBlockCongr, toFullBlockMat_blockScale]
    exact (hEfull.posSemidef.smul hc).conjTranspose_mul_mul_same (fullBlockShear h)
  refine Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hnumsym hnumps
    (Response.isSymmetricBlockMat_diagonalMetric hm)
    (Response.blockPosDef_diagonalMetric hm) ?_
    (blockMatLoewnerLE_skewBlockCongr_reference hE hEpd hsharp h hc htau)
  have h2 : (0 : ℝ) ≤ 2 + 2 * tau ^ 2 := by nlinarith only [sq_nonneg tau]
  exact mul_nonneg (mul_nonneg hc hkap0) h2

end

end HCPolySupport.HighContrast.Quenched
