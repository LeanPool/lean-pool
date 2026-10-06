/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLoadQuads
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringSmallness
public import LeanPool.HighContrastHomogenization.Provider.Sharp.ReflectionOrder

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakValue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak value

The weak-cap majorant, evaluated at the calibrated loads, is uniform over
unit directions: every load-dependent factor is a quadratic of the inflated
reference or of the recentered terminal mean at the load pair, and these are
bounded through the carried comparability and the smallness pack by the
absolute constants of the calibrated load quadratics.  With the per-scale
variance carriers and mean drops bounded by supplied real values, both weak
quantities are at most `ofReal` of one explicit real weak value.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

private theorem skew_quad_pair (g : Mat d) (A : BlockMat d) (x y : Vec d) :
    blockVecDot ((x, y) : BlockVec d)
        (blockMatVecMul (Response.skewBlockCongr g A) ((x, y) : BlockVec d)) =
      blockVecDot ((x, matVecMul g x + y) : BlockVec d)
        (blockMatVecMul A ((x, matVecMul g x + y) : BlockVec d)) :=
  Response.blockQuadratic_skewBlockCongr g A ((x, y) : BlockVec d)

private theorem blockQuad_nonneg' {H : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef H) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul H X) := by
  by_cases hX : X = 0
  · subst X
    simp [blockMatVecMul, blockVecDot, vecDot]
  · exact (hpos X hX).le

private theorem scaled_reference_quadratic_bound
    {E F H : BlockMat d} {c k b : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hF : F = blockScale c E)
    (hcomp : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul E X) ≤
      k * blockVecDot X (blockMatVecMul H X))
    (X : BlockVec d) (hX : blockVecDot X (blockMatVecMul H X) ≤ b) :
    blockVecDot X (blockMatVecMul F X) ≤ c * k * b := by
  rw [hF, Sharp.blockVecDot_blockMatVecMul_blockScale]
  refine le_trans (mul_le_mul_of_nonneg_left (hcomp X) hc) ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left hX (mul_nonneg hc hk)

/-- **The six calibrated weak-load bounds.** -/
theorem calibrated_weak_loads [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q0 : Mat d} (hq0 : q0.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q0 t)
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P q0 t) = schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    {E F2 : BlockMat d} {cF : ℝ} (hcF0 : 0 ≤ cF)
    (hF2eq : F2 = blockScale cF E)
    (hF2pd : Book.Ch02.BlockPosDef F2)
    {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X (blockMatVecMul (adaptedMean P q0 t) X))
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    Response.diagonalWeakLoadMinus
        (Response.skewBlockCongr (Response.responseSkew K0) F2)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) ≤
      Real.sqrt (cF * kap * 7) ∧
    Response.profileEnergyLoad
        (Response.diagonalWeakLoadMinus F2
          (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
          (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
              Response.responseSymmetric K0) SStar0) *ᵥ e -
            matVecMul (Response.responseSkew K0)
              (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
                SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)))
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e -
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)) ≤
      Real.sqrt (cF * kap * 7 + 1) ∧
    Response.diagonalWeakLoadMinus
        (Response.skewBlockCongr (Response.responseSkew K0) (adaptedMean P q0 t))
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) ≤
      Real.sqrt 7 ∧
    Response.diagonalWeakLoadPlus
        (Response.skewBlockCongr (Response.responseSkew K0) F2)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) ≤
      Real.sqrt (cF * kap * 7) ∧
    Response.profileEnergyLoad
        (Response.diagonalWeakLoadPlus F2
          (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
          (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
              Response.responseSymmetric K0) SStar0) *ᵥ e +
            matVecMul (Response.responseSkew K0)
              (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
                SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)))
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e +
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)) ≤
      Real.sqrt (cF * kap * 7 + 1) ∧
    Response.diagonalWeakLoadPlus
        (Response.skewBlockCongr (Response.responseSkew K0) (adaptedMean P q0 t))
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) ≤
      Real.sqrt 7 := by
  classical
  -- the smallness pack
  have hint' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hq0 t : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hint
  have hE' : toFullBlockMat
      (annealedBlock P
        ((Response.adaptedDomain hq0 t : Domain d) : Set (Vec d))) =
      schurBlock S0 SStar0 K0 := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hform
  obtain ⟨horder, hgapM, hskewM, _htrGap, _htrSkew⟩ :=
    centering_smallness_supply (Response.adaptedDomain hq0 t) hint' hS0 hStar0
      hE' hpos htr
  have hks : (Response.responseSymmetric K0)ᴴ = Response.responseSymmetric K0 :=
    Response.responseSymmetric_isHermitian K0
  have hquads := calibrated_load_quads_le hS0 hStar0 hks hpos.le heps1
    horder hgapM hskewM e he
  have hh0 : IsSkewMat (Response.responseSkew K0) :=
    Response.is_skew_mat_response_skew K0
  have hκpsd : (Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0).PosSemidef := by
    have h := hStar0.inv.posSemidef.conjTranspose_mul_mul_same
      (Response.responseSymmetric K0)
    rwa [hks] at h
  have hb : (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0).PosDef := hS0.add_posSemidef hκpsd
  have hpairs := calibrated_pair_skew_abs hb hStar0 hh0 e he
  -- the two closed hatted mean quadratics
  have hmg := hatMean_blockQuad_eq (P := P) (q := q0) t hform
    (-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e))
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
    sub_neg_eq_add] at hmg
  have hm7 : blockVecDot
      ((-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e),
        matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) : BlockVec d)
      (blockMatVecMul
        (Response.skewBlockCongr (Response.responseSkew K0) (adaptedMean P q0 t))
        ((-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
            SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e),
          matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e) : BlockVec d)) ≤ 7 := by
    rw [hmg]
    exact hquads.1
  have hmgA := hatMean_blockQuad_eq (P := P) (q := q0) t hform
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  have hm7A : blockVecDot
      ((matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e,
        matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e) : BlockVec d)
      (blockMatVecMul
        (Response.skewBlockCongr (Response.responseSkew K0) (adaptedMean P q0 t))
        ((matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e,
          matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e) : BlockVec d)) ≤ 7 := by
    rw [hmgA]
    exact hquads.2
  -- the slot rewrites
  have hslotm : matVecMul (Response.responseSkew K0)
      (-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)) +
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e -
      matVecMul (Response.responseSkew K0)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e) := by
    rw [matVecMul_neg, neg_add_eq_sub]
  have hslotp : matVecMul (Response.responseSkew K0)
      (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e) +
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e +
      matVecMul (Response.responseSkew K0)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e) :=
    add_comm _ _
  -- the mean quadratics at the shifted slots
  have hmeanY := skew_quad_pair (Response.responseSkew K0) (adaptedMean P q0 t)
    (-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e))
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  rw [hslotm] at hmeanY
  have hmeanY7 := hmeanY ▸ hm7
  have hmeanYA := skew_quad_pair (Response.responseSkew K0) (adaptedMean P q0 t)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  rw [hslotp] at hmeanYA
  have hmeanYA7 := hmeanYA ▸ hm7A
  -- the reference quadratics at the shifted slots
  have hF2Y := scaled_reference_quadratic_bound hcF0 hkap0 hF2eq hcomp _ hmeanY7
  have hF2YA := scaled_reference_quadratic_bound hcF0 hkap0 hF2eq hcomp _ hmeanYA7
  -- the hatted reference quadratics
  have hhatF2 := skew_quad_pair (Response.responseSkew K0) F2
    (-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e))
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  rw [hslotm] at hhatF2
  have hhatF2le := hhatF2.symm ▸ hF2Y
  have hhatF2A := skew_quad_pair (Response.responseSkew K0) F2
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  rw [hslotp] at hhatF2A
  have hhatF2Ale := hhatF2A.symm ▸ hF2YA
  -- nonnegativity of the reference quadratics
  have hq0min : 0 ≤ blockVecDot
      ((-(matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e),
        matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e -
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)) :
        BlockVec d)
      (blockMatVecMul F2 _) := blockQuad_nonneg' hF2pd _
  have hq0plus : 0 ≤ blockVecDot
      ((matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e,
        matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0) *ᵥ e +
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)) :
        BlockVec d)
      (blockMatVecMul F2 _) := blockQuad_nonneg' hF2pd _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Response.diagonalWeakLoadMinus_eq]
    exact Real.sqrt_le_sqrt hhatF2le
  · rw [Response.profileEnergyLoad_eq, Response.diagonalWeakLoadMinus_eq]
    refine Real.sqrt_le_sqrt ?_
    have hpairv : |vecDot
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e -
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e))| =
        1 := hpairs.1
    rw [Real.sq_sqrt hq0min, hpairv]
    linarith only [hF2Y]
  · rw [Response.diagonalWeakLoadMinus_eq]
    exact Real.sqrt_le_sqrt hm7
  · rw [Response.diagonalWeakLoadPlus_eq]
    exact Real.sqrt_le_sqrt hhatF2Ale
  · rw [Response.profileEnergyLoad_eq, Response.diagonalWeakLoadPlus_eq]
    refine Real.sqrt_le_sqrt ?_
    have hpairv : |vecDot
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
          Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
        (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
            Response.responseSymmetric K0) SStar0) *ᵥ e +
          matVecMul (Response.responseSkew K0)
            (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 *
              SStar0⁻¹ * Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e))| =
        1 := hpairs.2
    rw [Real.sq_sqrt hq0plus, hpairv]
    linarith only [hF2YA]
  · rw [Response.diagonalWeakLoadPlus_eq]
    exact Real.sqrt_le_sqrt hm7A

end

end HCPolySupport.HighContrast.Quenched
