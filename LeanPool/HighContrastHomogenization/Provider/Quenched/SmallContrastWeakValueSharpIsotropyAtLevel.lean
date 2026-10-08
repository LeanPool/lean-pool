/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCapSharpIsotropyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueIsoAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakValueSharpIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp weak values at a released split level

The two weak quantities against the released sharp weak value.  The three
coefficients are the ones the released weak-norm chain produces, and the bad
slot carries the residue-free majorant at the matched threshold.  Everything
else is the pinned proof: the six load bounds, the budget comparison, the three
group bounds and the assembly are unchanged.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

private theorem energy_load_group_bounds
    {energy bound bad good : ℝ} (henergy : energy ≤ bound)
    (hbad : 0 ≤ bad) (hgood : 0 ≤ good) :
    Real.sqrt 2 * energy * bad ≤ Real.sqrt 2 * bound * bad ∧
      good * energy ≤ good * bound := by
  constructor
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left henergy (Real.sqrt_nonneg 2)) hbad
  · exact mul_le_mul_of_nonneg_left henergy hgood

private theorem constant_seminorm_coefficient_nonnegative :
    0 ≤ Response.constantSeminormCoefficient := by
  have hconst0 : 0 ≤ Response.constantSeminormCoefficient := by
    rw [Response.constantSeminormCoefficient_eq]
    have h31 : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hpos1 : 0 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 2) := by
      linarith only [h31]
    positivity
  exact hconst0

/-- **The primal weak quantity by the released sharp weak value.** -/
theorem profilePrimalWeakQuantity_le_weakValueSharp_of_block_at_level [NeZero d]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l n))
    {m0 : Mat d} (hm0 : m0.PosDef)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (t : ℤ) (Hw : ℕ) (hstart : l ≤ t - (Hw : ℤ))
    {G : ℕ}
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF : ℝ} (hcF0 : 0 ≤ cF) (hFeq : F = blockScale cF E)
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid l n) k)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t))
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P (roundedGrid l n) t) =
      schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X))
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hV : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j) (hV0 : 0 ≤ V0)
    (hDr0 : ∀ j : ℕ, j ≤ Hw → 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean)
    (hvar : ∀ j : ℕ, j ≤ Hw →
      scaleVariance P (roundedGrid l n) (F)
        (t - (j : ℤ)) ≤ ENNReal.ofReal (V j))
    (hvart : scaleVariance P (roundedGrid l n)
      (F) t ≤ ENNReal.ofReal V0)
    (hdrop : ∀ j : ℕ, j ≤ Hw →
      blockSize (blockSub (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
        (adaptedMean P (roundedGrid l n) t))
        (F) ≤ Dr j)
    (hvmean : scaleVariance P (roundedGrid l n)
      (adaptedMean P (roundedGrid l n) t) t ≤ ENNReal.ofReal Vmean)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    Response.profilePrimalWeakQuantity P m0 (Recurrence.posDef_roundedGrid hl hn) t
        (fun a ↦ a.subSkew (Response.responseSkew K0)
          (Response.is_skew_mat_response_skew K0))
        (Response.centeredResponseLoadP S0 SStar0 K0 e)
        (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
      ENNReal.ofReal
        (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
          (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev)
          P m0 (Response.responseSkew K0) F
          (loadScaleOfScalar cF kap) n rho Hw
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev t l
          V V0 Dr Vmean) := by
  classical
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR1]
  have hcf0 : (0 : ℝ) ≤ Response.recentConstantAtLevel lev :=
    Response.zero_le_recentConstantAtLevel lev
  have hcm0 : (0 : ℝ) ≤ Response.maxGroupConstantAtLevel lev :=
    Response.zero_le_maxGroupConstantAtLevel lev
  have hct0 : (0 : ℝ) ≤ Response.energyGoodConstantAtLevel lev :=
    Real.sqrt_nonneg _
  -- the six load bounds
  have hloads := calibrated_weak_loads hq t (hintAll t) hS0 hStar0 hform
    hpos
    heps1 htr hcF0 hFeq hFpd hkap0 hcomp e he
  -- the load spellings
  have hloadP : Response.centeredResponseLoadP S0 SStar0 K0 e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e := by
    rw [Response.centeredResponseLoadP, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hloadQ : Response.centeredResponseLoadQ S0 SStar0 K0 e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e := by
    rw [Response.centeredResponseLoadQ, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  -- the weak cap at the spelled loads
  have hweak := eLpNorm_profilePrimalWeakRoot_reference_le_sharp_of_block_at_level hg hdag
    hstat hl hn hgrid hm0 hrho0 hrho1 t Hw hstart hFsym hFpd hR1 hlev henvMax
    hsK hDelta hintAll hEt (Response.responseSkew K0) (Response.is_skew_mat_response_skew K0)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  -- the budget bounds
  have hsum0 : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j + V0 + Dr j := fun j hj =>
    add_nonneg (add_nonneg (hV j hj) hV0) (hDr0 j hj)
  have hbudget : ∀ j ∈ Finset.range (Hw + 1),
      weakScaleBudget P (roundedGrid l n) (F)
        t j ≤ ENNReal.ofReal (V j + V0 + Dr j) := by
    intro j hj
    have hjHw : j ≤ Hw := Finset.mem_range_succ_iff.mp hj
    rw [weakScaleBudget,
      ENNReal.ofReal_add (add_nonneg (hV j hjHw) hV0) (hDr0 j hjHw),
      ENNReal.ofReal_add (hV j hjHw) hV0]
    exact add_le_add (add_le_add (hvar j hjHw) hvart)
      (ENNReal.ofReal_le_ofReal (hdrop j hjHw))
  -- nonnegativity bundle
  have hMF20 : 0 ≤ Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) := by
    rw [Response.diagonalWeakMetricFactor_eq]
    exact Real.sqrt_nonneg _
  have hMFm0 : 0 ≤ Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (adaptedMean P (roundedGrid l n) t)) := by
    rw [Response.diagonalWeakMetricFactor_eq]
    exact Real.sqrt_nonneg _
  have hS1'0 : 0 ≤ ∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j) :=
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (hsum0 j (Finset.mem_range_succ_iff.mp hj))
  have hS2'0 : 0 ≤ ∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
        Real.sqrt (2 * d * Dr j) :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hbad0 : 0 ≤ Response.profileBadMajorantAt 4
      (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev :=
    Response.profileBadMajorantAt_nonneg
      (by
        have := badMomentMajorant_nonneg K (t + (G : ℤ) - 1 - sK)
        positivity)
      (by linarith only [hR0])
  have hpow0 : 0 ≤ (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hconst0 := constant_seminorm_coefficient_nonnegative
  have hc20 : 0 ≤ Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) / (2 * ((1 - rho) / 2)) :=
    div_nonneg (mul_nonneg hcm0 hMF20)
      (by linarith only [hrho1])
  have hsqrt70 : (0 : ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  have hwls0 : 0 ≤ Real.sqrt
      (cF * kap * 7) :=
    Real.sqrt_nonneg _
  have hwls10 : 0 ≤ Real.sqrt
      (cF * kap * 7 +
        1) := Real.sqrt_nonneg _
  -- the three group bounds
  have hS1 : (∑ j ∈ Finset.range (Hw + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) *
        weakScaleBudget P (roundedGrid l n)
          (F) t j) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j hj =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (hsum0 j (Finset.mem_range_succ_iff.mp hj))]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact mul_le_mul' le_rfl (hbudget j hj)
  have hS2 : (∑ j ∈ Finset.range (Hw + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) *
        ENNReal.ofReal (Real.sqrt (2 * d *
          blockSize (blockSub
            (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
            (adaptedMean P (roundedGrid l n) t))
            (F)))) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt (2 * d * Dr j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjHw : j ≤ Hw := Finset.mem_range_succ_iff.mp hj
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left (hdrop j hjHw)
      (by positivity : (0 : ℝ) ≤ 2 * d)
  have h1 := mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hloads.1
        (mul_nonneg hcf0 hMF20)))
    (le_trans (add_le_add hS1 hS2)
      (le_of_eq (ENNReal.ofReal_add hS1'0 hS2'0).symm))
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (mul_nonneg hcf0 hMF20)
      hwls0)] at h1
  obtain ⟨hA1le, hA2le⟩ := energy_load_group_bounds hloads.2.1 hbad0
    (mul_nonneg hct0 hpow0)
  have hB10 : 0 ≤ Real.sqrt 2 * Real.sqrt
      (cF * kap * 7 +
        1) *
      Response.profileBadMajorantAt 4
        (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hwls10) hbad0
  have hB20 : 0 ≤ Response.energyGoodConstantAtLevel lev *
      (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
      Real.sqrt
        (cF * kap * 7 +
          1) :=
    mul_nonneg (mul_nonneg hct0 hpow0) hwls10
  have h2 := mul_le_mul'
    (le_refl (ENNReal.ofReal
      (Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
        (Response.skewBlockCongr (Response.responseSkew K0)
          (F)) / (2 * ((1 - rho) / 2)))))
    (le_trans
      (add_le_add (ENNReal.ofReal_le_ofReal hA1le)
        (ENNReal.ofReal_le_ofReal hA2le))
      (le_of_eq (ENNReal.ofReal_add hB10 hB20).symm))
  rw [← ENNReal.ofReal_mul hc20] at h2
  have h3inner := mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hloads.2.2.1 hMFm0))
    hvmean
  rw [← ENNReal.ofReal_mul (mul_nonneg hMFm0 hsqrt70)] at h3inner
  have h3 := mul_le_mul'
    (le_refl (ENNReal.ofReal Response.constantSeminormCoefficient)) h3inner
  rw [← ENNReal.ofReal_mul hconst0] at h3
  -- assemble
  have hW10 : 0 ≤ Response.recentConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) *
      Real.sqrt
        (cF * kap * 7) *
      ((∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
        ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt (2 * d * Dr j)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hcf0 hMF20) hwls0)
      (add_nonneg hS1'0 hS2'0)
  have hW20 : 0 ≤ Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) / (2 * ((1 - rho) / 2)) *
      (Real.sqrt 2 * Real.sqrt
          (cF * kap *
            7 + 1) *
        Response.profileBadMajorantAt 4
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev +
        Response.energyGoodConstantAtLevel lev *
            (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt
            (cF * kap *
              7 + 1)) :=
    mul_nonneg hc20 (add_nonneg hB10 hB20)
  have hW30 : 0 ≤ Response.constantSeminormCoefficient *
      (Response.diagonalWeakMetricFactor m0
        (Response.skewBlockCongr (Response.responseSkew K0)
          (adaptedMean P (roundedGrid l n) t)) * Real.sqrt 7 * Vmean) :=
    mul_nonneg hconst0
      (mul_nonneg (mul_nonneg hMFm0 hsqrt70) hVmean)
  have hM := add_le_add (add_le_add h1 h2) h3
  rw [← ENNReal.ofReal_add hW10 hW20,
    ← ENNReal.ofReal_add (add_nonneg hW10 hW20) hW30] at hM
  rw [hloadP, hloadQ, Response.profilePrimalWeakQuantity_eq]
  refine le_trans
    (ENNReal.pow_le_pow_left (le_trans hweak hM)) ?_
  rw [weakValueBoundSharpIsotropyAt, loadScaleOfScalar,
    ENNReal.ofReal_pow (add_nonneg (add_nonneg hW10 hW20) hW30)]

/-- **The adjoint weak quantity by the released sharp weak value.** -/
theorem profileAdjointWeakQuantity_le_weakValueSharp_of_block_at_level [NeZero d]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l n))
    {m0 : Mat d} (hm0 : m0.PosDef)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (t : ℤ) (Hw : ℕ) (hstart : l ≤ t - (Hw : ℤ))
    {G : ℕ}
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF : ℝ} (hcF0 : 0 ≤ cF) (hFeq : F = blockScale cF E)
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid l n) k)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t))
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P (roundedGrid l n) t) =
      schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X))
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hV : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j) (hV0 : 0 ≤ V0)
    (hDr0 : ∀ j : ℕ, j ≤ Hw → 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean)
    (hvar : ∀ j : ℕ, j ≤ Hw →
      scaleVariance P (roundedGrid l n) (F)
        (t - (j : ℤ)) ≤ ENNReal.ofReal (V j))
    (hvart : scaleVariance P (roundedGrid l n)
      (F) t ≤ ENNReal.ofReal V0)
    (hdrop : ∀ j : ℕ, j ≤ Hw →
      blockSize (blockSub (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
        (adaptedMean P (roundedGrid l n) t))
        (F) ≤ Dr j)
    (hvmean : scaleVariance P (roundedGrid l n)
      (adaptedMean P (roundedGrid l n) t) t ≤ ENNReal.ofReal Vmean)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    Response.profileAdjointWeakQuantity P m0 (Recurrence.posDef_roundedGrid hl hn) t
        (fun a ↦ a.subSkew (Response.responseSkew K0)
          (Response.is_skew_mat_response_skew K0))
        (Response.centeredResponseLoadP S0 SStar0 K0 e)
        (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
      ENNReal.ofReal
        (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
          (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev)
          P m0 (Response.responseSkew K0) F
          (loadScaleOfScalar cF kap) n rho Hw
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev t l
          V V0 Dr Vmean) := by
  classical
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR1]
  have hcf0 : (0 : ℝ) ≤ Response.recentConstantAtLevel lev :=
    Response.zero_le_recentConstantAtLevel lev
  have hcm0 : (0 : ℝ) ≤ Response.maxGroupConstantAtLevel lev :=
    Response.zero_le_maxGroupConstantAtLevel lev
  have hct0 : (0 : ℝ) ≤ Response.energyGoodConstantAtLevel lev :=
    Real.sqrt_nonneg _
  -- the six load bounds
  have hloads := calibrated_weak_loads hq t (hintAll t) hS0 hStar0 hform
    hpos
    heps1 htr hcF0 hFeq hFpd hkap0 hcomp e he
  -- the load spellings
  have hloadP : Response.centeredResponseLoadP S0 SStar0 K0 e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e := by
    rw [Response.centeredResponseLoadP, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hloadQ : Response.centeredResponseLoadQ S0 SStar0 K0 e =
      matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
        Response.responseSymmetric K0) SStar0) *ᵥ e := by
    rw [Response.centeredResponseLoadQ, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  -- the weak cap at the spelled loads
  have hweak := eLpNorm_profileAdjointWeakRoot_reference_le_sharp_of_block_at_level hg hdag
    hstat hl hn hgrid hm0 hrho0 hrho1 t Hw hstart hFsym hFpd hR1 hlev henvMax
    hsK hDelta hintAll hEt (Response.responseSkew K0) (Response.is_skew_mat_response_skew K0)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S0 + Response.responseSymmetric K0 * SStar0⁻¹ *
      Response.responseSymmetric K0) SStar0) *ᵥ e)
  -- the budget bounds
  have hsum0 : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j + V0 + Dr j := fun j hj =>
    add_nonneg (add_nonneg (hV j hj) hV0) (hDr0 j hj)
  have hbudget : ∀ j ∈ Finset.range (Hw + 1),
      weakScaleBudget P (roundedGrid l n) (F)
        t j ≤ ENNReal.ofReal (V j + V0 + Dr j) := by
    intro j hj
    have hjHw : j ≤ Hw := Finset.mem_range_succ_iff.mp hj
    rw [weakScaleBudget,
      ENNReal.ofReal_add (add_nonneg (hV j hjHw) hV0) (hDr0 j hjHw),
      ENNReal.ofReal_add (hV j hjHw) hV0]
    exact add_le_add (add_le_add (hvar j hjHw) hvart)
      (ENNReal.ofReal_le_ofReal (hdrop j hjHw))
  -- nonnegativity bundle
  have hMF20 : 0 ≤ Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) := by
    rw [Response.diagonalWeakMetricFactor_eq]
    exact Real.sqrt_nonneg _
  have hMFm0 : 0 ≤ Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (adaptedMean P (roundedGrid l n) t)) := by
    rw [Response.diagonalWeakMetricFactor_eq]
    exact Real.sqrt_nonneg _
  have hS1'0 : 0 ≤ ∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j) :=
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (hsum0 j (Finset.mem_range_succ_iff.mp hj))
  have hS2'0 : 0 ≤ ∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
        Real.sqrt (2 * d * Dr j) :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hbad0 : 0 ≤ Response.profileBadMajorantAt 4
      (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev :=
    Response.profileBadMajorantAt_nonneg
      (by
        have := badMomentMajorant_nonneg K (t + (G : ℤ) - 1 - sK)
        positivity)
      (by linarith only [hR0])
  have hpow0 : 0 ≤ (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hconst0 := constant_seminorm_coefficient_nonnegative
  have hc20 : 0 ≤ Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) / (2 * ((1 - rho) / 2)) :=
    div_nonneg (mul_nonneg hcm0 hMF20)
      (by linarith only [hrho1])
  have hsqrt70 : (0 : ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  have hwls0 : 0 ≤ Real.sqrt
      (cF * kap * 7) :=
    Real.sqrt_nonneg _
  have hwls10 : 0 ≤ Real.sqrt
      (cF * kap * 7 +
        1) := Real.sqrt_nonneg _
  -- the three group bounds
  have hS1 : (∑ j ∈ Finset.range (Hw + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) *
        weakScaleBudget P (roundedGrid l n)
          (F) t j) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j hj =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (hsum0 j (Finset.mem_range_succ_iff.mp hj))]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact mul_le_mul' le_rfl (hbudget j hj)
  have hS2 : (∑ j ∈ Finset.range (Hw + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) *
        ENNReal.ofReal (Real.sqrt (2 * d *
          blockSize (blockSub
            (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
            (adaptedMean P (roundedGrid l n) t))
            (F)))) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt (2 * d * Dr j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjHw : j ≤ Hw := Finset.mem_range_succ_iff.mp hj
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left (hdrop j hjHw)
      (by positivity : (0 : ℝ) ≤ 2 * d)
  have h1 := mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hloads.2.2.2.1
        (mul_nonneg hcf0 hMF20)))
    (le_trans (add_le_add hS1 hS2)
      (le_of_eq (ENNReal.ofReal_add hS1'0 hS2'0).symm))
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (mul_nonneg hcf0 hMF20)
      hwls0)] at h1
  obtain ⟨hA1le, hA2le⟩ := energy_load_group_bounds hloads.2.2.2.2.1 hbad0
    (mul_nonneg hct0 hpow0)
  have hB10 : 0 ≤ Real.sqrt 2 * Real.sqrt
      (cF * kap * 7 +
        1) *
      Response.profileBadMajorantAt 4
        (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hwls10) hbad0
  have hB20 : 0 ≤ Response.energyGoodConstantAtLevel lev *
      (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
      Real.sqrt
        (cF * kap * 7 +
          1) :=
    mul_nonneg (mul_nonneg hct0 hpow0) hwls10
  have h2 := mul_le_mul'
    (le_refl (ENNReal.ofReal
      (Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
        (Response.skewBlockCongr (Response.responseSkew K0)
          (F)) / (2 * ((1 - rho) / 2)))))
    (le_trans
      (add_le_add (ENNReal.ofReal_le_ofReal hA1le)
        (ENNReal.ofReal_le_ofReal hA2le))
      (le_of_eq (ENNReal.ofReal_add hB10 hB20).symm))
  rw [← ENNReal.ofReal_mul hc20] at h2
  have h3inner := mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hloads.2.2.2.2.2 hMFm0))
    hvmean
  rw [← ENNReal.ofReal_mul (mul_nonneg hMFm0 hsqrt70)] at h3inner
  have h3 := mul_le_mul'
    (le_refl (ENNReal.ofReal Response.constantSeminormCoefficient)) h3inner
  rw [← ENNReal.ofReal_mul hconst0] at h3
  -- assemble
  have hW10 : 0 ≤ Response.recentConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) *
      Real.sqrt
        (cF * kap * 7) *
      ((∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
        ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt (2 * d * Dr j)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hcf0 hMF20) hwls0)
      (add_nonneg hS1'0 hS2'0)
  have hW20 : 0 ≤ Response.maxGroupConstantAtLevel lev * Response.diagonalWeakMetricFactor m0
      (Response.skewBlockCongr (Response.responseSkew K0)
        (F)) / (2 * ((1 - rho) / 2)) *
      (Real.sqrt 2 * Real.sqrt
          (cF * kap *
            7 + 1) *
        Response.profileBadMajorantAt 4
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev +
        Response.energyGoodConstantAtLevel lev *
            (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt
            (cF * kap *
              7 + 1)) :=
    mul_nonneg hc20 (add_nonneg hB10 hB20)
  have hW30 : 0 ≤ Response.constantSeminormCoefficient *
      (Response.diagonalWeakMetricFactor m0
        (Response.skewBlockCongr (Response.responseSkew K0)
          (adaptedMean P (roundedGrid l n) t)) * Real.sqrt 7 * Vmean) :=
    mul_nonneg hconst0
      (mul_nonneg (mul_nonneg hMFm0 hsqrt70) hVmean)
  have hM := add_le_add (add_le_add h1 h2) h3
  rw [← ENNReal.ofReal_add hW10 hW20,
    ← ENNReal.ofReal_add (add_nonneg hW10 hW20) hW30] at hM
  rw [hloadP, hloadQ, Response.profileAdjointWeakQuantity_eq]
  refine le_trans
    (ENNReal.pow_le_pow_left (le_trans hweak hM)) ?_
  rw [weakValueBoundSharpIsotropyAt, loadScaleOfScalar,
    ENNReal.ofReal_pow (add_nonneg (add_nonneg hW10 hW20) hW30)]

end

end HCPolySupport.HighContrast.Quenched
