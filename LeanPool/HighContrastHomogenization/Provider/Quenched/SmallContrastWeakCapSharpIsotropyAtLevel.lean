/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakEnergyTailAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakCapSharpIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp weak caps at a released split level

The two sharp caps at a parametrized normalizer, with the profile's split level
free.  Three constants move with the level and one majorant is replaced:

* the recent group's coefficient becomes `recentConstantAtLevel lev`;
* the maximum group's becomes `maxGroupConstantAtLevel lev`;
* the good branch's becomes `energyGoodConstantAtLevel lev`;
* the bad slot carries `profileBadMajorantAt 4 (R ^ 4 · badMomentMajorant K Δ)
  (R / 2) lev` — the residue-free majorant at the matched threshold.

At `lev = 1` and `R = 1` the first three are the pinned numerals and the fourth
is the pinned majorant, so the pinned caps are the specialization.  Everything
else — the five-group discharge, the measurability inputs, the recentering
identities — is the pinned proof unchanged.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The weak seminorm of the metric-root image of a sampled optimizer state
minus a fixed vector is a.e. measurable once every aligned child average of the
state is, coordinatewise. -/
private theorem aemeasurable_adaptedWeakSeminorm_metricRoot_sub_const [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (S : Mat d) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (c : BlockVec d)
    (hcell : ∀ k : ℤ, k ≤ t → ∀ w ∈ Response.alignedIndex q k t,
      ∀ alpha : BlockCoord d, AEMeasurable (fun a ↦
        toFullBlockVec (Response.blockCellAverage (adaptedCellAt q k w)
          (Response.diagonalWeakState hq t (sample a) p r)) alpha) P) :
    AEMeasurable (fun a ↦ Response.adaptedWeakSeminorm q t (1 / 2) (fun x ↦
      blockMatVecMul (blockDiag S S⁻¹)
        (Response.diagonalWeakState hq t (sample a) p r x - c))) P := by
  have hdot : Continuous fun v : BlockVec d ↦ blockVecDot v v := by
    unfold blockVecDot vecDot
    fun_prop
  have hroot : Continuous fun v : BlockVec d ↦
      blockMatVecMul (blockDiag S S⁻¹) (v - c) := by
    unfold blockMatVecMul matVecMul
    fun_prop
  unfold Response.adaptedWeakSeminorm
  refine AEMeasurable.tsum fun j ↦ ?_
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  have hkt : t - (j : ℤ) ≤ t := by omega
  have hterm : ∀ z ∈ Response.alignedIndex q (t - (j : ℤ)) t, AEMeasurable
      (fun a ↦ blockVecDot
        (Response.blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) (fun x ↦
          blockMatVecMul (blockDiag S S⁻¹)
            (Response.diagonalWeakState hq t (sample a) p r x - c)))
        (Response.blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) (fun x ↦
          blockMatVecMul (blockDiag S S⁻¹)
            (Response.diagonalWeakState hq t (sample a) p r x - c)))) P := by
    intro z hz
    have hfst : AEMeasurable (fun a ↦
        (Response.blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
          (Response.diagonalWeakState hq t (sample a) p r)).1) P :=
      aemeasurable_pi_iff.mpr fun i ↦ hcell _ hkt z hz (Sum.inl i)
    have hsnd : AEMeasurable (fun a ↦
        (Response.blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
          (Response.diagonalWeakState hq t (sample a) p r)).2) P :=
      aemeasurable_pi_iff.mpr fun i ↦ hcell _ hkt z hz (Sum.inr i)
    have hcomp := (hdot.comp hroot).measurable.comp_aemeasurable
      (hfst.prodMk hsnd)
    refine hcomp.congr ?_
    filter_upwards [] with a
    simp only [Function.comp_apply]
    rw [Response.blockCellAverage_metricRoot_sub_const_diagonalWeakState hq hkt
      hz p r c]
  unfold Response.adaptedWeakScaleTerm Response.blockAvsumL2 Response.avsum
  exact ((Finset.aemeasurable_fun_sum _ hterm).const_mul _).sqrt.const_mul _

/-- **The sharp weak cap (primal), at a released split level.** -/
theorem eLpNorm_profilePrimalWeakRoot_reference_le_sharp_of_block_at_level [NeZero d]
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
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid l n) k)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t))
    (h0 : Mat d) (hh0 : IsSkewMat h0) (p r : Vec d) :
    eLpNorm
        (Response.profilePrimalWeakRoot m0 (Recurrence.posDef_roundedGrid hl hn) t
          (fun a => a.subSkew h0 hh0) p r
          (Response.profilePrimalCenter P (Recurrence.posDef_roundedGrid hl hn) t
            (fun a => a.subSkew h0 hh0) p r)) 2 P ≤
      ENNReal.ofReal
          (Response.recentConstantAtLevel lev *
              Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) *
            Response.diagonalWeakLoadMinus
              (Response.skewBlockCongr h0 F)
              p r) *
          ((∑ j ∈ Finset.range (Hw + 1),
              ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) *
                weakScaleBudget P (roundedGrid l n)
                  F t j) +
            ∑ j ∈ Finset.range (Hw + 1),
              ENNReal.ofReal
                  ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) *
                ENNReal.ofReal (Real.sqrt (2 * d *
                  blockSize (blockSub
                    (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
                    (adaptedMean P (roundedGrid l n) t))
                    F))) +
        ENNReal.ofReal
            (Response.maxGroupConstantAtLevel lev *
                Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) /
              (2 * ((1 - rho) / 2))) *
          (ENNReal.ofReal (Real.sqrt 2 *
              Response.profileEnergyLoad
                (Response.diagonalWeakLoadMinus F
                  p (r - matVecMul h0 p)) p (r - matVecMul h0 p) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK))
                (R / 2) lev) +
            ENNReal.ofReal (Response.energyGoodConstantAtLevel lev *
              (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
              Response.profileEnergyLoad
                (Response.diagonalWeakLoadMinus F
                  p (r - matVecMul h0 p)) p (r - matVecMul h0 p))) +
        ENNReal.ofReal Response.constantSeminormCoefficient *
          (ENNReal.ofReal
              (Response.diagonalWeakMetricFactor m0
                  (Response.skewBlockCongr h0
                    (adaptedMean P (roundedGrid l n) t)) *
                Response.diagonalWeakLoadMinus
                  (Response.skewBlockCongr h0
                    (adaptedMean P (roundedGrid l n) t)) p r) *
            scaleVariance P (roundedGrid l n)
              (adaptedMean P (roundedGrid l n) t) t) := by
  classical
  have hlev0 : (0 : ℝ) < lev := lt_of_lt_of_le one_pos hlev
  set q : Mat d := roundedGrid l n with hqdef
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hn
  -- measurability inputs at the recentered reference
  have hU : AEMeasurable
      (fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2)
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P :=
    Response.aemeasurable_diagonalWeakCellSum_subSkew hq t Hw (1 / 2)
      hFsym hFpd h0 hh0
  have hVplain : AEMeasurable
      (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a) P := by
    have hterm : ∀ j : ℕ, AEMeasurable
        (fun a => (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt
            (blockSize
              (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
              (blockIdentity d))) P := fun j =>
      ((aemeasurable_blockSize_averageDefect hq (t - (j : ℤ)) t
        F).sqrt.const_mul _)
    rw [show (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a) =
        fun a ↦ ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt
              (blockSize
                (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
                (blockIdentity d)) from by
      funext a
      rw [Response.diagonalWeakAverageSum]]
    exact Finset.aemeasurable_fun_sum _ fun j _ => hterm j
  have hV : AEMeasurable
      (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P := by
    refine hVplain.congr ?_
    filter_upwards [] with a
    exact (Response.diagonalWeakAverageSum_subSkew hq t Hw (1 / 2) rho
      hFsym hFpd a h0 hh0).symm
  have hM : AEMeasurable
      (fun a ↦ Response.diagonalWeakMaximum rho q t
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P :=
    Response.aemeasurable_diagonalWeakMaximum_subSkew hq hFsym hFpd h0 hh0
  have hEn : AEMeasurable
      (fun a ↦ Response.diagonalWeakEnergy hq t (a.subSkew h0 hh0) p r) P :=
    Response.aemeasurable_diagonalWeakEnergy_subSkew hq t h0 hh0 p r
  have havg : AEMeasurable
      (fun a ↦ Response.blockCellAverage (adaptedCell q t)
        (Response.diagonalWeakState hq t (a.subSkew h0 hh0) p r)) P :=
    Response.aemeasurable_blockCellAverage_diagonalWeakState_subSkew hq t
      h0 hh0 p r
  -- a.s. finiteness of the maximal function
  have hfinite : ∀ᵐ a ∂P, Response.diagonalWeakMaximum rho q t
      (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0) ≠ ⊤ := by
    filter_upwards [henvMax] with a hMa
    rw [Response.diagonalWeakMaximum_subSkew hq rho t F a h0 hh0]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMa
  -- measurability of the weak root
  have hroot : AEStronglyMeasurable
      (Response.profilePrimalWeakRoot m0 hq t (fun a => a.subSkew h0 hh0) p r
        (Response.profilePrimalCenter P hq t (fun a => a.subSkew h0 hh0) p r)) P :=
    ((aemeasurable_adaptedWeakSeminorm_metricRoot_sub_const hq t (matSqrt m0)
      (fun a => a.subSkew h0 hh0) p r
      (Response.profilePrimalCenter P hq t (fun a => a.subSkew h0 hh0) p r)
      fun _k hk _w hw alpha =>
        (Selection.aestronglyMeasurable_blockCellAverage_diagonalWeakState_subSkew_alignedIndex
          hq hk P h0 hh0 p r hw alpha).aemeasurable).const_mul _).aestronglyMeasurable
  -- the sample-level majorization
  have hmain := Response.eLpNorm_profilePrimalWeakRoot_sample_at_level_le hq t Hw hm0
    (Response.isSymmetricBlockMat_skewBlockCongr (g := h0) hFsym)
    (Response.blockPosDef_skewBlockCongr (g := h0) hFpd)
    hrho0 hrho1 hlev0 rfl (fun a => a.subSkew h0 hh0) p r hU hV hM hEn havg
    hfinite hroot
  refine le_trans hmain ?_
  -- discharge the five groups
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the cell and average sums
    refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · have hcell : (fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2)
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2) F a := by
        funext a
        exact Response.diagonalWeakCellSum_subSkew hq t Hw (1 / 2) F a h0 hh0
      rw [hcell]
      refine le_trans (eLpNorm_diagonalWeakCellSum_le_variance hstat hgrid
        Hw hstart hFsym hFpd) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [weakScaleBudget]
    · have havgs : (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a := by
        funext a
        exact Response.diagonalWeakAverageSum_subSkew hq t Hw (1 / 2) rho
          hFsym hFpd a h0 hh0
      rw [havgs]
      exact eLpNorm_diagonalWeakAverageSum_le_drops hstat hgrid Hw hstart
        hintAll hFsym hFpd
  · -- the bad and good optimizer energies
    refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · rw [show (fun a ↦ Response.diagonalWeakMaximum rho q t
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          Response.diagonalWeakMaximum rho q t F from
        funext fun a => Response.diagonalWeakMaximum_subSkew hq rho t F a
          h0 hh0,
        show (fun a ↦ Response.diagonalWeakEnergy hq t (a.subSkew h0 hh0) p r) =
          fun a ↦ Response.diagonalWeakEnergy hq t a p (r - matVecMul h0 p)
          from funext fun a =>
            Response.diagonalWeakEnergy_subSkew hq t a h0 hh0 p r,
        ]
      exact profileBadEnergyAt_of_maximum_envelope hg hdag hl hn t hsK hDelta
        hFsym hFpd hR1 hlev henvMax p (r - matVecMul h0 p)
    · rw [show (fun a ↦ Response.diagonalWeakMaximum rho q t
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          Response.diagonalWeakMaximum rho q t F from
        funext fun a => Response.diagonalWeakMaximum_subSkew hq rho t F a
          h0 hh0,
        show (fun a ↦ Response.diagonalWeakEnergy hq t (a.subSkew h0 hh0) p r) =
          fun a ↦ Response.diagonalWeakEnergy hq t a p (r - matVecMul h0 p)
          from funext fun a =>
            Response.diagonalWeakEnergy_subSkew hq t a h0 hh0 p r]
      refine le_trans (Response.profileGoodEnergyAt_diagonalWeakEnergy_le hq
        hFsym hFpd hlev p (r - matVecMul h0 p)) ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      ring
  · -- the centering variance
    refine mul_le_mul' le_rfl ?_
    exact profilePrimalCenterVariance_le_variance hm0 hq t (hintAll t) hEt
      h0 hh0 p r

/-- **The sharp weak cap (adjoint), at a released split level.** -/
theorem eLpNorm_profileAdjointWeakRoot_reference_le_sharp_of_block_at_level [NeZero d]
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
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid l n) k)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t))
    (h0 : Mat d) (hh0 : IsSkewMat h0) (p r : Vec d) :
    eLpNorm
        (Response.profileAdjointWeakRoot m0 (Recurrence.posDef_roundedGrid hl hn) t
          (fun a => a.subSkew h0 hh0) p r
          (Response.profileAdjointCenter P (Recurrence.posDef_roundedGrid hl hn) t
            (fun a => a.subSkew h0 hh0) p r)) 2 P ≤
      ENNReal.ofReal
          (Response.recentConstantAtLevel lev *
              Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) *
            Response.diagonalWeakLoadPlus
              (Response.skewBlockCongr h0 F)
              p r) *
          ((∑ j ∈ Finset.range (Hw + 1),
              ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) *
                weakScaleBudget P (roundedGrid l n)
                  F t j) +
            ∑ j ∈ Finset.range (Hw + 1),
              ENNReal.ofReal
                  ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) *
                ENNReal.ofReal (Real.sqrt (2 * d *
                  blockSize (blockSub
                    (adaptedMean P (roundedGrid l n) (t - (j : ℤ)))
                    (adaptedMean P (roundedGrid l n) t))
                    F))) +
        ENNReal.ofReal
            (Response.maxGroupConstantAtLevel lev *
                Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) /
              (2 * ((1 - rho) / 2))) *
          (ENNReal.ofReal (Real.sqrt 2 *
              Response.profileEnergyLoad
                (Response.diagonalWeakLoadPlus F
                  p (r + matVecMul h0 p)) p (r + matVecMul h0 p) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK))
                (R / 2) lev) +
            ENNReal.ofReal (Response.energyGoodConstantAtLevel lev *
              (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
              Response.profileEnergyLoad
                (Response.diagonalWeakLoadPlus F
                  p (r + matVecMul h0 p)) p (r + matVecMul h0 p))) +
        ENNReal.ofReal Response.constantSeminormCoefficient *
          (ENNReal.ofReal
              (Response.diagonalWeakMetricFactor m0
                  (Response.skewBlockCongr h0
                    (adaptedMean P (roundedGrid l n) t)) *
                Response.diagonalWeakLoadPlus
                  (Response.skewBlockCongr h0
                    (adaptedMean P (roundedGrid l n) t)) p r) *
            scaleVariance P (roundedGrid l n)
              (adaptedMean P (roundedGrid l n) t) t) := by
  classical
  have hlev0 : (0 : ℝ) < lev := lt_of_lt_of_le one_pos hlev
  set q : Mat d := roundedGrid l n with hqdef
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hn
  -- measurability inputs at the recentered reference
  have hU : AEMeasurable
      (fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2)
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P :=
    Response.aemeasurable_diagonalWeakCellSum_subSkew hq t Hw (1 / 2)
      hFsym hFpd h0 hh0
  have hVplain : AEMeasurable
      (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a) P := by
    have hterm : ∀ j : ℕ, AEMeasurable
        (fun a => (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt
            (blockSize
              (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
              (blockIdentity d))) P := fun j =>
      ((aemeasurable_blockSize_averageDefect hq (t - (j : ℤ)) t
        F).sqrt.const_mul _)
    rw [show (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a) =
        fun a ↦ ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt
              (blockSize
                (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
                (blockIdentity d)) from by
      funext a
      rw [Response.diagonalWeakAverageSum]]
    exact Finset.aemeasurable_fun_sum _ fun j _ => hterm j
  have hV : AEMeasurable
      (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P := by
    refine hVplain.congr ?_
    filter_upwards [] with a
    exact (Response.diagonalWeakAverageSum_subSkew hq t Hw (1 / 2) rho
      hFsym hFpd a h0 hh0).symm
  have hM : AEMeasurable
      (fun a ↦ Response.diagonalWeakMaximum rho q t
        (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) P :=
    Response.aemeasurable_diagonalWeakMaximum_subSkew hq hFsym hFpd h0 hh0
  have hEn : AEMeasurable
      (fun a ↦ Response.diagonalWeakAdjointEnergy hq t (a.subSkew h0 hh0) p r)
      P :=
    Response.aemeasurable_diagonalWeakAdjointEnergy_subSkew hq t h0 hh0 p r
  have havg : AEMeasurable
      (fun a ↦ Response.blockCellAverage (adaptedCell q t)
        (Response.diagonalWeakAdjointState hq t (a.subSkew h0 hh0) p r)) P :=
    Response.aemeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew
      hq t h0 hh0 p r
  -- a.s. finiteness of the maximal function
  have hfinite : ∀ᵐ a ∂P, Response.diagonalWeakMaximum rho q t
      (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0) ≠ ⊤ := by
    filter_upwards [henvMax] with a hMa
    rw [Response.diagonalWeakMaximum_subSkew hq rho t F a h0 hh0]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMa
  -- measurability of the weak root
  have hroot : AEStronglyMeasurable
      (Response.profileAdjointWeakRoot m0 hq t (fun a => a.subSkew h0 hh0) p r
        (Response.profileAdjointCenter P hq t (fun a => a.subSkew h0 hh0) p r)) P :=
    ((aemeasurable_adaptedWeakSeminorm_metricRoot_sub_const hq t (matSqrt m0)
      (fun a => (a.subSkew h0 hh0).transpose) p r
      (Response.profileAdjointCenter P hq t (fun a => a.subSkew h0 hh0) p r)
      fun _k hk _w hw alpha =>
        (Selection.aestronglyMeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew_alignedIndex
          hq hk P h0 hh0 p r hw alpha).aemeasurable).const_mul _).aestronglyMeasurable
  -- the sample-level majorization
  have hmain := Response.eLpNorm_profileAdjointWeakRoot_sample_at_level_le hq t Hw hm0
    (Response.isSymmetricBlockMat_skewBlockCongr (g := h0) hFsym)
    (Response.blockPosDef_skewBlockCongr (g := h0) hFpd)
    hrho0 hrho1 hlev0 rfl (fun a => a.subSkew h0 hh0) p r hU hV hM hEn havg
    hfinite hroot
  refine le_trans hmain ?_
  -- discharge the five groups
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the cell and average sums
    refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · have hcell : (fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2)
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          fun a ↦ Response.diagonalWeakCellSum q t Hw (1 / 2) F a := by
        funext a
        exact Response.diagonalWeakCellSum_subSkew hq t Hw (1 / 2) F a h0 hh0
      rw [hcell]
      refine le_trans (eLpNorm_diagonalWeakCellSum_le_variance hstat hgrid
        Hw hstart hFsym hFpd) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [weakScaleBudget]
    · have havgs : (fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          fun a ↦ Response.diagonalWeakAverageSum q t Hw (1 / 2) rho F a := by
        funext a
        exact Response.diagonalWeakAverageSum_subSkew hq t Hw (1 / 2) rho
          hFsym hFpd a h0 hh0
      rw [havgs]
      exact eLpNorm_diagonalWeakAverageSum_le_drops hstat hgrid Hw hstart
        hintAll hFsym hFpd
  · -- the bad and good optimizer energies
    refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · rw [show (fun a ↦ Response.diagonalWeakMaximum rho q t
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          Response.diagonalWeakMaximum rho q t F from
        funext fun a => Response.diagonalWeakMaximum_subSkew hq rho t F a
          h0 hh0,
        show (fun a ↦ Response.diagonalWeakAdjointEnergy hq t
            (a.subSkew h0 hh0) p r) =
          fun a ↦ Response.diagonalWeakAdjointEnergy hq t a p
            (r + matVecMul h0 p)
          from funext fun a =>
            Response.diagonalWeakAdjointEnergy_subSkew hq t a h0 hh0 p r,
        ]
      exact profileBadEnergyAt_adjoint_of_maximum_envelope hg hdag hl hn t hsK
        hDelta hFsym hFpd hR1 hlev henvMax p (r + matVecMul h0 p)
    · rw [show (fun a ↦ Response.diagonalWeakMaximum rho q t
          (Response.skewBlockCongr h0 F) (a.subSkew h0 hh0)) =
          Response.diagonalWeakMaximum rho q t F from
        funext fun a => Response.diagonalWeakMaximum_subSkew hq rho t F a
          h0 hh0,
        show (fun a ↦ Response.diagonalWeakAdjointEnergy hq t
            (a.subSkew h0 hh0) p r) =
          fun a ↦ Response.diagonalWeakAdjointEnergy hq t a p
            (r + matVecMul h0 p)
          from funext fun a =>
            Response.diagonalWeakAdjointEnergy_subSkew hq t a h0 hh0 p r]
      refine le_trans (Response.profileGoodEnergyAt_diagonalWeakAdjointEnergy_le
        hq hFsym hFpd hlev p (r + matVecMul h0 p)) ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      ring
  · -- the centering variance
    refine mul_le_mul' le_rfl ?_
    exact profileAdjointCenterVariance_le_variance hm0 hq t (hintAll t) hEt
      h0 hh0 p r

end

end HCPolySupport.HighContrast.Quenched
