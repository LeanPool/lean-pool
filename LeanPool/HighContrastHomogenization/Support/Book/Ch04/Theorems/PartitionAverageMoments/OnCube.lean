/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.PartitionAverageMoments.CenteredAverage

/-!
# Coarse-graining support: Support.Book.Ch04.Theorems.PartitionAverageMoments.OnCube

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch04

/-!
# Restriction-carrier partition-average moment estimates: parent-cube and response averages
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem descendantCubeSet_eq_translate_origin
    {d : ℕ} {Q R : TriadicCube d} {n : ℤ}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift n R))
        (cubeSet (originCube d n)) := by
  have hscaleR : R.scale = n := by
    calc
      R.scale = Q.scale - Int.toNat (Q.scale - n) :=
        scale_eq_sub_of_mem_descendantsAtScale hnQ hR
      _ = n := by
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnQ)]
        ring
  have hscale_nonneg : 0 ≤ R.scale := by
    simpa [hscaleR] using hn
  calc
    cubeSet R =
        translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
          (cubeSet (originCube d R.scale)) :=
      cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
    _ = translateSet (intVecToRealVec (scaleTranslationShift n R))
          (cubeSet (originCube d n)) := by simp [hscaleR]

private theorem descendantObservableMomentTransfer
    {d : ℕ} {Q R : TriadicCube d} {n : ℤ}
    {P : RestrictionCoeffLaw d} {p : ℕ} {K : ℝ}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n)
    (hPstat : RestrictionStationaryLaw P)
    (Y : Set (Vec d) → RegCoeffField d → ℝ)
    (hY_cov : IsRestrictionTranslationCovariant Y)
    (hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P)
    (hYR_aemeas : AEMeasurable (Y (cubeSet R)) P)
    (hY0Lp_int : Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P)
    (hY0Lp :
      (∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K) :
    Integrable (fun a => |Y (cubeSet R) a| ^ p) P ∧
      (∫ a, |Y (cubeSet R) a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
  have hshift := descendantCubeSet_eq_translate_origin hn hnQ hR
  have hmap :
      Measure.map (Y (cubeSet R)) P =
        Measure.map (Y (cubeSet (originCube d n))) P := by
    rw [hshift]
    exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
      (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
      (scaleTranslationShift n R)
  refine ⟨integrable_abs_pow_of_map_eq_map_aemeasurable
    hYR_aemeas hY0_aemeas hmap hY0Lp_int, ?_⟩
  have hint :=
    integral_abs_pow_eq_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap (p := p)
  simpa [hint] using hY0Lp

private theorem integral_centeredOriginObservable_eq_zero_of_integrableMoment
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hp : 2 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    ∫ a, restrictionCenteredOriginObservable P n X a ∂P = 0 := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  have hY0_memLp : MemLp (Y (cubeSet (originCube d n))) (p : ENNReal) P := by
    rw [← integrable_norm_rpow_iff
      hY0_aemeas.aestronglyMeasurable (by exact_mod_cast hp_nat_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hY0Lp_int
  have hY0_memL1 : MemLp (Y (cubeSet (originCube d n))) (1 : ENNReal) P := by
    exact hY0_memLp.mono_exponent (by exact_mod_cast (show 1 ≤ p by omega))
  have hY0_int : Integrable (Y (cubeSet (originCube d n))) P := by
    rwa [memLp_one_iff_integrable] at hY0_memL1
  have hX0_int : Integrable (X (cubeSet (originCube d n))) P := by
    have hX0_eq :
        (fun a => X (cubeSet (originCube d n)) a) =
          fun a => Y (cubeSet (originCube d n)) a + μ0 := by
      funext a
      simp [Y, μ0]
    simpa [hX0_eq] using hY0_int.add (integrable_const μ0)
  have hY0_mean : ∫ a, Y (cubeSet (originCube d n)) a ∂P = 0 := by
    calc
      ∫ a, Y (cubeSet (originCube d n)) a ∂P =
          ∫ a, X (cubeSet (originCube d n)) a ∂P - ∫ _a, μ0 ∂P := by
              simpa [Y] using integral_sub hX0_int (integrable_const μ0)
      _ = μ0 - μ0 := by
            simp [μ0]
      _ = 0 := by
            ring
  simpa [Y, μ0, restrictionCenteredOriginObservable] using hY0_mean

private theorem integral_abs_scaledFiniteSum_pow_root_eq
    {d : ℕ} {P : RestrictionCoeffLaw d}
    {p : ℕ} {c : ℝ} (D : Finset (TriadicCube d))
    (Z : TriadicCube d → RegCoeffField d → ℝ)
    (hp_nat_ne_zero : p ≠ 0) (hc_nonneg : 0 ≤ c)
    (hZ_aemeas : ∀ R ∈ D, AEMeasurable (Z R) P)
    (hZ_int : ∀ R ∈ D, Integrable (fun a => |Z R a| ^ p) P) :
    (∫ a, |c * ∑ R ∈ D, Z R a| ^ p ∂P) ^ (1 / (p : ℝ)) =
      c * (∫ a, |∑ R ∈ D, Z R a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
  let S : RegCoeffField d → ℝ := fun a => ∑ R ∈ D, Z R a
  have hS_aemeas : AEMeasurable S P := by
    have hsum : AEMeasurable (∑ R ∈ D, Z R) P :=
      Finset.aemeasurable_sum _ (fun R hR => hZ_aemeas R hR)
    convert hsum using 1
    ext a
    simp [S]
  have hS_memLp : MemLp S (p : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro R hR
    refine (integrable_norm_rpow_iff
      (hZ_aemeas R hR).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hZ_int R hR
  have hS_int : Integrable (fun a => |S a| ^ p) P := by
    simpa [S, Real.norm_eq_abs] using hS_memLp.integrable_norm_pow hp_nat_ne_zero
  let Aavg : RegCoeffField d → ℝ := c • S
  have hAavg_aemeas : AEMeasurable Aavg P := hS_aemeas.const_smul c
  have hAavg_memLp : MemLp Aavg (p : ENNReal) P := hS_memLp.const_smul c
  have hAavg_int : Integrable (fun a => |Aavg a| ^ p) P := by
    simpa [Aavg, S, Real.norm_eq_abs] using hAavg_memLp.integrable_norm_pow hp_nat_ne_zero
  have hS_toReal :
      ENNReal.toReal (eLpNorm S (p : ENNReal) P) =
        (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      (show 1 ≤ p by omega) hS_aemeas hS_int
  have hAavg_toReal :
      ENNReal.toReal (eLpNorm Aavg (p : ENNReal) P) =
        (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      (show 1 ≤ p by omega) hAavg_aemeas hAavg_int
  have hscale :
      ENNReal.toReal (eLpNorm Aavg (p : ENNReal) P) =
        c * ENNReal.toReal (eLpNorm S (p : ENNReal) P) := by
    rw [show Aavg = c • S by rfl, eLpNorm_const_smul]
    rw [ENNReal.toReal_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  change (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) =
    c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ))
  rw [← hAavg_toReal, hscale, hS_toReal]

/-- Centered polynomial-moment fluctuation bound for restriction-centered
descendant averages over an arbitrary parent cube. -/
theorem integral_abs_centeredDescendantMean_pow_rpow_inv_le_of_unitRangeLaw
    {d : ℕ} {Q : TriadicCube d} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X (cubeSet R)))
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K) :
    (∫ a, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      ((descendantsAtScale Q n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleLpConst d n p *
            ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
          rosenthalDescendantsAtScaleSqrtConst d n p *
            Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  let N : ℝ := ((descendantsAtScale Q n).card : ℝ)
  let c : ℝ := N⁻¹
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  have hdesc_nonempty : (descendantsAtScale Q n).Nonempty := by
    exact descendantsAtScale_nonempty Q hnQ
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hdesc_nonempty.card_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  have hY0Lp :
      (∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp
  have hY0_mean : ∫ a, Y (cubeSet (originCube d n)) a ∂P = 0 := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using
      integral_centeredOriginObservable_eq_zero_of_integrableMoment X hX0_aemeas hp hX0Lp_int
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_local :
      ∀ R ∈ descendantsAtScale Q n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hX_local R hR).sub measurable_const
  have hZ_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (Z R) P := by
    intro R hR
    simpa [Z] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
  have hZ_int :
      ∀ R ∈ descendantsAtScale Q n,
        Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    have hshift := descendantCubeSet_eq_translate_origin hn hnQ hR
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap :
        Measure.map (Y (cubeSet R)) P =
          Measure.map (Y (cubeSet (originCube d n))) P := by
      calc
        Measure.map (Y (cubeSet R)) P =
            Measure.map
              (Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n)))) P := by
              rw [hshift]
        _ = Measure.map (Y (cubeSet (originCube d n))) P := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
                (scaleTranslationShift n R)
    have hYR_int :
        Integrable (fun a => |Y (cubeSet R) a| ^ p) P := by
      exact integrable_abs_pow_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap hY0Lp_int
    simpa [Z, Y] using hYR_int
  have hZ_mean :
      ∀ R ∈ descendantsAtScale Q n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hshift := descendantCubeSet_eq_translate_origin hn hnQ hR
    have hint :
        ∫ a, Y (cubeSet R) a ∂P =
          ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
      calc
        ∫ a, Y (cubeSet R) a ∂P =
            ∫ a,
              Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              rw [hshift]
        _ = ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
              exact
                integral_eq_of_isRestrictionTranslationCovariant_of_stationary_aestronglyMeasurable
                (P := P) hPstat (U := cubeSet (originCube d n))
                hY0_aemeas.aestronglyMeasurable hY_cov (scaleTranslationShift n R)
    simpa [Z, Y] using hint.trans hY0_mean
  have hZ_bound :
      ∀ R ∈ descendantsAtScale Q n,
        (∫ a, |Z R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
    intro R hR
    have hshift := descendantCubeSet_eq_translate_origin hn hnQ hR
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap :
        Measure.map (Y (cubeSet R)) P =
          Measure.map (Y (cubeSet (originCube d n))) P := by
      calc
        Measure.map (Y (cubeSet R)) P =
            Measure.map
              (Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n)))) P := by
              rw [hshift]
        _ = Measure.map (Y (cubeSet (originCube d n))) P := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
                (scaleTranslationShift n R)
    have hYR :
        (∫ a, |Y (cubeSet R) a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
      have hint :
          ∫ a, |Y (cubeSet R) a| ^ p ∂P =
            ∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P :=
        integral_abs_pow_eq_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap
      simpa [hint] using hY0Lp
    simpa [Z, Y] using hYR
  have hsum :=
    integral_abs_finiteSum_pow_rpow_inv_le_rosenthal_uniform_descendants
      (Q := Q) (k := n) (P := P)
      hPdep hp hK_nonneg Z hZ_local hZ_aemeas hZ_int hZ_mean hZ_bound
  let S : RegCoeffField d → ℝ :=
    fun a => ∑ R ∈ descendantsAtScale Q n, Z R a
  let Aavg : RegCoeffField d → ℝ := c • S
  have hMomentScale :
      (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) =
        c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    simpa only [Aavg, S, Pi.smul_apply, smul_eq_mul] using
      integral_abs_scaledFiniteSum_pow_root_eq
        (descendantsAtScale Q n) Z hp_nat_ne_zero hc_nonneg
        hZ_aemeas hZ_int
  have hAavg_eq : Aavg = restrictionCenteredDescendantAverageOnCube P Q n X := by
    funext a
    simp [Aavg, S, Z, restrictionCenteredDescendantAverageOnCube, μ0, c, N]
  calc
    (∫ a, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p ∂P) ^ (1 / (p : ℝ))
        = (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
            simp [hAavg_eq]
    _ = c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := hMomentScale
    _ ≤ c *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              exact mul_le_mul_of_nonneg_left (by simpa [S, N] using hsum) hc_nonneg
    _ = N⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              simp [c]
    _ = ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p *
              ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p *
              Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) := by
              simp [N]

/-- Completed-local version of
`integral_abs_centeredDescendantMean_pow_rpow_inv_le_of_unitRangeLaw`.

The raw observable is allowed to be only a.e.-equal, under the law, to local
representatives on the finitely many descendant cubes.  This is the honest
surface for totalized Ch4 observables such as coarse-block entries: stationarity
and moment transfer use the raw translation-covariant observable, while
unit-range independence is applied to the local representatives internally. -/
theorem integral_abs_centeredDescendantMean_pow_rpow_inv_le_of_of_unitRangeLaw
    {d : ℕ} {Q : TriadicCube d} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hP : RestrictionLawCarrier P)
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_localRep :
      ∀ R ∈ descendantsAtScale Q n,
        ∃ Y : RegCoeffField d → ℝ,
          IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet
            R) =ᵐ[P] Y)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K) :
    (∫ a, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      ((descendantsAtScale Q n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleLpConst d n p *
            ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
          rosenthalDescendantsAtScaleSqrtConst d n p *
            Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) := by
  classical
  have hp_nat_ne_zero : p ≠ 0 := by omega
  let D : Finset (TriadicCube d) := descendantsAtScale Q n
  let N : ℝ := (D.card : ℝ)
  let c : ℝ := N⁻¹
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  let Yrep : TriadicCube d → RegCoeffField d → ℝ :=
    fun R =>
      if hR : R ∈ D then Classical.choose (hX_localRep R (by simpa [D] using hR))
      else fun _a => 0
  let Zraw : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => Yrep R a - μ0
  have hdesc_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty Q hnQ
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hdesc_nonempty.card_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  have hY0Lp :
      (∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp
  have hY0_mean : ∫ a, Y (cubeSet (originCube d n)) a ∂P = 0 := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using
      integral_centeredOriginObservable_eq_zero_of_integrableMoment X hX0_aemeas hp hX0Lp_int
  have hYrep_local :
      ∀ R ∈ D, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Yrep R) := by
    intro R hR
    dsimp [Yrep]
    rw [dite_eq_left hR]
    exact (Classical.choose_spec (hX_localRep R (by simpa [D] using hR))).1
  have hX_eq_Yrep :
      ∀ R ∈ D, X (cubeSet R) =ᵐ[P] Yrep R := by
    intro R hR
    dsimp [Yrep]
    rw [dite_eq_left hR]
    exact (Classical.choose_spec (hX_localRep R (by simpa [D] using hR))).2
  have hZraw_eq_Z :
      ∀ R ∈ D, Zraw R =ᵐ[P] Z R := by
    intro R hR
    filter_upwards [hX_eq_Yrep R hR] with a ha
    simp [Zraw, Z, ha]
  have hZ_local :
      ∀ R ∈ D, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hYrep_local R hR).sub measurable_const
  have hZ_aemeas :
      ∀ R ∈ D, AEMeasurable (Z R) P := by
    intro R hR
    exact hP.aemeasurable_of_isLocalRandomVariable (hZ_local R hR)
  have hMomentTransfer :
      ∀ R ∈ D, Integrable (fun a => |Y (cubeSet R) a| ^ p) P ∧
        (∫ a, |Y (cubeSet R) a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
    intro R hR
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using!
        (hX_desc_aemeas R (by simpa [D] using hR)).sub measurable_const.aemeasurable
    exact descendantObservableMomentTransfer hn hnQ (by simpa [D] using hR)
      hPstat Y hY_cov hY0_aemeas hYR_aemeas hY0Lp_int hY0Lp
  have hZraw_int :
      ∀ R ∈ D, Integrable (fun a => |Zraw R a| ^ p) P := by
    intro R hR
    simpa [Zraw, Y] using (hMomentTransfer R hR).1
  have hZraw_mean :
      ∀ R ∈ D, ∫ a, Zraw R a ∂P = 0 := by
    intro R hR
    have hshift := descendantCubeSet_eq_translate_origin hn hnQ (by simpa [D] using hR)
    have hint :
        ∫ a, Y (cubeSet R) a ∂P =
          ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
      calc
        ∫ a, Y (cubeSet R) a ∂P =
            ∫ a,
              Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              rw [hshift]
        _ = ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
              exact
                integral_eq_of_isRestrictionTranslationCovariant_of_stationary_aestronglyMeasurable
                (P := P) hPstat (U := cubeSet (originCube d n))
                hY0_aemeas.aestronglyMeasurable hY_cov (scaleTranslationShift n R)
    simpa [Zraw, Y] using hint.trans hY0_mean
  have hZraw_bound :
      ∀ R ∈ D, (∫ a, |Zraw R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
    intro R hR
    simpa [Zraw, Y] using (hMomentTransfer R hR).2
  have hZ_int :
      ∀ R ∈ D, Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    refine (hZraw_int R hR).congr ?_
    filter_upwards [(hZraw_eq_Z R hR).symm] with a ha
    simp [ha]
  have hZ_mean :
      ∀ R ∈ D, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    calc
      ∫ a, Z R a ∂P = ∫ a, Zraw R a ∂P :=
        integral_congr_ae (hZraw_eq_Z R hR).symm
      _ = 0 := hZraw_mean R hR
  have hZ_bound :
      ∀ R ∈ D,
        (∫ a, |Z R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
    intro R hR
    have hint :
        ∫ a, |Z R a| ^ p ∂P = ∫ a, |Zraw R a| ^ p ∂P :=
      integral_congr_ae (by
        filter_upwards [(hZraw_eq_Z R hR).symm] with a ha
        simp [ha])
    simpa [hint] using hZraw_bound R hR
  have hsum :=
    integral_abs_finiteSum_pow_rpow_inv_le_rosenthal_uniform_descendants
      (Q := Q) (k := n) (P := P)
      hPdep hp hK_nonneg Z
      (by intro R hR; exact hZ_local R (by simpa [D] using hR))
      (by intro R hR; exact hZ_aemeas R (by simpa [D] using hR))
      (by intro R hR; exact hZ_int R (by simpa [D] using hR))
      (by intro R hR; exact hZ_mean R (by simpa [D] using hR))
      (by intro R hR; exact hZ_bound R (by simpa [D] using hR))
  let S : RegCoeffField d → ℝ := fun a => ∑ R ∈ D, Z R a
  let Sraw : RegCoeffField d → ℝ := fun a => ∑ R ∈ D, Zraw R a
  have hSraw_eq_S : Sraw =ᵐ[P] S := by
    have hAll : ∀ᵐ a ∂P, ∀ R ∈ D, Zraw R a = Z R a := by
      rw [Filter.eventually_all_finset]
      intro R hR
      exact hZraw_eq_Z R hR
    filter_upwards [hAll] with a hAll_a
    change (∑ R ∈ D, Zraw R a) = ∑ R ∈ D, Z R a
    exact Finset.sum_congr rfl fun R hR => by simp [hAll_a R hR]
  let Aavg : RegCoeffField d → ℝ := c • S
  have hMomentScale :
      (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) =
        c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    simpa only [Aavg, S, Pi.smul_apply, smul_eq_mul] using
      integral_abs_scaledFiniteSum_pow_root_eq
        (descendantsAtScale Q n) Z hp_nat_ne_zero hc_nonneg
        (by intro R hR; exact hZ_aemeas R (by simpa [D] using hR))
        (by intro R hR; exact hZ_int R (by simpa [D] using hR))
  have hCentered_eq_Aavg :
      restrictionCenteredDescendantAverageOnCube P Q n X =ᵐ[P] Aavg := by
    filter_upwards [hSraw_eq_S] with a hS_a
    calc
      restrictionCenteredDescendantAverageOnCube P Q n X a = c * Sraw a := by
        simp [restrictionCenteredDescendantAverageOnCube, Sraw, Zraw, μ0, c, N, D]
      _ = c * S a := by rw [hS_a]
      _ = Aavg a := by simp [Aavg]
  have hCentered_integral_eq :
      ∫ a, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p ∂P =
        ∫ a, |Aavg a| ^ p ∂P :=
    integral_congr_ae (by
      filter_upwards [hCentered_eq_Aavg] with a ha
      simp [ha])
  calc
    (∫ a, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p ∂P) ^ (1 / (p : ℝ))
        = (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
            rw [hCentered_integral_eq]
    _ = c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := hMomentScale
    _ ≤ c *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              exact mul_le_mul_of_nonneg_left (by simpa [S, D, N] using hsum) hc_nonneg
    _ = N⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              simp [c]
    _ = ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p *
              ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p *
              Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) := by
              simp [N, D]

end

end Ch04
end Book
end HCPolySupport
