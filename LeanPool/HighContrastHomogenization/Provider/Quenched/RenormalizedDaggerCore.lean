/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CombinedSourceGauge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizedRadiusGauge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RestoredSource
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicRebasedDagger
public import LeanPool.HighContrastHomogenization.Provider.Quenched.StoppingRadiusCellExcess

/-!
# High-contrast homogenization: Provider.Quenched.RenormalizedDaggerCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The renormalized coarse-ellipticity datum

This module combines the native source scale with the random renormalization
radius, splits physical cells into the recent window and the older scales, and
transports the resulting datum to the triadically rebased law.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory IndependentSums

noncomputable section

variable {d : Nat}

/-- Pull a source scale on the original samples to the rebased coefficient
law. -/
@[expose]
def rebasedPullbackSource (n : Nat) (S : CoeffSpace d -> Real) :
    CoeffSpace d -> Real := fun a => S (CoeffSpace.triadicContraction n a)

@[simp] theorem rebasedPullbackSource_triadicDilation (n : Nat)
    (S : CoeffSpace d -> Real) (a : CoeffSpace d) :
    rebasedPullbackSource n S (CoeffSpace.triadicDilation n a) = S a := by
  simp only [rebasedPullbackSource, CoeffSpace.triadicContraction_triadicDilation]

theorem measurable_rebasedPullbackSource (n : Nat) {S : CoeffSpace d -> Real}
    (hS : Measurable S) : Measurable (rebasedPullbackSource n S) :=
  hS.comp (CoeffSpace.measurable_triadicContraction n)

/-- The native source in the units of the rebased law. -/
@[expose]
def normalizedNativeSource (n : Nat) (S : CoeffSpace d -> Real) :
    CoeffSpace d -> Real := flooredSource (fun a => S a / (3 : Real) ^ n)

/-- The renormalization radius in the units of the rebased law. -/
@[expose]
def normalizedRadiusSource (S : CoeffSpace d -> Real) (Ahat : BlockMat d)
    (delta rho : Real) (h n : Nat) : CoeffSpace d -> Real :=
  flooredSource (fun a => renormRadius S Ahat delta rho h n a / (3 : Real) ^ n)

/-- The single source scale carrying both the native and renormalized
constraints. -/
@[expose]
def renormalizedCombinedSource (S : CoeffSpace d -> Real) (Ahat : BlockMat d)
    (delta rho : Real) (h n : Nat) : CoeffSpace d -> Real :=
  combinedSource (normalizedNativeSource n S)
    (normalizedRadiusSource S Ahat delta rho h n)

/-- The gauge paired with `renormalizedCombinedSource`. -/
@[expose]
def renormalizedCombinedGauge (d : Nat) (n b : Nat) (mu : Real)
    (Psi : Real -> Real) : Real -> Real :=
  combinedSourceGauge
    (flooredSourceGauge (triadicRebasedGauge n Psi))
    (flooredSourceGauge (renormalizedRadiusGauge d mu b))

/-- The growth witness paired with `renormalizedCombinedGauge`. -/
@[expose]
def renormalizedCombinedGrowthWitness (d : Nat) (b : Nat) (mu K : Real) : Real :=
  (max 2 (max K (renormalizedRadiusGrowthWitness d mu b))) ^ (2 : Nat)

private theorem source_le_physical_scale {S : CoeffSpace d -> Real}
    {Ahat : BlockMat d} {delta rho : Real} {h n : Nat} {a : CoeffSpace d}
    {m : Int}
    (hsrc : renormalizedCombinedSource S Ahat delta rho h n a <= (3 : Real) ^ m) :
    S a <= (3 : Real) ^ ((n : Int) + m) := by
  have hnative : normalizedNativeSource n S a <= (3 : Real) ^ m :=
    (max_le_iff.mp hsrc).1
  have hraw : S a / (3 : Real) ^ n <= (3 : Real) ^ m :=
    (max_le_iff.mp hnative).2
  have hnpos : 0 < (3 : Real) ^ n := by positivity
  have hmul := (div_le_iff₀ hnpos).mp hraw
  rw [zpow_add₀ (by norm_num : (3 : Real) ≠ 0), zpow_natCast]
  simpa only [mul_comm] using hmul

private theorem radius_le_physical_scale {S : CoeffSpace d -> Real}
    {Ahat : BlockMat d} {delta rho : Real} {h n : Nat} {a : CoeffSpace d}
    {m : Int}
    (hsrc : renormalizedCombinedSource S Ahat delta rho h n a <= (3 : Real) ^ m) :
    renormRadius S Ahat delta rho h n a <= (3 : Real) ^ ((n : Int) + m) := by
  have hradius : normalizedRadiusSource S Ahat delta rho h n a <= (3 : Real) ^ m :=
    (max_le_iff.mp hsrc).2
  have hraw : renormRadius S Ahat delta rho h n a / (3 : Real) ^ n <=
      (3 : Real) ^ m := (max_le_iff.mp hradius).2
  have hnpos : 0 < (3 : Real) ^ n := by positivity
  have hmul := (div_le_iff₀ hnpos).mp hraw
  rw [zpow_add₀ (by norm_num : (3 : Real) ≠ 0), zpow_natCast]
  simpa only [mul_comm] using hmul

private theorem zero_le_outer_generation {S : CoeffSpace d -> Real}
    {Ahat : BlockMat d} {delta rho : Real} {h n : Nat} {a : CoeffSpace d}
    {m : Int}
    (hsrc : renormalizedCombinedSource S Ahat delta rho h n a <= (3 : Real) ^ m) :
    0 <= m := by
  have hnative : normalizedNativeSource n S a <= (3 : Real) ^ m :=
    (max_le_iff.mp hsrc).1
  have hone : (1 : Real) <= (3 : Real) ^ m :=
    (le_max_left _ _).trans hnative
  exact (one_le_zpow_iff_right₀ (by norm_num : (1 : Real) < 3)).mp hone

private theorem recent_scalar_le {delta rho : Real} (hrho : 0 <= rho)
    {m k : Int} (hk : k <= m) :
    1 + delta * (3 : Real) ^ (rho * ((m : Real) - (k : Real))) <=
      (3 : Real) ^ (rho * ((m : Real) - (k : Real))) * (1 + delta) := by
  have hpow : 1 <= (3 : Real) ^ (rho * ((m : Real) - (k : Real))) := by
    have hmr : (k : Real) <= (m : Real) := by exact_mod_cast hk
    exact Real.one_le_rpow (by norm_num) (mul_nonneg hrho (by linarith only [hmr]))
  nlinarith only [hpow]

/-- The one-time renormalization of the coarse-ellipticity datum, already
transported to the rebased coefficient law. -/
theorem coarseEllipticityDagger_rebased_of_renormalization [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g rho mu delta Gain : Real} {E Ahat : BlockMat d}
    {Psi : Real -> Real} {K : Real} {S : CoeffSpace d -> Real}
    {n l0 h b : Nat}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hAhatSymm : IsSymmetricBlockMat Ahat) (hAhat : Book.Ch02.BlockPosDef Ahat)
    (hdelta : 0 <= delta) (hmu : mu = (d : Real) / 2 - g) (hmupos : 0 < mu)
    (hgr : g <= rho) (hrho : rho ∈ Set.Ico (0 : Real) 1)
    (hGain : 0 < Gain)
    (hl0 : 1 <= renormBase g ((d : Real) / 2) mu delta Gain l0 h)
    (hthr : Real.log 2 <= frGaugeConst d *
      renormBase g ((d : Real) / 2) mu delta Gain l0 h ^ 2 *
        ((3 : Real) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat g ((d : Real) / 2) Gain n l0 h)
    (hb1 : 1 <= b) (hh1 : 1 <= h)
    (hbuf : Real.log (2 * renormCellCount d h) <=
      frGaugeConst d * ((3 : Real) ^ (2 * mu * (b : Real)) - 1))
    (href : BlockMatLoewnerLE E (blockScale (2 * kappaRef E) Ahat))
    (hburn : 2 * kappaRef E <=
      (1 + delta) * (3 : Real) ^ ((rho - g) * (h : Real))) :
    HCPoly.Frozen.CoarseEllipticityDagger
      (triadicRebasedLaw n P) rho (blockScale (1 + delta) Ahat)
      (renormalizedCombinedGauge d n b mu Psi)
      (renormalizedCombinedGrowthWitness d b mu K)
      (rebasedPullbackSource n
        (renormalizedCombinedSource S Ahat delta rho h n)) := by
  have hgn : g <= (d : Real) / 2 := by rw [hmu] at hmupos; linarith only [hmupos]
  have hKrad : 1 < renormalizedRadiusGrowthWitness d mu b :=
    one_lt_renormalizedRadiusGrowthWitness d hmupos b
  have hPsiNative : AdmissiblePsi
      (flooredSourceGauge (triadicRebasedGauge n Psi)) :=
    admissiblePsi_flooredSourceGauge
      (admissiblePsi_triadicRebasedGauge n hdag.gauge_admissible)
  have hPsiRadius : AdmissiblePsi
      (flooredSourceGauge (renormalizedRadiusGauge d mu b)) :=
    admissiblePsi_flooredSourceGauge (admissiblePsi_renormalizedRadiusGauge d hmupos b)
  have htailNative : forall t : Real, 0 < t ->
      P.real (upperTailEvent (normalizedNativeSource n S) t) <=
        (flooredSourceGauge (triadicRebasedGauge n Psi) t)⁻¹ :=
    fun t ht => by
      by_cases ht1 : t < 1
      · rw [flooredSourceGauge, ite_eq_left ht1, inv_one]
        exact measureReal_le_one
      · have h1t : 1 <= t := le_of_not_gt ht1
        rw [flooredSourceGauge, ite_eq_right ht1]
        simpa only [normalizedNativeSource, flooredSource,
          triadicRebasedGauge] using!
          measureReal_restored_source_upperTail_le hdag n h1t
  have htailRadius : forall t : Real, 0 < t ->
      P.real (upperTailEvent (normalizedRadiusSource S Ahat delta rho h n) t) <=
        (flooredSourceGauge (renormalizedRadiusGauge d mu b) t)⁻¹ :=
    sourceTail_flooredSource fun t ht =>
      measureReal_normalized_renormRadius_gt_le hAhat hGain hdelta hmu hmupos
        hgn hgr hl0 hthr hcell hb1 hh1 hbuf t (zero_lt_one.trans_le ht)
  let T : CoeffSpace d -> Real := renormalizedCombinedSource S Ahat delta rho h n
  let PsiNew : Real -> Real := renormalizedCombinedGauge d n b mu Psi
  let KNew : Real := renormalizedCombinedGrowthWitness d b mu K
  have hTmeas : Measurable T := measurable_combinedSource
    (measurable_flooredSource (hdag.source_measurable.div_const _))
    (measurable_flooredSource ((measurable_renormRadius hdag.source_measurable
      hAhatSymm hAhat hdelta h n).div_const _))
  have hTtail : forall t : Real, 0 < t ->
      P.real (upperTailEvent T t) <= (PsiNew t)⁻¹ :=
    sourceTail_combinedSource hPsiNative hPsiRadius htailNative htailRadius
  have hfinite := ae_renormScale_ne_top hAhat hGain hdelta hmu hmupos hgn hgr
    hl0 hthr hcell
  refine
    { g_mem := hrho
      refBlock_isSymm := isSymmetricBlockMat_blockScale _ hAhatSymm
      refBlock_posDef := ?_
      gauge_admissible := admissiblePsi_combinedSourceGauge hPsiNative hPsiRadius
      one_lt_growthWitness := ?_
      gauge_growth := ?_
      source_measurable := measurable_rebasedPullbackSource n hTmeas
      source_nonneg := ?_
      source_tail := ?_
      coarse_bound := ?_ }
  · intro X hX
    rw [blockVecDot_blockMatVecMul_blockScale]
    have hcoef : 0 < 1 + delta := by linarith only [hdelta]
    exact mul_pos hcoef (hAhat X hX)
  · rw [renormalizedCombinedGrowthWitness]
    have hbase : 1 < max 2 (max K (renormalizedRadiusGrowthWitness d mu b)) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    nlinarith only [hbase, sq_nonneg (max 2 (max K (renormalizedRadiusGrowthWitness d mu b)))]
  · rw [renormalizedCombinedGauge, renormalizedCombinedGrowthWitness]
    exact hasPsiGrowth_combinedSourceGauge hPsiNative hPsiRadius
      hdag.one_lt_growthWitness hKrad
      (hasPsiGrowth_flooredSourceGauge hdag.one_lt_growthWitness
        (hasPsiGrowth_triadicRebasedGauge n hdag.gauge_admissible hdag.gauge_growth))
      (hasPsiGrowth_flooredSourceGauge hKrad
        (hasPsiGrowth_renormalizedRadiusGauge d hmupos b))
  · intro a
    change 0 <= T (CoeffSpace.triadicContraction n a)
    dsimp only [T]
    rw [renormalizedCombinedSource, combinedSource]
    exact zero_le_one.trans <| le_max_of_le_left <|
      one_le_flooredSource (fun x => S x / (3 : Real) ^ n) _
  · intro t ht
    rw [triadicRebasedLaw]
    have hevent : MeasurableSet (upperTailEvent (rebasedPullbackSource n T) t) :=
      (measurable_rebasedPullbackSource n hTmeas) measurableSet_Ioi
    rw [map_measureReal_apply (CoeffSpace.measurable_triadicDilation n) hevent]
    have heq : CoeffSpace.triadicDilation n ⁻¹'
        upperTailEvent (rebasedPullbackSource n T) t = upperTailEvent T t := by
      ext a
      simp only [Set.mem_preimage, upperTailEvent, Set.mem_ofPred_eq,
        rebasedPullbackSource_triadicDilation]
    rw [heq]
    exact hTtail t ht
  · rw [triadicRebasedLaw]
    exact ((CoeffSpace.triadicDilationMeasurableEquiv n).measurableEmbedding.ae_map_iff).2 <| by
      filter_upwards [hdag.coarse_bound, hfinite] with a hold hfin
      intro m hsrc k hk w hw
      have hsrcT : T a <= (3 : Real) ^ m := by
        change rebasedPullbackSource n T (CoeffSpace.triadicDilation n a) <=
          (3 : Real) ^ m at hsrc
        rw [rebasedPullbackSource_triadicDilation] at hsrc
        exact hsrc
      have hm0 : 0 <= m := zero_le_outer_generation hsrcT
      have hnm : (n : Int) <= (n : Int) + m := by omega
      have hsrcPhysical : S a <= (3 : Real) ^ ((n : Int) + m) :=
        source_le_physical_scale hsrcT
      have hradiusPhysical : renormRadius S Ahat delta rho h n a <=
          (3 : Real) ^ ((n : Int) + m) := radius_le_physical_scale hsrcT
      have hkPhysical : (n : Int) + k <= (n : Int) + m := by omega
      have hwPhysical : standardCellCenter ((n : Int) + k) w ∈
          centeredCube d ((n : Int) + m) :=
        standardCellCenter_add_mem_centeredCube_add n hw
      change BlockMatLoewnerLE
        (coarseBlock (standardCell d k w) (CoeffSpace.triadicDilation n a))
        (blockScale ((3 : Real) ^ (rho * ((m : Real) - (k : Real))))
          (blockScale (1 + delta) Ahat))
      rw [coarseBlock_standardCell_triadicDilation, blockScale_blockScale]
      by_cases hrecent : (n : Int) + m - (h : Int) + 1 <= (n : Int) + k
      · have hrow := blockMatLoewnerLE_of_renormRadius_le hfin hnm
          hradiusPhysical hsrcPhysical ((n : Int) + k) hrecent hkPhysical w hwPhysical
        have hscalar := recent_scalar_le (delta := delta) hrho.1 hk
        exact hrow.trans (blockMatLoewnerLE_blockScale_of_scalar_le
          (by simpa only [Int.cast_add, Nat.cast_ofNat, add_sub_add_left_eq_sub,
            mul_assoc] using hscalar) hAhat)
      · have holdRow := hold ((n : Int) + m) hsrcPhysical ((n : Int) + k)
          hkPhysical w hwPhysical
        have hcast :
            g * (((((n : Int) + m) : Int) : Real) -
              ((((n : Int) + k) : Int) : Real)) =
              g * ((m : Real) - (k : Real)) := by
          push_cast
          ring
        rw [hcast] at holdRow
        have hD : (h : Real) <= (m : Real) - (k : Real) := by
          have : k <= m - (h : Int) := by omega
          exact_mod_cast (show (h : Int) <= m - k by omega)
        have hgap : (3 : Real) ^ (g * ((m : Real) - (k : Real))) *
              (2 * kappaRef E) <=
            (3 : Real) ^ (rho * ((m : Real) - (k : Real))) * (1 + delta) := by
          have hpowGap : (3 : Real) ^ ((rho - g) * (h : Real)) <=
              (3 : Real) ^ ((rho - g) * ((m : Real) - (k : Real))) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (mul_le_mul_of_nonneg_left hD (by linarith only [hgr]))
          have hpownn : 0 <= (3 : Real) ^ (g * ((m : Real) - (k : Real))) :=
            Real.rpow_nonneg (by norm_num) _
          have hburn' := mul_le_mul_of_nonneg_left hburn hpownn
          have hpowid : (3 : Real) ^ (g * ((m : Real) - (k : Real))) *
                (3 : Real) ^ ((rho - g) * ((m : Real) - (k : Real))) =
              (3 : Real) ^ (rho * ((m : Real) - (k : Real))) := by
            rw [← Real.rpow_add (by norm_num : (0 : Real) < 3)]
            congr 1
            ring
          calc
            (3 : Real) ^ (g * ((m : Real) - (k : Real))) * (2 * kappaRef E)
                <= (3 : Real) ^ (g * ((m : Real) - (k : Real))) *
                  ((1 + delta) * (3 : Real) ^ ((rho - g) * (h : Real))) := hburn'
            _ <= (3 : Real) ^ (g * ((m : Real) - (k : Real))) *
                  ((1 + delta) *
                    (3 : Real) ^ ((rho - g) * ((m : Real) - (k : Real)))) := by
                gcongr
            _ = (3 : Real) ^ (rho * ((m : Real) - (k : Real))) *
                  (1 + delta) := by rw [← hpowid]; ring
        have hpowg : 0 <= (3 : Real) ^ (g * ((m : Real) - (k : Real))) :=
          Real.rpow_nonneg (by norm_num) _
        have hscaled := blockMatLoewnerLE_blockScale_of_le hpowg href
        rw [blockScale_blockScale] at hscaled
        exact holdRow.trans <| hscaled.trans
          (blockMatLoewnerLE_blockScale_of_scalar_le hgap hAhat)

end

end Quenched
end HighContrast
end HCPolySupport
