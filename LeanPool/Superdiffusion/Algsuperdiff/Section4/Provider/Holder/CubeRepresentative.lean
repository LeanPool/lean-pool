/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylKernel
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.LatticeHolder

/-!
# CubeRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The continuous representative produced by the clipped-window family

A clipped-window oscillation family on the origin cube produces, through the
Campanato characterisation of Hölder spaces on a cube, a representative that is
continuous up to the boundary and carries an explicit `C^{0,beta}` seminorm
bound.  This file packages that passage in the form the localized estimates
consume: a witness of `IsCubeRepresentative` on the translated cube `y + □_m`
together with the seminorm bound.

Two adjustments are made along the way.

* The Campanato telescope is a statement about averages over balls of the
  ambient space, so it needs a globally locally integrable function; the family
  only controls the solution inside the cube.  Both are reconciled by running
  the telescope on the extension by zero, which agrees with the solution on the
  cube and is globally square integrable.  Every window of the family lies
  inside the cube, so the family itself is unchanged.
* The family lives at the origin and the estimate is read at the centre `y`, so
  the representative is recentred; the Hölder seminorm on a cube is invariant
  under that recentring.

## Main results

* `hasClipGridOscillationDecay_congr` — the family depends only on the values
  inside the ambient ball.
* `clipOffGridHolderConstant_le_uniform` — the chaining constant of the cube is
  bounded uniformly on `1/2 ≤ beta ≤ 1`.
* `exists_cubeRepresentative_of_grid` — the packaged representative.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Congruence of the oscillation family -/

private theorem volumeAverage_congr {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) :
    volumeAverage W f = volumeAverage W g := by
  unfold volumeAverage
  rw [setIntegral_congr_fun hW h]

private theorem normalizedL2On_congr {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) :
    normalizedL2On W f = normalizedL2On W g := by
  unfold normalizedL2On
  congr 1
  exact volumeAverage_congr hW fun x hx => by rw [h hx]

/-- The clipped-window oscillation decay depends only on the values inside the
ambient ball. -/
theorem hasClipGridOscillationDecay_congr {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)}
    {Rtop alpha K : ℝ} {j0 : ℕ} {f g : Vec d → ℝ}
    (h : Set.EqOn f g (Metric.ball c Rm))
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f) :
    HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 g := by
  intro j hj z hz
  have hW : MeasurableSet (clipBall c Rm z (triadicRadius Rtop j)) :=
    measurableSet_clipBall c Rm z _
  have hsub : clipBall c Rm z (triadicRadius Rtop j) ⊆ Metric.ball c Rm :=
    clipBall_subset_ambient c Rm z _
  have heq : Set.EqOn f g (clipBall c Rm z (triadicRadius Rtop j)) := h.mono hsub
  have havg : volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) f =
      volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) g :=
    volumeAverage_congr hW heq
  have hn := normalizedL2On_congr (f := fun w => f w -
      volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) f)
    (g := fun w => g w - volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) g)
    hW (fun x hx => by simp only [heq hx, havg])
  rw [← hn]
  exact hdec j hj z hz

/-! ## 2. A constant uniform over the upper half of the exponent range -/

/-- **The chaining constant of the cube, read uniformly on `1/2 ≤ alpha ≤ 1`.** -/
def uniformCubeHolderConstant (d : ℕ) : ℝ := 5832 * ballVolumePrice 6 d ^ 3

theorem uniformCubeHolderConstant_nonneg (d : ℕ) : 0 ≤ uniformCubeHolderConstant d := by
  have hP : (0 : ℝ) ≤ ballVolumePrice 6 d := ballVolumePrice_nonneg 6 d
  unfold uniformCubeHolderConstant
  have : (0 : ℝ) ≤ ballVolumePrice 6 d ^ 3 := pow_nonneg hP 3
  linarith only [this]

theorem clipOffGridHolderConstant_le_uniform (d : ℕ) {beta : ℝ}
    (h1 : (1 / 2 : ℝ) ≤ beta) (h2 : beta ≤ 1) :
    clipOffGridHolderConstant d beta 18 ≤ uniformCubeHolderConstant d := by
  have hP : (0 : ℝ) ≤ ballVolumePrice 6 d := ballVolumePrice_nonneg 6 d
  have hbpos : (0 : ℝ) < beta := by linarith only [h1]
  have h3 : (3 : ℝ) ^ beta ≤ 3 := by
    calc (3 : ℝ) ^ beta ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      _ = 3 := Real.rpow_one 3
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ beta := Real.rpow_nonneg (by norm_num) _
  have hT : campanatoTailConstant beta ≤ 3 := campanatoTailConstant_le_three h1
  have hTnn : (0 : ℝ) ≤ campanatoTailConstant beta := (campanatoTailConstant_pos hbpos).le
  have h18 : ((18 : ℕ) : ℝ) ^ (1 - beta) ≤ 18 := by
    have hcast : ((18 : ℕ) : ℝ) = (18 : ℝ) := by norm_num
    rw [hcast]
    calc (18 : ℝ) ^ (1 - beta) ≤ (18 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hbpos])
      _ = 18 := Real.rpow_one 18
  have hlocal : clipLocalHolderConstant d beta ≤ 36 * ballVolumePrice 6 d := by
    unfold clipLocalHolderConstant
    have e1 : 2 * (3 : ℝ) ^ beta ≤ 6 := by linarith only [h3]
    have e1n : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ beta := by linarith only [h3nn]
    have e2 : campanatoTailConstant beta + (3 : ℝ) ^ beta ≤ 6 := by linarith only [hT, h3]
    have e2n : (0 : ℝ) ≤ campanatoTailConstant beta + (3 : ℝ) ^ beta := by
      linarith only [hTnn, h3nn]
    have hprod : 2 * (3 : ℝ) ^ beta * (campanatoTailConstant beta + (3 : ℝ) ^ beta) ≤ 36 := by
      calc 2 * (3 : ℝ) ^ beta * (campanatoTailConstant beta + (3 : ℝ) ^ beta)
          ≤ 6 * 6 := mul_le_mul e1 e2 e2n (by norm_num)
        _ = 36 := by norm_num
    exact mul_le_mul_of_nonneg_right hprod hP
  have hstep : clipScaleStepConstant d beta ≤ 3 * ballVolumePrice 6 d := by
    unfold clipScaleStepConstant
    calc ballVolumePrice 6 d * (3 : ℝ) ^ beta ≤ ballVolumePrice 6 d * 3 :=
          mul_le_mul_of_nonneg_left h3 hP
      _ = 3 * ballVolumePrice 6 d := by ring
  have hstepnn : (0 : ℝ) ≤ clipScaleStepConstant d beta := clipScaleStepConstant_nonneg d beta
  have hlocaln : (0 : ℝ) ≤ clipLocalHolderConstant d beta :=
    clipLocalHolderConstant_nonneg d hbpos
  have hsq : clipScaleStepConstant d beta * clipScaleStepConstant d beta ≤
      9 * ballVolumePrice 6 d ^ 2 := by
    calc clipScaleStepConstant d beta * clipScaleStepConstant d beta
        ≤ (3 * ballVolumePrice 6 d) * (3 * ballVolumePrice 6 d) :=
          mul_le_mul hstep hstep hstepnn (by linarith only [hP])
      _ = 9 * ballVolumePrice 6 d ^ 2 := by ring
  have hsqnn : (0 : ℝ) ≤ clipScaleStepConstant d beta * clipScaleStepConstant d beta :=
    mul_nonneg hstepnn hstepnn
  have hinner : clipLocalHolderConstant d beta *
      (clipScaleStepConstant d beta * clipScaleStepConstant d beta) ≤
        324 * ballVolumePrice 6 d ^ 3 := by
    calc clipLocalHolderConstant d beta *
          (clipScaleStepConstant d beta * clipScaleStepConstant d beta)
        ≤ (36 * ballVolumePrice 6 d) * (9 * ballVolumePrice 6 d ^ 2) :=
          mul_le_mul hlocal hsq hsqnn (by linarith only [hP])
      _ = 324 * ballVolumePrice 6 d ^ 3 := by ring
  have hinnern : (0 : ℝ) ≤ clipLocalHolderConstant d beta *
      (clipScaleStepConstant d beta * clipScaleStepConstant d beta) :=
    mul_nonneg hlocaln hsqnn
  unfold clipOffGridHolderConstant uniformCubeHolderConstant
  calc ((18 : ℕ) : ℝ) ^ (1 - beta) *
        (clipLocalHolderConstant d beta *
          (clipScaleStepConstant d beta * clipScaleStepConstant d beta))
      ≤ 18 * (324 * ballVolumePrice 6 d ^ 3) :=
        mul_le_mul h18 hinner hinnern (by norm_num)
    _ = 5832 * ballVolumePrice 6 d ^ 3 := by ring

/-! ## 3. The continuous representative on `y + □_m` -/

/-- **From the clipped-window oscillation family at the origin to a continuous
representative on `y + □_m`.** -/
theorem exists_cubeRepresentative_of_grid [NeZero d] {y : Vec d} {m : ℤ} {beta K : ℝ}
    (hbeta : 0 < beta) (hK : 0 ≤ K) (u : H1Function (cubeSetAt y m))
    (hdec : HasClipGridOscillationDecay (0 : Vec d) ((3 : ℝ) ^ m / 2)
      (centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
      ((3 : ℝ) ^ m / 2) beta K 0 (originPullback y m u).toFun) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y m u uRep ∧
      holderSeminormOn (cubeSetAt y m) beta uRep ≤
        ENNReal.ofReal (clipOffGridHolderConstant d beta 18 * K) := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hRm : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by linarith only [h3]
  have hball : openCubeSet (originCube d m) = Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
    rw [← cubeSetAt_zero_eq m, cubeSetAt_eq_ball]
  have hU0meas : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isOpen.measurableSet
  set u0 : H1Function (openCubeSet (originCube d m)) := originPullback y m u with hu0
  set F : Vec d → ℝ := Set.indicator (openCubeSet (originCube d m)) u0.toFun with hFdef
  have hEq : Set.EqOn F u0.toFun (openCubeSet (originCube d m)) := fun x hx =>
    Set.indicator_of_mem hx _
  have hdecF : HasClipGridOscillationDecay (0 : Vec d) ((3 : ℝ) ^ m / 2)
      (centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
      ((3 : ℝ) ^ m / 2) beta K 0 F := by
    refine hasClipGridOscillationDecay_congr ?_ hdec
    rw [← hball]
    exact hEq.symm
  have hFmemGlobal : MemLp F 2 (volume : Measure (Vec d)) :=
    ExcessDecay.Schauder.memLp_indicator_h1 hU0meas u0
  have hfball : MemLp F 2 (volume.restrict (Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2))) :=
    hFmemGlobal.restrict _
  have hintF : LocallyIntegrable F (volume : Measure (Vec d)) :=
    ExcessDecay.Schauder.locallyIntegrable_indicator_h1 hU0meas u0
  have hGrid : ∀ j : ℕ,
      centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2) j ⊆
        Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) :=
    fun j => centredTriadicGrid_subset (0 : Vec d) _ _ j
  have happ : GridApproximatesOn
      (centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
      (Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2) 0 :=
    gridApproximatesOn_centredTriadicGrid hRm (0 : Vec d) _ 0
  have e1 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]; norm_num
  have e2 : (3 : ℝ) ^ (m - 2) = (3 : ℝ) ^ m / 9 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]; norm_num
  have htop : triadicRadius ((3 : ℝ) ^ m / 2) (0 + 1) = (3 : ℝ) ^ (m - 1) / 2 := by
    rw [triadicRadius_half_zpow]
    norm_num
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (m - 2) / 2 := by rw [e2]; linarith only [h3]
  have hRle : (3 : ℝ) ^ (m - 2) / 2 ≤ triadicRadius ((3 : ℝ) ^ m / 2) (0 + 1) := by
    rw [htop, e1, e2]; linarith only [h3]
  have hRle3 : 3 * ((3 : ℝ) ^ (m - 2) / 2) ≤ triadicRadius ((3 : ℝ) ^ m / 2) (0 + 1) := by
    rw [htop, e1, e2]; linarith only [h3]
  have hchain : 2 * ((3 : ℝ) ^ m / 2) ≤ ((18 : ℕ) : ℝ) * ((3 : ℝ) ^ (m - 2) / 2) := by
    rw [e2]; push_cast; linarith only [h3]
  have hbound := holderSeminormBoundOn_cubeSetAt_of_centredTriadicGrid
    (y := (0 : Vec d)) (m := m) (f := F) hbeta hK
    (by rw [cubeSetAt_zero_eq, hball]; exact hfball) hdecF
  have hae := campanatoRepresentative_ae_eq_of_grid (c := (0 : Vec d))
    (Rm := (3 : ℝ) ^ m / 2)
    (Grid := centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
    (Rtop := (3 : ℝ) ^ m / 2) (alpha := beta) (K := K)
    (R := (3 : ℝ) ^ (m - 2) / 2) (j0 := 0) (f := F)
    hRm le_rfl hbeta hK hRpos hRle hGrid hfball hintF hdecF happ
  have hcont := continuousOn_campanatoRepresentative_of_grid (c := (0 : Vec d))
    (Rm := (3 : ℝ) ^ m / 2)
    (Grid := centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
    (Rtop := (3 : ℝ) ^ m / 2) (alpha := beta) (K := K)
    (R := (3 : ℝ) ^ (m - 2) / 2) (j0 := 0) (N := 18) (f := F)
    hRm le_rfl hbeta hK hRpos hRle3 (by norm_num) hchain hGrid hfball hdecF happ
  refine ⟨fun x => campanatoRepresentative F ((3 : ℝ) ^ (m - 2) / 2) (x - y), ?_, ?_⟩
  · constructor
    · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_cubeSetAt y m)]
      have hshift := (measurePreserving_sub_right (volume : Measure (Vec d))
        y).quasiMeasurePreserving.ae hae
      filter_upwards [hshift] with x hx hmem
      have hxm : x - y ∈ Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
        rw [← hball]
        exact mem_cubeSetAt_iff.1 hmem
      have hFx : F (x - y) = u0.toFun (x - y) := hEq (by rw [hball]; exact hxm)
      rw [hx hxm, hFx, hu0, originPullback_toFun]
      congr 1
      abel
    · have hmaps : Set.MapsTo (fun x : Vec d => x - y) (cubeSetAt y m)
          (Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2)) := by
        intro x hx
        rw [← hball]
        exact mem_cubeSetAt_iff.1 hx
      have hsub : ContinuousOn (fun x : Vec d => x - y) (cubeSetAt y m) := by fun_prop
      exact hcont.comp hsub hmaps
  · have hseq : holderSeminormOn (cubeSetAt y m) beta
        (fun x => campanatoRepresentative F ((3 : ℝ) ^ (m - 2) / 2) (x - y)) =
      holderSeminormOn (cubeSetAt (0 : Vec d) m) beta
        (campanatoRepresentative F ((3 : ℝ) ^ (m - 2) / 2)) := by
      rw [holderSeminormOn_cubeSetAt_eq, cubeSetAt_zero_eq]
      congr 1
      funext x
      congr 1
      abel
    rw [hseq]
    exact (holderSeminormOn_le_ofReal_iff
      (mul_nonneg (clipOffGridHolderConstant_nonneg d hbeta 18) hK)).2 hbound

end

end Algsuperdiff.Section4.Provider.Holder
