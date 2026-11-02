/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueInterface
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapGeometry

/-!
# ResidueDatumFlush

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The datum step at the **flush pair** `(K, K')`

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`SealDatumStep.abs_volumeAverage_datum_sub_le_datumStep` compares the datum's
mean on the anchor's covering cube `V₁ = wellPlacedCentre x m (n+2) + □_{n+2}`
with its mean on a scale-`n` cube inside the boundary-flush cube
`K = wellPlacedCentre z m (n+2) + □_{n+2}`, in **three** two-scale transfers
(`V₁ → x+□_n → K → K'`), and needs the anchor's geometry binder to place the
intermediary `x + □_n` inside both scale-`(n+2)` cubes.

At the flush pair the intermediary is unnecessary: `K' ⊆ K` is the proved
`flushSubCube_subset_flushCube`, so **one** transfer suffices and the geometry
binder disappears.  The output constant is `datumStepConst d` unchanged (the
one-transfer bound is `datumStepConst d / 3` and is weakened to `datumStepConst
d` so the downstream arithmetic is the proved one).

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The datum step, at the flush pair.**

`|⨍_K h − ⨍_{K'} h| ≤ datumStepConst d · 3^n · Σᵢ‖∂ᵢh‖_{L²(W')}`, from the single
two-scale mean transfer `K' ⊆ K`, the equal-sides Poincaré on `K`, and the
binder-free window transport `K ⊆ W'`. -/
theorem abs_volumeAverage_datum_flushPair_le {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : H1Function (openCubeSet (originCube d m))) :
    |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) h.toFun -
        volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
          openCubeSet (originCube d n)) h.toFun| ≤
      datumStepConst d * (3 : ℝ) ^ n *
        ∑ i' : Fin d,
          (eLpNorm (fun y => h.grad y i') 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  classical
  have hTrans := abs_volumeAverage_sub_cubeAverage_le (k := n)
    (c := wellPlacedCentre z m (n + 2)) (c' := flushSubCentre z m n i σ)
    (flushSubCube_subset_flushCube z i hσ)
    (image_add_wellPlacedCentre_subset_openCubeSet z hnm) h
  have hPoin := normalizedL2On_sub_average_wellPlacedCube_le hnm z h
  have hWin := sum_toReal_eLpNorm_grad_cube_le_anchorWindow
    (image_add_wellPlacedCentre_z_subset_anchorWindow hnm hz) h
  rw [three_zpow_add_two n] at hPoin
  set T : ℝ := (3 : ℝ) ^ d with hT
  set uP : ℝ := unitMeanZeroPoincareConst d with huP
  set E3 : ℝ := (3 : ℝ) ^ n with hE3
  set HH : ℝ := ∑ i' : Fin d,
    (eLpNorm (fun y => h.grad y i') 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHH
  set P : ℝ := normalizedL2On ((fun y => wellPlacedCentre z m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)))
    (fun y => h.toFun y -
      volumeAverage ((fun y' => wellPlacedCentre z m (n + 2) + y') ''
        openCubeSet (originCube d (n + 2))) h.toFun) with hP
  set Q : ℝ := ∑ i' : Fin d,
    (eLpNorm (fun y => h.grad y i') 2
      (Support.normalizedVolumeMeasureOn
        ((fun y' => wellPlacedCentre z m (n + 2) + y') ''
          openCubeSet (originCube d (n + 2))))).toReal with hQ
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have huP0 : 0 ≤ uP := by rw [huP]; exact unitMeanZeroPoincareConst_nonneg d
  have hE30 : 0 ≤ E3 := by rw [hE3]; exact le_of_lt (zpow_pos (by norm_num) n)
  have hHH0 : 0 ≤ HH := by
    rw [hHH]; exact Finset.sum_nonneg fun i' _ => ENNReal.toReal_nonneg
  have hstep1 : P ≤ uP * (9 * E3) * (T * HH) :=
    hPoin.trans (mul_le_mul_of_nonneg_left hWin
      (mul_nonneg huP0 (by linarith only [hE30])))
  have hstep2 : T * P ≤ T * (uP * (9 * E3) * (T * HH)) :=
    mul_le_mul_of_nonneg_left hstep1 hT0
  have hdsc : datumStepConst d * E3 * HH = 27 * T * T * uP * E3 * HH := by
    rw [hT, huP, datumStepConst]
  have hslack : T * (uP * (9 * E3) * (T * HH)) ≤ 27 * T * T * uP * E3 * HH := by
    have hnn : 0 ≤ T * T * uP * E3 * HH := by
      have h1 : 0 ≤ T * T := mul_nonneg hT0 hT0
      have h2 : 0 ≤ T * T * uP := mul_nonneg h1 huP0
      have h3 : 0 ≤ T * T * uP * E3 := mul_nonneg h2 hE30
      exact mul_nonneg h3 hHH0
    have heq : T * (uP * (9 * E3) * (T * HH)) = 9 * (T * T * uP * E3 * HH) := by ring
    have heq2 : 27 * T * T * uP * E3 * HH = 27 * (T * T * uP * E3 * HH) := by ring
    rw [heq, heq2]
    linarith only [hnn]
  have habs : |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) h.toFun -
      volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) h.toFun| ≤ T * P := by
    rw [abs_sub_comm]
    exact hTrans
  rw [hdsc]
  linarith only [habs, hstep2, hslack]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
