/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BesovBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireCgMatching
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBArith

/-!
# RootPayloadDataB

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **The `dataB` constant** `K_d = C_bg(d)·C_{§4.4}(d,1/4)`: the Besov--Gagliardo
bridge constant times the Hölder--Gagliardo constant at the §4.4 exponent.  A
pure dimensional constant. -/
def rootClauseBDataBConst (d : ℕ) : ℝ :=
  besovGagliardoConstant d * stepFourGagliardoConst d stepSevenCgS

theorem rootClauseBDataBConst_nonneg (d : ℕ) : 0 ≤ rootClauseBDataBConst d :=
  mul_nonneg (besovGagliardoConstant_nonneg d) (stepFourGagliardoConst_nonneg d _)

/-- **The translated Besov datum at ANY interior scale.**

For every interior centre `z ∈ □_{m-1}` and every scale `j ≤ m-1`, the
translated forcing's `B^{1/4}_{2,∞}(□_j)` seminorm is dominated by the root's
own Hölder-`1/2` datum:

```text
  [ -𝐠(· + z) ]_{B^{1/4}_{2,∞}(□_j)}  ≤  K_d(d) · 3^{j/2} K_g .
```

This is the shared engine of the payload's `dataB` field (at `j = m-1`) and of
its `dataM` field (at `j = n'`). -/
theorem besovTranslated_neg_le_holder [NeZero d] {m j : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} {Khol : ℝ}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1)
    (hKhol : 0 ≤ Khol)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d j)
        stepSevenCgS (fun y => -gsrc (y + z)) ≤
      rootClauseBDataBConst d * (Real.rpow (3 : ℝ) ((j : ℝ) / 2) * Khol) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hs1 : stepSevenCgS ≤ 1 := by rw [stepSevenCgS_eq]; norm_num
  have hshalf : stepSevenCgS < 1 / 2 := by rw [stepSevenCgS_eq]; norm_num
  -- the two `MemLp` restrictions to the translated window
  have hsub : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_mem_inner hz hj
  have hL2 := memLp_two_child_of_clause_iv hsub hgL2
  have hW := memLp_normalizedGagliardoMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero z (originCube d j)) hgW
  -- step 1: the Besov--Gagliardo bridge in the translated frame
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (z := z) (originCube d j) (s := stepSevenCgS) stepSevenCgS_pos hs1 hL2 hW
  -- step 2: the translate IS the Step-3 window
  have hwin : stepThreeWindow z m j =
      (fun y => z + y) '' openCubeSet (originCube d j) := by
    change truncatedWindow z m j = _
    rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj, image_add_eq_translateSet]
  have hzm : z ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega) hz
  -- step 3: the Hoelder cap on that window
  have hgag := normalizedGagliardoESeminormOn_stepThreeWindow_le (z := z) (m := m)
    (j := j) (g := gsrc) (K := Khol) (s := stepSevenCgS) hd hzm
    stepSevenCgS_pos hshalf hKhol hgHol
  rw [hwin] at hgag
  have hnn : (0 : ℝ) ≤ Khol * stepFourGagliardoConst d stepSevenCgS *
      Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS)) :=
    mul_nonneg (mul_nonneg hKhol (stepFourGagliardoConst_nonneg d _))
      (Real.rpow_nonneg (by norm_num) _)
  have hG : (Support.normalizedGagliardoESeminormOn
        ((fun y => z + y) '' openCubeSet (originCube d j)) stepSevenCgS gsrc).toReal ≤
      Khol * stepFourGagliardoConst d stepSevenCgS *
        Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS)) :=
    ENNReal.toReal_le_of_le_ofReal hnn hgag
  -- the scale weight, evaluated
  have hzp : cubeScaleFactor (originCube d j) = Real.rpow (3 : ℝ) ((j : ℝ)) := by
    have hsc : ((3 : ℝ) ^ (j : ℤ)) = Real.rpow (3 : ℝ) ((j : ℝ)) :=
      (Real.rpow_intCast (3 : ℝ) j).symm
    rw [cubeScaleFactor]
    change ((3 : ℝ) ^ (j : ℤ)) = Real.rpow (3 : ℝ) ((j : ℝ))
    exact hsc
  have hweight : cubeBesovScaleWeight (-stepSevenCgS) (originCube d j) =
      Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) := by
    have hmul : Real.rpow (Real.rpow (3 : ℝ) ((j : ℝ))) stepSevenCgS =
        Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) ((j : ℝ)) stepSevenCgS).symm
    rw [cubeBesovScaleWeight, neg_neg, hzp]
    exact hmul
  -- the exponent cancellation
  have hsum : Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) *
      Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS)) =
      Real.rpow (3 : ℝ) ((j : ℝ) / 2) := by
    have hadd : Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS +
          (j : ℝ) * (1 / 2 - stepSevenCgS)) =
        Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) *
          Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS)) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    rw [← hadd]
    congr 1
    ring
  have hA : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
  have hWnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) :=
    Real.rpow_nonneg (by norm_num) _
  refine le_trans hbes ?_
  rw [hweight, rootClauseBDataBConst]
  calc besovGagliardoConstant d * Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => z + y) '' openCubeSet (originCube d j))
          stepSevenCgS gsrc).toReal
      ≤ besovGagliardoConstant d * Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) *
          (Khol * stepFourGagliardoConst d stepSevenCgS *
            Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS))) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hA hWnn)
    _ = besovGagliardoConstant d * stepFourGagliardoConst d stepSevenCgS * Khol *
          (Real.rpow (3 : ℝ) ((j : ℝ) * stepSevenCgS) *
            Real.rpow (3 : ℝ) ((j : ℝ) * (1 / 2 - stepSevenCgS))) := by ring
    _ = besovGagliardoConstant d * stepFourGagliardoConst d stepSevenCgS * Khol *
          Real.rpow (3 : ℝ) ((j : ℝ) / 2) := by rw [hsum]
    _ = besovGagliardoConstant d * stepFourGagliardoConst d stepSevenCgS *
          (Real.rpow (3 : ℝ) ((j : ℝ) / 2) * Khol) := by ring

end

end Algsuperdiff.Section4.Provider.Regularity
