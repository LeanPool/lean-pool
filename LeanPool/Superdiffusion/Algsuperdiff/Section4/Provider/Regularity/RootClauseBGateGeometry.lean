/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccBoundaryLattice

/-!
# RootClauseBGateGeometry

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

/-! ## 1. The window's volume, at the gate -/

/-- **The window IS the translate at the gate**, so its volume is exactly `3^{dj}`.
`RootClauseBCloseArith.volume_toReal_truncatedWindow_inner_gen` with the
printed pair replaced by `(GATE j)`. -/
theorem volume_toReal_truncatedWindow_gate (d : ℕ) {m j : ℤ} {z : Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    (volume (truncatedWindow z m j)).toReal = ((3 : ℝ) ^ j) ^ d := by
  rw [truncatedWindow_eq_translateSet_of_gate hgate, ← image_add_eq_translateSet,
    volume_image_add, volume_toReal_openCubeSet_originCube]

/-! ## 2. The `K_g` slot of the chain, at the gate -/

/-- **The window-to-cube step at the gate.**

```text
  ν^{1/2}‖∇u‖_{L²((z+□_j) ∩ □_m)}  ≤  3^{(m-j)d/2} · ν^{1/2}‖∇u‖_{L²(□_m)} .
```

`RootClauseBCloseArith.stepSevenNuGradNorm_window_le_cube` at `(GATE j)`.  Not
an estimate on `u`: integral monotonicity on nested sets plus the exact volume
computation of §1. -/
theorem stepSevenNuGradNorm_window_le_cube_gate (d : ℕ) {m j : ℤ} {z : Vec d} {nu : ℝ}
    (hnu : 0 ≤ nu)
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) :
    stepSevenNuGradNorm nu (truncatedWindow z m j) u.grad ≤
      Real.sqrt (((3 : ℝ) ^ (m - j)) ^ d) *
        stepSevenNuGradNorm nu (openCubeSet (originCube d m)) u.grad := by
  have hmono := stepSevenGradMass_mono hnu u (truncatedWindow_subset_domain z m j)
    (Set.Subset.refl (openCubeSet (originCube d m)))
  have hvolS : (0 : ℝ) < (volume (truncatedWindow z m j)).toReal := by
    rw [volume_toReal_truncatedWindow_gate d hgate]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hvolT : (0 : ℝ) < (volume (openCubeSet (originCube d m))).toReal := by
    rw [volume_toReal_openCubeSet_originCube]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hratio : Real.sqrt ((volume (openCubeSet (originCube d m))).toReal /
      (volume (truncatedWindow z m j)).toReal) =
      Real.sqrt (((3 : ℝ) ^ (m - j)) ^ d) := by
    rw [volume_toReal_truncatedWindow_gate d hgate,
      volume_toReal_openCubeSet_originCube, volumeRatio_inner_gen d m j]
  have hmain := normalizedSqrt_le_volumeRatio_mul hvolS hvolT hmono
  rw [hratio] at hmain
  rw [stepSevenNuGradNorm_eq_sqrt_div, stepSevenNuGradNorm_eq_sqrt_div]
  exact hmain

/-! ## 5. The translated Besov datum, at the gate -/

/-- **The translated forcing's Besov seminorm against the printed Hölder datum,
at the gate.**

`RootPayloadDataB.besovTranslated_neg_le_holder` with `z ∈ □_{m-1}`, `j ≤ m-1`
replaced by `(GATE j)` alone — the scale comparison is not needed at all on
this route, since `z ∈ □_m` comes from the gate. -/
theorem besovTranslated_neg_le_holder_gate [NeZero d] {m j : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} {Khol : ℝ}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m))
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
  have hL2 := memLp_two_child_of_clause_iv hgate hgL2
  have hW := memLp_normalizedGagliardoMeasureOn_subset hgate
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero z (originCube d j)) hgW
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (z := z) (originCube d j) (s := stepSevenCgS) stepSevenCgS_pos hs1 hL2 hW
  have hwin : stepThreeWindow z m j =
      (fun y => z + y) '' openCubeSet (originCube d j) := by
    change truncatedWindow z m j = _
    rw [truncatedWindow_eq_translateSet_of_gate hgate, image_add_eq_translateSet]
  have hzm : z ∈ openCubeSet (originCube d m) := mem_openCubeSet_of_gate hgate
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

/-! ## 6. The `dataB` field at the free coarse scale, at the gate -/

/-- **`dataB` at the re-cut coarse cube, at the gate.**

`RootClauseBClosePayload.rootClauseB_dataB_free` with the printed interiority
replaced by `(GATE k_c)`; `k_c ≤ m` is kept as the pure scale comparison the
final `3^{k_c/2} ≤ 3^{m/2}` step needs. -/
theorem rootClauseB_dataB_gate [NeZero d] {m kc : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} {Khol : ℝ}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d kc) ⊆
      openCubeSet (originCube d m))
    (hkc : kc ≤ m) (hKhol : 0 ≤ Khol)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
        stepSevenCgS (fun y => -gsrc (y + z)) ≤
      rootClauseBDataBConst d * edFinalDataOscG Khol m := by
  have hmain := besovTranslated_neg_le_holder_gate (m := m) (j := kc) hgate hKhol
    hgHol hgL2 hgW
  refine le_trans hmain ?_
  rw [edFinalDataOscG]
  have hcast : (kc : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkc
  have hmono : Real.rpow (3 : ℝ) ((kc : ℝ) / 2) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hcast])
  have hstep : Real.rpow (3 : ℝ) ((kc : ℝ) / 2) * Khol ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_le_mul_of_nonneg_right hmono hKhol
  exact mul_le_mul_of_nonneg_left hstep (rootClauseBDataBConst_nonneg d)

/-! ## 7. The `dataM` field, at the gate -/

/-- **`dataM` at the gate.**

`RootPayloadDataM.rootClauseB_dataM` with the printed interiority replaced by
`(GATE n')`.  The remaining `n' ≤ m - 1` is the pure scale comparison of the
`σ`-reconciliation (`n' + 1 ≤ m ≤ m₀`) and of the exponent budget; no
geometry rides on it. -/
theorem rootClauseB_dataM_gate [NeZero d] {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {m n' : ℤ} {z : Vec d} {a : CoeffFamily d}
    {gsrc : Vec d → Vec d} {Khol CBc : ℝ} (hmm0 : m ≤ m0) (hn' : n' ≤ m - 1)
    (hgate : (fun y => z + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m))
    (hKhol : 0 ≤ Khol) (hCBc : 0 ≤ CBc)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (hcaps : StepSevenLambdaCaps (originCube d (n' + 1)) a
      ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc) :
    stepSevenCaccDataM (originCube d n') a (fun y => -gsrc (y + z)) ≤
      rootClauseBDataMConst d CBc *
        (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Khol m) := by
  have hFnn : (0 : ℝ) ≤ stepSevenCaccForcingFactor := stepSevenCaccForcingFactor_nonneg
  have hKnn : (0 : ℝ) ≤ 4 * stepSevenCaccForcingFactor * (64 / 7 * CBc) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hFnn)
      (by linarith only [hCBc] : (0 : ℝ) ≤ 64 / 7 * CBc)
  have hidx : (n' + 1 - 1 : ℤ) = n' := by ring
  have hlam : (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
      (64 / 7 * CBc) * ((Annealed.sigmaBar M (n' + 1) : ℝ))⁻¹ := by
    have h := stepSevenLambdaS_inv_le_of_caps (k := n' + 1) a hcaps
    rwa [hidx] at h
  set E : ℝ := M.gamma * ((m : ℝ) - ((n' + 1 : ℤ) : ℝ)) with hEdef
  have hsig : ((Annealed.sigmaBar M (n' + 1) : ℝ))⁻¹ ≤
      4 * Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_sigmaBar_le_mul_inv_sigmaBar_of_inductionState hS (by omega) hmm0
  have hlamF : stepSevenCaccForcingFactor *
        (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
      (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
    have h1 : (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
        (64 / 7 * CBc) *
          (4 * Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹) :=
      le_trans hlam
        (mul_le_mul_of_nonneg_left hsig (by linarith only [hCBc]))
    have h2 := mul_le_mul_of_nonneg_left h1 hFnn
    exact le_trans h2 (le_of_eq (by ring))
  have hA : Real.sqrt (stepSevenCaccForcingFactor *
        (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹) ≤
      Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) (E / 2) *
          Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
    have hRnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) E := Real.rpow_nonneg (by norm_num) E
    refine le_trans (Real.sqrt_le_sqrt hlamF) (le_of_eq ?_)
    rw [Real.sqrt_mul hKnn, Real.sqrt_mul hRnn, sqrt_rpow_three]
  have hBes : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n')
        stepOneS (fun y => -gsrc (y + z)) ≤
      rootClauseBDataBConst d * (Real.rpow (3 : ℝ) ((n' : ℝ) / 2) * Khol) :=
    besovTranslated_neg_le_holder_gate (m := m) (j := n') hgate hKhol hgHol hgL2 hgW
  have hforce : ForceBesovRegularity (originCube d n') stepOneS
      (fun x => -gsrc (x + z)) :=
    forceBesovRegularity_stepSevenCacc_gate hgate hgL2 hgW
  have hBesnn : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n') stepOneS (fun y => -gsrc (y + z)) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ stepOneS _
      hforce.partialSeminorms_bddAbove
  have hAnn : (0 : ℝ) ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
      (Real.rpow (3 : ℝ) (E / 2) *
        Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
  have hcast : ((n' + 1 : ℤ) : ℝ) = (n' : ℝ) + 1 := by push_cast; ring
  have hX : (0 : ℝ) ≤ (m : ℝ) - ((n' : ℝ) + 1) := by
    have h : ((n' + 1 : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : n' + 1 ≤ m)
    rw [hcast] at h
    linarith only [h]
  have hEle : E ≤ (m : ℝ) - (n' : ℝ) := by
    rw [hEdef, hcast]
    have hprod : M.gamma * ((m : ℝ) - ((n' : ℝ) + 1)) ≤
        (1 / 2 : ℝ) * ((m : ℝ) - ((n' : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (le_of_lt hgamma) hX
    linarith only [hprod, hX]
  have hexp : Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2) ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) := by
    have hadd : Real.rpow (3 : ℝ) (E / 2 + (n' : ℝ) / 2) =
        Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    rw [← hadd]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hEle])
  have hcoef : (0 : ℝ) ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
      rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (rootClauseBDataBConst_nonneg d))
      (Real.sqrt_nonneg _)
  have hstep : (Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2)) * Khol ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_le_mul_of_nonneg_right hexp hKhol
  rw [stepSevenCaccDataM, rootClauseBDataMConst, edFinalDataOscG]
  refine le_trans (mul_le_mul hA hBes hBesnn hAnn) ?_
  calc Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) (E / 2) * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) *
        (rootClauseBDataBConst d * (Real.rpow (3 : ℝ) ((n' : ℝ) / 2) * Khol))
      = Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
          ((Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2)) * Khol) := by
        ring
    _ ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
          (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol) :=
        mul_le_mul_of_nonneg_left hstep hcoef
    _ = Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d *
          (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by ring

end

end Algsuperdiff.Section4.Provider.Regularity
