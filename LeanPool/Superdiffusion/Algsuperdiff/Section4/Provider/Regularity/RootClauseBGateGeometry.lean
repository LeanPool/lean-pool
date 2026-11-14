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
  exact rootClauseB_dataM_of_besov_bound hS hgamma hmm0 hn' hKhol hCBc hcaps
    (besovTranslated_neg_le_holder_gate (m := m) (j := n') hgate hKhol hgHol hgL2 hgW)
    (forceBesovRegularity_stepSevenCacc_gate hgate hgL2 hgW)

end

end Algsuperdiff.Section4.Provider.Regularity
