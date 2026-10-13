/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerRamp

/-!
# OneStepOddClassCornerApp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Corner pricing: the three slab applications

The packaged single-face and corner-slab applications of the two-point Taylor
elimination, each combining: the window-hugging geometry, the Hessian value on
the Taylor box, the box-generic slab estimate, the volume-ratio transfers, and
the affine box-moment transfer back to the window.

* `corner_faceApp_le` — the single-face application at a met upper face: the
  even part of any affine competitor is priced by the residual on the window
  and the Hessian remainder on the doubled window.
* `corner_pairApp_le` — the corner application at the second face `j` against
  the competitor `evenᵢ(ℓ*)` (passed abstractly through its split identity):
  the doubly even part is priced by the residual, the normal-ramp size
  `|Aᵢ|·delta`, and the Hessian remainder of the shifted residual.

All constants are literal `C(d)` expressions; `t` is the free depth fraction
(`delta = t·3^{n−2}`, `t ≤ 1/16`), chosen in the assembly.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The single-face application.**  For a competitor odd at the met upper
`face` and an arbitrary affine `(c, A)`, the even part at `face` is priced on
the window by the residual and the doubled-window Hessian remainder. -/
theorem corner_faceApp_le {m n : ℤ} {x : Vec d} {face : Fin d} {V : Vec d → ℝ}
    {c : ℝ} {A : Vec d} {tt delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    (hup : MeetsUpperFace x m (n - 2) face)
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) face z) = -V z)
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (htt0 : 0 < tt) (htt16 : tt ≤ 1 / 16)
    (hdeltadef : delta = tt * (3 : ℝ) ^ (n - 2))
    {CH : ℝ} (hCH0 : 0 ≤ CH)
    (hCH : ∀ (W : Set (Vec d)) (F : Vec d → ℝ) (p : Vec d) (r : ℝ),
      volume W ≠ ⊤ → 0 < (volume W).toReal →
      HarmonicOnNhd (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' W) →
      IntegrableOn (fun y => F y ^ 2) W volume →
      0 < r → Metric.ball p r ⊆ W →
      ‖fderiv ℝ (fderiv ℝ (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)))
          (toEuc p)‖
        ≤ CH * r⁻¹ * r⁻¹ * Real.sqrt ((volume W).toReal / r ^ d)
            * normalizedL2On W F) :
    normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m face c A)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * (3 * (Real.sqrt ((1 / tt) ^ d)
              * normalizedL2On (truncatedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))
            + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
              * normalizedL2On (reflectedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))) := by
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hdelta0 : 0 < delta := by
    rw [hdeltadef]
    exact mul_pos htt0 hw0
  have hdelta16 : 16 * delta ≤ (3 : ℝ) ^ (n - 2) := by
    have h16 : 16 * tt ≤ 1 := by linarith only [htt16]
    calc 16 * delta = (16 * tt) * (3 : ℝ) ^ (n - 2) := by
          rw [hdeltadef]; ring
      _ ≤ 1 * (3 : ℝ) ^ (n - 2) := mul_le_mul_of_nonneg_right h16 hw0.le
      _ = (3 : ℝ) ^ (n - 2) := one_mul _
  have hUR := truncatedWindow_subset_reflectedWindow x m (n - 2)
  have hfR : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hfU : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    hfR.mono_measure (Measure.restrict_mono hUR le_rfl)
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hUvol : (volume (truncatedWindow x m (n - 2))).toReal
      ≤ ((3 : ℝ) ^ (n - 2)) ^ d :=
    (volume_toReal_truncatedWindow_bounds x hx (by omega)).2
  have hfharmR : HarmonicOnNhd
      ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) :=
    harmonicOnNhd_sub_vec_affine hharm (c - vecDot A x) A
  obtain ⟨M, hM0, hMB, hMd⟩ := exists_hessian_value hx (by omega : n - 2 < m)
    htt0 hdeltadef
    (Tbox := coordBox (cornerFaceTaylorLo x m (n - 2) face delta)
      (cornerFaceTaylorHi x m (n - 2) face delta))
    (fun z hz => metricBall_subset_reflectedWindow_of_mem_cornerFaceTaylor hx
      (by omega) hup hdelta16 hz) hfR hfharmR hCH0 hCH
  have hTiR := coordBox_cornerFaceTaylor_subset_reflectedWindow hx
    (by omega : n - 2 < m) hup hdelta16
  have hPiU := coordBox_cornerFaceSlab_subset_truncatedWindow hx
    (by omega : n - 2 < m) hup hdelta16
  have hDiU := coordBox_cornerFaceSlab_pushed_subset_truncatedWindow hx
    (by omega : n - 2 < m) hup hdelta0 hdelta16
  have hPi_vol : delta ^ d ≤ (volume (coordBox
      (cornerFaceSlabLo x m (n - 2) face delta)
      (cornerFaceSlabHi x m (n - 2) face))).toReal :=
    volume_toReal_coordBox_ge_of_edges hdelta0
      (cornerFaceSlab_edge_ge hx (by omega) hdelta16)
  have hDi_vol : delta ^ d ≤ (volume (coordBox
      (fun l => cornerFaceSlabLo x m (n - 2) face delta l
        - (delta • (basisVec face : Vec d)) l)
      (fun l => cornerFaceSlabHi x m (n - 2) face l
        - (delta • (basisVec face : Vec d)) l))).toReal := by
    refine volume_toReal_coordBox_ge_of_edges hdelta0 fun l => ?_
    have h := cornerFaceSlab_edge_ge hx (by omega : n - 2 < m)
      (i := face) hdelta16 l
    show delta ≤ (cornerFaceSlabHi x m (n - 2) face l
        - (delta • (basisVec face : Vec d)) l)
      - (cornerFaceSlabLo x m (n - 2) face delta l
        - (delta • (basisVec face : Vec d)) l)
    linarith only [h]
  have hδd0 : (0 : ℝ) < delta ^ d := by positivity
  have happ := normalizedL2On_evenAffinePart_slab_le (face := face)
    hVodd hdelta0 hM0 (lt_of_lt_of_le hδd0 hPi_vol)
    (fun z hz => hfharmR (toEuc z) ⟨z, hTiR hz, rfl⟩) hMB
    (coordBox_cornerFaceSlab_subset_taylor hdelta0)
    (fun y hy => reflection_cornerFaceSlab_mem_taylor hdelta0 hy)
    (fun y hy => pushed_cornerFaceSlab_mem_taylor hdelta0 hy)
    (fun y hy => cornerFaceSlab_depth hy)
    (hfU.mono_measure (Measure.restrict_mono hPiU le_rfl))
    (hfU.mono_measure (Measure.restrict_mono hDiU le_rfl))
  have htrP : normalizedL2On (coordBox (cornerFaceSlabLo x m (n - 2) face delta)
      (cornerFaceSlabHi x m (n - 2) face))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y) :=
    transfer_le hPiU hUpos (lt_of_lt_of_le hδd0 hPi_vol) hfU.integrable_sq
      (ratio_le_inv_t_pow ENNReal.toReal_nonneg hUvol hPi_vol hw0 htt0
        hdeltadef rfl)
  have htrD : normalizedL2On (coordBox
      (fun l => cornerFaceSlabLo x m (n - 2) face delta l
        - (delta • (basisVec face : Vec d)) l)
      (fun l => cornerFaceSlabHi x m (n - 2) face l
        - (delta • (basisVec face : Vec d)) l))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y) :=
    transfer_le hDiU hUpos (lt_of_lt_of_le hδd0 hDi_vol) hfU.integrable_sq
      (ratio_le_inv_t_pow ENNReal.toReal_nonneg hUvol hDi_vol hw0 htt0
        hdeltadef rfl)
  have hmom : normalizedL2On (truncatedWindow x m (n - 2))
      (evenAffinePart x m face c A)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * normalizedL2On (coordBox (cornerFaceSlabLo x m (n - 2) face delta)
              (cornerFaceSlabHi x m (n - 2) face))
              (evenAffinePart x m face c A) := by
    have hcases : ∀ l, evenAffineSlope face A l = 0 ∨
        (cornerFaceSlabLo x m (n - 2) face delta l = hugLo x m (n - 2) l ∧
          cornerFaceSlabHi x m (n - 2) face l = hugHi x m (n - 2) l) := by
      intro l
      by_cases hlf : l = face
      · refine Or.inl ?_
        rw [hlf]
        exact evenAffineSlope_apply_self face A
      · refine Or.inr ⟨?_, ?_⟩
        · rw [cornerFaceSlabLo]
          rw [ite_eq_right hlf]
        · rw [cornerFaceSlabHi]
          rw [ite_eq_right hlf]
    rw [evenAffinePart]
    exact moment_transfer_window_le hx (by omega : n - 2 < m)
      (cornerFaceSlabLo_lt_hi hx (by omega) hdelta0) hcases
  have hchain : normalizedL2On (coordBox (cornerFaceSlabLo x m (n - 2) face delta)
      (cornerFaceSlabHi x m (n - 2) face)) (evenAffinePart x m face c A)
      ≤ 3 * (Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y))
        + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)) := by
    linarith only [happ, htrP, htrD, hMd]
  calc normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m face c A)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * normalizedL2On (coordBox (cornerFaceSlabLo x m (n - 2) face delta)
              (cornerFaceSlabHi x m (n - 2) face))
              (evenAffinePart x m face c A) := hmom
    _ ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * (3 * (Real.sqrt ((1 / tt) ^ d)
              * normalizedL2On (truncatedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))
            + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
              * normalizedL2On (reflectedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))) :=
        mul_le_mul_of_nonneg_left hchain (Real.sqrt_nonneg _)

/-- **The corner application** at the face `j`, against the shifted competitor
`(c', A')` (in the assembly, the even part of the minimizer at `i`, so that
its even part at `j` is the doubly even part).  The residual of the shifted
competitor is split through `hsplit3` into the minimizer residual plus the
normal ramp, which is pointwise at most `|Aᵢ|·delta` on the corner slab. -/
theorem corner_pairApp_le {m n : ℤ} {x : Vec d} {i j : Fin d} {V : Vec d → ℝ}
    {c : ℝ} {A : Vec d} {c' : ℝ} {A' : Vec d} {tt delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) (hij : i ≠ j)
    (hupi : MeetsUpperFace x m (n - 2) i) (hupj : MeetsUpperFace x m (n - 2) j)
    (hVoddj : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z) = -V z)
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (htt0 : 0 < tt) (htt16 : tt ≤ 1 / 16)
    (hdeltadef : delta = tt * (3 : ℝ) ^ (n - 2))
    (hsplit3 : ∀ y, V y - affineEval (c' - vecDot A' x) A' y
      = (V y - affineEval (c - vecDot A x) A y) + oddAffinePart x m i A y)
    (hgi : evenAffineSlope j A' i = 0)
    {CH : ℝ} (hCH0 : 0 ≤ CH)
    (hCH : ∀ (W : Set (Vec d)) (F : Vec d → ℝ) (p : Vec d) (r : ℝ),
      volume W ≠ ⊤ → 0 < (volume W).toReal →
      HarmonicOnNhd (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' W) →
      IntegrableOn (fun y => F y ^ 2) W volume →
      0 < r → Metric.ball p r ⊆ W →
      ‖fderiv ℝ (fderiv ℝ (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)))
          (toEuc p)‖
        ≤ CH * r⁻¹ * r⁻¹ * Real.sqrt ((volume W).toReal / r ^ d)
            * normalizedL2On W F) :
    normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m j c' A')
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * (3 * (Real.sqrt ((1 / tt) ^ d)
              * normalizedL2On (truncatedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))
            + 3 * (|A i| * delta)
            + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
              * normalizedL2On (reflectedWindow x m (n - 2))
                  (fun y => V y - affineEval (c' - vecDot A' x) A' y))) := by
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hdelta0 : 0 < delta := by
    rw [hdeltadef]
    exact mul_pos htt0 hw0
  have hdelta16 : 16 * delta ≤ (3 : ℝ) ^ (n - 2) := by
    have h16 : 16 * tt ≤ 1 := by linarith only [htt16]
    calc 16 * delta = (16 * tt) * (3 : ℝ) ^ (n - 2) := by
          rw [hdeltadef]; ring
      _ ≤ 1 * (3 : ℝ) ^ (n - 2) := mul_le_mul_of_nonneg_right h16 hw0.le
      _ = (3 : ℝ) ^ (n - 2) := one_mul _
  have hUR := truncatedWindow_subset_reflectedWindow x m (n - 2)
  have hfR : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hfU : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    hfR.mono_measure (Measure.restrict_mono hUR le_rfl)
  have hf3R : MemLp (fun y => V y - affineEval (c' - vecDot A' x) A' y) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hf3U : MemLp (fun y => V y - affineEval (c' - vecDot A' x) A' y) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    hf3R.mono_measure (Measure.restrict_mono hUR le_rfl)
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hUvol : (volume (truncatedWindow x m (n - 2))).toReal
      ≤ ((3 : ℝ) ^ (n - 2)) ^ d :=
    (volume_toReal_truncatedWindow_bounds x hx (by omega)).2
  have hf3harmR : HarmonicOnNhd
      ((fun y => V y - affineEval (c' - vecDot A' x) A' y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) :=
    harmonicOnNhd_sub_vec_affine hharm (c' - vecDot A' x) A'
  obtain ⟨M, hM0, hMB, hMd⟩ := exists_hessian_value hx (by omega : n - 2 < m)
    htt0 hdeltadef
    (Tbox := coordBox (cornerPairTaylorLo x m (n - 2) i j delta)
      (cornerPairTaylorHi x m (n - 2) i j delta))
    (fun z hz => metricBall_subset_reflectedWindow_of_mem_cornerPairTaylor hx
      (by omega) hupi hupj hdelta16 hz) hf3R hf3harmR hCH0 hCH
  have hT3R := coordBox_cornerPairTaylor_subset_reflectedWindow hx
    (by omega : n - 2 < m) hupi hupj hdelta16
  have hQU := coordBox_cornerPairSlab_subset_truncatedWindow hx
    (by omega : n - 2 < m) hupi hupj hdelta16
  have hD3U := coordBox_cornerPairSlab_pushed_subset_truncatedWindow hx
    (by omega : n - 2 < m) hupi hupj hdelta0 hdelta16
  have hQ_vol : delta ^ d ≤ (volume (coordBox
      (cornerPairSlabLo x m (n - 2) i j delta)
      (cornerPairSlabHi x m (n - 2) i j))).toReal :=
    volume_toReal_coordBox_ge_of_edges hdelta0
      (cornerPairSlab_edge_ge hx (by omega) hdelta16)
  have hD3_vol : delta ^ d ≤ (volume (coordBox
      (fun l => cornerPairSlabLo x m (n - 2) i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m (n - 2) i j l
        - (delta • (basisVec j : Vec d)) l))).toReal := by
    refine volume_toReal_coordBox_ge_of_edges hdelta0 fun l => ?_
    have h := cornerPairSlab_edge_ge hx (by omega : n - 2 < m)
      (i := i) (j := j) hdelta16 l
    show delta ≤ (cornerPairSlabHi x m (n - 2) i j l
        - (delta • (basisVec j : Vec d)) l)
      - (cornerPairSlabLo x m (n - 2) i j delta l
        - (delta • (basisVec j : Vec d)) l)
    linarith only [h]
  have hδd0 : (0 : ℝ) < delta ^ d := by positivity
  have happ := normalizedL2On_evenAffinePart_slab_le (face := j)
    hVoddj hdelta0 hM0 (lt_of_lt_of_le hδd0 hQ_vol)
    (fun z hz => hf3harmR (toEuc z) ⟨z, hT3R hz, rfl⟩) hMB
    (coordBox_cornerPairSlab_subset_taylor hdelta0)
    (fun y hy => reflection_cornerPairSlab_mem_taylor hij hdelta0 hy)
    (fun y hy => pushed_cornerPairSlab_mem_taylor hij hdelta0 hy)
    (fun y hy => (cornerPairSlab_depth hy).2)
    (hf3U.mono_measure (Measure.restrict_mono hQU le_rfl))
    (hf3U.mono_measure (Measure.restrict_mono hD3U le_rfl))
  -- the split of the shifted residual on the two boxes
  have hoddQmem : MemLp (oddAffinePart x m i A) 2
      (volume.restrict (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
        (cornerPairSlabHi x m (n - 2) i j))) := by
    rw [oddAffinePart]
    exact memLp_affineEval_coordBox _ _ _ _
  have hoddD3mem : MemLp (oddAffinePart x m i A) 2
      (volume.restrict (coordBox
        (fun l => cornerPairSlabLo x m (n - 2) i j delta l
          - (delta • (basisVec j : Vec d)) l)
        (fun l => cornerPairSlabHi x m (n - 2) i j l
          - (delta • (basisVec j : Vec d)) l))) := by
    rw [oddAffinePart]
    exact memLp_affineEval_coordBox _ _ _ _
  have hsplitQ : normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
      (cornerPairSlabHi x m (n - 2) i j))
      (fun y => V y - affineEval (c' - vecDot A' x) A' y)
      ≤ normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
          (cornerPairSlabHi x m (n - 2) i j))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + |A i| * delta := by
    have hcongr : normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
        (cornerPairSlabHi x m (n - 2) i j))
        (fun y => V y - affineEval (c' - vecDot A' x) A' y)
        = normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
          (cornerPairSlabHi x m (n - 2) i j))
          (fun y => (V y - affineEval (c - vecDot A x) A y)
            + oddAffinePart x m i A y) := by
      congr 1
      funext y
      exact hsplit3 y
    rw [hcongr]
    have hadd := normalizedL2On_add_le
      (hfU.mono_measure (Measure.restrict_mono hQU le_rfl)) hoddQmem
    have hramp := normalizedL2On_oddRamp_cornerPairSlab_le (j := j) hdelta0
      (lt_of_lt_of_le hδd0 hQ_vol) (A := A)
    linarith only [hadd, hramp]
  have hsplitD3 : normalizedL2On (coordBox
      (fun l => cornerPairSlabLo x m (n - 2) i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m (n - 2) i j l
        - (delta • (basisVec j : Vec d)) l))
      (fun y => V y - affineEval (c' - vecDot A' x) A' y)
      ≤ normalizedL2On (coordBox
          (fun l => cornerPairSlabLo x m (n - 2) i j delta l
            - (delta • (basisVec j : Vec d)) l)
          (fun l => cornerPairSlabHi x m (n - 2) i j l
            - (delta • (basisVec j : Vec d)) l))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + |A i| * delta := by
    have hcongr : normalizedL2On (coordBox
        (fun l => cornerPairSlabLo x m (n - 2) i j delta l
          - (delta • (basisVec j : Vec d)) l)
        (fun l => cornerPairSlabHi x m (n - 2) i j l
          - (delta • (basisVec j : Vec d)) l))
        (fun y => V y - affineEval (c' - vecDot A' x) A' y)
        = normalizedL2On (coordBox
          (fun l => cornerPairSlabLo x m (n - 2) i j delta l
            - (delta • (basisVec j : Vec d)) l)
          (fun l => cornerPairSlabHi x m (n - 2) i j l
            - (delta • (basisVec j : Vec d)) l))
          (fun y => (V y - affineEval (c - vecDot A x) A y)
            + oddAffinePart x m i A y) := by
      congr 1
      funext y
      exact hsplit3 y
    rw [hcongr]
    have hadd := normalizedL2On_add_le
      (hfU.mono_measure (Measure.restrict_mono hD3U le_rfl)) hoddD3mem
    have hramp := normalizedL2On_oddRamp_cornerPairSlabPushed_le hij hdelta0
      (lt_of_lt_of_le hδd0 hD3_vol) (A := A)
    linarith only [hadd, hramp]
  have htrQ : normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
      (cornerPairSlabHi x m (n - 2) i j))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y) :=
    transfer_le hQU hUpos (lt_of_lt_of_le hδd0 hQ_vol) hfU.integrable_sq
      (ratio_le_inv_t_pow ENNReal.toReal_nonneg hUvol hQ_vol hw0 htt0
        hdeltadef rfl)
  have htrD3 : normalizedL2On (coordBox
      (fun l => cornerPairSlabLo x m (n - 2) i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m (n - 2) i j l
        - (delta • (basisVec j : Vec d)) l))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y) :=
    transfer_le hD3U hUpos (lt_of_lt_of_le hδd0 hD3_vol) hfU.integrable_sq
      (ratio_le_inv_t_pow ENNReal.toReal_nonneg hUvol hD3_vol hw0 htt0
        hdeltadef rfl)
  have hmom : normalizedL2On (truncatedWindow x m (n - 2))
      (evenAffinePart x m j c' A')
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
              (cornerPairSlabHi x m (n - 2) i j))
              (evenAffinePart x m j c' A') := by
    have hcases : ∀ l, evenAffineSlope j A' l = 0 ∨
        (cornerPairSlabLo x m (n - 2) i j delta l = hugLo x m (n - 2) l ∧
          cornerPairSlabHi x m (n - 2) i j l = hugHi x m (n - 2) l) := by
      intro l
      by_cases hli : l = i
      · refine Or.inl ?_
        rw [hli]
        exact hgi
      · by_cases hlj : l = j
        · refine Or.inl ?_
          rw [hlj]
          exact evenAffineSlope_apply_self j A'
        · refine Or.inr ⟨?_, ?_⟩
          · rw [cornerPairSlabLo]
            rw [ite_eq_right (fun h => h.elim hli hlj)]
          · rw [cornerPairSlabHi]
            rw [ite_eq_right (fun h => h.elim hli hlj)]
    rw [evenAffinePart]
    exact moment_transfer_window_le hx (by omega : n - 2 < m)
      (cornerPairSlabLo_lt_hi hx (by omega) hdelta0) hcases
  have hchain : normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
      (cornerPairSlabHi x m (n - 2) i j)) (evenAffinePart x m j c' A')
      ≤ 3 * (Real.sqrt ((1 / tt) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y))
        + 3 * (|A i| * delta)
        + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c' - vecDot A' x) A' y)) := by
    linarith only [happ, hsplitQ, hsplitD3, htrQ, htrD3, hMd]
  calc normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m j c' A')
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * normalizedL2On (coordBox (cornerPairSlabLo x m (n - 2) i j delta)
              (cornerPairSlabHi x m (n - 2) i j))
              (evenAffinePart x m j c' A') := hmom
    _ ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * (3 * (Real.sqrt ((1 / tt) ^ d)
              * normalizedL2On (truncatedWindow x m (n - 2))
                  (fun y => V y - affineEval (c - vecDot A x) A y))
            + 3 * (|A i| * delta)
            + 3 * (CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
              * normalizedL2On (reflectedWindow x m (n - 2))
                  (fun y => V y - affineEval (c' - vecDot A' x) A' y))) :=
        mul_le_mul_of_nonneg_left hchain (Real.sqrt_nonneg _)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
