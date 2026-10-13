/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerSeam
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryComposeGlue

/-!
# CubeSchauderFold

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the reflected-window excess fold

`CubeSchauderBoundaryTwin.exists_gradientLipschitz_boundary` prices the harmonic
gradient's Lipschitz constant on the inner window by the excess of the competitor
on the **doubled** window `reflectedWindow x m (n-2)`.  The Campanato recursion
needs that excess folded back onto the *truncated* window, where the solution
lives.  This module performs the fold, at every met configuration and with no
analytic input beyond the competitor's own binders:

```text
  E(V, reflectedWindow x m (n-2)) ≤ C(d) · E(V, truncatedWindow x m (n-2)) .
```

## The four items of the fold, and where each comes from

* *the odd-affine projection* —
  `ExcessDecay.affineExcessRaw_reflectedWindow_le_odd_ae`: for a competitor
  fixed by the partial odd extension and an affine datum of the odd class
  `𝕃_odd`, the doubled excess costs at most `2^d` times the affine distance on
  `U₂`;
* *the even-function odd transfer* — the same atom's `2^d`, which is
  `ExcessDecay.normalizedL2On_oddExtend_le` ('s cellwise change of variables);
* *the near-side pricing at one met face* —'s `(★)`
  (`exists_oddClassDefect_le_affineExcessRaw`) and its lower twin;
* *the corner degeneracy* — 's `(★★)`
  (`exists_oddClassDefect_le_affineExcessRaw_corner_any`): at two met faces the
  odd class collapses to `{0}` and the collapse is *priced*, so no
  distance-to-boundary dichotomy is needed.

That is what lets a single boundary-route one step replace the interior chain
at *every* base point of `□_m`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The odd affine datum, priced at every met configuration -/

/-- **The odd-class datum selector.**

For a competitor odd about every met face at every point of the doubled window,
classically harmonic there, and an affine minimizer datum `(c,A)` on `U₂`, there
is an affine datum of the odd class `𝕃_odd` whose odd-class defect is priced by
the excess minimum on `U₂`.

Three regimes, three suppliers: no met face (the odd class is everything, the
minimizer itself works and the defect is `0`); exactly one met face ('s `(★)`
at either orientation); at least two met faces ('s `(★★)`, orientation-free
through 's transport). -/
theorem exists_oddAffineDatum_priced (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (V : Vec d → ℝ) (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      ∃ (cdat : ℝ) (Adat : Vec d), IsOddAffineData x m (n - 2) (cdat - 0) Adat ∧
        oddClassDefect x m n V cdat Adat
          ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := exists_oddClassDefect_le_affineExcessRaw_corner_any d
  obtain ⟨C2, hC20, hC2⟩ := exists_oddClassDefect_le_affineExcessRaw d
  obtain ⟨C3, hC30, hC3⟩ := exists_oddClassDefect_le_affineExcessRaw_lower d
  refine ⟨C1 + C2 + C3, by linarith only [hC10, hC20, hC30], ?_⟩
  intro m n x V c A hx hmn hupV hlowV hharm hVR hmin
  have hRmeas : MeasurableSet (reflectedWindow x m (n - 2)) :=
    (isOpen_reflectedWindow x m (n - 2)).measurableSet
  -- the piecewise globally odd representative
  obtain ⟨W, hWup, hWlow, hWeq⟩ :=
    exists_faceOdd_forall_eqOn_reflectedWindow (x := x) (m := m) (k := n - 2) hmn
      hupV hlowV (O := fun _ => (0 : ℝ)) (fun _ _ _ => neg_zero.symm)
      (fun _ _ _ => neg_zero.symm)
  have hWV : W =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] V :=
    ae_eq_restrict_of_eqOn hRmeas hWeq
  have hWVU : W =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] V :=
    ae_eq_restrict_of_eqOn (measurableSet_truncatedWindow x m (n - 2))
      (hWeq.mono (truncatedWindow_subset_reflectedWindow x m (n - 2)))
  have hWharm : HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) :=
    harmonicOnNhd_congr_eqOn (isOpen_reflectedWindow x m (n - 2)) hWeq hharm
  have hWR : MemLp W 2 (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.ae_eq hWV.symm
  have hWmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) W (c - vecDot A x) A :=
    (isAffineMinimizer_congr_ae hWVU (c - vecDot A x) A).mpr hmin
  have hexc : affineExcessRaw (truncatedWindow x m (n - 2)) W
      = affineExcessRaw (truncatedWindow x m (n - 2)) V :=
    affineExcessRaw_congr_ae hWVU
  by_cases hmet : ∃ i : Fin d, MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i
  · obtain ⟨i, hmeti⟩ := hmet
    by_cases hcorner : ∃ j : Fin d, j ≠ i ∧
        (MeetsUpperFace x m (n - 2) j ∨ MeetsLowerFace x m (n - 2) j)
    · obtain ⟨j, hji, hj⟩ := hcorner
      refine ⟨0, 0, by rw [sub_zero]; exact isOddAffineData_zero x m (n - 2), ?_⟩
      have hmain := hC1 m n x i j W c A hx hmn (Ne.symm hji) hmeti hj hWup hWlow
        hWharm hWR hWmin
      rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
      refine le_trans hmain (mul_le_mul_of_nonneg_right ?_ (affineExcessRaw_nonneg _ _))
      linarith only [hC20, hC30]
    · push Not at hcorner
      have hother : ∀ j, j ≠ i →
          ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j := hcorner
      rcases hmeti with hup | hlow
      · refine ⟨oddAffineIntercept x m i A, oddAffineSlope i A, ?_, ?_⟩
        · rw [sub_zero]
          exact isOddAffineData_oddAffineDatum hmn hup hother A
        · have hmain := hC2 m n x i W c A hx hmn hup hother
            (fun z => hWup i hup z) hWharm hWR hWmin
          rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
          refine le_trans hmain (mul_le_mul_of_nonneg_right ?_ (affineExcessRaw_nonneg _ _))
          linarith only [hC10, hC30]
      · refine ⟨oddAffineInterceptLower x m i A, oddAffineSlope i A, ?_, ?_⟩
        · rw [sub_zero]
          exact isOddAffineData_oddAffineDatumLower hmn hlow hother A
        · have hmain := hC3 m n x i W c A hx hmn hlow hother
            (fun z => hWlow i hlow z) hWharm hWR hWmin
          rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
          refine le_trans hmain (mul_le_mul_of_nonneg_right ?_ (affineExcessRaw_nonneg _ _))
          linarith only [hC10, hC20]
  · -- the unmet configuration: the odd class is the full affine class
    push Not at hmet
    have hnup : ∀ i : Fin d, ¬ MeetsUpperFace x m (n - 2) i := fun i h => (hmet i).1 h
    have hnlow : ∀ i : Fin d, ¬ MeetsLowerFace x m (n - 2) i := fun i h => (hmet i).2 h
    refine ⟨c, A, isOddAffineData_of_no_met_face _ _ hnup hnlow, ?_⟩
    rw [oddClassDefect_of_isAffineMinimizer hmin]
    have hCnn : (0 : ℝ) ≤ C1 + C2 + C3 := by linarith only [hC10, hC20, hC30]
    exact mul_nonneg hCnn (affineExcessRaw_nonneg _ _)

/-! ## 2. The fold -/

/-- **The reflected-window excess fold.**

For a competitor odd about every met face at every point of the doubled window,
classically harmonic there and square integrable there,

```text
  E(V, reflectedWindow x m (n-2)) ≤ C(d) · E(V, truncatedWindow x m (n-2)) .
```

No affine-minimizer hypothesis: the minimizer is produced internally by
`ExcessDecay.exists_isAffineMinimizer_shifted_truncatedWindow`.  The constant is
`2^d · (1 + C_price(d))` with `C_price(d)` the odd-class pricing constant of
`exists_oddAffineDatum_priced`; the normalizers cost nothing, because the doubled
window contains the truncated one. -/
theorem exists_affineExcess_reflectedWindow_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (V : Vec d → ℝ),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      affineExcess (reflectedWindow x m (n - 2)) V
        ≤ C * affineExcess (truncatedWindow x m (n - 2)) V := by
  classical
  obtain ⟨Cp, hCp0, hCp⟩ := exists_oddAffineDatum_priced d
  refine ⟨2 ^ d * (1 + Cp), by positivity, ?_⟩
  intro m n x V hx hmn hupV hlowV hharm hVR
  have hRmeas : MeasurableSet (reflectedWindow x m (n - 2)) :=
    (isOpen_reflectedWindow x m (n - 2)).measurableSet
  have hVU : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hVR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl)
  have hRpos : 0 < (volume (reflectedWindow x m (n - 2))).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  obtain ⟨c, A, hmin⟩ :=
    exists_isAffineMinimizer_shifted_truncatedWindow hx (by omega : n - 2 - 1 ≤ m) hVU
  obtain ⟨cdat, Adat, hodd, hprice⟩ :=
    hCp m n x V c A hx hmn hupV hlowV hharm hVR hmin
  -- the globally odd representative feeding the a.e. odd bridge
  obtain ⟨W, hWup, hWlow, hWeq⟩ :=
    exists_faceOdd_forall_eqOn_reflectedWindow (x := x) (m := m) (k := n - 2) hmn
      hupV hlowV (O := fun _ => (0 : ℝ)) (fun _ _ _ => neg_zero.symm)
      (fun _ _ _ => neg_zero.symm)
  have hWV : W =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] V :=
    ae_eq_restrict_of_eqOn hRmeas hWeq
  have hWR : MemLp W 2 (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.ae_eq hWV.symm
  have hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] fun y => W y + 0 := by
    filter_upwards [hWV] with y hy
    rw [hy]
    ring
  have hWodd : oddExtend x m (n - 2) W
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] W :=
    MeasureTheory.ae_restrict_of_ae (oddExtend_ae_eq_self_of_faceOdd_forall hmn hWup hWlow)
  have hbridge := affineExcessRaw_reflectedWindow_le_odd_ae (k := n - 2) hmn hVO hWodd
    hodd hRpos hUpos hWR
  -- the affine distance splits into the excess minimum and the defect
  have hdist : affineDistOn (truncatedWindow x m (n - 2)) V (cdat - vecDot Adat x) Adat
      = affineExcessRaw (truncatedWindow x m (n - 2)) V + oddClassDefect x m n V cdat Adat := by
    rw [oddClassDefect]
    ring
  rw [hdist] at hbridge
  set Eraw : ℝ := affineExcessRaw (truncatedWindow x m (n - 2)) V with hEraw
  have hErawnn : 0 ≤ Eraw := affineExcessRaw_nonneg _ _
  have hstep : affineExcessRaw (reflectedWindow x m (n - 2)) V ≤ 2 ^ d * ((1 + Cp) * Eraw) := by
    refine hbridge.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith only [hprice]
  -- the normalizer comparison: the doubled window is the larger one
  have hvolle : (volume (truncatedWindow x m (n - 2))).toReal
      ≤ (volume (reflectedWindow x m (n - 2))).toReal :=
    ENNReal.toReal_mono (volume_reflectedWindow_ne_top x m (n - 2))
      (volume_truncatedWindow_le_volume_reflectedWindow x m (n - 2))
  have hexp : -(d : ℝ)⁻¹ ≤ 0 := by
    have h : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    linarith only [h]
  have hnorm : ((volume (reflectedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹)
      ≤ ((volume (truncatedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hUpos hvolle hexp
  have hRawR : 0 ≤ affineExcessRaw (reflectedWindow x m (n - 2)) V :=
    affineExcessRaw_nonneg _ _
  have hUnn : (0 : ℝ) ≤ ((volume (truncatedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc affineExcess (reflectedWindow x m (n - 2)) V
      = ((volume (reflectedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹)
          * affineExcessRaw (reflectedWindow x m (n - 2)) V := rfl
    _ ≤ ((volume (truncatedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹)
          * (2 ^ d * ((1 + Cp) * Eraw)) :=
        mul_le_mul hnorm hstep hRawR hUnn
    _ = 2 ^ d * (1 + Cp)
          * (((volume (truncatedWindow x m (n - 2))).toReal) ^ (-(d : ℝ)⁻¹) * Eraw) := by
        ring
    _ = 2 ^ d * (1 + Cp) * affineExcess (truncatedWindow x m (n - 2)) V := rfl

end

end Algsuperdiff.Section4.Provider.Schauder
