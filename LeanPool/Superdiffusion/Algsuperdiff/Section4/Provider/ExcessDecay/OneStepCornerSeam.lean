/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerTransportFace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerSeamCore

/-!
# OneStepCornerSeam

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary gradient-Hölder producer at every met configuration

The single boundary producer of the §4.3 one-step chain: for a competitor odd
about every met face **of the doubled window**, classically harmonic there, the
gradient-Hölder seminorm on `U₃` is bounded by the interior display

```text
  [∇V]_{C^{0,1/2}(U₃)} ≤ C(d) (3^{-n})^{1/2} E(V, U₂)
```

with **no** boundary-datum leg, at *every* met configuration: one met face upper
or lower, and every corner/edge orientation.

## The three inputs it composes

* the orientation-free corner pricing `(★★)`
  (`OneStepCornerTransport.exists_oddClassDefect_le_affineExcessRaw_corner_any`)
  and the two one-met-face pricings `(★)`
  (`OneStepEvenBoundFinal`'s upper face,
  `OneStepCornerTransportFace`'s lower face);
* the a.e. seam of `OneStepCornerSeamCore`: the oddness binder here is the
  *pointwise-on-the-window* one, which is what a Weyl representative satisfies
  (its a.e. oddness upgrades by continuity), while `(★)`/`(★★)` want the global
  pointwise binder.  The piecewise representative `W = V` on the doubled window,
  `= 0` off it, is globally odd about every met face, and every quantity the
  pricing reads is an a.e. invariant, so the pricing transfers back to `V`;
* the almost-everywhere odd bridge
  `OneStepBoundaryOdd.exists_gradientHolder_boundary_odd_ae`, run at `O := W`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The fold arithmetic -/

private theorem fold_defect_bound {kappa Cd E Eraw D r : ℝ} (hkappa0 : 0 ≤ kappa)
    (hCd0 : 0 ≤ Cd) (hr0 : 0 < r) (hD : D ≤ Cd * Eraw) (hnorm : r * Eraw ≤ E) :
    kappa * E + kappa * (r * D) ≤ kappa * E + kappa * (Cd * E) := by
  have h1 : r * D ≤ r * (Cd * Eraw) := mul_le_mul_of_nonneg_left hD hr0.le
  have h2 : r * (Cd * Eraw) = Cd * (r * Eraw) := by ring
  have h3 : Cd * (r * Eraw) ≤ Cd * E := mul_le_mul_of_nonneg_left hnorm hCd0
  have h4 : r * D ≤ Cd * E := by linarith only [h1, h2, h3]
  have h5 : kappa * (r * D) ≤ kappa * (Cd * E) := mul_le_mul_of_nonneg_left h4 hkappa0
  linarith only [h5]

/-! ## 2. The producer -/

/-- **The boundary producer at every met configuration, from window-pointwise
oddness: one leg.**

The met set is arbitrary but nonempty; the oddness binders are read *on the
doubled window*, which is what the chain's Weyl representative satisfies.  The
odd-class defect has been folded into the excess leg by `(★)` / `(★★)`. -/
theorem exists_gradientHolder_boundary_metSet (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      (MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i) →
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
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ l, IntegrableOn (fun p => gradField V p l)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K
          (gradField V) ∧
        K ≤ C * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := exists_oddClassDefect_le_affineExcessRaw_corner_any d
  obtain ⟨C2, hC20, hC2⟩ := exists_oddClassDefect_le_affineExcessRaw d
  obtain ⟨C3, hC30, hC3⟩ := exists_oddClassDefect_le_affineExcessRaw_lower d
  refine ⟨(1 + (C1 + C2 + C3)) * boundaryOddSchauderConst d,
    mul_nonneg (by linarith only [hC10, hC20, hC30])
      (boundaryOddSchauderConst_nonneg d), ?_⟩
  intro m n x i V c A hx hmn hmet hupV hlowV hharm hVR hmin
  have hCd0 : (0 : ℝ) ≤ C1 + C2 + C3 := by linarith only [hC10, hC20, hC30]
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
  -- the odd affine datum and the priced defect, by the met configuration
  obtain ⟨cdat, Adat, hodd, hprice⟩ :
      ∃ (cdat : ℝ) (Adat : Vec d), IsOddAffineData x m (n - 2) (cdat - 0) Adat ∧
        oddClassDefect x m n V cdat Adat
          ≤ (C1 + C2 + C3) * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
    by_cases hcorner : ∃ j : Fin d, j ≠ i ∧
        (MeetsUpperFace x m (n - 2) j ∨ MeetsLowerFace x m (n - 2) j)
    · obtain ⟨j, hji, hj⟩ := hcorner
      refine ⟨0, 0, by rw [sub_zero]; exact isOddAffineData_zero x m (n - 2), ?_⟩
      have hmain := hC1 m n x i j W c A hx hmn (Ne.symm hji) hmet hj hWup hWlow
        hWharm hWR hWmin
      rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
      refine le_trans hmain (mul_le_mul_of_nonneg_right ?_
        (affineExcessRaw_nonneg _ _))
      linarith only [hC20, hC30]
    · push Not at hcorner
      have hother : ∀ j, j ≠ i →
          ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j := hcorner
      rcases hmet with hup | hlow
      · refine ⟨oddAffineIntercept x m i A, oddAffineSlope i A, ?_, ?_⟩
        · rw [sub_zero]
          exact isOddAffineData_oddAffineDatum hmn hup hother A
        · have hmain := hC2 m n x i W c A hx hmn hup hother
            (fun z => hWup i hup z) hWharm hWR hWmin
          rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
          refine le_trans hmain (mul_le_mul_of_nonneg_right ?_
            (affineExcessRaw_nonneg _ _))
          linarith only [hC10, hC30]
      · refine ⟨oddAffineInterceptLower x m i A, oddAffineSlope i A, ?_, ?_⟩
        · rw [sub_zero]
          exact isOddAffineData_oddAffineDatumLower hmn hlow hother A
        · have hmain := hC3 m n x i W c A hx hmn hlow hother
            (fun z => hWlow i hlow z) hWharm hWR hWmin
          rw [oddClassDefect_congr_ae hWVU, hexc] at hmain
          refine le_trans hmain (mul_le_mul_of_nonneg_right ?_
            (affineExcessRaw_nonneg _ _))
          linarith only [hC10, hC20]
  -- the almost-everywhere odd bridge at `O := W`
  have hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))]
      fun y => W y + 0 := by
    filter_upwards [hWV] with y hy
    rw [hy]
    ring
  have hWodd : oddExtend x m (n - 2) W
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] W :=
    MeasureTheory.ae_restrict_of_ae
      (oddExtend_ae_eq_self_of_faceOdd_forall hmn hWup hWlow)
  obtain ⟨K, hK, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_boundary_odd_ae hd hx hmn hVO hWodd hodd hharm hVR
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hbound ?_⟩
  have hkappa0 : (0 : ℝ) ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) :=
    mul_nonneg (boundaryOddSchauderConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) (-n)).le _)
  have hnormz : (3 : ℝ) ^ (-(n - 2))
        * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hfold := fold_defect_bound (kappa :=
      boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ))
    (E := affineExcess (truncatedWindow x m (n - 2)) V)
    (Eraw := affineExcessRaw (truncatedWindow x m (n - 2)) V)
    (D := oddClassDefect x m n V cdat Adat) hkappa0 hCd0
    (zpow_pos (by norm_num) (-(n - 2))) hprice hnormz
  have hrewrite : (1 + (C1 + C2 + C3)) * boundaryOddSchauderConst d
        * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) V
      = boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m (n - 2)) V
        + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * ((C1 + C2 + C3) * affineExcess (truncatedWindow x m (n - 2)) V) := by
    ring
  rw [hrewrite]
  exact hfold

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
