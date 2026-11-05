/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderWindow

/-!
# OneStepSchauderProducer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Schauder gradient-Hölder estimate, interior branch: the producer

This module produces, for a competitor `v` harmonic on the replacement window
`(x + □_{n-2}) ∩ □_m` of the interior branch, **exactly** the four-hypothesis
package that `OneStepConditional.excessDecay_oneStep_of_harmonicApprox` consumes
in its `hint / hgrad / hhol / hschauder` slots:

```text
  Gv := gradField v ,
  ∀ i, IntegrableOn (fun p => Gv p i) ((x + □_{n-3}) ∩ □_m) ,
  HasGradientOn ((x + □_{n-3}) ∩ □_m) v Gv ,
  HolderSeminormBoundOn ((x + □_{n-3}) ∩ □_m) (1/2) K Gv ,
  K ≤ Csch(d) · (3^{-n})^{1/2} · E(v, (x + □_{n-2}) ∩ □_m)  +  0 ,
```

with

```text
  Csch(d) = schauderWindowConst d
          = 48 · 3^{3/2} · schauderConst d · √((12(d+1))^d) ,
  schauderConst d = d · C_native(d) ,
```

`C_native(d)` the constant of the transplanted native interior Hessian estimate
`interiorSecondDerivEstimateL2_ball`.  The boundary-datum contribution is
`K_h = 0`: on the interior branch the replacement window is a full translated
cube and no face of `∂□_m` is met.

## What the harmonicity hypothesis is

`hharm : HarmonicOnNhd (v ∘ toEuc.symm) (toEuc '' ((x + □_{n-2}) ∩ □_m))` — the
**classical** predicate.  For the competitor produced by
`ResidualCorrectorExistence.exists_weaklyHarmonicOn_of_datum` (which satisfies
the *variational* `Support.IsWeaklyHarmonicOn`), the Weyl bridge of
`OneStepSchauderWeyl` supplies this for every CoarseGraining convex smoothing
of the competitor, at the full radius.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec basisVec euclideanBall openCubeSet originCube)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- **The Schauder constant of the interior branch.**  `C(d)` explicit:
`48 · 3^{3/2} · schauderConst d · √((12(d+1))^d)`. -/
def schauderWindowConst (d : ℕ) [NeZero d] : ℝ :=
  48 * (3 : ℝ) ^ (3 / 2 : ℝ) * schauderConst d * schauderRatioConst d

theorem schauderWindowConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ schauderWindowConst d :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    (schauderConst_nonneg d)) (schauderRatioConst_nonneg d)

/-! ## 2. The scale arithmetic -/

theorem sqrt_zpow_div_self (n : ℤ) :
    Real.sqrt ((3 : ℝ) ^ (n - 3)) / (3 : ℝ) ^ (n - 3)
      = (3 : ℝ) ^ (3 / 2 : ℝ) * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcast : ((3 : ℝ) ^ (n - 3)) = (3 : ℝ) ^ (((n : ℝ) - 3)) := by
    rw [show ((n : ℝ) - 3) = (((n - 3 : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast]
  have hcastn : ((3 : ℝ) ^ (-n)) = (3 : ℝ) ^ ((-(n : ℝ))) := by
    rw [show (-(n : ℝ)) = (((-n : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast]
  rw [Real.sqrt_eq_rpow, hcast, hcastn, ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le,
    ← Real.rpow_sub h3, ← Real.rpow_add h3]
  congr 1
  ring

/-! ## 3. Differentiability and integrability of the gradient field -/

/-- **The gradient field realizes `HasGradientOn`.** -/
theorem hasGradientOn_gradField {v : Vec d → ℝ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {W : Set (Vec d)} (hharm : HarmonicOnNhd (v ∘ toEuc.symm) S)
    (hWS : ∀ p ∈ W, toEuc p ∈ S) : HasGradientOn W v (gradField v) := by
  intro y hy
  have hdiff : DifferentiableAt ℝ v y := differentiableAt_of_harmonic_avatar hharm (hWS y hy)
  have hfd : HasFDerivAt v (fderiv ℝ v y) y := hdiff.hasFDerivAt
  rw [← slopeCLM_gradField v y] at hfd
  exact hfd.hasFDerivWithinAt

/-- The coordinates of the gradient field are continuous on a window of
harmonicity. -/
theorem continuousOn_gradField_coord {v : Vec d → ℝ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {W : Set (Vec d)} (hharm : HarmonicOnNhd (v ∘ toEuc.symm) S)
    (hWS : ∀ p ∈ W, toEuc p ∈ S) (i : Fin d) :
    ContinuousOn (fun p => gradField v p i) W := by
  intro p hp
  have hc2 : ContDiffAt ℝ 2 v p := by
    have hg : ContDiffAt ℝ 2 (v ∘ toEuc.symm) (toEuc p) := (hharm (toEuc p) (hWS p hp)).1
    have hcomp : ContDiffAt ℝ 2 ((v ∘ toEuc.symm) ∘ toEuc) p :=
      hg.comp p (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).contDiff.contDiffAt
    rwa [comp_toEuc_symm_toEuc] at hcomp
  have hc1 : ContDiffAt ℝ 1 (fderiv ℝ v) p := by
    have h := hc2.fderiv_right (m := 1) (by norm_num)
    simpa using h
  have hcont : ContinuousAt (fun q => (fderiv ℝ v q) (basisVec i)) p :=
    ((ContinuousLinearMap.apply ℝ ℝ (basisVec (d := d) i)).continuous.continuousAt).comp
      hc1.continuousAt
  exact hcont.continuousWithinAt

/-- The gradient field is integrable coordinatewise on a bounded window on which
it satisfies a Hölder bound. -/
theorem integrableOn_gradField_coord {v : Vec d → ℝ} {W : Set (Vec d)} {K D : ℝ}
    (hWmeas : MeasurableSet W) (hWfin : volume W ≠ ⊤) (hK : 0 ≤ K)
    (hcont : ∀ i, ContinuousOn (fun p => gradField v p i) W)
    (hhol : HolderSeminormBoundOn W (1 / 2 : ℝ) K (gradField v))
    (hdiam : ∀ p ∈ W, ∀ q ∈ W, ‖p - q‖ ≤ D) {p₀ : Vec d} (hp₀ : p₀ ∈ W) (i : Fin d) :
    IntegrableOn (fun p => gradField v p i) W volume := by
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hWfin⟩
  have hD : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) (hdiam p₀ hp₀ p₀ hp₀)
  set C : ℝ := ‖gradField v p₀‖ + K * D ^ (1 / 2 : ℝ) with hCdef
  have hbound : ∀ p ∈ W, ‖gradField v p i‖ ≤ C := by
    intro p hp
    have hcoord : ‖gradField v p i‖ ≤ ‖gradField v p‖ := norm_le_pi_norm _ i
    have hdiff : ‖gradField v p - gradField v p₀‖ ≤ K * ‖p - p₀‖ ^ (1 / 2 : ℝ) :=
      hhol p hp p₀ hp₀
    have hrp : ‖p - p₀‖ ^ (1 / 2 : ℝ) ≤ D ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) (hdiam p hp p₀ hp₀) (by norm_num)
    have hsplit : ‖gradField v p‖ ≤ ‖gradField v p - gradField v p₀‖ + ‖gradField v p₀‖ := by
      have := norm_add_le (gradField v p - gradField v p₀) (gradField v p₀)
      simpa using this
    have hmul : K * ‖p - p₀‖ ^ (1 / 2 : ℝ) ≤ K * D ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hrp hK
    rw [hCdef]
    linarith only [hcoord, hsplit, hdiff, hmul]
  refine MeasureTheory.Integrable.mono' (g := fun _ : Vec d => C) (integrable_const C)
    ((hcont i).aestronglyMeasurable hWmeas) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hWmeas] with p hp
  exact hbound p hp

/-! ## 4. The producer -/

/-- **The Schauder gradient-Hölder estimate, interior branch — the producer.**

For `v` harmonic on the replacement window `(x + □_{n-2}) ∩ □_m` of the interior
branch (`x + □_{n-2} ⊆ □_m`), the gradient field `gradField v` realizes the four
slots `hint / hgrad / hhol / hschauder` of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`, with

```text
  Csch = schauderWindowConst d ,   K_h = 0 .
```
-/
theorem exists_gradientHolder_interior [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 3 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {v : Vec d → ℝ}
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (v y - affineEval c g y) ^ 2)
        (truncatedWindow x m (n - 2)) volume) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField v p i) (truncatedWindow x m (n - 3)) volume) ∧
      HasGradientOn (truncatedWindow x m (n - 3)) v (gradField v) ∧
      HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField v) ∧
      K ≤ schauderWindowConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m (n - 2)) v + 0 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  have hR2 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have hWS : ∀ p ∈ truncatedWindow x m (n - 3),
      toEuc p ∈ (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2) :=
    fun p hp => ⟨p, truncatedWindow_mono x m (by omega : n - 3 ≤ n - 2) hp, rfl⟩
  -- the Hölder bound with the atom's constant
  have hhol0 := gradField_holderHalf_of_harmonic
    (S := (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2))
    (W := truncatedWindow x m (n - 3)) (W₂ := truncatedWindow x m (n - 2))
    (R := (3 : ℝ) ^ (n - 3) / 2) (ratio := schauderRatioConst d)
    (D := (3 : ℝ) ^ (n - 3)) hharm (convex_truncatedWindow x m (n - 3)) hR
    (schauderRatioConst_nonneg d)
    (fun p hp => metricBall_toEuc_subset_image_of_interior hcube hp)
    (fun p hp => euclideanBall_subset_truncatedWindow_of_interior hcube hp hR2
      (by linarith only [h3]))
    (volume_toReal_truncatedWindow_pos x hx (by omega : n - 2 - 1 ≤ m))
    (fun p _ => lt_of_lt_of_le (by positivity) (volume_toReal_euclideanBall_ge p hR2))
    (fun p _ => sqrt_volume_ratio_le hx hnm p)
    hintsq
    (fun p hp q hq => norm_sub_le_of_mem_truncatedWindow_pair hp hq)
  -- the excess normalizer on the enveloping window
  set W₂ : Set (Vec d) := truncatedWindow x m (n - 2) with hW₂def
  set E : ℝ := affineExcessRaw W₂ v with hEdef
  set A : ℝ := affineExcess W₂ v with hAdef
  have hEnn : 0 ≤ E := affineExcessRaw_nonneg W₂ v
  have hAnn : 0 ≤ A := affineExcess_nonneg W₂ v
  have hlo : (3 : ℝ) ^ (-(n - 2)) ≤ ((volume W₂).toReal) ^ (-(d : ℝ)⁻¹) :=
    (rpow_volume_truncatedWindow_bounds hd x hx (by omega : n - 2 - 1 ≤ m)).1
  have hEA : E ≤ (3 : ℝ) ^ (n - 2) * A := by
    have hstep : (3 : ℝ) ^ (-(n - 2)) * E ≤ A := by
      rw [hAdef, affineExcess]
      exact mul_le_mul_of_nonneg_right hlo hEnn
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hstep hpos.le
    rwa [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero,
      one_mul] at hmul
  -- the constant comparison
  set C : ℝ := schauderConst d with hCdef
  set ra : ℝ := schauderRatioConst d with hradef
  have hCnn : 0 ≤ C := schauderConst_nonneg d
  have hrann : 0 ≤ ra := schauderRatioConst_nonneg d
  have htne : ((3 : ℝ) ^ (n - 3)) ≠ 0 := ne_of_gt h3
  have hscale : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  have hrewrite : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        * Real.sqrt ((3 : ℝ) ^ (n - 3))
      = (16 * C * ra * Real.sqrt ((3 : ℝ) ^ (n - 3)) / ((3 : ℝ) ^ (n - 3)) ^ 2) * E := by
    field_simp
    ring
  have hfacnn : (0 : ℝ)
      ≤ 16 * C * ra * Real.sqrt ((3 : ℝ) ^ (n - 3)) / ((3 : ℝ) ^ (n - 3)) ^ 2 := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (n - 3)) := Real.sqrt_nonneg _
    have hnum : (0 : ℝ) ≤ 16 * C * ra * Real.sqrt ((3 : ℝ) ^ (n - 3)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) hrann) hs
    exact div_nonneg hnum (by positivity)
  have hcollapse : (16 * C * ra * Real.sqrt ((3 : ℝ) ^ (n - 3)) / ((3 : ℝ) ^ (n - 3)) ^ 2)
        * ((3 : ℝ) ^ (n - 2) * A)
      = 48 * C * ra * A * (Real.sqrt ((3 : ℝ) ^ (n - 3)) / (3 : ℝ) ^ (n - 3)) := by
    rw [hscale]
    field_simp
    ring
  have hfinal : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        * Real.sqrt ((3 : ℝ) ^ (n - 3))
      ≤ schauderWindowConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * A := by
    rw [hrewrite]
    refine le_trans (mul_le_mul_of_nonneg_left hEA hfacnn) ?_
    rw [hcollapse, sqrt_zpow_div_self n, schauderWindowConst, ← hCdef, ← hradef]
    ring_nf
    exact le_rfl
  -- assemble
  refine ⟨4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
      * Real.sqrt ((3 : ℝ) ^ (n - 3)), ?_, ?_, ?_, ?_, ?_⟩
  · have hs : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (n - 3)) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hCnn) (inv_nonneg.2 hR.le)) (inv_nonneg.2 hR.le))
      (mul_nonneg hrann hEnn)) hs
  · intro i
    refine integrableOn_gradField_coord (K := 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹
        * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E) * Real.sqrt ((3 : ℝ) ^ (n - 3)))
      (D := (3 : ℝ) ^ (n - 3))
      (measurableSet_truncatedWindow x m (n - 3))
      (ne_of_lt (volume_truncatedWindow_lt_top x m (n - 3))) ?_
      (fun j => continuousOn_gradField_coord hharm hWS j) hhol0
      (fun p hp q hq => norm_sub_le_of_mem_truncatedWindow_pair hp hq)
      (mem_truncatedWindow_self (n - 3) hx) i
    have hs : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (n - 3)) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hCnn) (inv_nonneg.2 hR.le)) (inv_nonneg.2 hR.le))
      (mul_nonneg hrann hEnn)) hs
  · exact hasGradientOn_gradField hharm hWS
  · exact hhol0
  · rw [add_zero]
    exact hfinal

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
