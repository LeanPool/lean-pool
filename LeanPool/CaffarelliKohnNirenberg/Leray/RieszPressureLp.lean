/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondAllExponentsPaper

/-!
# Spatial pressure operators

This file packages CKN's double Riesz transforms as the spatial operators
used in `def:riesz-pressure`.
-/

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The nine spatial tensor components, used by `def:riesz-pressure`. -/
abbrev PressureTensorLp (r : ℝ) :=
  Fin 3 → Fin 3 → Lp ℝ (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3)

section RieszLp

/-- CKN's bound for one double Riesz transform, used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureOperatorBound (r : ℝ) (hr : 1 < r) : ℝ :=
  Classical.choose (CKN.Foundation.Euclidean.riesz_second_all_exponents r hr)

/-- CKN's double Riesz transform at exponent `r`, used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureOperator (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Lp ℝ (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3) →L[ℝ]
      Lp ℝ (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3) := by
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact Classical.choose
    ((Classical.choose_spec
      (CKN.Foundation.Euclidean.riesz_second_all_exponents r hr)).2 i j)

/-- The chosen operator norm is bounded by the CKN constant, for `def:riesz-pressure`. -/
theorem rieszPressureOperator_norm_le (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    ‖rieszPressureOperator r hr i j‖ ≤ rieszPressureOperatorBound r hr := by
  exact (Classical.choose_spec
    ((Classical.choose_spec
      (CKN.Foundation.Euclidean.riesz_second_all_exponents r hr)).2 i j)).1

/-- The CKN all-exponent extension agrees with its signed L² definition on
inputs in both spaces, as required by `def:riesz-pressure`. -/
theorem rieszPressureOperator_ae_eq_negRaw (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (g : CKN.Foundation.Parabolic.Vec3 → ℝ)
    (hg : MemLp g (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3))
    (hg2 : MemLp g 2 (volume : Measure CKN.Foundation.Parabolic.Vec3)) :
    (fun x => rieszPressureOperator r hr i j (hg.toLp g) x) =ᵐ[volume]
      fun x => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator
        (CKN.Foundation.Euclidean.rieszSecondL2Input i j) g x := by
  exact (Classical.choose_spec
    ((Classical.choose_spec
      (CKN.Foundation.Euclidean.riesz_second_all_exponents r hr)).2 i j)).2 g hg hg2

/-- The all-exponent operators coincide almost everywhere on the common
`L^r`, `L^s`, and `L²` domain, as required by `def:riesz-pressure`. -/
theorem rieszPressureOperator_ae_eq_of_memLp_common
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s) (i j : Fin 3)
    (g : CKN.Foundation.Parabolic.Vec3 → ℝ)
    (hgr : MemLp g (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3))
    (hgs : MemLp g (ENNReal.ofReal s) (volume : Measure CKN.Foundation.Parabolic.Vec3))
    (hg2 : MemLp g 2 (volume : Measure CKN.Foundation.Parabolic.Vec3)) :
    (fun x => rieszPressureOperator r hr i j (hgr.toLp g) x) =ᵐ[volume]
      fun x => rieszPressureOperator s hs i j (hgs.toLp g) x := by
  have hleft := rieszPressureOperator_ae_eq_negRaw r hr i j g hgr hg2
  let Ts := Classical.choose
    ((Classical.choose_spec (CKN.Foundation.Euclidean.riesz_second_all_exponents s hs)).2 i j)
  have hT : (fun x => Ts (hgs.toLp g) x) =ᵐ[volume]
      fun x => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator
        (CKN.Foundation.Euclidean.rieszSecondL2Input i j) g x :=
    (Classical.choose_spec
      ((Classical.choose_spec
        (CKN.Foundation.Euclidean.riesz_second_all_exponents s hs)).2 i j)).2 g hgs hg2
  filter_upwards [hleft, hT] with x hxleft hxt
  exact hxleft.trans hxt.symm

/-- The spatial pressure as the sum of the nine CKN double Riesz transforms,
used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureSlice (r : ℝ) (hr : 1 < r) (F : PressureTensorLp r) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Lp ℝ (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3) := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact ∑ i : Fin 3, ∑ j : Fin 3, rieszPressureOperator r hr i j (F i j)

/-- The spatial pressure bound by the sum of the component norms, used by
`def:riesz-pressure`. -/
theorem rieszPressureSlice_norm_le (r : ℝ) (hr : 1 < r)
    (F : PressureTensorLp r) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    ‖rieszPressureSlice r hr F‖ ≤
      rieszPressureOperatorBound r hr * ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  calc
    ‖rieszPressureSlice r hr F‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ‖rieszPressureOperator r hr i j (F i j)‖ := by
      dsimp [rieszPressureSlice]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureOperatorBound r hr * ‖F i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖rieszPressureOperator r hr i j (F i j)‖ ≤
            ‖rieszPressureOperator r hr i j‖ * ‖F i j‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ rieszPressureOperatorBound r hr * ‖F i j‖ :=
          mul_le_mul_of_nonneg_right (rieszPressureOperator_norm_le r hr i j)
            (norm_nonneg _)
    _ = rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ := by
      simp only [Finset.mul_sum]

/-- A measurable function representative of the spatial pressure used by
`def:riesz-pressure`. -/
@[expose]
def rieszPressureSliceRepresentative (r : ℝ) (hr : 1 < r)
    (F : PressureTensorLp r) : CKN.Foundation.Parabolic.Vec3 → ℝ :=
  (Lp.aestronglyMeasurable (rieszPressureSlice r hr F)).aemeasurable.mk
    (rieszPressureSlice r hr F)

/-- The spatial pressure representative agrees almost everywhere with its
`L^r` class, used by `def:riesz-pressure`. -/
theorem rieszPressureSliceRepresentative_ae_eq (r : ℝ) (hr : 1 < r)
    (F : PressureTensorLp r) :
    (rieszPressureSlice r hr F : CKN.Foundation.Parabolic.Vec3 → ℝ) =ᵐ[volume]
      rieszPressureSliceRepresentative r hr F :=
  (Lp.aestronglyMeasurable (rieszPressureSlice r hr F)).aemeasurable.ae_eq_mk

/-- The signed distributional Laplacian identity for one tensor component,
used by `def:riesz-pressure`. -/
theorem rieszPressureOperator_laplacian_pairing (r : ℝ) (hr : 1 < r)
    (i j : Fin 3) (g : CKN.Foundation.Parabolic.Vec3 → ℝ)
    (hgr : MemLp g (ENNReal.ofReal r) (volume : Measure CKN.Foundation.Parabolic.Vec3))
    (hg2 : MemLp g 2 (volume : Measure CKN.Foundation.Parabolic.Vec3))
    (ψ : CKN.Foundation.Parabolic.Vec3 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, rieszPressureOperator r hr i j (hgr.toLp g) x *
        CKN.spatialLaplacian ψ x =
      -∫ x, g x * CKN.mixedSecond ψ i j x := by
  let hL2 := CKN.Foundation.Euclidean.rieszSecondL2Input i j
  have hRiesz := rieszPressureOperator_ae_eq_negRaw r hr i j g hgr hg2
  have hRaw := CKN.Foundation.Euclidean.rieszSecondL2RawOperator_ae_eq hL2 hg2
  have hOutput :
      (fun x => rieszPressureOperator r hr i j (hgr.toLp g) x) =ᵐ[volume]
        fun x => -CKN.Foundation.Euclidean.rieszSecondL2MeasurableOperator
          hL2 (hg2.toLp g) x := by
    filter_upwards [hRiesz, hRaw] with x hRx hOx
    exact hRx.trans (congrArg Neg.neg hOx)
  have hDistribution := CKN.Foundation.Euclidean.rieszSecondL2_distributional_identity
    hL2 hψ hψc (hg2.toLp g)
  calc
    ∫ x, rieszPressureOperator r hr i j (hgr.toLp g) x *
        CKN.spatialLaplacian ψ x =
        ∫ x, -(CKN.Foundation.Euclidean.rieszSecondL2MeasurableOperator
          hL2 (hg2.toLp g) x * CKN.spatialLaplacian ψ x) := by
      apply integral_congr_ae
      filter_upwards [hOutput] with x hx
      rw [hx]
      ring
    _ = -∫ x, CKN.Foundation.Euclidean.rieszSecondL2MeasurableOperator
          hL2 (hg2.toLp g) x * CKN.spatialLaplacian ψ x := by
      rw [integral_neg]
    _ = -∫ x, g x * CKN.mixedSecond ψ i j x := by
      rw [hDistribution]
      congr 1
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx
      rw [hx]

end RieszLp

end CKN.Leray

end
