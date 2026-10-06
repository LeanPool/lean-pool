/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionForceBounds

/-!
# Lipschitz bounds for the forcing of the short-time construction

The cut-off pressure is Lipschitz in `L²` and `L^{5/2}` with respect to the
quadratic tensor, and the forcing tensor `-(U ⊗ U + p I)` is quadratically
Lipschitz with respect to the velocity in `L⁴` and `L⁵` of the slab. These give
the bilinear estimate of `prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slab `ℝ³ × (0, σ)` as a measure. -/
local notation "μQ" σ => (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) :
  Measure ParabolicPoint)

theorem one_le_ofReal_of_one_le {r : ℝ} (hr : 1 ≤ r) : 1 ≤ ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hr

/-- The cut-off pressure agrees almost everywhere with the cut-off Riesz
pressure at any exponent `r > 1` at which the tensor is integrable. -/
theorem pvSlabPressure_ae_eq_indicator {σ r : ℝ} (hr : 1 < r) {W : ParabolicPoint → Vec3}
    (hW2 : ∀ i j, MemLp (pvSlabTensor σ W W i j) (ENNReal.ofReal 2) volume)
    (hWr : ∀ i j, MemLp (pvSlabTensor σ W W i j) (ENNReal.ofReal r) volume) :
    pvSlabPressure σ W =ᵐ[volume]
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)).indicator
        (CKN.Leray.rieszPressureSpaceTime r hr (pvSlabTensor σ W W) hWr) := by
  rw [pvSlabPressure_eq hW2]
  have h := CKN.Leray.rieszPressureSpaceTime_ae_eq_of_memLp_common 2 (by norm_num) r hr
    (pvSlabTensor σ W W) hW2 hWr
  filter_upwards [h] with z hz
  unfold Set.indicator
  split_ifs
  · exact hz
  · rfl

/-- The cut-off pressure lies in `L^r` whenever the tensor lies in `L² ∩ L^r`. -/
theorem pvSlabPressure_memLp {σ r : ℝ} (hr : 1 < r) {W : ParabolicPoint → Vec3}
    (hW2 : ∀ i j, MemLp (pvSlabTensor σ W W i j) (ENNReal.ofReal 2) volume)
    (hWr : ∀ i j, MemLp (pvSlabTensor σ W W i j) (ENNReal.ofReal r) volume) :
    MemLp (pvSlabPressure σ W) (ENNReal.ofReal r) volume :=
  (memLp_congr_ae (pvSlabPressure_ae_eq_indicator hr hW2 hWr)).2
    ((CKN.Leray.rieszPressureSpaceTime_memLp r hr _ hWr).indicator (pvSlab_measurableSet σ))

/-- The cut-off pressure is Lipschitz with respect to the tensor, at any exponent
`r > 1` at which both tensors are integrable. -/
theorem pvSlabPressure_sub_eLpNorm_le {σ r : ℝ} (hr : 1 < r) {U V : ParabolicPoint → Vec3}
    (hU2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume)
    (hV2 : ∀ i j, MemLp (pvSlabTensor σ V V i j) (ENNReal.ofReal 2) volume)
    (hUr : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal r) volume)
    (hVr : ∀ i j, MemLp (pvSlabTensor σ V V i j) (ENNReal.ofReal r) volume) :
    eLpNorm (pvSlabPressure σ U - pvSlabPressure σ V) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr) *
        ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (pvSlabTensor σ U U i j - pvSlabTensor σ V V i j) (ENNReal.ofReal r) volume := by
  have hae : pvSlabPressure σ U - pvSlabPressure σ V =ᵐ[volume]
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)).indicator (CKN.Leray.rieszPressureSpaceTime r hr (pvSlabTensor σ U U) hUr -
        CKN.Leray.rieszPressureSpaceTime r hr (pvSlabTensor σ V V) hVr) := by
    filter_upwards [pvSlabPressure_ae_eq_indicator hr hU2 hUr,
      pvSlabPressure_ae_eq_indicator hr hV2 hVr] with z h1 h2
    rw [Pi.sub_apply, h1, h2]
    unfold Set.indicator
    split_ifs
    · rfl
    · exact sub_zero 0
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_indicator_le _ (pvSlab_measurableSet σ)).trans
    (rieszPressureSpaceTime_sub_eLpNorm_le r hr _ _ hUr hVr)

/-- The difference of two quadratic tensors is bounded by the distance of the
velocities times the sum of their sizes. -/
theorem pvSlabTensor_sub_eLpNorm_le {σ : ℝ} {p r : ℝ≥0∞} (hr : 1 ≤ r)
    [ENNReal.HolderTriple p p r] {U V : ParabolicPoint → Vec3}
    (hU : MemLp U p (μQ σ)) (hV : MemLp V p (μQ σ)) (i j : Fin 3) :
    eLpNorm (pvSlabTensor σ U U i j - pvSlabTensor σ V V i j) r volume ≤
      eLpNorm (U - V) p (μQ σ) * (eLpNorm U p (μQ σ) + eLpNorm V p (μQ σ)) := by
  rw [pvSlabTensor_sub]
  refine (eLpNorm_add_le hr).trans ?_
  have h1 := pvSlabTensor_eLpNorm_le (σ := σ) (p := p) (r := r)
    (hU.sub hV).aestronglyMeasurable hU.aestronglyMeasurable i j
  have h2 := pvSlabTensor_eLpNorm_le (σ := σ) (p := p) (r := r)
    hV.aestronglyMeasurable (hU.sub hV).aestronglyMeasurable i j
  calc _ ≤ eLpNorm (U - V) p (μQ σ) * eLpNorm U p (μQ σ) +
        eLpNorm V p (μQ σ) * eLpNorm (U - V) p (μQ σ) := add_le_add h1 h2
    _ = _ := by ring

/-- The forcing tensor is quadratically Lipschitz in the velocity. -/
theorem pvSlabForce_sub_eLpNorm_le {σ r : ℝ} (hr : 1 < r) {p : ℝ≥0∞}
    [ENNReal.HolderTriple p p (ENNReal.ofReal r)] {U V : ParabolicPoint → Vec3}
    (hU : MemLp U p (μQ σ)) (hV : MemLp V p (μQ σ))
    (hU2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume)
    (hV2 : ∀ i j, MemLp (pvSlabTensor σ V V i j) (ENNReal.ofReal 2) volume)
    (hUr : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal r) volume)
    (hVr : ∀ i j, MemLp (pvSlabTensor σ V V i j) (ENNReal.ofReal r) volume) (i j : Fin 3) :
    eLpNorm (pvSlabForce σ U i j - pvSlabForce σ V i j) (ENNReal.ofReal r) volume ≤
      (1 + 9 * ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr)) *
        (eLpNorm (U - V) p (μQ σ) * (eLpNorm U p (μQ σ) + eLpNorm V p (μQ σ))) := by
  have hr1 : 1 ≤ ENNReal.ofReal r := one_le_ofReal_of_one_le hr.le
  set B := ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr)
  set X := eLpNorm (U - V) p (μQ σ) * (eLpNorm U p (μQ σ) + eLpNorm V p (μQ σ))
  have hT (k l : Fin 3) := pvSlabTensor_sub_eLpNorm_le (σ := σ) hr1 hU hV k l
  have hP : eLpNorm (pvSlabPressure σ U - pvSlabPressure σ V) (ENNReal.ofReal r) volume ≤
      B * (9 * X) := by
    refine (pvSlabPressure_sub_eLpNorm_le hr hU2 hV2 hUr hVr).trans ?_
    gcongr
    calc (∑ k : Fin 3, ∑ l : Fin 3, eLpNorm (pvSlabTensor σ U U k l -
          pvSlabTensor σ V V k l) (ENNReal.ofReal r) volume) ≤
          ∑ _k : Fin 3, ∑ _l : Fin 3, X :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hT k l
      _ = 9 * X := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; norm_num; ring
  have hsplit : pvSlabForce σ U i j - pvSlabForce σ V i j =
      -((pvSlabTensor σ U U i j - pvSlabTensor σ V V i j) +
        if i = j then pvSlabPressure σ U - pvSlabPressure σ V else 0) := by
    funext z
    by_cases hij : i = j
    · simp only [pvSlabForce, hij, ite_true, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
      ring
    · simp only [pvSlabForce, hij, ite_false, Pi.sub_apply, Pi.neg_apply, Pi.add_apply,
        Pi.zero_apply]
      ring
  rw [hsplit, eLpNorm_neg]
  refine (eLpNorm_add_le hr1).trans ?_
  have hite : eLpNorm (if i = j then pvSlabPressure σ U - pvSlabPressure σ V else 0)
      (ENNReal.ofReal r) volume ≤ B * (9 * X) := by
    split_ifs
    · exact hP
    · simp
  calc _ ≤ X + B * (9 * X) := add_le_add (hT i j) hite
    _ = (1 + 9 * B) * X := by ring

end ESS

end
