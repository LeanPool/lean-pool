/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionForce

/-!
# Bounds for the forcing of the short-time construction

The forced heat response depends only on the almost-everywhere class of its
tensor and is additive at almost every point of the slab. The canonical
pressure is Lipschitz in every exponent `r > 1` with the constant of the double
Riesz transform. These are the ingredients of the contraction estimate in
`prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The forced heat response of a tensor depends only on its almost-everywhere
class. -/
theorem forcedHeat_congr_ae {G G' : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (h : ∀ i j, G i j =ᵐ[volume] G' i j) : forcedHeat G = forcedHeat G' := by
  funext z
  rw [forcedHeat_eq_kernelResponse, forcedHeat_eq_kernelResponse]
  funext i
  unfold kernelResponse
  apply integral_congr_ae
  let z' : Vec3 × ℝ := z
  have hmp : Measure.QuasiMeasurePreserving (fun p : Vec3 × ℝ => z' - p) volume volume :=
    quasiMeasurePreserving_sub_left volume z'
  have hj : ∀ j : Fin 3, (fun p : Vec3 × ℝ => G i j (z' - p)) =ᵐ[volume]
      fun p : Vec3 × ℝ => G' i j (z' - p) :=
    fun j => hmp.ae_eq_comp (h i j)
  filter_upwards [eventually_all.2 hj] with p hp
  exact Finset.sum_congr rfl fun j _ => by rw [hp j]

/-- The forced heat response is additive at almost every point of the slab, for
square-integrable tensors vanishing at nonpositive times. -/
theorem forcedHeat_sub_ae {τ : ℝ} (hτ : 0 < τ) {G G' : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) 2 volume) (hG' : ∀ i j, MemLp (G' i j) 2 volume)
    (hsG : ∀ i j z, G i j z ≠ 0 → 0 < z.2) (hsG' : ∀ i j z, G' i j z ≠ 0 → 0 < z.2) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))),
      forcedHeat (G - G') z = forcedHeat G z - forcedHeat G' z := by
  have hint (H : Fin 3 → Fin 3 → ParabolicPoint → ℝ) (hH : ∀ i j, MemLp (H i j) 2 volume)
      (hs : ∀ i j z, H i j z ≠ 0 → 0 < z.2) :
      ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))), ∀ i j,
        Integrable (fun p : ParabolicPoint =>
          heatKernelSpaceDerivative p.1 p.2 j * H i j (z.1 - p.1, z.2 - p.2)) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    exact kernel_integrable_ae_slab hτ j (H := fun p : Vec3 × ℝ => H i j p) (hH i j)
      (hs i j)
  have hnegG' : ∀ i j, MemLp (((-1 : ℝ) • G') i j) 2 volume := fun i j =>
    (hG' i j).const_smul (-1 : ℝ)
  filter_upwards [hint G hG hsG, hint _ hnegG' (fun i j z hz => hsG' i j z (by
      intro h0; apply hz; simp [h0]))] with z h1 h2
  have hsub : G - G' = G + (-1 : ℝ) • G' := by
    funext i j w
    simp [sub_eq_add_neg]
  rw [hsub, forcedHeat_add h1 h2, forcedHeat_smul]
  simp [sub_eq_add_neg]

/-- The canonical Riesz pressure is Lipschitz in space-time `L^r`. -/
theorem rieszPressureSpaceTime_sub_eLpNorm_le (r : ℝ) (hr : 1 < r)
    (F F' : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (hF' : ∀ i j, MemLp (F' i j) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
    eLpNorm (CKN.Leray.rieszPressureSpaceTime r hr F hF -
        CKN.Leray.rieszPressureSpaceTime r hr F' hF') (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr) *
        ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (F i j - F' i j) (ENNReal.ofReal r) volume := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  set T := CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F hF
  set T' := CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F' hF'
  have hrep (H : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (hH : ∀ i j, MemLp (H i j) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
      CKN.Leray.rieszPressureSpaceTime r hr H hH =ᵐ[volume]
        (CKN.Leray.rieszPressureSpaceTimeClass r hr
          (CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr H hH) : Vec3 × ℝ → ℝ) := by
    simpa [CKN.Leray.rieszPressureSpaceTime,
      CKN.Leray.rieszPressureSpaceTimeRepresentative] using
      ((Lp.aestronglyMeasurable (CKN.Leray.rieszPressureSpaceTimeClass r hr
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr H hH))).aemeasurable.ae_eq_mk.symm)
  have hclass : CKN.Leray.rieszPressureSpaceTimeClass r hr T -
      CKN.Leray.rieszPressureSpaceTimeClass r hr T' =
      CKN.Leray.rieszPressureSpaceTimeClass r hr (fun i j => T i j - T' i j) := by
    simp only [CKN.Leray.rieszPressureSpaceTimeClass, map_sub, Finset.sum_sub_distrib]
  have hae : CKN.Leray.rieszPressureSpaceTime r hr F hF -
      CKN.Leray.rieszPressureSpaceTime r hr F' hF' =ᵐ[volume]
      (CKN.Leray.rieszPressureSpaceTimeClass r hr (fun i j => T i j - T' i j) :
        Vec3 × ℝ → ℝ) := by
    rw [← hclass]
    filter_upwards [hrep F hF, hrep F' hF', Lp.coeFn_sub
      (CKN.Leray.rieszPressureSpaceTimeClass r hr T)
      (CKN.Leray.rieszPressureSpaceTimeClass r hr T')] with z h1 h2 h3
    rw [h3, Pi.sub_apply, Pi.sub_apply, h1, h2]
  rw [eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  have hTsub (i j : Fin 3) : T i j - T' i j = ((hF i j).sub (hF' i j)).toLp (F i j - F' i j) :=
    ((hF i j).toLp_sub (hF' i j)).symm
  have hnorm := CKN.Leray.rieszPressureSpaceTimeClass_norm_le r hr (fun i j => T i j - T' i j)
  simp only [hTsub, Lp.norm_toLp] at hnorm
  refine (ENNReal.ofReal_le_ofReal hnorm).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    ENNReal.toReal_nonneg), ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ENNReal.ofReal_toReal ((hF i j).sub (hF' i j)).eLpNorm_ne_top

end ESS

end
