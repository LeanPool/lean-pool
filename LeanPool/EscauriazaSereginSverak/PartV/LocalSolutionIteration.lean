/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionMapBound
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPicard

/-!
# The fixed point of the Duhamel map

For a datum in `L² ∩ L³` the Duhamel map of `prop:pv-local-solution` has a
fixed point in `L⁵ ∩ L⁴` of a short slab: the heat orbit is small there
(`lem:pv-small-heat`), and the map is quadratically Lipschitz with a constant
independent of the length of the slab. The fixed point is then normalized so
that the fixed-point identity holds at every positive time and the datum is its
value at time zero.
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

/-- The canonical Riesz pressure of a tensor vanishing almost everywhere
vanishes almost everywhere. -/
theorem rieszPressureSpaceTime_ae_zero (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (h0 : ∀ i j, F i j =ᵐ[volume] 0) :
    CKN.Leray.rieszPressureSpaceTime r hr F hF =ᵐ[volume] 0 := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hT : CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F hF = 0 := by
    funext i j
    exact (hF i j).toLp_congr MemLp.zero (h0 i j)
  have hrep : CKN.Leray.rieszPressureSpaceTime r hr F hF =ᵐ[volume]
      (CKN.Leray.rieszPressureSpaceTimeClass r hr
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F hF) : Vec3 × ℝ → ℝ) := by
    simpa [CKN.Leray.rieszPressureSpaceTime,
      CKN.Leray.rieszPressureSpaceTimeRepresentative] using
      ((Lp.aestronglyMeasurable (CKN.Leray.rieszPressureSpaceTimeClass r hr
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F hF))).aemeasurable.ae_eq_mk.symm)
  have hclass : CKN.Leray.rieszPressureSpaceTimeClass r hr
      (CKN.Leray.rieszPressureSpaceTimeTensorToLp r hr F hF) = 0 := by
    rw [hT]
    simp [CKN.Leray.rieszPressureSpaceTimeClass]
  rw [hclass] at hrep
  exact hrep.trans (Lp.coeFn_zero _ _ _)

/-- The forcing of the zero velocity vanishes, so the Duhamel map sends zero to
the heat orbit. -/
theorem pvLocalMap_zero (a : Vec3 → Vec3) (σ : ℝ) : pvLocalMap a σ 0 = heatOrbit a := by
  have hT : pvSlabTensor σ 0 0 = 0 := by
    funext i j z
    simp [pvSlabTensor]
  have hT2 : ∀ i j, MemLp (pvSlabTensor σ 0 0 i j) (ENNReal.ofReal 2)
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    rw [hT]
    exact MemLp.zero
  have hP : pvSlabPressure σ 0 =ᵐ[volume] 0 := by
    rw [pvSlabPressure_eq hT2]
    have h := rieszPressureSpaceTime_ae_zero 2 (by norm_num) _ hT2
      (fun i j => by rw [hT]; rfl)
    filter_upwards [h] with z hz
    unfold Set.indicator
    split_ifs
    · exact hz
    · rfl
  have hG : ∀ i j, pvSlabForce σ 0 i j =ᵐ[volume] (0 : Fin 3 → Fin 3 → ParabolicPoint → ℝ) i j := by
    intro i j
    filter_upwards [hP] with z hz
    simp [pvSlabForce, hT, hz]
  have h0 (z : ParabolicPoint) : forcedHeat 0 z = 0 := by
    funext i
    unfold forcedHeat
    have hpt (p : ParabolicPoint) : ∑ j : Fin 3,
        Foundation.Heat.heatKernelSpaceDerivative p.1 p.2 j *
          (0 : Fin 3 → Fin 3 → ParabolicPoint → ℝ) i j (z.1 - p.1, z.2 - p.2) = 0 :=
      Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ rfl
    change (∫ p : ParabolicPoint, ∑ j : Fin 3,
        Foundation.Heat.heatKernelSpaceDerivative p.1 p.2 j *
          (0 : Fin 3 → Fin 3 → ParabolicPoint → ℝ) i j (z.1 - p.1, z.2 - p.2)) = 0
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_zero]
  funext z
  rw [pvLocalMap, forcedHeat_congr_ae hG, h0, add_zero]

/-- The Duhamel map only sees the velocity almost everywhere on the slab. -/
theorem pvLocalMap_congr {a : Vec3 → Vec3} {σ : ℝ} {U V : ParabolicPoint → Vec3}
    (hUV : U =ᵐ[μQ σ] V) : pvLocalMap a σ U = pvLocalMap a σ V := by
  have hTae : ∀ i j, pvSlabTensor σ U U i j =ᵐ[volume] pvSlabTensor σ V V i j := by
    intro i j
    have h := (ae_restrict_iff' (pvSlab_measurableSet σ)).1 hUV
    filter_upwards [h] with z hz
    unfold pvSlabTensor Set.indicator
    split_ifs with hzQ
    · change U z i * U z j = V z i * V z j
      rw [hz hzQ]
    · rfl
  have hP : pvSlabPressure σ U = pvSlabPressure σ V := by
    unfold pvSlabPressure
    congr 1
    funext z
    split_ifs with hU hV hV
    · unfold CKN.Leray.rieszPressureSpaceTime
      congr 1
      funext i j
      exact (hU i j).toLp_congr (hV i j) (hTae i j)
    · exact absurd (fun i j => (memLp_congr_ae (hTae i j)).1 (hU i j)) hV
    · exact absurd (fun i j => (memLp_congr_ae (hTae i j)).2 (hV i j)) hU
    · rfl
  have hG : ∀ i j, pvSlabForce σ U i j =ᵐ[volume] pvSlabForce σ V i j := by
    intro i j
    filter_upwards [hTae i j] with z hz
    simp only [pvSlabForce, hz, hP]
  funext z
  simp only [pvLocalMap, forcedHeat_congr_ae hG]

/-- The Duhamel map sends `L⁵ ∩ L⁴` of the slab to itself. -/
theorem pvLocalMap_memLp {a : Vec3 → Vec3} (ha2 : MemLp a 2 volume) (ha3 : MemLp a 3 volume)
    {σ : ℝ} (hσ : 0 < σ) {U : ParabolicPoint → Vec3}
    (hU5 : MemLp U (ENNReal.ofReal 5) (μQ σ)) (hU4 : MemLp U (ENNReal.ofReal 4) (μQ σ)) :
    MemLp (pvLocalMap a σ U) (ENNReal.ofReal 5) (μQ σ) ∧
      MemLp (pvLocalMap a σ U) (ENNReal.ofReal 4) (μQ σ) := by
  obtain ⟨C, _, hC⟩ := forcedHeat_rough_bounds
  have hGU := pvSlabForce_memLp_both hU5 hU4
  obtain ⟨hZ5, hZ4, -, -⟩ := hC σ hσ (pvSlabForce σ U) (fun i j => (hGU i j).1)
    (fun i j => (hGU i j).2) (fun i j z hz => pvSlabForce_eq_zero hz i j)
  have hle : (μQ σ) ≤ volume := Measure.restrict_le_self
  have hfin (r : ℝ≥0∞) (hr : 1 ≤ r) (hG : ∀ i j, MemLp (pvSlabForce σ U i j) r volume) :
      eLpNorm (fun z => fun i j => pvSlabForce σ U i j z) r (μQ σ) < ⊤ := by
    refine (eLpNorm_tensor_le_sum hr _
      fun i j => ((hG i j).aestronglyMeasurable.mono_measure hle)).trans_lt ?_
    refine ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ => ?_
    exact (eLpNorm_mono_measure _ hle).trans_lt (hG i j).eLpNorm_lt_top
  have h52 := hfin _ (one_le_ofReal_of_one_le (by norm_num)) fun i j => (hGU i j).1
  have h2 := hfin _ one_le_two fun i j => (hGU i j).2
  have hZ5' : MemLp (forcedHeat (pvSlabForce σ U)) 5 (μQ σ) := by
    rw [memLp_iff]
    exact hZ5.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h52)
  have hZ4' : MemLp (forcedHeat (pvSlabForce σ U)) 4 (μQ σ) := by
    rw [memLp_iff]
    exact hZ4.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨h52, h2⟩))
  have e5 : ENNReal.ofReal 5 = 5 := by simp
  have e4 : ENNReal.ofReal 4 = 4 := by simp
  rw [e5, e4]
  exact ⟨(heatOrbit_memLp_five ha3 hσ).add hZ5', (heatOrbit_memLp_four ha2 ha3 hσ).add hZ4'⟩

/-- The Duhamel map has a fixed point in `L⁵ ∩ L⁴` of a short slab, which
satisfies the fixed-point identity at every nonzero time and equals the datum
at time zero. -/
theorem pvLocal_fixedPoint {a : Vec3 → Vec3} (ha2 : MemLp a 2 volume)
    (ha3 : MemLp a 3 volume) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ U : ParabolicPoint → Vec3,
      MemLp U (ENNReal.ofReal 5) (μQ σ) ∧ MemLp U (ENNReal.ofReal 4) (μQ σ) ∧
      (∀ z : ParabolicPoint, z.2 ≠ 0 → U z = pvLocalMap a σ U z) ∧
      ∀ x : Vec3, U (x, 0) = a x := by
  obtain ⟨K, hK, hlip⟩ := pvLocalMap_lipschitz
  have hs := pvSmallHeat ha2 ha3
  have hε : (0 : ℝ≥0∞) < (8 * K)⁻¹ := ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by norm_num) hK)
  obtain ⟨σ, hσN, hσ⟩ := ((hs.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  have hσ0 : 0 < σ := hσ
  have e5 : ENNReal.ofReal 5 = 5 := by simp
  have e4 : ENNReal.ofReal 4 = 4 := by simp
  have hsmall : 8 * K * (eLpNorm (heatOrbit a) (ENNReal.ofReal 5) (μQ σ) +
      eLpNorm (heatOrbit a) (ENNReal.ofReal 4) (μQ σ)) ≤ 1 := by
    rw [e5, e4]
    calc _ ≤ 8 * K * (8 * K)⁻¹ := by gcongr
      _ ≤ 1 := ENNReal.mul_inv_le_one _
  have hh5 : MemLp (heatOrbit a) (ENNReal.ofReal 5) (μQ σ) := by
    rw [e5]; exact heatOrbit_memLp_five ha3 hσ0
  have hh4 : MemLp (heatOrbit a) (ENNReal.ofReal 4) (μQ σ) := by
    rw [e4]; exact heatOrbit_memLp_four ha2 ha3 hσ0
  obtain ⟨U, hU5, hU4, hfix⟩ := picard_fixedPoint (one_le_ofReal_of_one_le (by norm_num))
    (one_le_ofReal_of_one_le (by norm_num)) (pvLocalMap a σ) (heatOrbit a) hK hh5 hh4
    (fun V hV5 hV4 => pvLocalMap_memLp ha2 ha3 hσ0 hV5 hV4) (hlip a σ hσ0)
    (by rw [pvLocalMap_zero]) hsmall
  classical
  let W : ParabolicPoint → Vec3 := fun z => if z.2 = 0 then a z.1 else pvLocalMap a σ U z
  have hWU : W =ᵐ[μQ σ] U := by
    have hin : ∀ᵐ z ∂(μQ σ), z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ) :=
      ae_restrict_mem (pvSlab_measurableSet σ)
    filter_upwards [hfix, hin] with z hz hzQ
    have hz2 : z.2 ≠ 0 := hzQ.2.1.ne'
    simp only [W, hz2, ite_false]
    exact hz
  have hmap : pvLocalMap a σ W = pvLocalMap a σ U := pvLocalMap_congr hWU
  refine ⟨σ, hσ0, W, (memLp_congr_ae hWU).2 hU5, (memLp_congr_ae hWU).2 hU4, ?_, ?_⟩
  · intro z hz
    rw [hmap]
    simp only [W, hz, ite_false]
  · intro x
    simp [W]

end ESS

end
