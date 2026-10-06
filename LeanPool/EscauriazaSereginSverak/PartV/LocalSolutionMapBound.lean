/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionContraction
public import LeanPool.EscauriazaSereginSverak.PartV.HeatSmallOrbit

/-!
# The bilinear estimate for the Duhamel map

For velocities in `L⁵ ∩ L⁴` of the slab `ℝ³ × (0, σ)`, the forcing tensor lies
in `L^{5/2} ∩ L²` and vanishes off the slab, and the Duhamel map of
`prop:pv-local-solution` is quadratically Lipschitz for the norm
`‖·‖₅ + ‖·‖₄`, with a constant independent of `σ`.
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

/-- The quadratic tensor of a velocity in `L⁵ ∩ L⁴` of the slab lies in
`L^{5/2} ∩ L²`. -/
theorem pvSlabTensor_memLp_both {σ : ℝ} {U : ParabolicPoint → Vec3}
    (hU5 : MemLp U (ENNReal.ofReal 5) (μQ σ)) (hU4 : MemLp U (ENNReal.ofReal 4) (μQ σ))
    (i j : Fin 3) :
    MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal (5 / 2)) volume ∧
      MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume := by
  have h5 := pvSlab_holderTriple_five
  have h4 := pvSlab_holderTriple_four
  exact ⟨pvSlabTensor_memLp hU5 hU5 i j, pvSlabTensor_memLp hU4 hU4 i j⟩

/-- The forcing tensor of a velocity in `L⁵ ∩ L⁴` of the slab lies in
`L^{5/2} ∩ L²`. -/
theorem pvSlabForce_memLp_both {σ : ℝ} {U : ParabolicPoint → Vec3}
    (hU5 : MemLp U (ENNReal.ofReal 5) (μQ σ)) (hU4 : MemLp U (ENNReal.ofReal 4) (μQ σ))
    (i j : Fin 3) :
    MemLp (pvSlabForce σ U i j) (ENNReal.ofReal (5 / 2)) volume ∧
      MemLp (pvSlabForce σ U i j) 2 volume := by
  have hT := pvSlabTensor_memLp_both hU5 hU4
  have hP52 := pvSlabPressure_memLp (by norm_num : (1 : ℝ) < 5 / 2)
    (fun k l => (hT k l).2) (fun k l => (hT k l).1)
  have hP2 := pvSlabPressure_memLp (by norm_num : (1 : ℝ) < 2)
    (fun k l => (hT k l).2) (fun k l => (hT k l).2)
  have hform : pvSlabForce σ U i j =
      -(pvSlabTensor σ U U i j + if i = j then pvSlabPressure σ U else 0) := by
    funext z
    by_cases hij : i = j
    · simp [pvSlabForce, hij]
    · simp [pvSlabForce, hij]
  rw [hform]
  have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  constructor
  · refine ((hT i j).1.add ?_).neg
    split_ifs
    · exact hP52
    · exact MemLp.zero
  · rw [e2]
    refine ((hT i j).2.add ?_).neg
    split_ifs
    · exact hP2
    · exact MemLp.zero

/-- The forcing tensor vanishes at nonpositive times. -/
theorem pvSlabForce_pos_time {σ : ℝ} {U : ParabolicPoint → Vec3} (i j : Fin 3)
    (z : ParabolicPoint) (hz : pvSlabForce σ U i j z ≠ 0) : 0 < z.2 := by
  by_contra hneg
  apply hz
  refine pvSlabForce_eq_zero (fun hmem => hneg ?_) i j
  exact hmem.2.1

/-- The Duhamel map is quadratically Lipschitz for `‖·‖₅ + ‖·‖₄` on the slab,
with a constant independent of the length of the slab. -/
theorem pvLocalMap_lipschitz :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (a : Vec3 → Vec3) (σ : ℝ), 0 < σ →
      ∀ U V : ParabolicPoint → Vec3,
        MemLp U (ENNReal.ofReal 5) (μQ σ) → MemLp U (ENNReal.ofReal 4) (μQ σ) →
        MemLp V (ENNReal.ofReal 5) (μQ σ) → MemLp V (ENNReal.ofReal 4) (μQ σ) →
        eLpNorm (pvLocalMap a σ U - pvLocalMap a σ V) (ENNReal.ofReal 5) (μQ σ) +
            eLpNorm (pvLocalMap a σ U - pvLocalMap a σ V) (ENNReal.ofReal 4) (μQ σ) ≤
          K * (eLpNorm (U - V) (ENNReal.ofReal 5) (μQ σ) +
              eLpNorm (U - V) (ENNReal.ofReal 4) (μQ σ)) *
            (eLpNorm U (ENNReal.ofReal 5) (μQ σ) + eLpNorm U (ENNReal.ofReal 4) (μQ σ) +
              (eLpNorm V (ENNReal.ofReal 5) (μQ σ) +
                eLpNorm V (ENNReal.ofReal 4) (μQ σ))) := by
  obtain ⟨C, _, hC⟩ := forcedHeat_rough_bounds
  set c52 := 1 + 9 * ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound (5 / 2)
    (by norm_num : (1 : ℝ) < 5 / 2))
  set c2 := 1 + 9 * ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound 2
    (by norm_num : (1 : ℝ) < 2))
  have hc52 : c52 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hc2 : c2 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  refine ⟨ENNReal.ofReal C * (9 * (2 * c52 + c2)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hc52, hc2⟩))
  intro a σ hσ U V hU5 hU4 hV5 hV4
  have hh5 := pvSlab_holderTriple_five
  have hh4 := pvSlab_holderTriple_four
  have hTU := pvSlabTensor_memLp_both hU5 hU4
  have hTV := pvSlabTensor_memLp_both hV5 hV4
  have hGU := pvSlabForce_memLp_both hU5 hU4
  have hGV := pvSlabForce_memLp_both hV5 hV4
  set GU := pvSlabForce σ U
  set GV := pvSlabForce σ V
  set ΔG : Fin 3 → Fin 3 → ParabolicPoint → ℝ := GU - GV
  have hΔ52 : ∀ i j, MemLp (ΔG i j) (ENNReal.ofReal (5 / 2)) volume :=
    fun i j => (hGU i j).1.sub (hGV i j).1
  have hΔ2 : ∀ i j, MemLp (ΔG i j) 2 volume := fun i j => (hGU i j).2.sub (hGV i j).2
  have hΔsupp : ∀ i j z, z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ) → ΔG i j z = 0 := by
    intro i j z hz
    simp [ΔG, GU, GV, pvSlabForce_eq_zero hz]
  obtain ⟨hZ5, hZ4, -, -⟩ := hC σ hσ ΔG hΔ52 hΔ2 hΔsupp
  have hae : pvLocalMap a σ U - pvLocalMap a σ V =ᵐ[μQ σ] forcedHeat ΔG := by
    filter_upwards [forcedHeat_sub_ae hσ (fun i j => (hGU i j).2) (fun i j => (hGV i j).2)
      pvSlabForce_pos_time pvSlabForce_pos_time] with z hz
    simp only [Pi.sub_apply, pvLocalMap, hz, ΔG, GU, GV]
    abel
  rw [eLpNorm_congr_ae hae, eLpNorm_congr_ae hae]
  -- sizes
  set D5 := eLpNorm (U - V) (ENNReal.ofReal 5) (μQ σ)
  set D4 := eLpNorm (U - V) (ENNReal.ofReal 4) (μQ σ)
  set M := (D5 + D4) * (eLpNorm U (ENNReal.ofReal 5) (μQ σ) +
    eLpNorm U (ENNReal.ofReal 4) (μQ σ) + (eLpNorm V (ENNReal.ofReal 5) (μQ σ) +
      eLpNorm V (ENNReal.ofReal 4) (μQ σ)))
  have hX5 : D5 * (eLpNorm U (ENNReal.ofReal 5) (μQ σ) + eLpNorm V (ENNReal.ofReal 5) (μQ σ))
      ≤ M :=
    mul_le_mul' le_self_add (add_le_add le_self_add le_self_add)
  have hX4 : D4 * (eLpNorm U (ENNReal.ofReal 4) (μQ σ) + eLpNorm V (ENNReal.ofReal 4) (μQ σ))
      ≤ M :=
    mul_le_mul' le_add_self (add_le_add le_add_self le_add_self)
  have hle : (μQ σ) ≤ volume := Measure.restrict_le_self
  have hT52 : eLpNorm (fun z => fun i j => ΔG i j z) (ENNReal.ofReal (5 / 2)) (μQ σ) ≤
      9 * c52 * M := by
    refine (eLpNorm_tensor_le_sum (one_le_ofReal_of_one_le (by norm_num)) _
      fun i j => ((hΔ52 i j).aestronglyMeasurable.mono_measure hle)).trans ?_
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, c52 * M := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine (eLpNorm_mono_measure _ hle).trans ?_
        refine (pvSlabForce_sub_eLpNorm_le (by norm_num) hU5 hV5 (fun k l => (hTU k l).2)
          (fun k l => (hTV k l).2) (fun k l => (hTU k l).1) (fun k l => (hTV k l).1) i j).trans ?_
        gcongr
      _ = 9 * c52 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring
  have hT2 : eLpNorm (fun z => fun i j => ΔG i j z) 2 (μQ σ) ≤ 9 * c2 * M := by
    refine (eLpNorm_tensor_le_sum one_le_two _
      fun i j => ((hΔ2 i j).aestronglyMeasurable.mono_measure hle)).trans ?_
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, c2 * M := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine (eLpNorm_mono_measure _ hle).trans ?_
        have h := pvSlabForce_sub_eLpNorm_le (by norm_num : (1 : ℝ) < 2) hU4 hV4
          (fun k l => (hTU k l).2) (fun k l => (hTV k l).2) (fun k l => (hTU k l).2)
          (fun k l => (hTV k l).2) i j
        rw [ENNReal.ofReal_ofNat] at h
        refine h.trans ?_
        gcongr
      _ = 9 * c2 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring
  have e5 : ENNReal.ofReal 5 = 5 := by simp
  have e4 : ENNReal.ofReal 4 = 4 := by simp
  rw [← e5] at hZ5
  rw [← e4] at hZ4
  refine le_trans ?_ (le_of_eq (mul_assoc _ _ _).symm)
  calc
    _ ≤ ENNReal.ofReal C * (9 * c52 * M) + ENNReal.ofReal C * (9 * c52 * M + 9 * c2 * M) := by
        gcongr
        · exact hZ5.trans (by gcongr)
        · exact hZ4.trans (by gcongr)
    _ = ENNReal.ofReal C * (9 * (2 * c52 + c2)) * M := by ring

end ESS

end
