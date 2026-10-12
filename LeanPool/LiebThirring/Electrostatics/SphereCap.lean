/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Sphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
/-!
# Euclidean cap volumes

Volume coordinates separating height `x 2` from the horizontal Euclidean plane.

The open unit cone selected by the height-to-radius threshold `t`.
-/

public section

open MeasureTheory Set Metric WithLp intervalIntegral
open scoped ENNReal Pointwise
namespace LiebThirring

/-- Volume coordinates separating height `x 2` from the horizontal Euclidean plane. -/
@[expose] noncomputable def sphereHeightSplit : Position ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem sphereHeightSplit_preserving : MeasurePreserving sphereHeightSplit := by
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurePreserving.id volume).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm))

theorem sphereHeightSplit_fst (x : Position) : (sphereHeightSplit x).1 = x 2 := rfl

theorem sphereHeightSplit_norm (x : Position) :
    ‖x‖ ^ 2 = (sphereHeightSplit x).1 ^ 2 + ‖(sphereHeightSplit x).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change x 0 ^ 2 + (x 1 ^ 2 + (x 2 ^ 2 + 0)) =
    x 2 ^ 2 + (x 0 ^ 2 + (x 1 ^ 2 + 0))
  ring

theorem height_sub_one (x : Position) (hx : ‖x‖ < 1) : x 2 < 1 := by
  have hb := PiLp.norm_apply_le x 2
  exact (le_abs_self _).trans_lt (hb.trans_lt hx)

-- Real core: slice below the cone slope.
theorem cap_slice_low {t s q n : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hs : 0 < s) (hst : s ≤ t) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hn2 : n ^ 2 = s ^ 2 + q ^ 2) :
    (n < 1 ∧ t * n < s) ↔ q < s * Real.sqrt (1 - t ^ 2) / t := by
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have ha : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht2
  have hc : 0 ≤ s * Real.sqrt (1 - t ^ 2) / t := by positivity
  have hnum : (s * Real.sqrt (1 - t ^ 2)) ^ 2 = s ^ 2 * (1 - t ^ 2) := by
    rw [mul_pow, ha2]
  have hscaled := congrArg (fun z : ℝ => t ^ 2 * z) hn2
  rw [← sq_lt_sq₀ hq hc, div_pow, lt_div_iff₀ (sq_pos_of_pos ht)]
  constructor
  · rintro ⟨_, hc⟩
    have hcs : (t * n) ^ 2 < s ^ 2 := (sq_lt_sq₀ (mul_nonneg ht.le hn) hs.le).mpr hc
    nlinarith only [hcs, hscaled, hnum]
  · intro hc
    have hcs : (t * n) ^ 2 < s ^ 2 := by nlinarith only [hc, hscaled, hnum]
    have hcone := (sq_lt_sq₀ (mul_nonneg ht.le hn) hs.le).mp hcs
    have hn1 : n < 1 := (mul_lt_mul_iff_right₀ ht).mp (by
      simpa only [mul_one] using hcone.trans_le hst)
    exact ⟨hn1, hcone⟩

theorem cap_slice_high {t s q n : ℝ} (ht : 0 < t) (hst : t ≤ s) (hs1 : s < 1)
    (hq : 0 ≤ q) (hn : 0 ≤ n) (hn2 : n ^ 2 = s ^ 2 + q ^ 2) :
    (n < 1 ∧ t * n < s) ↔ q < Real.sqrt (1 - s ^ 2) := by
  have hs : 0 < s := ht.trans_le hst
  have hs2 : 0 ≤ 1 - s ^ 2 := by nlinarith only [hs, hs1]
  rw [← sq_lt_sq₀ hq (Real.sqrt_nonneg _), Real.sq_sqrt hs2]
  constructor
  · rintro ⟨hn1, _⟩
    have hns : n ^ 2 < 1 := by simpa using (sq_lt_sq₀ hn zero_le_one).mpr hn1
    linarith only [hns, hn2]
  · intro hq2
    have hn1 : n < 1 := (sq_lt_sq₀ hn zero_le_one).mp (by nlinarith only [hq2, hn2])
    have hprod : t * n < t := by simpa only [mul_one] using mul_lt_mul_of_pos_left hn1 ht
    have hcone : t * n < s := hprod.trans_le hst
    exact ⟨hn1, hcone⟩

/-- The open unit cone selected by the height-to-radius threshold `t`. -/
@[expose] def sphereCone (t : ℝ) : Set Position := {x | ‖x‖ < 1 ∧ t * ‖x‖ < x 2}

theorem measurableSet_sphereCone (t : ℝ) : MeasurableSet (sphereCone t) := by
  apply MeasurableSet.inter
  · exact isOpen_lt continuous_norm continuous_const |>.measurableSet
  · exact isOpen_lt (continuous_const.mul continuous_norm) (PiLp.continuous_apply 2 (fun _ : Fin 3
    => ℝ) 2) |>.measurableSet

theorem cap_cone_eq (t : ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' {ω : sphere (0 : Position) 1 | t < (ω : Position) 2}) =
      sphereCone t := by
  ext x
  constructor
  · rintro ⟨s, hs, z, ⟨ω, hω, rfl⟩, rfl⟩
    have hnorm : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    change ‖s • (ω : Position)‖ < 1 ∧ t * ‖s • (ω : Position)‖ < (s • (ω : Position)) 2
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hnorm, mul_one, PiLp.smul_apply,
      smul_eq_mul]
    exact ⟨hs.2, by simpa only [mul_comm t s] using mul_lt_mul_of_pos_left hω hs.1⟩
  · intro hx
    have hpos : 0 < ‖x‖ := by
      apply norm_pos_iff.mpr
      intro heq
      simp only [sphereCone, mem_ofPred_eq, heq, norm_zero, mul_zero, PiLp.zero_apply,
        lt_self_iff_false,
        and_false] at hx
    refine ⟨‖x‖, ⟨hpos, hx.1⟩, ‖x‖⁻¹ • x, ?_, ?_⟩
    · refine ⟨⟨‖x‖⁻¹ • x, ?_⟩, ?_, rfl⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
      · change t < (‖x‖⁻¹ • x) 2
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [inv_mul_eq_div, lt_div_iff₀ hpos]
        exact hx.2
    · change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
theorem cone_slice_eq_disk_low {t s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hs : 0 < s) (hst : s ≤ t) :
    (fun y : EuclideanSpace ℝ (Fin 2) => sphereHeightSplit.symm (s,y)) ⁻¹' sphereCone t =
      ball 0 (s * Real.sqrt (1 - t ^ 2) / t) := by
  ext y
  have hx := sphereHeightSplit_norm (sphereHeightSplit.symm (s,y))
  rw [sphereHeightSplit.apply_symm_apply] at hx
  have hh : (sphereHeightSplit.symm (s,y)) 2 = s := by
    rw [← sphereHeightSplit_fst, sphereHeightSplit.apply_symm_apply]
  simp only [sphereCone, mem_preimage, mem_ofPred_eq, hh, mem_ball_zero_iff]
  exact cap_slice_low ht ht1 hs hst (norm_nonneg y) (norm_nonneg _) hx

theorem cone_slice_eq_disk_high {t s : ℝ} (ht : 0 < t) (hst : t ≤ s) (hs1 : s < 1) :
    (fun y : EuclideanSpace ℝ (Fin 2) => sphereHeightSplit.symm (s,y)) ⁻¹' sphereCone t =
      ball 0 (Real.sqrt (1 - s ^ 2)) := by
  ext y
  have hx := sphereHeightSplit_norm (sphereHeightSplit.symm (s,y))
  rw [sphereHeightSplit.apply_symm_apply] at hx
  have hh : (sphereHeightSplit.symm (s,y)) 2 = s := by
    rw [← sphereHeightSplit_fst, sphereHeightSplit.apply_symm_apply]
  simp only [sphereCone, mem_preimage, mem_ofPred_eq, hh, mem_ball_zero_iff]
  exact cap_slice_high ht hst hs1 (norm_nonneg y) (norm_nonneg _) hx

theorem cone_slice_empty {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 0 ∨ 1 ≤ s) :
    (fun y : EuclideanSpace ℝ (Fin 2) => sphereHeightSplit.symm (s,y)) ⁻¹' sphereCone t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hh : (sphereHeightSplit.symm (s,y)) 2 = s := by
    rw [← sphereHeightSplit_fst, sphereHeightSplit.apply_symm_apply]
  change ‖sphereHeightSplit.symm (s,y)‖ < 1 ∧ t * ‖sphereHeightSplit.symm (s,y)‖ < s at hy
  rcases hs with hs | hs
  · exact (not_lt_of_ge hs) ((mul_nonneg ht (norm_nonneg _)).trans_lt hy.2)
  · have hheight := height_sub_one (sphereHeightSplit.symm (s,y)) hy.1
    rw [hh] at hheight
    exact (not_lt_of_ge hs) hheight
theorem cone_slice_area {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (s : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      ((fun y => sphereHeightSplit.symm (s,y)) ⁻¹' sphereCone t) =
      (Ioo 0 t).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * ((1 - t ^ 2) / t ^ 2) * s ^ 2)) s
        +
      (Ico t 1).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * (1 - s ^ 2))) s := by
  by_cases hs0 : 0 < s
  · by_cases hs1 : s < 1
    · by_cases hst : s < t
      · rw [cone_slice_eq_disk_low ht ht1 hs0 hst.le, EuclideanSpace.volume_ball_fin_two]
        have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith only [ht, ht1]
        have hc : 0 ≤ s * Real.sqrt (1 - t ^ 2) / t := by positivity
        have heq : (s * Real.sqrt (1 - t ^ 2) / t) ^ 2 * Real.pi =
            Real.pi * ((1 - t ^ 2) / t ^ 2) * s ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt ht2]
          ring
        simp only [Set.indicator_of_mem (show s ∈ Ioo 0 t from ⟨hs0,hst⟩),
          Set.indicator_of_notMem (show s ∉ Ico t 1 from fun h => not_le_of_gt hst h.1), add_zero]
        rw [← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul (sq_nonneg _), heq]
      · rw [cone_slice_eq_disk_high ht (le_of_not_gt hst) hs1, EuclideanSpace.volume_ball_fin_two]
        have hs2 : 0 ≤ 1 - s ^ 2 := by nlinarith only [hs0,hs1]
        simp only [Set.indicator_of_notMem (show s ∉ Ioo 0 t from fun h => hst h.2),
          Set.indicator_of_mem (show s ∈ Ico t 1 from ⟨le_of_not_gt hst,hs1⟩), zero_add]
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hs2,
          ← ENNReal.ofReal_mul hs2, mul_comm]
    · rw [cone_slice_empty ht.le (Or.inr (le_of_not_gt hs1)), measure_empty]
      simp only [Set.indicator_of_notMem (show s ∉ Ioo 0 t from fun h => hs1 (h.2.trans ht1)),
        Set.indicator_of_notMem (show s ∉ Ico t 1 from fun h => hs1 h.2), add_zero]
  · rw [cone_slice_empty ht.le (Or.inl (le_of_not_gt hs0)), measure_empty]
    simp only [Set.indicator_of_notMem (show s ∉ Ioo 0 t from fun h => hs0 h.1),
      Set.indicator_of_notMem (show s ∉ Ico t 1 from fun h => hs0 (ht.trans_le h.1)), add_zero]

theorem lintegral_sq_Ioo (c a b : ℝ) (hab : a ≤ b) (hc : 0 ≤ c) :
    (∫⁻ s in Ioo a b, ENNReal.ofReal (c * s ^ 2)) =
      ENNReal.ofReal (c * ((b ^ 3 - a ^ 3) / 3)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_pow 2).const_mul c).1]
  · rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · exact Filter.Eventually.of_forall (fun s => mul_nonneg hc (sq_nonneg s))

theorem lintegral_one_sub_sq_Ico {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ s in Ico t 1, ENNReal.ofReal (Real.pi * (1 - s ^ 2))) =
      ENNReal.ofReal (Real.pi * ((1 - t) - (1 - t ^ 3) / 3)) := by
  have hi : IntervalIntegrable (fun s : ℝ => Real.pi * (1 - s ^ 2)) volume t 1 :=
    (intervalIntegrable_const.sub (intervalIntegrable_pow 2)).const_mul Real.pi
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi.1]
  · rw [← intervalIntegral.integral_of_le ht1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegrable_pow 2),
      integral_pow, intervalIntegral.integral_const]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply mul_nonneg Real.pi_pos.le
    have hs0 := ht.trans hs.1.le
    nlinarith only [hs0, hs.2]

theorem volume_sphereCone {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (volume : Measure Position) (sphereCone t) = ENNReal.ofReal ((2 * Real.pi / 3) * (1 - t)) := by
  rw [← sphereHeightSplit_preserving.symm.measure_preimage_emb
    sphereHeightSplit.symm.measurableEmbedding,
    Measure.volume_eq_prod, Measure.prod_apply ((measurableSet_sphereCone t).preimage
      sphereHeightSplit.symm.measurable)]
  have heq : (fun s : ℝ => (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Prod.mk s ⁻¹' (sphereHeightSplit.symm ⁻¹' sphereCone t))) =
      (Ioo 0 t).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * ((1 - t ^ 2) / t ^ 2) * s ^ 2)) +
      (Ico t 1).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * (1 - s ^ 2))) := by
    funext s
    exact cone_slice_area ht ht1 s
  rw [heq]
  change (∫⁻ s : ℝ,
    (Ioo 0 t).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * ((1 - t ^ 2) / t ^ 2) * s ^ 2)) s +
    (Ico t 1).indicator (fun s : ℝ => ENNReal.ofReal (Real.pi * (1 - s ^ 2))) s) = _
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith only [ht, ht1]
  rw [lintegral_add_left ((by fun_prop : Measurable (fun s : ℝ =>
    ENNReal.ofReal (Real.pi * ((1 - t ^ 2) / t ^ 2) * s ^ 2))).indicator measurableSet_Ioo),
      lintegral_indicator measurableSet_Ioo,
    lintegral_indicator measurableSet_Ico, lintegral_sq_Ioo _ _ _ ht.le (by positivity),
    lintegral_one_sub_sq_Ico ht.le ht1.le]
  have hlow : 0 ≤ Real.pi * ((1 - t ^ 2) / t ^ 2) * ((t ^ 3 - 0 ^ 3) / 3) := by
    norm_num only [zero_pow (by norm_num : 2 + 1 ≠ 0), sub_zero]
    positivity
  have hhigh : 0 ≤ Real.pi * ((1 - t) - (1 - t ^ 3) / 3) := by
    have heq : (1 - t) - (1 - t ^ 3) / 3 = (1 - t) ^ 2 * (t + 2) / 3 := by ring
    rw [heq]
    positivity
  rw [← ENNReal.ofReal_add hlow hhigh]
  congr 1
  field_simp [ht.ne']
  ring
theorem unitSphereMeasure_cap {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    unitSphereMeasure {ω : sphere (0 : Position) 1 | t < (ω : Position) 2} =
      ENNReal.ofReal ((1 - t) / 2) := by
  have hm : MeasurableSet {ω : sphere (0 : Position) 1 | t < (ω : Position) 2} := by
    exact isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_subtype_val)
        |>.measurableSet
  rw [unitSphereMeasure, Measure.smul_apply, smul_eq_mul, sphere_area,
    Measure.toSphere_apply' _ hm, cap_cone_eq, volume_sphereCone ht ht1]
  simp only [Position, finrank_euclideanSpace_fin]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 4 * Real.pi),
    ← ENNReal.ofReal_natCast]
  norm_num only [Nat.cast_ofNat]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi)⁻¹),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi)⁻¹ * 3)]
  congr 1
  field_simp
  ring
theorem measurable_sphereHeight :
    Measurable (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_subtype_val).measurable

theorem sphereHeight_Ioi {t : ℝ} (ht : 0 < t) :
    (unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => (ω : Position) 2)) (Ioi t) =
      (ENNReal.ofReal 2)⁻¹ * ENNReal.ofReal (max (1 - t) 0) := by
  rw [Measure.map_apply measurable_sphereHeight measurableSet_Ioi]
  by_cases ht1 : t < 1
  · change unitSphereMeasure {ω : sphere (0 : Position) 1 | t < (ω : Position) 2} = _
    rw [unitSphereMeasure_cap ht ht1, max_eq_left (sub_nonneg.mpr ht1.le)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv, mul_comm]
  · have he : (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) ⁻¹' Ioi t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hnorm : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
      have hc : (ω : Position) 2 ≤ 1 := by
        have h := PiLp.norm_apply_le (ω : Position) 2
        rw [hnorm, Real.norm_eq_abs] at h
        exact (le_abs_self _).trans h
      exact not_lt_of_ge ((le_of_not_gt ht1).trans' hc) hω
    rw [he, measure_empty, max_eq_right (sub_nonpos.mpr (le_of_not_gt ht1)),
      ENNReal.ofReal_zero, mul_zero]

theorem sphereHeight_neg_invariant :
    (unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => (ω : Position) 2)).map
      (fun s : ℝ => -s) =
    unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) := by
  let Q : Position ≃ₗᵢ[ℝ] Position := LinearIsometryEquiv.neg ℝ
  rw [Measure.map_map measurable_neg measurable_sphereHeight]
  have hc : (fun s : ℝ => -s) ∘ (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) =
      (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) ∘ unitSphereRotation Q := by
    funext ω
    rfl
  rw [hc, ← Measure.map_map measurable_sphereHeight (measurable_unitSphereRotation Q),
    map_unitSphereMeasure_rotation]
end LiebThirring

end
