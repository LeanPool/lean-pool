/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityRaw
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices

/-!
# Agreement of pressure extensions

The bounded extensions at different exponents define one operator on their
common domains, as in `def:riesz-pressure`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem rieszPressureSignedTest_mul_nonneg (y : ℝ) :
    0 ≤ y * (if 0 < y then (1 : ℝ) else if y < 0 then -1 else 0) := by
  by_cases hpos : 0 < y
  · simp only [ite_eq_left hpos, mul_one]
    exact le_of_lt hpos
  · by_cases hneg : y < 0
    · simp only [ite_eq_right hpos, ite_eq_left hneg, mul_neg_one]
      exact neg_nonneg.mpr (le_of_lt hneg)
    · have hy : y = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hy]

private theorem rieszPressureSignedTest_mul_abs (y : ℝ) :
    y * (if 0 < y then (1 : ℝ) else if y < 0 then -1 else 0) = |y| := by
  by_cases hpos : 0 < y
  · simp [hpos, abs_of_pos hpos]
  · by_cases hneg : y < 0
    · simp [hpos, hneg, abs_of_neg hneg]
    · have hy : y = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hy]

private theorem rieszPressureSpaceTimeComponent_ae_eq_of_memLp_common_l2
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (i j : Fin 3) (g : Vec3 × ℝ → ℝ)
    (hgr : MemLp g (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (hgs : MemLp g (ENNReal.ofReal s) (volume : Measure (Vec3 × ℝ)))
    (hg2 : MemLp g 2 (volume : Measure (Vec3 × ℝ))) :
    rieszPressureSpaceTimeComponentRepresentative r hr i j (hgr.toLp g) =ᵐ[volume]
      rieszPressureSpaceTimeComponentRepresentative s hs i j (hgs.toLp g) := by
  have hR := rieszPressureSpaceTimeComponent_slice_ae_eq r hr i j hgr
  have hS := rieszPressureSpaceTimeComponent_slice_ae_eq s hs i j hgs
  have hg2' : MemLp g (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by simpa using hg2
  have h2 := rieszPressureSpaceTimeComponent_slice_ae_eq 2
    (by norm_num : (1 : ℝ) < 2) i j hg2'
  have hRmeas : Measurable
      (rieszPressureSpaceTimeComponentRepresentative r hr i j (hgr.toLp g)) :=
    rieszPressureSpaceTimeComponentRepresentative_measurable r hr i j (hgr.toLp g)
  have hSmeas : Measurable
      (rieszPressureSpaceTimeComponentRepresentative s hs i j (hgs.toLp g)) :=
    rieszPressureSpaceTimeComponentRepresentative_measurable s hs i j (hgs.toLp g)
  apply ae_eq_of_ae_time_sections hRmeas hSmeas
  filter_upwards [hR, hS, h2] with t hRt hSt h2t
  obtain ⟨hGrt, hRsl⟩ := hRt
  obtain ⟨hGst, hSsl⟩ := hSt
  obtain ⟨hG2t, _h2sl⟩ := h2t
  have hG2t' : MemLp (fun x : Vec3 => g (x, t)) 2 volume := by
    simpa using hG2t
  have hOp := rieszPressureOperator_ae_eq_of_memLp_common
    r hr s hs i j (fun x : Vec3 => g (x, t)) hGrt hGst hG2t'
  exact hRsl.trans (hOp.trans hSsl.symm)

private theorem rieszPressureSpaceTimeComponent_coe_ae_eq_of_memLp_common_l2
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (i j : Fin 3) (g : Vec3 × ℝ → ℝ)
    (hgr : MemLp g (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (hgs : MemLp g (ENNReal.ofReal s) (volume : Measure (Vec3 × ℝ)))
    (hg2 : MemLp g 2 (volume : Measure (Vec3 × ℝ))) :
    (rieszPressureSpaceTimeComponent r hr i j (hgr.toLp g) : Vec3 × ℝ → ℝ) =ᵐ[volume]
      (rieszPressureSpaceTimeComponent s hs i j (hgs.toLp g) : Vec3 × ℝ → ℝ) := by
  have hRep := rieszPressureSpaceTimeComponent_ae_eq_of_memLp_common_l2
    r hr s hs i j g hgr hgs hg2
  have hR := (Lp.aestronglyMeasurable
    (rieszPressureSpaceTimeComponent r hr i j (hgr.toLp g))).aemeasurable.ae_eq_mk
  have hS := (Lp.aestronglyMeasurable
    (rieszPressureSpaceTimeComponent s hs i j (hgs.toLp g))).aemeasurable.ae_eq_mk
  exact hR.trans (hRep.trans hS.symm)

private theorem rieszPressureBoundedTest_memLp
    (n : ℕ) (g : Vec3 × ℝ → ℝ) (hg : Measurable g) :
    ∀ p : ℝ, MemLp
      ((Metric.closedBall (0 : Vec3 × ℝ) (n : ℝ)).indicator
        (fun x => if 0 < g x then (1 : ℝ) else if g x < 0 then -1 else 0))
      (ENNReal.ofReal p) (volume : Measure (Vec3 × ℝ)) := by
  intro p
  let B : Set (Vec3 × ℝ) := Metric.closedBall 0 (n : ℝ)
  let σ : Vec3 × ℝ → ℝ := fun x => if 0 < g x then 1 else if g x < 0 then -1 else 0
  have hB : IsCompact B := by
    exact isCompact_closedBall 0 (n : ℝ)
  have hSupport : HasCompactSupport (B.indicator σ) := by
    apply HasCompactSupport.of_support_subset_isCompact hB
    intro x hx
    by_contra hxB
    change B.indicator σ x ≠ 0 at hx
    exact hx (Set.indicator_of_notMem hxB σ)
  have hσ : Measurable σ := by
    dsimp [σ]
    exact Measurable.ite (by measurability) measurable_const
      (Measurable.ite (by measurability) measurable_const measurable_const)
  have hmeas : AEStronglyMeasurable (B.indicator σ)
      (volume : Measure (Vec3 × ℝ)) := by
    exact hσ.aestronglyMeasurable.indicator measurableSet_closedBall
  have hbound : ∀ᵐ x ∂(volume : Measure (Vec3 × ℝ)), ‖B.indicator σ x‖ ≤ 1 := by
    filter_upwards [] with x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx, σ]
      split_ifs <;> norm_num
    · simp [Set.indicator_of_notMem hx]
  exact hSupport.memLp_of_bound hmeas 1 hbound

theorem rieszPressureSpaceTime_ae_eq_of_memLp_common
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hFr : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hFs : ∀ i j, MemLp (F i j) (ENNReal.ofReal s)
      (volume : Measure (Vec3 × ℝ))) :
    rieszPressureSpaceTime r hr F hFr =ᵐ[volume]
      rieszPressureSpaceTime s hs F hFs := by
  let PR : Vec3 × ℝ → ℝ := rieszPressureSpaceTime r hr F hFr
  let PS : Vec3 × ℝ → ℝ := rieszPressureSpaceTime s hs F hFs
  have hPRmeas : Measurable PR := rieszPressureSpaceTime_measurable r hr F hFr
  have hPSmeas : Measurable PS := rieszPressureSpaceTime_measurable s hs F hFs
  have hPRmem : MemLp PR (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp r hr F hFr
  have hPSmem : MemLp PS (ENNReal.ofReal s) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp s hs F hFs
  let qR : ℝ := Real.conjExponent r
  let qS : ℝ := Real.conjExponent s
  have hqR : 1 < qR := by
    dsimp [qR, Real.conjExponent]
    rw [lt_div_iff₀ (sub_pos.mpr hr)]
    linarith only [hr]
  have hqS : 1 < qS := by
    dsimp [qS, Real.conjExponent]
    rw [lt_div_iff₀ (sub_pos.mpr hs)]
    linarith only [hs]
  have hHolderR : r.HolderConjugate qR := by
    exact Real.HolderConjugate.conjExponent hr
  have hHolderS : s.HolderConjugate qS := by
    exact Real.HolderConjugate.conjExponent hs
  let B : ℕ → Set (Vec3 × ℝ) := fun n => Metric.closedBall 0 (n : ℝ)
  have hBunion : (⋃ n, B n) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    refine ⟨n, ?_⟩
    simpa [B, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hn.le
  have hOnBall : ∀ n, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ B n → PR z = PS z := by
    intro n
    let G : Vec3 × ℝ → ℝ := (B n).indicator
      (fun z => if 0 < PR z - PS z then 1 else if PR z - PS z < 0 then -1 else 0)
    have hGmeas : Measurable G := by
      dsimp [G]
      have hmPos : MeasurableSet {z : Vec3 × ℝ | 0 < PR z - PS z} := by
        measurability
      have hmNeg : MeasurableSet {z : Vec3 × ℝ | PR z - PS z < 0} := by
        measurability
      exact (Measurable.ite hmPos measurable_const
        (Measurable.ite hmNeg measurable_const measurable_const)).indicator
          measurableSet_closedBall
    have hGmemR : MemLp G (ENNReal.ofReal qR) (volume : Measure (Vec3 × ℝ)) := by
      simpa [G] using rieszPressureBoundedTest_memLp n (PR - PS)
        (hPRmeas.sub hPSmeas) qR
    have hGmemS : MemLp G (ENNReal.ofReal qS) (volume : Measure (Vec3 × ℝ)) := by
      simpa [G] using rieszPressureBoundedTest_memLp n (PR - PS)
        (hPRmeas.sub hPSmeas) qS
    have hGmem2 : MemLp G 2 (volume : Measure (Vec3 × ℝ)) := by
      have h := rieszPressureBoundedTest_memLp n (PR - PS)
        (hPRmeas.sub hPSmeas) 2
      simpa [G] using h
    have hDualR := rieszPressureSpaceTime_duality r hr qR hqR hHolderR F hFr G hGmemR
    have hDualS := rieszPressureSpaceTime_duality s hs qS hqS hHolderS F hFs G hGmemS
    have hTerms : ∀ i j,
        ∫ z, F i j z *
          (rieszPressureSpaceTimeComponent qR hqR j i (hGmemR.toLp G) :
            Vec3 × ℝ → ℝ) z =
        ∫ z, F i j z *
          (rieszPressureSpaceTimeComponent qS hqS j i (hGmemS.toLp G) :
            Vec3 × ℝ → ℝ) z := by
      intro i j
      have hComp := rieszPressureSpaceTimeComponent_coe_ae_eq_of_memLp_common_l2
        qR hqR qS hqS j i G hGmemR hGmemS hGmem2
      apply integral_congr_ae
      filter_upwards [hComp] with z hz
      rw [hz]
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, F i j z *
            (rieszPressureSpaceTimeComponent qR hqR j i (hGmemR.toLp G) :
              Vec3 × ℝ → ℝ) z) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, F i j z *
            (rieszPressureSpaceTimeComponent qS hqS j i (hGmemS.toLp G) :
              Vec3 × ℝ → ℝ) z := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hTerms i j
    have hpair : ∫ z, PR z * G z = ∫ z, PS z * G z := by
      calc
        ∫ z, PR z * G z =
            ∑ i : Fin 3, ∑ j : Fin 3,
              ∫ z, F i j z *
                (rieszPressureSpaceTimeComponent qR hqR j i (hGmemR.toLp G) :
                  Vec3 × ℝ → ℝ) z := by
          simpa [PR] using hDualR
        _ = ∑ i : Fin 3, ∑ j : Fin 3,
              ∫ z, F i j z *
                (rieszPressureSpaceTimeComponent qS hqS j i (hGmemS.toLp G) :
                  Vec3 × ℝ → ℝ) z := hsum
        _ = ∫ z, PS z * G z := by
          simpa [PS] using hDualS.symm
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    have : Fact (1 ≤ ENNReal.ofReal qR) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hqR.le⟩
    let _ : (ENNReal.ofReal r).HolderTriple (ENNReal.ofReal qR) 1 :=
      ENNReal.HolderTriple.of_toReal (by
        simpa [ENNReal.toReal_ofReal (lt_trans zero_lt_one hr).le,
          ENNReal.toReal_ofReal (lt_trans zero_lt_one hqR).le] using hHolderR)
    have : Fact (1 ≤ ENNReal.ofReal s) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hs.le⟩
    have : Fact (1 ≤ ENNReal.ofReal qS) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hqS.le⟩
    let _ : (ENNReal.ofReal s).HolderTriple (ENNReal.ofReal qS) 1 :=
      ENNReal.HolderTriple.of_toReal (by
        simpa [ENNReal.toReal_ofReal (lt_trans zero_lt_one hs).le,
          ENNReal.toReal_ofReal (lt_trans zero_lt_one hqS).le] using hHolderS)
    have hprodIntR : Integrable (fun z => PR z * G z) (volume : Measure (Vec3 × ℝ)) := by
      exact hPRmem.integrable_mul hGmemR
    have hprodIntS : Integrable (fun z => PS z * G z) (volume : Measure (Vec3 × ℝ)) := by
      exact hPSmem.integrable_mul hGmemS
    have hdiffInt : Integrable (fun z => (PR z - PS z) * G z)
        (volume : Measure (Vec3 × ℝ)) := by
      apply (hprodIntR.sub hprodIntS).congr
      filter_upwards [] with z
      change PR z * G z - PS z * G z = (PR z - PS z) * G z
      ring
    have hdiffNonneg : 0 ≤ᵐ[volume] fun z => (PR z - PS z) * G z := by
      filter_upwards [] with z
      dsimp [G]
      by_cases hzB : z ∈ B n
      · rw [Set.indicator_of_mem hzB]
        exact rieszPressureSignedTest_mul_nonneg (PR z - PS z)
      · rw [Set.indicator_of_notMem hzB]
        simp
    have hpair' : ∫ z, (PR z - PS z) * G z = 0 := by
      have hcalc : (fun z => (PR z - PS z) * G z) =
          (fun z => PR z * G z - PS z * G z) := by
        funext z
        ring
      rw [hcalc, integral_sub hprodIntR hprodIntS, hpair, sub_self]
    have hdiffZero : (fun z => (PR z - PS z) * G z) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hdiffNonneg hdiffInt).mp hpair'
    filter_upwards [hdiffZero] with z hz
    intro hzB
    have hsign : (PR z - PS z) * G z = |PR z - PS z| := by
      simpa [G, hzB] using rieszPressureSignedTest_mul_abs (PR z - PS z)
    have hz0 : (PR z - PS z) * G z = 0 := by simpa using hz
    rw [hsign] at hz0
    exact sub_eq_zero.mp (abs_eq_zero.mp hz0)
  have hAll : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ∀ n, z ∈ B n → PR z = PS z := ae_all_iff.mpr hOnBall
  have hInUnion : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), z ∈ ⋃ n, B n := by
    rw [hBunion]
    exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  filter_upwards [hAll, hInUnion] with z hzall hzunion
  obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzunion
  exact hzall n hzn

end CKN.Leray

end
