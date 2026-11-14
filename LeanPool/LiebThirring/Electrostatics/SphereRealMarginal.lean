/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Determining a symmetric real probability measure from positive tails

Symmetric probability measures with equal positive upper tails agree. The cap formula then
identifies the sphere height distribution with uniform measure on `[-1,1]`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Reflection symmetry and agreement of strictly positive upper tails determine
an arbitrary real probability measure. -/
lemma symmetric_probability_ext_of_positive_tails
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ.map (fun x => -x) = μ) (hν : ν.map (fun x => -x) = ν)
    (h : ∀ t > 0, μ (Ioi t) = ν (Ioi t)) : μ = ν := by
  have hzero : μ (Ioi 0) = ν (Ioi 0) := by
    let s := fun q : {q : ℚ // 0 < q} => Ioi (q.val : ℝ)
    have hs : Antitone s := by
      intro i j hij
      exact Ioi_subset_Ioi (Rat.cast_le.mpr hij)
    have heq : (⋃ q, s q) = Ioi 0 := by
      ext x
      simp only [mem_iUnion, mem_Ioi]
      constructor
      · rintro ⟨q, hqx⟩
        exact lt_trans (Rat.cast_pos.mpr q.property) hqx
      · intro hx
        obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn hx
        exact ⟨⟨q, Rat.cast_pos.mp hq0⟩, hqx⟩
    rw [← heq, hs.measure_iUnion, hs.measure_iUnion]
    congr 1
    ext q
    exact h q.val (Rat.cast_pos.mpr q.property)
  have hclosed : ∀ b > 0, μ (Ici b) = ν (Ici b) := by
    intro b hb
    let s := fun q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < b} => Ioi (q.val : ℝ)
    have hs : Antitone s := by
      intro i j hij
      exact Ioi_subset_Ioi (Rat.cast_le.mpr hij)
    have heq : (⋂ q, s q) = Ici b := by
      ext x
      simp only [mem_iInter, mem_Ici]
      constructor
      · intro hx
        by_contra hxb
        have hmax : max x 0 < b := max_lt (lt_of_not_ge hxb) hb
        obtain ⟨q, hq0, hqb⟩ := exists_rat_btwn hmax
        have hq : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_right x 0) hq0
        have hqx := hx ⟨q, hq, hqb⟩
        exact (not_lt_of_ge (le_max_left x 0)) (lt_trans hq0 hqx)
      · intro hbx q
        exact lt_of_lt_of_le q.property.2 hbx
    obtain ⟨q, hq0, hqb⟩ := exists_rat_btwn hb
    have hfμ : ∃ q, μ (s q) ≠ ⊤ := ⟨⟨q, hq0, hqb⟩, measure_ne_top μ _⟩
    have hfν : ∃ q, ν (s q) ≠ ⊤ := ⟨⟨q, hq0, hqb⟩, measure_ne_top ν _⟩
    rw [← heq, hs.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet) hfμ,
      hs.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet) hfν]
    congr 1
    ext q
    exact h q.val q.property.1
  apply Measure.ext_of_Iic μ ν
  intro a
  by_cases ha : 0 ≤ a
  · have htail : μ (Ioi a) = ν (Ioi a) := by
      rcases ha.eq_or_lt with ha | ha
      · subst a
        exact hzero
      · exact h a ha
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top μ _),
      measure_compl measurableSet_Ioi (measure_ne_top ν _), measure_univ, measure_univ, htail]
  · have hp : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    have hpre : (fun x : ℝ => -x) ⁻¹' Iic a = Ici (-a) := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_Ici]
      exact neg_le
    calc
      μ (Iic a) = μ (Ici (-a)) := by
        conv_lhs => rw [← hμ, Measure.map_apply measurable_neg measurableSet_Iic, hpre]
      _ = ν (Ici (-a)) := hclosed (-a) hp
      _ = ν (Iic a) := by
        conv_rhs => rw [← hν, Measure.map_apply measurable_neg measurableSet_Iic, hpre]

/-- A symmetric probability distribution with the uniform positive-tail formula
is normalized Lebesgue measure on `[-1, 1]`. -/
theorem eq_uniform_interval_of_symmetric_positive_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun z => -z) = μ)
    (h : ∀ t > 0, μ (Ioi t) = (ENNReal.ofReal 2)⁻¹ * ENNReal.ofReal (max (1 - t) 0)) :
    μ = (ENNReal.ofReal 2)⁻¹ • (volume : Measure ℝ).restrict (Icc (-1) 1) := by
  let ν : Measure ℝ := (ENNReal.ofReal 2)⁻¹ • (volume : Measure ℝ).restrict (Icc (-1) 1)
  have huniv : ν univ = 1 := by
    dsimp [ν]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  let : IsProbabilityMeasure ν := ⟨huniv⟩
  have hpre : (fun z : ℝ => -z) ⁻¹' Icc (-1) 1 = Icc (-1) 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro hx <;> constructor <;> linarith
  have hν : ν.map (fun z => -z) = ν := by
    dsimp [ν]
    rw [Measure.map_smul _ measurable_neg.aemeasurable]
    rw [← hpre, ← measurableEmbedding_neg.restrict_map, Measure.map_neg_eq_self, hpre]
  apply symmetric_probability_ext_of_positive_tails μ ν hμ hν
  intro t ht
  rw [h t ht]
  dsimp [ν]
  rw [Measure.restrict_apply measurableSet_Ioi]
  have hinter : Ioi t ∩ Icc (-1 : ℝ) 1 = Ioc t 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, le_trans (by linarith : (-1 : ℝ) ≤ t) hx.1.le, hx.2⟩
  rw [hinter, Real.volume_Ioc, ENNReal.ofReal_max]
  simp only [ENNReal.ofReal_zero, max_zero]

end LiebThirring

end
