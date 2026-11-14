/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingScalarBoundary
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar fundamental theorem on a finite halfspace slice

Integration of a compactly supported scalar derivative over the interval
cut out by finitely many affine inequalities, with the endpoints written as
the signed sum of genuine transverse constraint values.
-/

public section

open Set MeasureTheory

namespace LiebThirring

theorem integral_derivative_finite_halfspaces {ι : Type*} [Fintype ι]
    (a b : ι → ℝ)
    (hregular : ∀ t i j, i ≠ j → (∀ p, t * a p ≤ b p) →
      t * a i = b i → t * a j = b j → False)
    (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hgc : HasCompactSupport g) (hg'c : HasCompactSupport g') :
    (∫ t in {t | ∀ i, t * a i < b i}, g' t) =
      (∑ i : ι, if 0 < a i then halfspaceFaceValue a b g i else 0) -
        ∑ i : ι, if a i < 0 then halfspaceFaceValue a b g i else 0 := by
  classical
  by_cases hnonempty : ∃ t, ∀ i, t * a i < b i
  · obtain ⟨t₀, h₀⟩ := hnonempty
    obtain ⟨C, hC⟩ := (hgc.isCompact.union hg'c.isCompact).isBounded.exists_norm_le
    let D : ℝ := max C |t₀| + 1
    have hDC : C < D := by dsimp [D]; linarith only [le_max_left C |t₀|]
    have hDt₀ : |t₀| < D := by dsimp [D]; linarith only [le_max_right C |t₀|]
    have hzero (t : ℝ) (ht : t ≤ -D ∨ D ≤ t) : g t = 0 ∧ g' t = 0 := by
      have hn : C < ‖t‖ := by
        rw [Real.norm_eq_abs]
        rcases ht with ht | ht
        · linarith only [hDC, ht, neg_le_abs t]
        · exact hDC.trans_le (ht.trans (le_abs_self t))
      constructor
      · apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact (not_le_of_gt hn) (hC t (Or.inl hm))
      · apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact (not_le_of_gt hn) (hC t (Or.inr hm))
    have hA : -D < t₀ := by linarith only [hDt₀, neg_le_abs t₀]
    have hB : t₀ < D := (le_abs_self t₀).trans_lt hDt₀
    obtain ⟨L, U, hAL, hLt₀, ht₀U, hUB, hp, hm, hup, hlo, hinterval⟩ :=
      exists_truncated_halfspace_interval a b hA hB h₀
    have hLU : L < U := hLt₀.trans ht₀U
    have hclosedL (i : ι) : L * a i ≤ b i := by
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · exact (div_le_iff_of_neg hi).mp (hm i hi)
      · simpa only [hi, mul_zero] using (h₀ i).le
      · exact ((lt_div_iff₀ hi).mp (hLU.trans_le (hp i hi))).le
    have hclosedU (i : ι) : U * a i ≤ b i := by
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · exact ((div_lt_iff_of_neg hi).mp ((hm i hi).trans_lt hLU)).le
      · simpa only [hi, mul_zero] using (h₀ i).le
      · exact (le_div_iff₀ hi).mp (hp i hi)
    have hpositive := sum_positive_halfspaceFaceValue a b g U D hp hclosedU
      (fun i j hij => hregular U i j hij hclosedU) hup
      (fun t ht => (hzero t (Or.inr ht)).1)
    have hnegative := sum_negative_halfspaceFaceValue a b g L (-D) hm hclosedL
      (fun i j hij => hregular L i j hij hclosedL) hlo
      (fun t ht => (hzero t (Or.inl ht)).1)
    have hset : MeasurableSet {t : ℝ | ∀ i, t * a i < b i} := by
      have he : {t : ℝ | ∀ i, t * a i < b i} = ⋂ i, {t : ℝ | t * a i < b i} := by
        ext t; simp only [mem_ofPred_eq, mem_iInter]
      rw [he]
      exact (isOpen_iInter_of_finite (fun i =>
        isOpen_lt (show Continuous (fun t : ℝ => t * a i) from continuous_id.mul continuous_const)
          continuous_const)).measurableSet
    have he : {t : ℝ | ∀ i, t * a i < b i}.indicator g' = (Ioo L U).indicator g' := by
      ext t
      by_cases ht : -D < t ∧ t < D
      · have hs : (∀ i, t * a i < b i) ↔ L < t ∧ t < U := by
          simpa only [ht.1, ht.2, and_true] using hinterval t
        by_cases hc : ∀ i, t * a i < b i
        · rw [indicator_of_mem (show t ∈ {t : ℝ | ∀ i, t * a i < b i} from hc),
            indicator_of_mem (show t ∈ Ioo L U from hs.mp hc)]
        · rw [indicator_of_notMem (show t ∉ {t : ℝ | ∀ i, t * a i < b i} from hc),
            indicator_of_notMem (show t ∉ Ioo L U from fun h => hc (hs.mpr h))]
      · have hz := (hzero t (by simpa only [not_and_or, not_lt] using ht)).2
        simp only [indicator, hz, ite_self]
    rw [hpositive, hnegative, ← integral_indicator hset, he,
      integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hLU.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
      (hg'.intervalIntegrable L U)
  · have hempty : {t : ℝ | ∀ i, t * a i < b i} = ∅ := by
      ext t
      exact iff_false_intro (fun ht => hnonempty ⟨t, ht⟩)
    have hfacezero (i : ι) (hi : a i ≠ 0) : halfspaceFaceValue a b g i = 0 := by
      unfold halfspaceFaceValue
      split_ifs with hf
      · exact False.elim (hnonempty (exists_strict_halfspace_of_face a b i hi hf))
      · rfl
    have hpos : (∑ i : ι, if 0 < a i then halfspaceFaceValue a b g i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact hfacezero i hi.ne'
      · rfl
    have hneg : (∑ i : ι, if a i < 0 then halfspaceFaceValue a b g i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact hfacezero i hi.ne
      · rfl
    rw [hempty, setIntegral_empty, hpos, hneg, sub_self]

end LiebThirring

end
