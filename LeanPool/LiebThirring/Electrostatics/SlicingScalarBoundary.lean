/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingIntervals

/-!
# Genuine endpoints of a finite halfspace slice

The scalar boundary bookkeeping for the cell divergence theorem: a finite
endpoint is either an artificial outer endpoint, where the compact field
vanishes, or the unique genuine facet having the appropriate orientation.
-/

public section

namespace LiebThirring

/-- The value of a scalar field at a genuine transverse constraint endpoint. -/
@[expose] noncomputable def halfspaceFaceValue {ι : Type*}
    (a b : ι → ℝ) (g : ℝ → ℝ) (i : ι) : ℝ := by
  classical
  exact if ∀ j, j ≠ i → (b i / a i) * a j < b j then g (b i / a i) else 0

/-- Positive-oriented genuine facets give precisely the value at the upper end. -/
theorem sum_positive_halfspaceFaceValue {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (g : ℝ → ℝ) (U B : ℝ)
    (hmin : ∀ i, 0 < a i → U ≤ b i / a i)
    (hclosed : ∀ i, U * a i ≤ b i)
    (hregular : ∀ i j, i ≠ j → U * a i = b i → U * a j = b j → False)
    (hupper : U = B ∨ ∃ i, 0 < a i ∧ U = b i / a i)
    (hzero : ∀ t, B ≤ t → g t = 0) :
    (∑ i : ι, if 0 < a i then halfspaceFaceValue a b g i else 0) = g U := by
  classical
  rcases hupper with he | ⟨i, hi, he⟩
  · rw [he, hzero B le_rfl]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : 0 < a i
    · rw [ite_eq_left hi]
      unfold halfspaceFaceValue
      split_ifs with hf
      · exact hzero _ (he ▸ hmin i hi)
      · rfl
    · exact ite_eq_right hi
  · have hei : U * a i = b i := by rw [he, div_mul_cancel₀ _ hi.ne']
    have hface : ∀ j, j ≠ i → U * a j < b j := by
      intro j hj
      apply lt_of_le_of_ne (hclosed j)
      intro hej
      exact hregular i j hj.symm hei hej
    have hs : (∑ j : ι, if 0 < a j then halfspaceFaceValue a b g j else 0) =
        (if 0 < a i then halfspaceFaceValue a b g i else 0) := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        by_cases hjpos : 0 < a j
        · rw [ite_eq_left hjpos]
          unfold halfspaceFaceValue
          split_ifs with hjface
          · have hlt : b j / a j < U := by
              rw [he]
              exact (lt_div_iff₀ hi).mpr (hjface i hj.symm)
            exact False.elim (not_lt_of_ge (hmin j hjpos) hlt)
          · rfl
        · exact ite_eq_right hjpos
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i))
    rw [hs, ite_eq_left hi, halfspaceFaceValue]
    rw [ite_eq_left (he ▸ hface)]
    rw [← he]

theorem halfspaceFaceValue_reflect {ι : Type*} (a b : ι → ℝ) (g : ℝ → ℝ) (i : ι) :
    halfspaceFaceValue (fun i => -a i) b (fun t => g (-t)) i =
      halfspaceFaceValue a b g i := by
  unfold halfspaceFaceValue
  dsimp only
  have he : (∀ j, j ≠ i → (b i / -a i) * (-a j) < b j) ↔
      (∀ j, j ≠ i → (b i / a i) * a j < b j) := by
    apply forall_congr'
    intro j
    rw [div_neg, neg_mul_neg]
  simp only [div_neg, neg_neg]
  by_cases hf : ∀ j, j ≠ i → (b i / a i) * a j < b j
  · rw [ite_eq_left (he.mpr hf), ite_eq_left hf]
  · rw [ite_eq_right (fun hn => hf (he.mp hn)), ite_eq_right hf]

/-- Negative-oriented genuine facets give precisely the value at the lower end. -/
theorem sum_negative_halfspaceFaceValue {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (g : ℝ → ℝ) (L A : ℝ)
    (hmax : ∀ i, a i < 0 → b i / a i ≤ L)
    (hclosed : ∀ i, L * a i ≤ b i)
    (hregular : ∀ i j, i ≠ j → L * a i = b i → L * a j = b j → False)
    (hlower : L = A ∨ ∃ i, a i < 0 ∧ L = b i / a i)
    (hzero : ∀ t, t ≤ A → g t = 0) :
    (∑ i : ι, if a i < 0 then halfspaceFaceValue a b g i else 0) = g L := by
  have hmin' (i : ι) (hi : 0 < -a i) : -L ≤ b i / -a i := by
    rw [div_neg]
    exact neg_le_neg (hmax i (neg_pos.mp hi))
  have hclosed' (i : ι) : (-L) * (-a i) ≤ b i := by simpa only [neg_mul_neg] using hclosed i
  have hreg' (i j : ι) (hij : i ≠ j) (hi : (-L) * (-a i) = b i)
      (hj : (-L) * (-a j) = b j) : False :=
    hregular i j hij (by simpa only [neg_mul_neg] using hi) (by simpa only [neg_mul_neg] using hj)
  have hupper' : -L = -A ∨ ∃ i, 0 < -a i ∧ -L = b i / -a i := by
    rcases hlower with he | ⟨i, hi, he⟩
    · exact Or.inl (congrArg Neg.neg he)
    · exact Or.inr ⟨i, neg_pos.mpr hi, by rw [he, div_neg]⟩
  have hzero' (t : ℝ) (ht : -A ≤ t) : g (-t) = 0 := hzero _ (by linarith only [ht])
  have hh := sum_positive_halfspaceFaceValue (fun i => -a i) b (fun t => g (-t))
    (-L) (-A) hmin' hclosed' hreg' hupper' hzero'
  simpa only [neg_pos, halfspaceFaceValue_reflect, neg_neg] using hh

end LiebThirring

end
