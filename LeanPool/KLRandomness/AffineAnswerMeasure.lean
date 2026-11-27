/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.RemainingRank
import Mathlib.Tactic.NormNum

/-!
# Fair-coin translations and conditional answer probabilities

Adding a fixed binary-field sequence to the input preserves the concrete
infinite-product fair-coin measure.  If such a translation preserves a
conditioning event and flips a queried coordinate, the conditional answer is
fair.  This supplies the measure step for affine kernel translations.
-/

@[expose] public section

namespace Klr.AffineAnswer

open MeasureTheory ProbabilityTheory FiniteMeasure
open scoped ENNReal

/-- Translate a bit by an element of the binary field. -/
def translateBit (a : ZMod 2) : Bool ≃ Bool where
  toFun b := boolEquivF2.symm (boolEquivF2 b + a)
  invFun b := boolEquivF2.symm (boolEquivF2 b - a)
  left_inv b := by simp
  right_inv b := by simp

@[simp] theorem boolEquivF2_translateBit (a : ZMod 2) (b : Bool) :
    boolEquivF2 (translateBit a b) = boolEquivF2 b + a := by
  simp [translateBit]

@[simp] theorem translateBit_zero (b : Bool) : translateBit 0 b = b := by
  simp [translateBit]

@[simp] theorem translateBit_one (b : Bool) : translateBit 1 b = !b := by
  cases b <;> apply boolEquivF2.injective <;> norm_num
  exact ZMod.natCast_self 2

/-- Coordinatewise translation by a fixed binary-field sequence. -/
def translate (z : ℕ → ZMod 2) (X : Cantor) : Cantor :=
  fun n => translateBit (z n) (X n)

theorem measurable_translate (z : ℕ → ZMod 2) : Measurable (translate z) := by
  apply Measurable.of_eval
  intro n
  exact (Measurable.of_discrete (f := translateBit (z n))).comp (measurable_pi_apply n)

theorem fairBit_map_translateBit (a : ZMod 2) : fairBit.map (translateBit a) = fairBit := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (Measurable.of_discrete (f := translateBit a))
    (measurableSet_singleton b)]
  have he : (translateBit a) ⁻¹' {b} = {(translateBit a).symm b} := by
    ext x
    change translateBit a x = b ↔ x = (translateBit a).symm b
    exact (translateBit a).eq_symm_apply.symm
  rw [he, fairBit_singleton, fairBit_singleton]

/-- Translation invariance of the actual infinite-product fair-coin measure. -/
theorem fairCoin_map_translate (z : ℕ → ZMod 2) :
    fairCoin.map (translate z) = fairCoin := by
  unfold fairCoin translate
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => fairBit)
    (fun n => Measurable.of_discrete (f := translateBit (z n)))]
  simp only [fairBit_map_translateBit]

/-- A translation vanishing on an event's supporting coordinates preserves that event. -/
theorem translate_mem_of_dependsOn (H : Set Cantor) (S : Set ℕ)
    (hH : DependsOn (fun X : Cantor => X ∈ H) S) (z : ℕ → ZMod 2)
    (hz : ∀ n ∈ S, z n = 0) (X : Cantor) : translate z X ∈ H ↔ X ∈ H := by
  apply iff_of_eq
  apply hH
  intro n hn
  simp [translate, hz n hn]

/-- One specified input bit. -/
def bitEvent (q : ℕ) (b : Bool) : Set Cantor := {X | X q = b}

theorem measurableSet_bitEvent (q : ℕ) (b : Bool) : MeasurableSet (bitEvent q b) := by
  change MeasurableSet ((fun X : Cantor => X q) ⁻¹' ({b} : Set Bool))
  exact (measurable_pi_apply q) (measurableSet_singleton b)

/-- A translation preserving a history and flipping its next bit equates the two
answer probabilities, even for a null history. -/
theorem fairCoin_inter_bit_eq_of_translation (H : Set Cantor) (hH : MeasurableSet H)
    (z : ℕ → ZMod 2) (hinv : ∀ X, translate z X ∈ H ↔ X ∈ H)
    (q : ℕ) (hz : z q = 1) :
    fairCoin (H ∩ bitEvent q false) = fairCoin (H ∩ bitEvent q true) := by
  have he : translate z ⁻¹' (H ∩ bitEvent q true) = H ∩ bitEvent q false := by
    ext X
    simp [hinv, bitEvent, translate, hz]
  calc
    fairCoin (H ∩ bitEvent q false) =
        fairCoin (translate z ⁻¹' (H ∩ bitEvent q true)) := by rw [he]
    _ = (fairCoin.map (translate z)) (H ∩ bitEvent q true) :=
      (Measure.map_apply (measurable_translate z) (hH.inter (measurableSet_bitEvent q true))).symm
    _ = _ := by rw [fairCoin_map_translate]

/-- A symmetry interchanging the two answers makes the conditional next bit fair.
The explicit nonnull hypothesis is precisely compatibility of this history. -/
theorem cond_bit_eq_half_of_translation (H : Set Cantor) (hH : MeasurableSet H)
    (hpos : fairCoin H ≠ 0) (z : ℕ → ZMod 2)
    (hinv : ∀ X, translate z X ∈ H ↔ X ∈ H) (q : ℕ) (hz : z q = 1) (b : Bool) :
    (cond fairCoin H) (bitEvent q b) = (1 / 2 : ℝ≥0∞) := by
  have heq := fairCoin_inter_bit_eq_of_translation H hH z hinv q hz
  have hdis : Disjoint (H ∩ bitEvent q false) (H ∩ bitEvent q true) := by
    apply Set.disjoint_left.mpr
    intro X hx hy
    exact Bool.false_ne_true (hx.2.symm.trans hy.2)
  have hunion : (H ∩ bitEvent q false) ∪ (H ∩ bitEvent q true) = H := by
    ext X
    cases hb : X q <;> simp [bitEvent, hb]
  have hsum : fairCoin H = fairCoin (H ∩ bitEvent q false) +
      fairCoin (H ∩ bitEvent q true) := by
    calc
      fairCoin H = fairCoin ((H ∩ bitEvent q false) ∪ (H ∩ bitEvent q true)) := by
        rw [hunion]
      _ = _ := measure_union hdis (hH.inter (measurableSet_bitEvent q true))
  have htwo : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  have hhalf (a : Bool) : fairCoin (H ∩ bitEvent q a) =
      (1 / 2 : ℝ≥0∞) * fairCoin H := by
    cases a
    · rw [hsum, ← heq, ← two_mul, ← mul_assoc, htwo, one_mul]
    · rw [← heq, hsum, ← heq, ← two_mul, ← mul_assoc, htwo, one_mul]
  rw [cond_apply hH, hhalf, mul_left_comm,
    ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), mul_one]

/-- If a compatible history determines the bit, its conditional probability is one,
and the probability of the opposite bit is zero. -/
theorem cond_bit_eq_one_zero_of_subset (H : Set Cantor) (hH : MeasurableSet H)
    (hpos : fairCoin H ≠ 0) (q : ℕ) (b : Bool) (hsub : H ⊆ bitEvent q b) :
    (cond fairCoin H) (bitEvent q b) = 1 ∧
      (cond fairCoin H) (bitEvent q (!b)) = 0 := by
  constructor
  · rw [cond_apply hH, Set.inter_eq_left.mpr hsub,
      ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)]
  · have he : H ∩ bitEvent q (!b) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro X hX
      have hb := (hsub hX.1).symm.trans hX.2
      cases b <;> cases hb
    rw [cond_apply hH, he, measure_empty, mul_zero]

end Klr.AffineAnswer
