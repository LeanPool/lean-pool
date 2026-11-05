/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.BadPrimeMoments
public import LeanPool.NairTenenbaum.Smooth.SmoothMomentUniformity

/-! # Smooth tails with the full bad-prime mass retained -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The product of the bad-prime and good-part smooth-moment constants. -/
noncomputable def splitSmoothTailBound (A B κ : ℝ) (g D : ℕ) : ℝ :=
  badPrimeMomentBound B g D * smoothTailUniformBound A B κ g D

theorem splitSmoothTailBound_pos {A B κ : ℝ} (hB : 0 < B) {g D : ℕ} (hg : 0 < g) (hD : 0 < D) :
    0 < splitSmoothTailBound A B κ g D :=
  mul_pos (badPrimeMomentBound_pos hB hg hD) (smoothTailUniformBound_pos A B κ g D)

/-- The moments of the bad and good parts multiply. The cutoff on the bad
part may depend on the good tuple. -/
theorem PolynomialSystem.split_smooth_moment_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hg : 0 < P.total.natDegree) (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (N : ℕ+) (U : Tuple r → Finset (Tuple r))
    (hbox : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, u i ≤ N)
    (hs : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∑ u ∈ U v, (badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u *
        (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist P.total.natDegree (v i))) *
          (weightedMass P.exponent (u * v) : ℝ) ^ (κ / Real.log z)) ≤
      splitSmoothTailBound A B κ P.total.natDegree P.badDiscriminant *
        ∑ m ∈ positiveUpTo z, P.weight F m := by
  let V := smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N
  let W := fun v => rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist P.total.natDegree (v i)
  let β := κ / Real.log z
  have hβ : 0 ≤ β := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have hW (v : Tuple r) : 0 ≤ W v := mul_nonneg (rootTupleWeight_nonneg P.exponent hF.nonneg P.R v)
    (Finset.prod_nonneg (fun i _ => totientTwist_nonneg _ _))
  have H := sum_split_weightedMass_moment_le P.exponent V U
    (badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical) W hW
    (fun v hv => P.badPrimeTupleKernel_moment_sum_le hA hB hε hβ hg hsmall
      (U v) N (hbox v hv) (hs v hv))
  have HM := P.totient_smooth_moment_uniform hF hA hB hε hκ hz hzκ hgε N
  have H' := H.trans (mul_le_mul_of_nonneg_left HM
    (badPrimeMomentBound_pos (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le)
  simpa only [splitSmoothTailBound, mul_assoc, V, W, β] using H'

/-- The smooth-tail saving is imposed on the original combined prefix mass.
Arbitrarily large bad-prime powers are allowed and accounted for in the constant. -/
theorem PolynomialSystem.split_smooth_tail_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z X : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hX : 0 < X)
    (hg : 0 < P.total.natDegree) (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (N : ℕ+) (U : Tuple r → Finset (Tuple r))
    (hbox : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, u i ≤ N)
    (hs : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∑ u ∈ (U v).filter (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
        badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u *
          (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist P.total.natDegree (v i))) ≤
      splitSmoothTailBound A B κ P.total.natDegree P.badDiscriminant *
        Real.exp (-κ * Real.log X / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m := by
  classical
  let V := smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N
  let W := fun v => rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist P.total.natDegree (v i)
  let β := κ / Real.log z
  have hβ : 0 ≤ β := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have H := sum_sum_tail_le_moment V U
    (fun v u => badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u * W v)
    (fun v u => (weightedMass P.exponent (u * v) : ℝ))
    (fun v u => mul_nonneg (badPrimeTupleKernel_nonneg hA (zero_le_one.trans hB) _ _ u)
      (mul_nonneg (rootTupleWeight_nonneg P.exponent hF.nonneg P.R v)
        (Finset.prod_nonneg (fun i _ => totientTwist_nonneg P.total.natDegree (v i)))))
    (fun _ _ => Nat.cast_nonneg _) hX hβ
  have HM := P.split_smooth_moment_le hF hA hB hε hκ hz hg hgε hsmall hzκ N U hbox hs
  have H' := H.trans (mul_le_mul_of_nonneg_left HM (Real.rpow_nonneg hX.le (-β)))
  have heq : X ^ (-β) = Real.exp (-κ * Real.log X / Real.log z) := by
    rw [Real.rpow_def_of_pos hX]
    dsimp [β]
    congr 1
    ring
  rw [heq] at H'
  simpa only [V, W, mul_assoc, mul_left_comm] using H'

/-- One logarithmic lower bound supplies both moment gaps. -/
theorem split_moment_conditions {g : ℕ} (hg : 0 < g) {ε κ z : ℝ}
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hlog : 8 * (g : ℝ) ^ 2 * κ ≤ Real.log z) :
    (g : ℝ) * ε ≤ 1 / 8 ∧ (g : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4 ∧
      (4 : ℝ) ^ ((g : ℝ) * κ) ≤ z := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hβ : (g : ℝ) ^ 2 * (κ / Real.log z) ≤ 1 / 8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogz).mpr
    linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hε (mul_nonneg hg₀.le (sub_nonneg.mpr hg₁))]
  · nlinarith
  · have hlog4 : Real.log 4 ≤ 3 := by
      have H := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    have H : (g : ℝ) * κ * Real.log 4 ≤ Real.log z := by
      have H₁ := mul_le_mul_of_nonneg_left hlog4 (mul_nonneg hg₀.le hκ)
      have H₂ := mul_nonneg hκ (mul_nonneg hg₀.le (sub_nonneg.mpr hg₁))
      nlinarith
    have H' := Real.exp_le_exp.mpr H
    rw [Real.exp_log (by linarith : 0 < z)] at H'
    simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_comm] using H'

end NairTenenbaum
