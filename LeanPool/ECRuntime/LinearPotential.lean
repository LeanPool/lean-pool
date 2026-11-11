/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.Objective
public import LeanPool.ECRuntime.Transition
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

/-!
# Linear Potential

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Positive linear pseudo-Boolean instances, normalized to have the all-one optimum. -/
def PositiveLinearWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ i, 0 < w i

/-- A convenient ordering convention for later linear-function drift proofs. -/
def NonincreasingLinearWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ i j, i.val ≤ j.val → w j ≤ w i

/-- Weighted error potential: positive coefficient `g i` for each zero bit. -/
def linearErrorPotential {n : ℕ} (g : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ i, g i * bitValueReal (!(x i))

@[simp] theorem linearErrorPotential_allOnes {n : ℕ} (g : Fin n → ℝ) :
    linearErrorPotential g (allOnes n) = 0 := by
  simp [linearErrorPotential, allOnes]

/-- Nonnegative potential coefficients give a nonnegative error potential. -/
theorem linearErrorPotential_nonneg {n : ℕ}
    (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) (x : BitString n) :
    0 ≤ linearErrorPotential g x := by
  unfold linearErrorPotential
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hg i) (by cases x i <;> simp [bitValueReal])

/--
Rank-based coefficients for the classical Doerr--Johannsen--Winzen linear-function
analysis, written in the reversed coordinate convention used here.  Their coefficients
`1 + i/n` increase with objective importance; because our coordinate `0` is the most
important one, the equivalent coefficients are `2 - (i+1)/n`.
-/
noncomputable def rankPotentialWeight (n : ℕ) (i : Fin n) : ℝ :=
  2 - ((i.val + 1 : ℕ) : ℝ) / (n : ℝ)

/-- Rank-potential coefficients are at least one in positive dimension. -/
theorem one_le_rankPotentialWeight {n : ℕ} (hn : 0 < n) (i : Fin n) :
    1 ≤ rankPotentialWeight n i := by
  unfold rankPotentialWeight
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiNat : i.val + 1 ≤ n := by omega
  have hi : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hiNat
  have hratio : ((i.val + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 :=
    (div_le_one hnreal).2 hi
  linarith

/-- The rank-based error potential proposed for the first linear-function formalization. -/
noncomputable def rankLinearPotential {n : ℕ} (x : BitString n) : ℝ :=
  linearErrorPotential (rankPotentialWeight n) x

@[simp] theorem rankLinearPotential_allOnes (n : ℕ) :
    rankLinearPotential (allOnes n) = 0 := by
  simp [rankLinearPotential]

/-- The rank potential is nonnegative in positive dimension. -/
theorem rankLinearPotential_nonneg {n : ℕ} (hn : 0 < n) (x : BitString n) :
    0 ≤ rankLinearPotential x := by
  unfold rankLinearPotential
  apply linearErrorPotential_nonneg
  intro i
  exact zero_le_one.trans (one_le_rankPotentialWeight hn i)

/-- The rank-potential coefficients never exceed two. -/
theorem rankPotentialWeight_le_two {n : ℕ} (i : Fin n) :
    rankPotentialWeight n i ≤ 2 := by
  unfold rankPotentialWeight
  have hnum : 0 ≤ (((i.val + 1 : ℕ) : ℝ)) := by positivity
  have hden : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdiv : 0 ≤ (((i.val + 1 : ℕ) : ℝ) / (n : ℝ)) :=
    div_nonneg hnum hden
  linarith

/-- Real-valued zero count as a sum of real-valued complemented bits. -/
theorem zeroCount_cast_eq_sum_bitValueReal_not {n : ℕ} (x : BitString n) :
    (zeroCount x : ℝ) = ∑ i, bitValueReal (!(x i)) := by
  unfold zeroCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp [bitValue, bitValueReal]

/-- If all error coefficients are at least one, weighted error dominates Hamming error. -/
theorem zeroCount_le_linearErrorPotential {n : ℕ}
    (g : Fin n → ℝ) (hg : ∀ i, 1 ≤ g i) (x : BitString n) :
    (zeroCount x : ℝ) ≤ linearErrorPotential g x := by
  rw [zeroCount_cast_eq_sum_bitValueReal_not]
  unfold linearErrorPotential
  apply Finset.sum_le_sum
  intro i hi
  cases hxi : x i <;> simp [bitValueReal, hg i]

/-- If all error coefficients are at most two, weighted error is at most twice Hamming error. -/
theorem linearErrorPotential_le_two_mul_zeroCount {n : ℕ}
    (g : Fin n → ℝ) (hg : ∀ i, g i ≤ 2) (x : BitString n) :
    linearErrorPotential g x ≤ 2 * (zeroCount x : ℝ) := by
  have hsum :
      linearErrorPotential g x ≤ ∑ i, 2 * bitValueReal (!(x i)) := by
    unfold linearErrorPotential
    apply Finset.sum_le_sum
    intro i hi
    cases hxi : x i <;> simp [bitValueReal, hg i]
  calc
    linearErrorPotential g x ≤ ∑ i, 2 * bitValueReal (!(x i)) := hsum
    _ = 2 * (∑ i, bitValueReal (!(x i))) := by rw [Finset.mul_sum]
    _ = 2 * (zeroCount x : ℝ) := by rw [← zeroCount_cast_eq_sum_bitValueReal_not]

/-- The rank potential dominates the ordinary zero count. -/
theorem zeroCount_le_rankLinearPotential {n : ℕ} (hn : 0 < n) (x : BitString n) :
    (zeroCount x : ℝ) ≤ rankLinearPotential x := by
  unfold rankLinearPotential
  exact zeroCount_le_linearErrorPotential
    (rankPotentialWeight n) (one_le_rankPotentialWeight hn) x

/-- The rank potential is at most twice the ordinary zero count. -/
theorem rankLinearPotential_le_two_mul_zeroCount {n : ℕ} (x : BitString n) :
    rankLinearPotential x ≤ 2 * (zeroCount x : ℝ) := by
  unfold rankLinearPotential
  exact linearErrorPotential_le_two_mul_zeroCount
    (rankPotentialWeight n) rankPotentialWeight_le_two x

/-- In positive dimension, the rank potential vanishes exactly at the all-one string. -/
theorem rankLinearPotential_eq_zero_iff {n : ℕ} (hn : 0 < n) (x : BitString n) :
    rankLinearPotential x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hzreal : (zeroCount x : ℝ) ≤ 0 := by
      have h := zeroCount_le_rankLinearPotential hn x
      simpa [hx] using h
    have hzle : zeroCount x ≤ 0 := by
      exact_mod_cast hzreal
    have hz : zeroCount x = 0 := by omega
    have hcard : (zeroPositions x).card = 0 := by
      rw [zeroPositions_card]
      exact hz
    have hempty : zeroPositions x = ∅ := Finset.card_eq_zero.mp hcard
    funext i
    cases hxi : x i with
    | false =>
        have himem : i ∈ zeroPositions x := (mem_zeroPositions x i).2 hxi
        rw [hempty] at himem
        simp at himem
    | true =>
        simp [allOnes]
  · intro hx
    subst x
    exact rankLinearPotential_allOnes n

/-- Every non-optimal search point has rank potential at least one. -/
theorem one_le_rankLinearPotential_of_ne_allOnes {n : ℕ}
    (hn : 0 < n) (x : BitString n) (hx : x ≠ allOnes n) :
    1 ≤ rankLinearPotential x := by
  have hz : zeroCount x ≠ 0 := by
    intro hz0
    apply hx
    have hcard : (zeroPositions x).card = 0 := by
      rw [zeroPositions_card]
      exact hz0
    have hempty : zeroPositions x = ∅ := Finset.card_eq_zero.mp hcard
    funext i
    cases hxi : x i with
    | false =>
        have himem : i ∈ zeroPositions x := (mem_zeroPositions x i).2 hxi
        rw [hempty] at himem
        simp at himem
    | true => simp [allOnes]
  have hzNat : 1 ≤ zeroCount x := Nat.one_le_iff_ne_zero.mpr hz
  have hzReal : (1 : ℝ) ≤ (zeroCount x : ℝ) := by exact_mod_cast hzNat
  exact hzReal.trans (zeroCount_le_rankLinearPotential hn x)

/-- The rank potential is globally at most `2n`. -/
theorem rankLinearPotential_le_two_mul_n {n : ℕ} (x : BitString n) :
    rankLinearPotential x ≤ 2 * (n : ℝ) := by
  have hzero : (zeroCount x : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast zeroCount_le x
  exact (rankLinearPotential_le_two_mul_zeroCount x).trans
    (mul_le_mul_of_nonneg_left hzero (by norm_num : (0 : ℝ) ≤ 2))

/-- Flipping one zero coordinate changes a positive linear objective by exactly its weight. -/
theorem linearFitness_mutate_single_of_false {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearFitness w (mutateWithMask x ({i} : MutationMask n)) =
      linearFitness w x + w i := by
  unfold linearFitness
  have hiu : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hrest :
      (Finset.univ.erase i).sum
          (fun j => w j * bitValueReal (mutateWithMask x ({i} : MutationMask n) j)) =
        (Finset.univ.erase i).sum (fun j => w j * bitValueReal (x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [mutateWithMask, hji]
  rw [← Finset.sum_erase_add Finset.univ
      (fun j => w j * bitValueReal (mutateWithMask x ({i} : MutationMask n) j)) hiu]
  rw [← Finset.sum_erase_add Finset.univ
      (fun j => w j * bitValueReal (x j)) hiu]
  rw [hrest]
  simp [mutateWithMask, hi, bitValueReal]

/-- A single zero-to-one flip is strictly improving for a positive linear objective. -/
theorem linearFitness_single_zero_flip_improves {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearFitness w x < linearFitness w (mutateWithMask x ({i} : MutationMask n)) := by
  rw [linearFitness_mutate_single_of_false w x i hi]
  linarith [hw i]

/-- Signed contribution of a flipped coordinate to an improvement quantity. -/
def flipContribution {n : ℕ}
    (a : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (i : Fin n) : ℝ :=
  if i ∈ mask then if x i = false then a i else -a i else 0

/-- Exact signed-sum decomposition of a linear objective change under a mutation mask. -/
theorem linearFitness_mutation_delta {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    linearFitness w (mutateWithMask x mask) - linearFitness w x =
      ∑ i, flipContribution w x mask i := by
  unfold linearFitness
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases him : i ∈ mask
  · cases hxi : x i <;>
      simp [mutateWithMask, flipContribution, him, hxi, bitValueReal]
  · simp [mutateWithMask, flipContribution, him]

/-- Exact signed-sum decomposition of weighted error decrease under a mutation mask. -/
theorem linearErrorPotential_mutation_drop {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    linearErrorPotential g x - linearErrorPotential g (mutateWithMask x mask) =
      ∑ i, flipContribution g x mask i := by
  unfold linearErrorPotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases him : i ∈ mask
  · cases hxi : x i <;>
      simp [mutateWithMask, flipContribution, him, hxi, bitValueReal]
  · simp [mutateWithMask, flipContribution, him]

/-- Elitist acceptance of a linear mutation is exactly nonnegativity of its signed weight sum. -/
theorem accepts_linearFitness_iff_flipContribution_nonneg {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    Accepts (linearFitness w) x (mutateWithMask x mask) ↔
      0 ≤ ∑ i, flipContribution w x mask i := by
  unfold Accepts
  have hdelta := linearFitness_mutation_delta w x mask
  constructor <;> intro h <;> linarith

/-- If a linear offspring is accepted, the selected weighted-error decrease is the raw signed sum.
-/
theorem linearErrorPotential_selected_drop_of_accepts {n : ℕ}
    (w g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) =
      ∑ i, flipContribution g x mask i := by
  rw [selectedAfterMask,
    elitistSelect_of_accepts (linearFitness w) x (mutateWithMask x mask) hacc]
  exact linearErrorPotential_mutation_drop g x mask

/-- If a linear offspring is rejected, elitist selection leaves the weighted-error potential
unchanged. -/
theorem linearErrorPotential_selected_drop_of_rejects {n : ℕ}
    (w g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : ¬ Accepts (linearFitness w) x (mutateWithMask x mask)) :
    linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) = 0 := by
  rw [selectedAfterMask,
    elitistSelect_of_rejects (linearFitness w) x (mutateWithMask x mask) hacc]
  ring

/-- Specialized accepted-step decomposition for the classical rank potential. -/
theorem rankLinearPotential_selected_drop_of_accepts {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask) =
      ∑ i, flipContribution (rankPotentialWeight n) x mask i := by
  simpa [rankLinearPotential] using
    (linearErrorPotential_selected_drop_of_accepts
      w (rankPotentialWeight n) x mask hacc)

/-- Specialized rejected-step decomposition for the classical rank potential. -/
theorem rankLinearPotential_selected_drop_of_rejects {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : ¬ Accepts (linearFitness w) x (mutateWithMask x mask)) :
    rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask) = 0 := by
  simpa [rankLinearPotential] using
    (linearErrorPotential_selected_drop_of_rejects
      w (rankPotentialWeight n) x mask hacc)

/-- Weighted error is exactly the sum of coefficients on the currently-zero positions. -/
theorem linearErrorPotential_eq_sum_zeroPositions {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) :
    linearErrorPotential g x = ∑ i ∈ zeroPositions x, g i := by
  unfold linearErrorPotential zeroPositions
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp [bitValueReal]

/-- A uniform coefficient lower bound transfers to the weighted error potential. -/
theorem mul_zeroCount_le_linearErrorPotential {n : ℕ}
    (c : ℝ) (g : Fin n → ℝ) (hg : ∀ i, c ≤ g i) (x : BitString n) :
    c * (zeroCount x : ℝ) ≤ linearErrorPotential g x := by
  rw [zeroCount_cast_eq_sum_bitValueReal_not]
  unfold linearErrorPotential
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  cases x i <;> simp [bitValueReal, hg i]

/-- Positive objective weights make every selected objective-error drop nonnegative. -/
theorem linearErrorPotential_selected_drop_nonneg {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    0 ≤ linearErrorPotential w x -
      linearErrorPotential w (selectedAfterMask (linearFitness w) x mask) := by
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · rw [linearErrorPotential_selected_drop_of_accepts w w x mask hacc]
    exact (accepts_linearFitness_iff_flipContribution_nonneg w x mask).mp hacc
  · rw [linearErrorPotential_selected_drop_of_rejects w w x mask hacc]

/-- A singleton zero-to-one mutation is selected and drops objective error by exactly its weight. -/
theorem linearErrorPotential_selected_single_zero_flip_drop {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearErrorPotential w x -
        linearErrorPotential w
          (selectedAfterMask (linearFitness w) x ({i} : MutationMask n)) =
      w i := by
  have himprove := linearFitness_single_zero_flip_improves w hw x i hi
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt himprove
  rw [linearErrorPotential_selected_drop_of_accepts w w x ({i} : MutationMask n) hacc]
  simp [flipContribution, hi]

/-- The analogous selected singleton drop for the bounded rank potential. -/
theorem rankLinearPotential_selected_single_zero_flip_drop {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    rankLinearPotential x -
        rankLinearPotential
          (selectedAfterMask (linearFitness w) x ({i} : MutationMask n)) =
      rankPotentialWeight n i := by
  have himprove := linearFitness_single_zero_flip_improves w hw x i hi
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt himprove
  rw [rankLinearPotential_selected_drop_of_accepts w x ({i} : MutationMask n) hacc]
  simp [flipContribution, hi]

/-- The bounded rank potential is the sum of its rank weights over zero positions. -/
theorem rankLinearPotential_eq_sum_zeroPositions {n : ℕ} (x : BitString n) :
    rankLinearPotential x = ∑ i ∈ zeroPositions x, rankPotentialWeight n i := by
  exact linearErrorPotential_eq_sum_zeroPositions (rankPotentialWeight n) x

/-- Coordinates flipped from zero to one by a mutation mask. -/
def zeroToOneFlips {n : ℕ} (x : BitString n) (mask : MutationMask n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ mask ∧ x i = false)

@[simp] theorem mem_zeroToOneFlips {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n) :
    i ∈ zeroToOneFlips x mask ↔ i ∈ mask ∧ x i = false := by
  simp [zeroToOneFlips]

/-- Coordinates flipped from one to zero by a mutation mask. -/
def oneToZeroFlips {n : ℕ} (x : BitString n) (mask : MutationMask n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ mask ∧ x i = true)

@[simp] theorem mem_oneToZeroFlips {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n) :
    i ∈ oneToZeroFlips x mask ↔ i ∈ mask ∧ x i = true := by
  simp [oneToZeroFlips]

/-- The signed flip sum is positive zero-to-one mass minus negative one-to-zero mass. -/
theorem flipContribution_sum_eq_flip_sums {n : ℕ}
    (a : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    (∑ i, flipContribution a x mask i) =
      (∑ i ∈ zeroToOneFlips x mask, a i) -
        (∑ i ∈ oneToZeroFlips x mask, a i) := by
  classical
  unfold zeroToOneFlips oneToZeroFlips
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases him : i ∈ mask
  · cases hxi : x i <;> simp [flipContribution, him, hxi]
  · simp [flipContribution, him]

/-- Linear-objective acceptance is exactly balance of improving and worsening flip weights. -/
theorem accepts_linearFitness_iff_flip_sums {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    Accepts (linearFitness w) x (mutateWithMask x mask) ↔
      (∑ i ∈ oneToZeroFlips x mask, w i) ≤
        ∑ i ∈ zeroToOneFlips x mask, w i := by
  rw [accepts_linearFitness_iff_flipContribution_nonneg,
    flipContribution_sum_eq_flip_sums]
  exact sub_nonneg

/-- Erasing a coordinate that is currently one does not change the zero-to-one flip set. -/
theorem zeroToOneFlips_erase_of_true {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (j : Fin n) (hxj : x j = true) :
    zeroToOneFlips x (mask.erase j) = zeroToOneFlips x mask := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [zeroToOneFlips, hxj]
  · simp [zeroToOneFlips, hij]

/-- Erasing a currently-one coordinate erases exactly that element from the one-to-zero set. -/
theorem oneToZeroFlips_erase_of_true {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (j : Fin n) (hxj : x j = true) :
    oneToZeroFlips x (mask.erase j) = (oneToZeroFlips x mask).erase j := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [oneToZeroFlips, hxj]
  · simp [oneToZeroFlips, hij]

/-- Removing a worsening one-to-zero flip from an accepted mutation preserves acceptance. -/
theorem accepts_erase_oneToZero_of_accepts {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (j : Fin n)
    (hjmask : j ∈ mask) (hxj : x j = true)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    Accepts (linearFitness w) x (mutateWithMask x (mask.erase j)) := by
  have hjneg : j ∈ oneToZeroFlips x mask :=
    (mem_oneToZeroFlips x mask j).2 ⟨hjmask, hxj⟩
  have hbalance := (accepts_linearFitness_iff_flip_sums w x mask).mp hacc
  have hneg_le :
      (∑ i ∈ oneToZeroFlips x (mask.erase j), w i) ≤
        ∑ i ∈ oneToZeroFlips x mask, w i := by
    rw [oneToZeroFlips_erase_of_true x mask j hxj]
    have hsum := Finset.sum_erase_add (oneToZeroFlips x mask) w hjneg
    have hwj : 0 ≤ w j := (hw j).le
    linarith
  apply (accepts_linearFitness_iff_flip_sums w x (mask.erase j)).2
  rw [zeroToOneFlips_erase_of_true x mask j hxj]
  exact hneg_le.trans hbalance

/-- On an accepted mutation, the rank-potential drop is the same positive-minus-negative split. -/
theorem rankLinearPotential_selected_drop_eq_flip_sums_of_accepts {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask) =
      (∑ i ∈ zeroToOneFlips x mask, rankPotentialWeight n i) -
        (∑ i ∈ oneToZeroFlips x mask, rankPotentialWeight n i) := by
  rw [rankLinearPotential_selected_drop_of_accepts w x mask hacc,
    flipContribution_sum_eq_flip_sums]

/-- Number of currently-zero coordinates flipped to one by a mask. -/
def zeroToOneFlipCount {n : ℕ} (x : BitString n) (mask : MutationMask n) : ℕ :=
  (zeroToOneFlips x mask).card

/-- Literature case C1: no improving (zero-to-one) coordinate is flipped. -/
def IsClassicalLinearCaseC1 {n : ℕ} (x : BitString n) (mask : MutationMask n) : Prop :=
  zeroToOneFlipCount x mask = 0

/-- Literature case C2: exactly one improving (zero-to-one) coordinate is flipped. -/
def IsClassicalLinearCaseC2 {n : ℕ} (x : BitString n) (mask : MutationMask n) : Prop :=
  zeroToOneFlipCount x mask = 1

/-- Literature case C3: at least two improving (zero-to-one) coordinates are flipped. -/
def IsClassicalLinearCaseC3 {n : ℕ} (x : BitString n) (mask : MutationMask n) : Prop :=
  2 ≤ zeroToOneFlipCount x mask

/-- Every mutation mask lies in exactly the numerical regime C1, C2, or C3. -/
theorem classicalLinearCase_trichotomy {n : ℕ} (x : BitString n) (mask : MutationMask n) :
    IsClassicalLinearCaseC1 x mask ∨
      IsClassicalLinearCaseC2 x mask ∨
        IsClassicalLinearCaseC3 x mask := by
  unfold IsClassicalLinearCaseC1 IsClassicalLinearCaseC2 IsClassicalLinearCaseC3
  omega

/-- Erasing a worsening flip preserves the numerical C3 condition. -/
theorem classicalLinearCaseC3_erase_of_true {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (j : Fin n) (hxj : x j = true)
    (hC3 : IsClassicalLinearCaseC3 x mask) :
    IsClassicalLinearCaseC3 x (mask.erase j) := by
  unfold IsClassicalLinearCaseC3 zeroToOneFlipCount at hC3 ⊢
  rw [zeroToOneFlips_erase_of_true x mask j hxj]
  exact hC3

/--
For positive linear weights, a C1 mutation contributes zero selected rank drift.
If such a mutation is accepted, objective-weight balance forces every one-to-zero flip
to disappear as well; otherwise rejection leaves the parent unchanged.
-/
theorem rankLinearPotential_selected_drop_eq_zero_of_caseC1 {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n)
    (hC1 : IsClassicalLinearCaseC1 x mask) :
    rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask) = 0 := by
  have hzeroempty : zeroToOneFlips x mask = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [IsClassicalLinearCaseC1, zeroToOneFlipCount] using hC1
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · have hbalance := (accepts_linearFitness_iff_flip_sums w x mask).mp hacc
    rw [hzeroempty] at hbalance
    simp only [Finset.sum_empty] at hbalance
    have hnonneg : 0 ≤ ∑ i ∈ oneToZeroFlips x mask, w i := by
      apply Finset.sum_nonneg
      intro i hi
      exact (hw i).le
    have hsum0 : (∑ i ∈ oneToZeroFlips x mask, w i) = 0 :=
      le_antisymm hbalance hnonneg
    have honeempty : oneToZeroFlips x mask = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hle : w i ≤ ∑ j ∈ oneToZeroFlips x mask, w j :=
        Finset.single_le_sum (fun j hj => (hw j).le) hi
      rw [hsum0] at hle
      exact (not_le_of_gt (hw i)) hle
    rw [rankLinearPotential_selected_drop_eq_flip_sums_of_accepts
      w x mask hacc, hzeroempty, honeempty]
    simp
  · exact rankLinearPotential_selected_drop_of_rejects w x mask hacc

/-- A singleton flip of a zero coordinate is a C2 mutation. -/
theorem singleton_zero_is_classicalLinearCaseC2 {n : ℕ}
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    IsClassicalLinearCaseC2 x ({i} : MutationMask n) := by
  unfold IsClassicalLinearCaseC2 zeroToOneFlipCount
  have hset : zeroToOneFlips x ({i} : MutationMask n) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [zeroToOneFlips, hi]
    · simp [zeroToOneFlips, hji]
  rw [hset]
  simp

/--
Case C2 localized at its unique improving coordinate `i`.  In the repository's
maximization convention this means that `i` is the unique zero-to-one flip.
-/
def IsClassicalLinearCaseC2At {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n) : Prop :=
  zeroToOneFlips x mask = {i}

/--
The `A_i` subcase of C2 in the reversed coordinate convention: `i` is the unique
zero-to-one flip and no more-important coordinate `j < i` flips from one to zero.
-/
def IsClassicalLinearCaseC2A {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n) : Prop :=
  IsClassicalLinearCaseC2At x mask i ∧
    ∀ j ∈ oneToZeroFlips x mask, ¬ j.val < i.val

/--
The `B_i` subcase of C2: `i` is the unique zero-to-one flip and at least one
more-important coordinate `j < i` flips from one to zero.
-/
def IsClassicalLinearCaseC2B {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n) : Prop :=
  IsClassicalLinearCaseC2At x mask i ∧
    ∃ j ∈ oneToZeroFlips x mask, j.val < i.val

/-- A localized C2 event is, in particular, a C2 mutation. -/
theorem classicalLinearCaseC2_of_caseC2At {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i) :
    IsClassicalLinearCaseC2 x mask := by
  unfold IsClassicalLinearCaseC2 zeroToOneFlipCount
  rw [hAt]
  simp

/-- In a C2 mutation, any improving flip is the unique improving coordinate. -/
theorem classicalLinearCaseC2At_of_caseC2_of_mem {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hC2 : IsClassicalLinearCaseC2 x mask)
    (hi : i ∈ zeroToOneFlips x mask) :
    IsClassicalLinearCaseC2At x mask i := by
  unfold IsClassicalLinearCaseC2 zeroToOneFlipCount at hC2
  unfold IsClassicalLinearCaseC2At
  have hcardErase : ((zeroToOneFlips x mask).erase i).card = 0 := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have hempty : (zeroToOneFlips x mask).erase i = ∅ :=
    Finset.card_eq_zero.mp hcardErase
  ext j
  simp only [Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hji
    have hje : j ∈ (zeroToOneFlips x mask).erase i :=
      Finset.mem_erase.mpr ⟨hji, hj⟩
    rw [hempty] at hje
    simp at hje
  · intro hji
    subst j
    exact hi

/-- The localized improving coordinate is currently zero. -/
theorem false_of_classicalLinearCaseC2At {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i) :
    x i = false := by
  have hi : i ∈ zeroToOneFlips x mask := by
    rw [hAt]
    simp
  exact ((mem_zeroToOneFlips x mask i).mp hi).2

/-- The localized improving coordinate belongs to the mutation mask. -/
theorem mem_mask_of_classicalLinearCaseC2At {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i) :
    i ∈ mask := by
  have hi : i ∈ zeroToOneFlips x mask := by
    rw [hAt]
    simp
  exact ((mem_zeroToOneFlips x mask i).mp hi).1

/-- Every localized C2 event lies in exactly one of the `A_i` or `B_i` subcases. -/
theorem classicalLinearCaseC2A_or_C2B {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i) :
    IsClassicalLinearCaseC2A x mask i ∨ IsClassicalLinearCaseC2B x mask i := by
  classical
  by_cases hB : ∃ j ∈ oneToZeroFlips x mask, j.val < i.val
  · exact Or.inr ⟨hAt, hB⟩
  · exact Or.inl ⟨hAt, by
      intro j hj hji
      exact hB ⟨j, hj, hji⟩⟩

/-- In `A_i`, every worsening flip is strictly less important than `i`. -/
theorem index_lt_of_mem_oneToZero_of_caseC2A {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i j : Fin n)
    (hA : IsClassicalLinearCaseC2A x mask i)
    (hj : j ∈ oneToZeroFlips x mask) :
    i.val < j.val := by
  have hi0 : x i = false := false_of_classicalLinearCaseC2At x mask i hA.1
  have hj1 : x j = true := ((mem_oneToZeroFlips x mask j).mp hj).2
  have hji : j ≠ i := by
    intro h
    subst j
    simp [hi0] at hj1
  have hvalne : j.val ≠ i.val := by
    intro h
    apply hji
    exact Fin.ext h
  have hnotlt : ¬ j.val < i.val := hA.2 j hj
  omega

/-- Erasing a worsening flip preserves the deterministic `A_i` predicate. -/
theorem classicalLinearCaseC2A_erase_oneToZero {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i j : Fin n)
    (hA : IsClassicalLinearCaseC2A x mask i)
    (hj : j ∈ oneToZeroFlips x mask) :
    IsClassicalLinearCaseC2A x (mask.erase j) i := by
  rcases hA with ⟨hAt, hNoHigh⟩
  have hjData := (mem_oneToZeroFlips x mask j).mp hj
  constructor
  · unfold IsClassicalLinearCaseC2At at hAt ⊢
    rw [zeroToOneFlips_erase_of_true x mask j hjData.2]
    exact hAt
  · intro k hk
    rw [oneToZeroFlips_erase_of_true x mask j hjData.2] at hk
    exact hNoHigh k (Finset.mem_erase.mp hk).2

/-- Exact algebraic difference between two rank-potential coefficients. -/
theorem rankPotentialWeight_sub_eq_index_gap {n : ℕ} (i j : Fin n) :
    rankPotentialWeight n i - rankPotentialWeight n j =
      ((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ) := by
  unfold rankPotentialWeight
  push_cast
  ring

/--
The deterministic heart of the `B_i` argument.  With positive nonincreasing objective
weights, an accepted `B_i` mutation has exactly one worsening flip `j < i`; its objective
weight equals `w i`, and no other bit flips besides `i` and `j`.
-/
theorem accepted_caseC2B_eq_equalWeight_pair {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    ∃ j : Fin n,
      j ∈ oneToZeroFlips x mask ∧
      j.val < i.val ∧
      w j = w i ∧
      oneToZeroFlips x mask = {j} ∧
      mask = {i, j} := by
  rcases hB with ⟨hAt, j, hj, hji⟩
  have hzero : zeroToOneFlips x mask = {i} := hAt
  have hbalance := (accepts_linearFitness_iff_flip_sums w x mask).mp hacc
  rw [hzero] at hbalance
  simp only [Finset.sum_singleton] at hbalance
  have hwi_le_wj : w i ≤ w j := hmono j i (Nat.le_of_lt hji)
  have hwj_le_sum :
      w j ≤ ∑ k ∈ oneToZeroFlips x mask, w k :=
    Finset.single_le_sum (fun k hk => (hw k).le) hj
  have hsum_le_wi : (∑ k ∈ oneToZeroFlips x mask, w k) ≤ w i := by
    simpa using hbalance
  have hwj_eq_wi : w j = w i := by
    apply le_antisymm
    · exact hwj_le_sum.trans hsum_le_wi
    · exact hwi_le_wj
  have hsum_eq_wj : (∑ k ∈ oneToZeroFlips x mask, w k) = w j := by
    apply le_antisymm
    · simpa [hwj_eq_wi] using hsum_le_wi
    · exact hwj_le_sum
  have hone : oneToZeroFlips x mask = {j} := by
    ext k
    simp only [Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hkj
      have hkErase : k ∈ (oneToZeroFlips x mask).erase j :=
        Finset.mem_erase.mpr ⟨hkj, hk⟩
      have hsumErase := Finset.sum_erase_add (oneToZeroFlips x mask) w hj
      have hsumEraseZero : (∑ l ∈ (oneToZeroFlips x mask).erase j, w l) = 0 := by
        rw [hsum_eq_wj] at hsumErase
        linarith
      have hwk_le : w k ≤ ∑ l ∈ (oneToZeroFlips x mask).erase j, w l :=
        Finset.single_le_sum (fun l hl => (hw l).le) hkErase
      rw [hsumEraseZero] at hwk_le
      exact (not_le_of_gt (hw k)) hwk_le
    · intro hkj
      subst k
      exact hj
  have hiMask : i ∈ mask := mem_mask_of_classicalLinearCaseC2At x mask i hAt
  have hjMask : j ∈ mask := ((mem_oneToZeroFlips x mask j).mp hj).1
  have hmaskPair : mask = {i, j} := by
    ext k
    constructor
    · intro hk
      cases hxk : x k with
      | false =>
          have hkPos : k ∈ zeroToOneFlips x mask :=
            (mem_zeroToOneFlips x mask k).2 ⟨hk, hxk⟩
          rw [hzero] at hkPos
          have hki : k = i := by simpa using hkPos
          simp [hki]
      | true =>
          have hkNeg : k ∈ oneToZeroFlips x mask :=
            (mem_oneToZeroFlips x mask k).2 ⟨hk, hxk⟩
          rw [hone] at hkNeg
          have hkj : k = j := by simpa using hkNeg
          simp [hkj]
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hki | hkj
      · simpa [hki] using hiMask
      · simpa [hkj] using hjMask
  exact ⟨j, hj, hji, hwj_eq_wi, hone, hmaskPair⟩

/--
Consequently, every accepted `B_i` mutation has rank drop equal to the index gap of
its unique equal-weight swap partner.
-/
theorem rankLinearPotential_selected_drop_of_caseC2B {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    ∃ j : Fin n,
      j.val < i.val ∧ w j = w i ∧ mask = {i, j} ∧
      rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask) =
        ((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ) := by
  rcases accepted_caseC2B_eq_equalWeight_pair w hw hmono x mask i hB hacc with
    ⟨j, hj, hji, hwji, hone, hmask⟩
  refine ⟨j, hji, hwji, hmask, ?_⟩
  have hzero : zeroToOneFlips x mask = {i} := hB.1
  rw [rankLinearPotential_selected_drop_eq_flip_sums_of_accepts w x mask hacc]
  rw [hzero, hone]
  simp only [Finset.sum_singleton]
  exact rankPotentialWeight_sub_eq_index_gap i j

end ECRuntime
