/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentTailReindex

/-! # The conditional sieve on a smooth mass tail

The smoothness cutoff and the sieve cutoff are separate. This permits grouping
prefixes into bands whose upper and lower prime cutoffs differ.
-/

@[expose] public section

namespace NairTenenbaum

/-- The discriminant-dependent cost of the prime-argument smooth-tail sieve. -/
noncomputable def primeArgumentTailSieveCost (A B κ : ℝ) (g D : ℕ) : ℝ :=
  totientTwist (g + 1) D * primeArgumentSplitTailBound A B κ g D

theorem primeArgumentTailSieveCost_pos {A B κ : ℝ} (hB : 0 < B) {g D : ℕ} (hg : 0 < g) (hD : 0 <
    D) :
    0 < primeArgumentTailSieveCost A B κ g D :=
  mul_pos (lt_of_lt_of_le zero_lt_one (totientTwist_one_le (g + 1) hD.ne'))
    (primeArgumentSplitTailBound_pos hB hg hD)

/-- The sieve bound for an original smooth divisor tail, with uniform constants
and all bad-prime moments accounted for. The cutoff for smoothness is `w`, and
the cutoff for sifting is `z`. -/
theorem exists_primeSmoothTailSiftedSum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0
    < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
        P.total.eval 0 ≠ 0 →
      ∀ (A B ε κ : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε → 0 ≤ κ →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 → ∀ (w X : ℝ), 2 ≤ w → 8 * (g : ℝ) ^ 2 * κ ≤ Real.log w → 0 < X →
      ∀ (N : ℕ+) (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (N : ℝ) * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      P.primeSmoothTailSiftedSum F g N (Finset.Icc 0 ⌊w⌋₊) X a b z ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct
            P.total z *
          Real.exp (-κ * Real.log X / Real.log w) * (∑ n ∈ positiveUpTo w, P.weight F n) *
              primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_bad_sieve_bound g hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero A B ε κ F hF hA hB hε hκ hsmall w X hw hwlog hX N a b z hab hz hzlog hlevel
  let V := smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊w⌋₊) N
  let U := fun v => smallBadParts P.exponent P.badDiscriminant v N
  let W := fun v => rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (g + 1) (v i)
  let C := K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist (g + 1) P.badDiscriminant *
      primeArgumentFactor P.total z
  have hC : 0 ≤ C := by
    have hlen : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hK) hlen)
      (sieveProduct_pos P.noFixedPrime z).le) (totientTwist_nonneg (g + 1) P.badDiscriminant))
      (primeArgumentFactor_nonneg P.total (z := z) (by linarith))
  have hsupport (v : Tuple r) (u : Tuple r) (hu : u ∈ U v) :
      ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors :=
    ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).1
  have hsize (v : Tuple r) (u : Tuple r) (hu : u ∈ U v) :
      L * (tupleLCM u : ℝ) * mass v * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a := by
    have huN := ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).2
    have hmod := (mass_badSieveModuli_le_weightedMass P.exponent P.exponent_pos u v).trans huN
    have H' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmod : (mass (badSieveModuli u v) : ℝ) ≤ N)
        (zero_le_one.trans hL)) (Real.rpow_nonneg (by
          linarith : 0 ≤ z) (4 * ((g : ℝ) + 1) * (1 + η) + δ))
    apply le_trans ?_ hlevel
    simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using H'
  have Hsum : (∑ v ∈ V, ∑ u ∈ (U v).filter (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
      pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z) ≤
      C * ∑ v ∈ V, ∑ u ∈ (U v).filter (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
        badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u * W v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    have hv' := P.dagger_bad_of_dagger ((mem_smoothWeightUpTo P.exponent P.exponent_pos
        P.discriminant
      (Finset.Icc 0 ⌊w⌋₊) N v).mp hv).1.2
    have hcross (i j : Fin r) : Nat.Coprime (u i) (v j) :=
      factoredNumbers_coprime_of_coprime (hsupport v u hu' i) (hv'.2 j).symm
    have Hcount := H k r P hdeg.le hzero u v hv' (hsupport v u hu') a b z hab hz hzlog (hsize v u
      hu')
    have H' := P.weighted_count_le_badPrimeKernel hF hA hB u v hcross
      (C := C * ∏ i, totientTwist (g + 1) (v i))
      (Nat.cast_nonneg (P.primeArgumentBadSiftedCount g u v a b z)) (by
        simpa only [C, mul_assoc, mul_comm, mul_left_comm] using Hcount)
    convert H' using 1
    dsimp only [W]
    ring
  have hgP : 0 < P.total.natDegree := by simpa only [hdeg] using hg
  obtain ⟨hgood, hbad, hcut⟩ := primeArgument_split_moment_conditions hg hε.le hκ hw hsmall hwlog
  have HT := P.primeArgument_split_smooth_tail_le hF hA hB hε hκ hw hX hgP
    (by
      simpa only [hdeg] using hgood) (by simpa only [hdeg] using hbad) (by simpa only [hdeg] using
          hcut)
    N U (fun v _ u hu i => mem_tupleBox.mp (Finset.mem_filter.mp hu).1 i)
    (fun v _ u hu => hsupport v u hu)
  rw [hdeg] at HT
  have H' := (P.primeSmoothTailSiftedSum_le_split hF.nonneg g N (Finset.Icc 0 ⌊w⌋₊) X a b z).trans
      Hsum
  have H'' := H'.trans (mul_le_mul_of_nonneg_left HT hC)
  convert H'' using 1
  dsimp only [C, primeArgumentTailSieveCost]
  ring

end NairTenenbaum
