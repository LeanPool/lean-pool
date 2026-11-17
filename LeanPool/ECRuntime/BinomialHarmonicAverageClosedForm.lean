/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel

/-!
The binomial transform of harmonic numbers.
For a Bin(n, 1/2) variable, the mean harmonic number is
`H_n - sum_{j=1}^n 1 / (j * 2^j)`, as used by Doerr and Doerr (2013).

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- The elementary harmonic recurrence, shared with the RLS Bellman line.
It isolates the only harmonic-number rewrite needed by the Pascal
recurrence for the binomial transform. -/
private theorem stage138_harmonic_succ (k : Nat) :
    harmonicReal (k + 1) =
      harmonicReal k + ((k + 1 : Nat) : Real)⁻¹ := by
  simp [harmonicReal, harmonic_succ]

/-- The empty harmonic sum is zero. Keeping this rewrite local avoids
unfolding every variable-index harmonic number during Pascal reindexing. -/
private theorem stage138_harmonic_zero : harmonicReal 0 = 0 := by
  simp [harmonicReal]

/-- Every row of the binomial triangle has total weight `2^n`.
The same proof has independently compiled in Stage 137. -/
private theorem stage138_binomial_mass (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) =
      (2 : Real) ^ n := by
  have h : ((1 : Real) + 1) ^ n =
      (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) := by
    simp [add_pow]
  simpa only [one_add_one_eq_two] using h.symm

/-- Pascal's rule after casting natural binomial coefficients to reals.
This is the index-level equality needed to transform a row-n+1 weighted
harmonic sum into two row-n sums. The separate reciprocal coefficient proof is developed below. -/
private theorem stage138_pascal_cast (n k : Nat) :
    (Nat.choose (n + 1) (k + 1) : Real) =
      (Nat.choose n k : Real) + (Nat.choose n (k + 1) : Real) := by
  exact_mod_cast Nat.choose_succ_succ n k

/-! We isolate the entire remaining combinatorial obligation in one
Pascal-recurrence lemma. The correction recurrence and algebraic induction are independent
of the binomial index shift proved below. -/

private noncomputable def stage138_weightedSum (n : Nat) : Real :=
  (Finset.range (n + 1)).sum (fun k =>
    (Nat.choose n k : Real) * harmonicReal k)

private noncomputable def stage138_correction (n : Nat) : Real :=
  (Finset.Icc 1 n).sum (fun j =>
    (1 : Real) / ((j : Real) * (2 : Real) ^ j))

/-- Reindex `0,...,n` into its initial term and the `1,...,n`
tail. It is a generic finite-sum lemma: no binomial or analytic assumptions. -/
private theorem stage138_range_shift (f : Nat → Real) (n : Nat) :
    (Finset.range (n + 1)).sum f =
      f 0 + (Finset.range n).sum (fun k => f (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (Finset.range (n + 1 + 1)).sum f =
            (Finset.range (n + 1)).sum f + f (n + 1) := by
              rw [Finset.sum_range_succ]
        _ = (f 0 + (Finset.range n).sum (fun k => f (k + 1))) +
              f (n + 1) := by rw [ih]
        _ = f 0 + (Finset.range (n + 1)).sum (fun k => f (k + 1)) := by
              rw [Finset.sum_range_succ]
              ring

/-- The Pascal decomposition for the *weighted* row of harmonic numbers.
It reduces the remaining Stage 138 issue to one finite reciprocal-binomial
sum, and avoids any limits or infinite series. -/
private theorem stage138_pascal_weighted_shift (n : Nat) :
    stage138_weightedSum (n + 1) =
      stage138_weightedSum n +
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal (k + 1)) := by
  have htop : stage138_weightedSum (n + 1) =
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose (n + 1) (k + 1) : Real) * harmonicReal (k + 1)) := by
    unfold stage138_weightedSum
    rw [stage138_range_shift]
    simp only [stage138_harmonic_zero, mul_zero, zero_add]
  have hbottom :
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n (k + 1) : Real) * harmonicReal (k + 1)) =
          stage138_weightedSum n := by
    have hb :
        (Finset.range n).sum (fun k =>
          (Nat.choose n (k + 1) : Real) * harmonicReal (k + 1)) =
            stage138_weightedSum n := by
      unfold stage138_weightedSum
      rw [stage138_range_shift]
      simp only [stage138_harmonic_zero, mul_zero, zero_add]
    rw [Finset.sum_range_succ]
    simpa using hb
  calc
    stage138_weightedSum (n + 1) =
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose (n + 1) (k + 1) : Real) * harmonicReal (k + 1)) := htop
    _ = (Finset.range (n + 1)).sum (fun k =>
          ((Nat.choose n k : Real) + (Nat.choose n (k + 1) : Real)) *
            harmonicReal (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [stage138_pascal_cast]
    _ = (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal (k + 1)) +
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n (k + 1) : Real) * harmonicReal (k + 1)) := by
            simp only [add_mul, Finset.sum_add_distrib]
    _ = stage138_weightedSum n +
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal (k + 1)) := by
            rw [hbottom]
            ring

/-- The binomial index shift, in the orientation used below. -/
private theorem stage138_choose_shift_nat (n k : Nat) :
    (k + 1) * Nat.choose (n + 1) (k + 1) =
      (n + 1) * Nat.choose n k := by
  simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k).symm

/-- Cast the natural-number index shift into an exact reciprocal identity;
all divisors are positive, including both endpoints of the binomial row. -/
private theorem stage138_choose_div_shift (n k : Nat) :
    (Nat.choose n k : Real) / ((k + 1 : Nat) : Real) =
      (Nat.choose (n + 1) (k + 1) : Real) / ((n + 1 : Nat) : Real) := by
  have hnat := stage138_choose_shift_nat n k
  have hcast :
      ((k + 1 : Nat) : Real) * (Nat.choose (n + 1) (k + 1) : Real) =
        ((n + 1 : Nat) : Real) * (Nat.choose n k : Real) := by
    exact_mod_cast hnat
  have hk : (0 : Real) < ((k + 1 : Nat) : Real) := by positivity
  have hn : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  apply (div_eq_div_iff (ne_of_gt hk) (ne_of_gt hn)).2
  simpa only [mul_comm] using hcast.symm

/-- The remaining finite combinatorial bridge is now given a full proof
attempt, with its two independent ingredients exposed explicitly:
pointwise binomial index shift and the row-mass identity. -/
private theorem stage138_reciprocal_binomial_sum (n : Nat) :
    (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) / ((k + 1 : Nat) : Real)) =
      ((2 : Real) ^ (n + 1) - 1) / ((n + 1 : Nat) : Real) := by
  have htail :
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose (n + 1) (k + 1) : Real)) =
        (2 : Real) ^ (n + 1) - 1 := by
    have hm := stage138_binomial_mass (n + 1)
    rw [stage138_range_shift] at hm
    have hzero : (Nat.choose (n + 1) 0 : Real) = 1 := by simp
    rw [hzero] at hm
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hm)
  calc
    (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) / ((k + 1 : Nat) : Real)) =
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose (n + 1) (k + 1) : Real) /
          ((n + 1 : Nat) : Real)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact stage138_choose_div_shift n k
    _ = ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose (n + 1) (k + 1) : Real))) /
          ((n + 1 : Nat) : Real) := by rw [Finset.sum_div]
    _ = ((2 : Real) ^ (n + 1) - 1) / ((n + 1 : Nat) : Real) := by
      rw [htail]

/-- The finite correction acquires exactly one summand when the dimension
is increased. This is a purely finite, non-asymptotic identity. -/
private theorem stage138_correction_succ (n : Nat) :
    stage138_correction (n + 1) =
      stage138_correction n +
        (1 : Real) / (((n + 1 : Nat) : Real) * (2 : Real) ^ (n + 1)) := by
  have hout : n + 1 ∉ Finset.Icc 1 n := by simp
  have hIcc : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  simp only [stage138_correction, hIcc, Finset.sum_insert hout]
  ring

/-- The successor recurrence for the binomial-harmonic weighted sum.
Both the Pascal reindexing and the reciprocal coefficient identity
are now explicit proof attempts, subject to compiler verification. -/
private theorem stage138_weightedSum_succ (n : Nat) :
    stage138_weightedSum (n + 1) =
      2 * stage138_weightedSum n +
        ((2 : Real) ^ (n + 1) - 1) / ((n + 1 : Nat) : Real) := by
  have hshift :
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal (k + 1)) =
        stage138_weightedSum n +
          (Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) / ((k + 1 : Nat) : Real)) := by
    calc
      (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal (k + 1)) =
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) *
            (harmonicReal k + ((k + 1 : Nat) : Real)⁻¹)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [stage138_harmonic_succ]
      _ = (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k) +
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * ((k + 1 : Nat) : Real)⁻¹) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = stage138_weightedSum n +
          (Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) / ((k + 1 : Nat) : Real)) := by
              simp only [stage138_weightedSum, div_eq_mul_inv]
  calc
    stage138_weightedSum (n + 1) =
        stage138_weightedSum n +
          (Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal (k + 1)) :=
      stage138_pascal_weighted_shift n
    _ = stage138_weightedSum n + (stage138_weightedSum n +
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) / ((k + 1 : Nat) : Real))) := by rw [hshift]
    _ = 2 * stage138_weightedSum n +
          ((2 : Real) ^ (n + 1) - 1) / ((n + 1 : Nat) : Real) := by
      rw [stage138_reciprocal_binomial_sum]
      ring

/-- Exact binomial average of harmonic numbers with a finite correction. -/
theorem proposed_binomialHarmonicAverage_closedForm (n : Nat) :
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
      harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
  change stage138_weightedSum n / (2 : Real) ^ n =
    harmonicReal n - stage138_correction n
  induction n with
  | zero =>
      simp [stage138_weightedSum, stage138_correction, harmonicReal]
  | succ n ih =>
      have hn : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
      have hp : (2 : Real) ^ n ≠ 0 := by positivity
      have hs : stage138_weightedSum n =
          (2 : Real) ^ n * (harmonicReal n - stage138_correction n) := by
        simpa only [mul_comm] using (div_eq_iff hp).mp ih
      rw [stage138_weightedSum_succ, hs,
        stage138_harmonic_succ, stage138_correction_succ]
      simp only [pow_succ]
      field_simp [hn, hp]
      ring

end ECRuntime
