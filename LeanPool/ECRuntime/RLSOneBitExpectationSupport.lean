/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMax
public import LeanPool.ECRuntime.UniformOneBitMutation

/-!
One-step expectations under uniform one-bit mutation. Singleton masks
have mass `1/n`; observable expectations become ordinary coordinate averages.
The zero-count contraction and harmonic predecessor identities follow.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Under the uniform one-bit law, every observable's one-step expectation
is the ordinary average over the `n` possible singleton mutations. -/
theorem candidate_rls_expectedValueAfter_eq_singleton_average
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (F : BitString n → Real) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness) F x =
    (n : Real)⁻¹ *
      (∑ i : Fin n,
        F (selectedAfterMask fitness x ({i} : MutationMask n))) := by
  classical
  let S : Finset (MutationMask n) :=
    Finset.powersetCard 1 (Finset.univ : Finset (Fin n))
  have hcard (mask : MutationMask n) : mask.card = 1 ↔ mask ∈ S := by
    simp [S]
  have himage :
      S = Finset.univ.image (fun i : Fin n => ({i} : MutationMask n)) := by
    ext mask
    constructor
    · intro hm
      have hcard1 : mask.card = 1 := (Finset.mem_powersetCard.mp hm).2
      rcases Finset.card_eq_one.mp hcard1 with ⟨i, hi⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
    · intro hm
      rcases Finset.mem_image.mp hm with ⟨i, _, rfl⟩
      simp [S]
  calc
    expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness) F x =
        ∑ mask : MutationMask n,
          (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).weight mask *
            F (selectedAfterMask fitness x mask) := by
          unfold expectedValueAfter StaticUnaryUnbiasedMutation.transition
            finiteRandomTransition
          exact pushforwardWeight_expectation
            (w := (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).weight)
            (f := selectedAfterMask fitness x) F
    _ = ∑ mask ∈ S,
          (n : Real)⁻¹ * F (selectedAfterMask fitness x mask) := by
          change (∑ mask : MutationMask n,
            (if mask.card = 1 then (n : Real)⁻¹ else 0) *
              F (selectedAfterMask fitness x mask)) = _
          simp_rw [hcard, ite_mul, zero_mul]
          exact Finset.sum_ite_mem_eq _ _
    _ = ∑ i : Fin n,
          (n : Real)⁻¹ * F (selectedAfterMask fitness x ({i} : MutationMask n)) := by
          rw [himage, Finset.sum_image]
          intro i _ j _ hij
          exact Finset.singleton_injective hij
    _ = (n : Real)⁻¹ *
          (∑ i : Fin n,
            F (selectedAfterMask fitness x ({i} : MutationMask n))) := by
          rw [Finset.mul_sum]

/-- The accepted singleton mutation decreases OneMax's zero count exactly
when the selected coordinate is zero. -/
theorem candidate_rls_selectedZeroCount
    {n : Nat} (x : BitString n) (i : Fin n) :
    zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
      if x i = false then zeroCount x - 1 else zeroCount x := by
  by_cases hxi : x i = false
  · have hacc : Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact_mod_cast Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi)
    rw [selectedAfterMask,
      elitistSelect_of_accepts _ _ _ hacc, ite_eq_left hxi]
    have hcount := zeroCount_mutate_single_of_false x i hxi
    omega
  · have hxi' : x i = true := by
      cases hi : x i <;> simp_all
    have hrej : ¬ Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hxi'
      have hdrop : oneCount (mutateWithMask x ({i} : MutationMask n)) <
          oneCount x := by omega
      exact not_le_of_gt (by exact_mod_cast hdrop :
        (oneCount (mutateWithMask x ({i} : MutationMask n)) : Real) <
          (oneCount x : Real))
    rw [selectedAfterMask,
      elitistSelect_of_rejects _ _ _ hrej, ite_eq_right hxi]

/-- Exactly `zeroCount x` singleton coordinates are improving. -/
theorem candidate_rls_sum_zeroIndicators {n : Nat} (x : BitString n) :
    (∑ i : Fin n, if x i = false then (1 : Real) else 0) =
      (zeroCount x : Real) := by
  classical
  calc
    (∑ i : Fin n, if x i = false then (1 : Real) else 0) =
        ∑ i ∈ zeroPositions x, (1 : Real) := by
          simp [zeroPositions]
    _ = ((zeroPositions x).card : Real) := by simp
    _ = (zeroCount x : Real) := by rw [zeroPositions_card]

/-- Convert the natural-number singleton identity to a real difference. -/
theorem candidate_rls_selectedZeroCount_real
    {n : Nat} (x : BitString n) (i : Fin n) :
    (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) : Real) =
      (zeroCount x : Real) - (if x i = false then 1 else 0) := by
  by_cases hi : x i = false
  · have hmem : i ∈ zeroPositions x := (mem_zeroPositions x i).mpr hi
    have hkpos : 0 < zeroCount x := by
      have hp : 0 < (zeroPositions x).card := Finset.card_pos.mpr ⟨i, hmem⟩
      rwa [zeroPositions_card] at hp
    have hstep := candidate_rls_selectedZeroCount x i
    rw [hstep, ite_eq_left hi, Nat.cast_sub (by omega : 1 ≤ zeroCount x)]
    simp [hi]
  · have hstep := candidate_rls_selectedZeroCount x i
    simp [hstep, hi]

/-- Exact one-step conditional zero-count mean for one-bit elitist OneMax. -/
theorem candidate_rlsOneMax_expectedZeroCount_exact
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x =
      (1 - 1 / (n : Real)) * (zeroCount x : Real) := by
  classical
  have hn0 : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hsum :
      (∑ i : Fin n,
        (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) : Real)) =
      (n : Real) * (zeroCount x : Real) - (zeroCount x : Real) := by
    simp_rw [candidate_rls_selectedZeroCount_real]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      candidate_rls_sum_zeroIndicators]
    simp
  calc
    expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (fun y : BitString n => (zeroCount y : Real)) x =
      (n : Real)⁻¹ *
        (∑ i : Fin n,
          (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) : Real)) :=
          candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal
            (fun y : BitString n => (zeroCount y : Real)) x
    _ = (n : Real)⁻¹ *
      ((n : Real) * (zeroCount x : Real) - (zeroCount x : Real)) := by
        rw [hsum]
    _ = (1 - 1 / (n : Real)) * (zeroCount x : Real) := by
        field_simp [hn0]

/-- Exact harmonic predecessor identity. This is also the content of the
approved, independently checked Stage 126 wrapper. -/
theorem candidate_rls_harmonic_predecessor
    (k : Nat) (hk : 0 < k) :
    harmonicReal (k - 1) + (1 : Real) / k = harmonicReal k := by
  cases k with
  | zero => omega
  | succ j =>
      simp [harmonicReal, harmonic_succ, div_eq_mul_inv]

/-- Every singleton removes exactly `1/k` harmonic units if it selects
one of the `k` currently zero coordinates. -/
theorem candidate_rls_harmonic_oneBit_drop
    {n : Nat} (x : BitString n) (i : Fin n) :
    harmonicReal (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n))) =
      harmonicReal (zeroCount x) -
        (if x i = false then (zeroCount x : Real)⁻¹ else 0) := by
  by_cases hi : x i = false
  · have hmem : i ∈ zeroPositions x := (mem_zeroPositions x i).mpr hi
    have hkpos : 0 < zeroCount x := by
      have hp : 0 < (zeroPositions x).card := Finset.card_pos.mpr ⟨i, hmem⟩
      rwa [zeroPositions_card] at hp
    have hstep := candidate_rls_selectedZeroCount x i
    have hh := candidate_rls_harmonic_predecessor (zeroCount x) hkpos
    rw [hstep, ite_eq_left hi]
    simp only [ite_eq_left hi]
    have hdiv : (1 : Real) / (zeroCount x : Real) =
        (zeroCount x : Real)⁻¹ := by ring
    rw [hdiv] at hh
    linarith
  · have hstep := candidate_rls_selectedZeroCount x i
    simpa [hi] using congrArg harmonicReal (by simpa [hi] using hstep)

/-- Exact one-step coupon-collector Bellman identity for OneMax. -/
theorem candidate_rlsOneMax_harmonic_one_step
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (n : Real) * harmonicReal (zeroCount y)) x =
      if zeroCount x = 0 then 0
      else (n : Real) * harmonicReal (zeroCount x) - 1 := by
  classical
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsumDrop :
      (∑ i : Fin n,
        if x i = false then (zeroCount x : Real)⁻¹ else 0) =
      (zeroCount x : Real) * (zeroCount x : Real)⁻¹ := by
    calc
      _ = ∑ i : Fin n,
          (if x i = false then (1 : Real) else 0) * (zeroCount x : Real)⁻¹ := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
      _ = (∑ i : Fin n, if x i = false then (1 : Real) else 0) *
          (zeroCount x : Real)⁻¹ := by rw [Finset.sum_mul]
      _ = _ := by rw [candidate_rls_sum_zeroIndicators]
  have hsumH :
      (∑ i : Fin n,
        harmonicReal (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)))) =
      (n : Real) * harmonicReal (zeroCount x) -
        (zeroCount x : Real) * (zeroCount x : Real)⁻¹ := by
    simp_rw [candidate_rls_harmonic_oneBit_drop]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsumDrop]
    simp
  calc
    expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (fun y : BitString n => (n : Real) * harmonicReal (zeroCount y)) x =
      (n : Real)⁻¹ *
        (∑ i : Fin n, (n : Real) *
          harmonicReal (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)))) :=
          candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal
            (fun y : BitString n => (n : Real) * harmonicReal (zeroCount y)) x
    _ = ∑ i : Fin n,
        harmonicReal (zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n))) := by
          rw [← Finset.mul_sum]
          field_simp [hn0]
    _ = (n : Real) * harmonicReal (zeroCount x) -
      (zeroCount x : Real) * (zeroCount x : Real)⁻¹ := hsumH
    _ = if zeroCount x = 0 then 0
      else (n : Real) * harmonicReal (zeroCount x) - 1 := by
        by_cases hk : zeroCount x = 0
        · simp [hk]
        · have hkr : (zeroCount x : Real) ≠ 0 := by exact_mod_cast hk
          simp [hk, hkr]

end ECRuntime
