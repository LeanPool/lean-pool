/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.ConditionalPolynomialSieve

/-! # Common reindexing of sifted divisor sums

The polynomial and sieve modulus can vary independently of the divisor tuple
set. A congruence witness supplies the discriminant conditions for the split.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- A sifted divisor sum with the divisor set, the sifted polynomial and the modulus as
parameters. -/
noncomputable def PolynomialSystem.siftedDivisorSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (T : Finset (Tuple r)) (H : ℤ[X]) (M : Tuple r → ℕ) (a b : ℤ) : ℝ :=
  ∑ m ∈ T, pullback P.exponent F m * conditionalPolynomialSiftedCount H (M m) P.R m a b

/-- Generic whole-prime-power split. `hmem` is the only instance-specific fact. -/
theorem PolynomialSystem.siftedDivisorSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (T : Finset (Tuple r)) (H : ℤ[X]) (M : Tuple r → ℕ)
    (a b : ℤ) (V : Finset (Tuple r)) (U : Tuple r → Finset (Tuple r))
    (hmem : ∀ m ∈ T, ∀ n : ℤ, (∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs) →
      primeReject m P.discriminant.primeFactors ∈ V ∧
      primeSelect m P.discriminant.primeFactors ∈ U (primeReject m P.discriminant.primeFactors)) :
    P.siftedDivisorSum F T H M a b ≤
      ∑ v ∈ V, ∑ u ∈ U v, pullback P.exponent F (u * v) *
        conditionalPolynomialSiftedCount H (M (u * v)) P.R (u * v) a b := by
  classical
  let count := fun m => conditionalPolynomialSiftedCount H (M m) P.R m a b
  let e : Tuple r → (Σ _v : Tuple r, Tuple r) := fun m =>
    ⟨primeReject m P.discriminant.primeFactors, primeSelect m P.discriminant.primeFactors⟩
  have heprod (m : Tuple r) : (e m).2 * (e m).1 = m := primeSelect_mul_primeReject _ _
  have heinj : Function.Injective e := by
    intro m n h
    simpa only [heprod] using congrArg (fun t : Σ _v : Tuple r, Tuple r => t.2 * t.1) h
  have himage : Finset.image e (T.filter fun m => count m ≠ 0) ⊆ V.sigma U := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨n, hn⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
    have hdiv : ∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs := fun i =>
      Int.natCast_dvd.mp ((Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2 i)
    exact Finset.mem_sigma.mpr (hmem m hm n hdiv)
  have hrestrict : P.siftedDivisorSum F T H M a b =
      ∑ m ∈ T.filter (fun m => count m ≠ 0), pullback P.exponent F m * count m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnot
    have hc : count m = 0 := by by_contra h; exact hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
    simp only [hc, Nat.cast_zero, mul_zero]
  rw [hrestrict]
  have Hle := Finset.sum_le_sum_of_injOn e heinj.injOn himage
    (f := fun m => pullback P.exponent F m * count m)
    (g := fun t => pullback P.exponent F (t.2 * t.1) *
      conditionalPolynomialSiftedCount H (M (t.2 * t.1)) P.R (t.2 * t.1) a b)
    (fun m _ => by rw [heprod])
    (fun t _ _ => mul_nonneg (hF _) (Nat.cast_nonneg _))
  simpa only [Finset.sum_sigma] using Hle

/-- Group selected divisor tuples by their fibers; a sieve witness bounds each fiber. -/
theorem PolynomialSystem.sum_selected_le_siftedDivisorSum {k r : ℕ}
    (P : PolynomialSystem k r) {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    (V : Finset (Tuple r)) (H : ℤ[X]) (M : Tuple r → ℕ) (a b : ℤ)
    (T : Finset ℤ) (m : ℤ → Tuple r) (hT : T ⊆ Finset.Ioc a b)
    (hmap : ∀ t ∈ T, m t ∈ V)
    (hdiv : ∀ t ∈ T, ∀ i, (m t i : ℤ) ∣ (P.R i).eval t)
    (hsift : ∀ t ∈ T, Nat.Coprime (M (m t)) (H.eval t).natAbs) :
    (∑ t ∈ T, pullback P.exponent F (m t)) ≤ P.siftedDivisorSum F V H M a b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  unfold PolynomialSystem.siftedDivisorSum
  apply Finset.sum_le_sum
  intro v _
  have hcard : (T.filter (fun t => m t = v)).card ≤
      conditionalPolynomialSiftedCount H (M v) P.R v a b := by
    apply Finset.card_le_card
    intro t ht
    obtain ⟨ht, hmt⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hT ht, hmt ▸ hdiv t ht⟩,
      hmt ▸ hsift t ht⟩
  calc
    _ = (T.filter (fun t => m t = v)).card * pullback P.exponent F v := by
      rw [Finset.sum_congr rfl (fun t ht =>
        congrArg (pullback P.exponent F) (Finset.mem_filter.mp ht).2)]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      rw [mul_comm (pullback P.exponent F v)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hF _)

end NairTenenbaum
