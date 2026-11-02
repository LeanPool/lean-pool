/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.JointCongruence

/-! # Summing densities of disjoint congruence conditions

The exact CRT interval count, with its fixed remainder, implies density
comparison for any finite disjoint collection of congruence conditions. This
avoids choosing a common modulus or lifting residue representatives.
-/

@[expose] public section

namespace NairTenenbaum

/-- A bounded additive remainder disappears when a counting inequality holds
for every natural interval length. -/
theorem le_of_nat_mul_le_add {u v C : ℝ} (H : ∀ N : ℕ, (N : ℝ) * u ≤ N * v + C) : u ≤ v := by
  by_contra h
  have hgap : 0 < u - v := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (u - v))
  have HN := (div_lt_iff₀ hgap).mp hN
  nlinarith [H N]

/-- Root density for simultaneous polynomial congruences at coprime moduli. -/
noncomputable def jointRootDensity {ι : Type*} [Fintype ι]
    (Q : ι → Polynomial ℤ) (q : ι → ℕ) : ℝ :=
  ∏ i, (rootCount (Q i) (q i) : ℝ) / q i

theorem jointCongruenceCount_density_error {ι : Type*} [Fintype ι]
    (Q : ι → Polynomial ℤ) (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j)) (N : ℕ) :
    |(jointCongruenceCount Q q 0 N : ℝ) - N * jointRootDensity Q q| ≤
      ∏ i, (rootCount (Q i) (q i) : ℝ) := by
  have H := jointCongruenceCount_error Q q hq hcop 0 (N : ℤ) (Int.natCast_nonneg N)
  simpa only [jointRootDensity, Finset.prod_div_distrib, Int.cast_natCast, Int.cast_zero,
    sub_zero, Nat.cast_prod, mul_div_assoc] using H

/-- A disjoint family of joint congruence conditions has total density at
most any joint condition containing their union. -/
theorem sum_jointRootDensity_le {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Finset α) (Q : α → ι → Polynomial ℤ) (q : α → ι → ℕ)
    (hq : ∀ s ∈ S, ∀ i, 0 < q s i)
    (hcop : ∀ s ∈ S, Pairwise fun i j => Nat.Coprime (q s i) (q s j))
    (R : κ → Polynomial ℤ) (m : κ → ℕ) (hm : ∀ i, 0 < m i)
    (hmCop : Pairwise fun i j => Nat.Coprime (m i) (m j))
    (hdisjoint : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∀ t : ℤ,
      (∀ i, (q s i : ℤ) ∣ (Q s i).eval t) → ¬(∀ i, (q s' i : ℤ) ∣ (Q s' i).eval t))
    (hsub : ∀ s ∈ S, ∀ t : ℤ, (∀ i, (q s i : ℤ) ∣ (Q s i).eval t) →
      ∀ i, (m i : ℤ) ∣ (R i).eval t) :
    (∑ s ∈ S, jointRootDensity (Q s) (q s)) ≤ jointRootDensity R m := by
  classical
  apply le_of_nat_mul_le_add (C := (∑ s ∈ S, ∏ i, (rootCount (Q s i) (q s i) : ℝ)) +
    ∏ i, (rootCount (R i) (m i) : ℝ))
  intro N
  have hcount : (∑ s ∈ S, jointCongruenceCount (Q s) (q s) 0 N) ≤
      jointCongruenceCount R m 0 N := by
    let T : α → Finset ℤ := fun s => (Finset.Ioc 0 (N : ℤ)).filter
      (fun t => ∀ i, (q s i : ℤ) ∣ (Q s i).eval t)
    have hd : (S : Set α).PairwiseDisjoint T := by
      intro s hs s' hs' hne
      apply Finset.disjoint_left.mpr
      intro t ht ht'
      exact hdisjoint s hs s' hs' hne t (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp ht').2
    have hsubset : S.biUnion T ⊆ (Finset.Ioc 0 (N : ℤ)).filter
        (fun t => ∀ i, (m i : ℤ) ∣ (R i).eval t) := by
      intro t ht
      obtain ⟨s, hs, ht⟩ := Finset.mem_biUnion.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
        hsub s hs t (Finset.mem_filter.mp ht).2⟩
    have H := Finset.card_le_card hsubset
    rw [Finset.card_biUnion hd] at H
    exact H
  have hcountR : (∑ s ∈ S, (jointCongruenceCount (Q s) (q s) 0 N : ℝ)) ≤
      (jointCongruenceCount R m 0 N : ℝ) := by exact_mod_cast hcount
  have Hlower : (N : ℝ) * (∑ s ∈ S, jointRootDensity (Q s) (q s)) ≤
      (∑ s ∈ S, (jointCongruenceCount (Q s) (q s) 0 N : ℝ)) +
      ∑ s ∈ S, ∏ i, (rootCount (Q s i) (q s i) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have H := (abs_le.mp (jointCongruenceCount_density_error (Q s) (q s) (hq s hs) (hcop s hs) N)).1
    linarith
  have Hupper := (abs_le.mp (jointCongruenceCount_density_error R m hm hmCop N)).2
  linarith

end NairTenenbaum
