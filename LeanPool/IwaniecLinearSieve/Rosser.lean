/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Rosser's linear sieve, combinatorial part ([I71, §2], `k = 1`)

* `rosserSet lower y z`: the supports `D⁻` (`lower = true`) and `D⁺` (`lower = false`) of
  Rosser's `β = 2` sieve, defined recursively by
  `D^± (y, z) = {1} ∪ ⋃_{p < z} p · D^∓ (y / p, p)`, where `D⁺` only admits `p³ < y`.
* `rosserSieve_le_siftIndicator_le`: the sieve property
  `∑_{d ∈ D⁻, d ∣ m} μ(d) ≤ [(m, P(z)) = 1] ≤ ∑_{d ∈ D⁺, d ∣ m} μ(d)`, from Buchstab's identity.
* `rosserMain lower y z = ∑_{d ∈ D^±} μ(d)/d` and the depth-truncated deficits `fail`, with
  `R(z) - rosserMain true y z = fail true r y z` and
  `rosserMain false y z - R(z) = fail false r y z` for `r > π(z)` (`fail_eq_of_card_lt`);
  `R(z) = 1 - ∑_{p < z} R(p)/p` is `R_eq`.
* `card_rosserSet`, `card_filter_rosserSet_succ`: the counting recursions ([I71, Lemma 17]).
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace IwaniecLinearSieve

section primesLT

variable {z : ℝ} {p : ℕ}

theorem lt_ceil_of_mem_primesLT (hp : p ∈ primesLT z) : p < ⌈z⌉₊ :=
  Nat.lt_of_mem_primesBelow hp

theorem prime_of_mem_primesLT (hp : p ∈ primesLT z) : p.Prime :=
  (mem_primesLT.1 hp).1

theorem lt_of_mem_primesLT (hp : p ∈ primesLT z) : (p : ℝ) < z :=
  (mem_primesLT.1 hp).2

theorem primesLT_natCast_subset (hp : p ∈ primesLT z) : primesLT p ⊆ primesLT z := by
  intro q hq
  rw [mem_primesLT] at hq ⊢
  exact ⟨hq.1, hq.2.trans (lt_of_mem_primesLT hp)⟩

theorem notMem_primesLT_self : p ∉ primesLT p := by
  simp [mem_primesLT]

theorem primesLT_natCast_ssubset (hp : p ∈ primesLT z) : primesLT p ⊂ primesLT z :=
  ssubset_of_subset_of_ne (primesLT_natCast_subset hp) fun h ↦
    notMem_primesLT_self (h ▸ hp)

/-- For `p < z` prime, the primes below `z` that are smaller than `p` are the primes below `p`. -/
theorem filter_lt_primesLT (hp : p ∈ primesLT z) :
    (primesLT z).filter (· < p) = primesLT p := by
  ext q
  simp only [mem_filter, mem_primesLT, Nat.cast_lt]
  constructor
  · rintro ⟨⟨hq, -⟩, hqp⟩
    exact ⟨hq, hqp⟩
  · rintro ⟨hq, hqp⟩
    exact ⟨⟨hq, (Nat.cast_lt.2 hqp).trans (lt_of_mem_primesLT hp)⟩, hqp⟩

/-- Strong induction on `⌈z⌉₊`, descending from `z` to the primes below `z`. -/
theorem primesLT_induction {P : ℝ → Prop} (h : ∀ z, (∀ p ∈ primesLT z, P p) → P z) (z : ℝ) :
    P z := by
  suffices ∀ n : ℕ, ∀ z : ℝ, ⌈z⌉₊ = n → P z from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro z rfl
    exact h z fun p hp ↦ ih p (by simpa using lt_ceil_of_mem_primesLT hp) p (by simp)

/-- [I71, (2.11)] with `k = 1`: `R(z) = 1 - ∑_{p < z} R(p) / p`. -/
theorem R_eq (z : ℝ) : R z = 1 - ∑ p ∈ primesLT z, R p / p := by
  rw [R, prod_one_sub_ordered]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [filter_lt_primesLT hp, R, div_eq_inv_mul]

end primesLT

/-! ### The sets `D^±` -/

/-- The primes `p < z` admitted at the top level of `rosserSet lower y z`: all of them for the
lower-bound sieve, and those with `p³ < y` for the upper-bound sieve. -/
noncomputable def rosserPrimes (lower : Bool) (y z : ℝ) : Finset ℕ :=
  (primesLT z).filter fun p ↦ lower = true ∨ (p : ℝ) ^ 3 < y

/-- Rosser's sieve support (`β = 2`, [I71, §2]): `rosserSet true y z` is `D⁻` and
`rosserSet false y z` is `D⁺`. Equivalently `d = p₁ ⋯ p_l` with `z > p₁ > ⋯ > p_l` prime and
`p₁ ⋯ p_m p_m² < y` for every `m ≤ l` which is even (for `D⁻`) or odd (for `D⁺`). -/
noncomputable def rosserSet (lower : Bool) (y z : ℝ) : Finset ℕ :=
  insert 1 ((rosserPrimes lower y z).attach.biUnion fun p ↦
    (rosserSet (!lower) (y / p.1) p.1).image (p.1 * ·))
termination_by ⌈z⌉₊
decreasing_by
  rw [Nat.ceil_natCast]
  exact lt_ceil_of_mem_primesLT (mem_filter.1 p.2).1

variable {lower : Bool} {y z : ℝ} {p d : ℕ}

theorem mem_rosserPrimes :
    p ∈ rosserPrimes lower y z ↔ p ∈ primesLT z ∧ (lower = true ∨ (p : ℝ) ^ 3 < y) :=
  mem_filter

@[simp] theorem rosserPrimes_true : rosserPrimes true y z = primesLT z := by
  simp [rosserPrimes]

theorem rosserPrimes_false :
    rosserPrimes false y z = (primesLT z).filter fun p : ℕ ↦ (p : ℝ) ^ 3 < y := by
  simp [rosserPrimes]

theorem rosserPrimes_subset : rosserPrimes lower y z ⊆ primesLT z :=
  filter_subset _ _

theorem rosserSet_eq (lower : Bool) (y z : ℝ) :
    rosserSet lower y z = insert 1 ((rosserPrimes lower y z).biUnion fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·)) := by
  rw [rosserSet]
  ext d
  simp

theorem one_mem_rosserSet : 1 ∈ rosserSet lower y z := by
  rw [rosserSet_eq]
  exact mem_insert_self _ _

theorem mem_rosserSet : d ∈ rosserSet lower y z ↔
    d = 1 ∨ ∃ p ∈ rosserPrimes lower y z, ∃ e ∈ rosserSet (!lower) (y / p) p, d = p * e := by
  rw [rosserSet_eq]
  simp [eq_comm (a := d)]

/-- Elements of `rosserSet lower y z` are squarefree products of primes below `z`. -/
theorem squarefree_and_primeFactors_subset (hd : d ∈ rosserSet lower y z) :
    Squarefree d ∧ d.primeFactors ⊆ primesLT z := by
  induction z using primesLT_induction generalizing lower y d with
  | h z ih =>
    rcases mem_rosserSet.1 hd with rfl | ⟨p, hp, e, he, rfl⟩
    · simp
    have hpz := rosserPrimes_subset hp
    have hpp := prime_of_mem_primesLT hpz
    obtain ⟨hse, hpe⟩ := ih p hpz he
    have hne : ¬ p ∣ e := fun h ↦
      notMem_primesLT_self (hpe (Nat.mem_primeFactors.2 ⟨hpp, h, hse.ne_zero⟩))
    refine ⟨Nat.squarefree_mul_iff.2 ⟨(Nat.Prime.coprime_iff_not_dvd hpp).2 hne,
      hpp.squarefree, hse⟩, ?_⟩
    rw [Nat.primeFactors_mul hpp.ne_zero hse.ne_zero, hpp.primeFactors]
    exact union_subset (singleton_subset_iff.2 hpz) (hpe.trans (primesLT_natCast_subset hpz))

theorem squarefree_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) : Squarefree d :=
  (squarefree_and_primeFactors_subset hd).1

theorem primeFactors_subset_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) :
    d.primeFactors ⊆ primesLT z :=
  (squarefree_and_primeFactors_subset hd).2

theorem pos_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) : 0 < d :=
  Nat.pos_of_ne_zero (squarefree_of_mem_rosserSet hd).ne_zero

/-- Elements of `rosserSet` are squarefree divisors of `primorialLT z`. -/
theorem dvd_primorialLT_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) :
    d ∣ primorialLT z := by
  rw [← Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
  exact prod_dvd_prod_of_subset _ _ _ (primeFactors_subset_of_mem_rosserSet hd)

theorem lt_of_prime_dvd_of_mem_rosserSet {q : ℕ} (hq : q.Prime) (hd : d ∈ rosserSet lower y z)
    (hqd : q ∣ d) : (q : ℝ) < z :=
  lt_of_mem_primesLT <| primeFactors_subset_of_mem_rosserSet hd <|
    Nat.mem_primeFactors.2 ⟨hq, hqd, (pos_of_mem_rosserSet hd).ne'⟩

theorem not_dvd_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) : ¬ p ∣ d :=
  fun h ↦ (lt_irrefl _) (lt_of_prime_dvd_of_mem_rosserSet hp hd h)

theorem coprime_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) :
    p.Coprime d :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_mem_rosserSet hp hd)


theorem pairwiseDisjoint_rosserSet_image (lower : Bool) (y z : ℝ) :
    (rosserPrimes lower y z : Set ℕ).PairwiseDisjoint fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·) := by
  intro p hp q hq hpq
  simp only [Function.onFun]
  rw [disjoint_left]
  simp only [mem_image, not_exists, not_and]
  rintro _ ⟨d, hd, rfl⟩ e he hde
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  have hq' := prime_of_mem_primesLT (rosserPrimes_subset hq)
  have key : ∀ {p q d e : ℕ}, p.Prime → q.Prime → p ≠ q → e ∈ rosserSet (!lower) (y / q) q →
      q * e = p * d → (p : ℝ) < q := by
    intro p q d e hp hq hpq he h
    have : p ∣ q * e := h ▸ dvd_mul_right p d
    rcases (Nat.Prime.dvd_mul hp).1 this with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).1 h') hpq
    · exact lt_of_prime_dvd_of_mem_rosserSet hp he h'
  exact lt_asymm (key hp' hq' hpq he hde) (key hq' hp' (Ne.symm hpq) hd hde.symm)

theorem one_notMem_biUnion_rosserSet (lower : Bool) (y z : ℝ) :
    1 ∉ (rosserPrimes lower y z).biUnion fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·) := by
  simp only [mem_biUnion, mem_image, not_exists, not_and]
  intro p hp d _ h
  exact (prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt.ne'
    (Nat.eq_one_of_mul_eq_one_right h)

/-- Sums over `rosserSet` unfold along the recursion. -/
theorem sum_rosserSet {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lower : Bool) (y z : ℝ) :
    ∑ d ∈ rosserSet lower y z, f d =
      f 1 + ∑ p ∈ rosserPrimes lower y z, ∑ d ∈ rosserSet (!lower) (y / p) p, f (p * d) := by
  rw [rosserSet_eq, sum_insert (one_notMem_biUnion_rosserSet lower y z),
    sum_biUnion (pairwiseDisjoint_rosserSet_image lower y z)]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [sum_image]
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_left (prime_of_mem_primesLT (rosserPrimes_subset hp)).pos h

/-- The size of the sieve support satisfies the same recursion as the set. -/
theorem card_rosserSet (lower : Bool) (y z : ℝ) :
    #(rosserSet lower y z) = 1 + ∑ p ∈ rosserPrimes lower y z, #(rosserSet (!lower) (y / p) p) := by
  simpa using sum_rosserSet (fun _ ↦ (1 : ℕ)) lower y z

theorem card_primeFactors_mul_of_mem_rosserSet (hp : p.Prime)
    (hd : d ∈ rosserSet lower y p) : #(p * d).primeFactors = #d.primeFactors + 1 := by
  rw [Nat.primeFactors_mul hp.ne_zero (pos_of_mem_rosserSet hd).ne', hp.primeFactors,
    singleton_union, card_insert_of_notMem]
  exact fun h ↦ not_dvd_of_mem_rosserSet hp hd (Nat.dvd_of_mem_primeFactors h)

/-- The elements of `rosserSet` with at most `0` prime factors. -/
theorem card_filter_rosserSet_zero (lower : Bool) (y z : ℝ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ 0) = 1 := by
  rw [card_eq_one]
  refine ⟨1, ?_⟩
  ext d
  simp only [mem_filter, nonpos_iff_eq_zero, card_eq_zero, Nat.primeFactors_eq_empty,
    mem_singleton]
  constructor
  · rintro ⟨hd, h0 | h1⟩
    · exact absurd h0 (pos_of_mem_rosserSet hd).ne'
    · exact h1
  · rintro rfl
    exact ⟨one_mem_rosserSet, Or.inr rfl⟩

/-- Depth-truncated counts ([I71, Lemma 17]): the elements of `rosserSet` with at most `n + 1`
prime factors. -/
theorem card_filter_rosserSet_succ (n : ℕ) (lower : Bool) (y z : ℝ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ n + 1) =
      1 + ∑ p ∈ rosserPrimes lower y z,
        #((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) := by
  simp only [card_filter]
  rw [sum_rosserSet]
  simp only [Nat.primeFactors_one, card_empty, zero_le, ite_true]
  congr 1
  refine sum_congr rfl fun p hp ↦ sum_congr rfl fun d hd ↦ ?_
  rw [card_primeFactors_mul_of_mem_rosserSet (prime_of_mem_primesLT (rosserPrimes_subset hp)) hd]
  simp

/-! ### Main terms -/

/-- `∑_{d ∈ D^±} μ(d) / d`. -/
noncomputable def rosserMain (lower : Bool) (y z : ℝ) : ℝ :=
  ∑ d ∈ rosserSet lower y z, (μ d : ℝ) / d

theorem moebius_mul_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) :
    μ (p * d) = -μ d := by
  rw [isMultiplicative_moebius.map_mul_of_coprime (coprime_of_mem_rosserSet hp hd),
    moebius_apply_prime hp, neg_one_mul]

theorem rosserMain_eq (lower : Bool) (y z : ℝ) :
    rosserMain lower y z = 1 - ∑ p ∈ rosserPrimes lower y z, rosserMain (!lower) (y / p) p / p := by
  rw [rosserMain, sum_rosserSet, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [moebius_apply_one, Int.cast_one, Nat.cast_one, div_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  rw [rosserMain, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [moebius_mul_of_mem_rosserSet hp' hd]
  push_cast
  field_simp


/-! ### The sieve property -/

/-- `1` if no prime `p < z` divides `m`, and `0` otherwise. -/
noncomputable def siftIndicator (z : ℝ) (m : ℕ) : ℤ :=
  if ∀ p ∈ primesLT z, ¬ p ∣ m then 1 else 0

theorem siftIndicator_nonneg (z : ℝ) (m : ℕ) : 0 ≤ siftIndicator z m := by
  unfold siftIndicator
  split_ifs <;> norm_num

/-- Buchstab's identity for the indicator: `[(m, P(z)) = 1] = 1 - ∑_{p < z, p ∣ m} [(m, P(p)) = 1]`,
i.e. [I71, (2.3)] for a single integer. -/
theorem siftIndicator_eq (z : ℝ) (m : ℕ) :
    siftIndicator z m = 1 - ∑ p ∈ (primesLT z).filter (· ∣ m), siftIndicator p m := by
  set F := (primesLT z).filter (· ∣ m)
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF, sum_empty, sub_zero, siftIndicator, ite_eq_left]
    intro p hp hpm
    have : p ∈ F := mem_filter.2 ⟨hp, hpm⟩
    simp [hF] at this
  set p₀ := F.min' hF
  have hp₀ : p₀ ∈ F := F.min'_mem hF
  have hsum : ∑ p ∈ F, siftIndicator p m = ∑ p ∈ F, if p = p₀ then 1 else 0 := by
    refine sum_congr rfl fun p hp ↦ ?_
    rw [siftIndicator]
    have hpz := (mem_filter.1 hp).1
    congr 1
    apply propext
    constructor
    · intro h
      refine le_antisymm ?_ (F.min'_le p hp)
      by_contra hlt
      exact h p₀ (mem_primesLT.2 ⟨prime_of_mem_primesLT (mem_filter.1 hp₀).1,
        by exact_mod_cast not_le.1 hlt⟩) (mem_filter.1 hp₀).2
    · rintro rfl q hq hqm
      have hqF : q ∈ F := mem_filter.2 ⟨primesLT_natCast_subset hpz hq, hqm⟩
      exact absurd (F.min'_le q hqF) (not_le.2 (by exact_mod_cast lt_of_mem_primesLT hq))
  rw [hsum, sum_ite_eq' F p₀, ite_eq_left hp₀, siftIndicator, ite_eq_right]
  · norm_num
  · push Not
    exact ⟨p₀, (mem_filter.1 hp₀).1, (mem_filter.1 hp₀).2⟩

/-- For `m ∣ P(z)`, the indicator is `[m = 1]`. -/
theorem siftIndicator_of_dvd_primorialLT {m : ℕ} (hm : m ∣ primorialLT z) :
    siftIndicator z m = if m = 1 then 1 else 0 := by
  rw [siftIndicator]
  congr 1
  apply propext
  constructor
  · intro h
    by_contra hm1
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hqP : q ∣ primorialLT z := hqm.trans hm
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hqP
    rw [(Nat.prime_dvd_prime_iff_eq hq (prime_of_mem_primesLT hp)).1 hqp] at hqm
    exact h p hp hqm
  · rintro rfl p hp h
    exact (prime_of_mem_primesLT hp).one_lt.ne' (Nat.dvd_one.1 h)


/-- `∑_{d ∈ D^±, d ∣ m} μ(d)`. -/
noncomputable def rosserSieve (lower : Bool) (y z : ℝ) (m : ℕ) : ℤ :=
  ∑ d ∈ (rosserSet lower y z).filter (· ∣ m), μ d

theorem rosserSieve_eq (lower : Bool) (y z : ℝ) (m : ℕ) :
    rosserSieve lower y z m =
      1 - ∑ p ∈ (rosserPrimes lower y z).filter (· ∣ m), rosserSieve (!lower) (y / p) p m := by
  rw [rosserSieve, sum_filter, sum_rosserSet, sum_filter, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [one_dvd, ite_true, moebius_apply_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  split_ifs with hpm
  · rw [rosserSieve, sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun d hd ↦ ?_
    have key : p * d ∣ m ↔ d ∣ m :=
      ⟨fun h ↦ (dvd_mul_left d p).trans h,
        fun h ↦ Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_of_mem_rosserSet hp' hd) hpm h⟩
    simp only [key, moebius_mul_of_mem_rosserSet hp' hd]
    split_ifs <;> simp
  · refine sum_eq_zero fun d _ ↦ ?_
    rw [ite_eq_right]
    exact fun h ↦ hpm ((dvd_mul_right p d).trans h)


/-- The sieve property of Rosser's weights, for every `m`:
`∑_{d ∈ D⁻, d ∣ m} μ(d) ≤ [(m, P(z)) = 1] ≤ ∑_{d ∈ D⁺, d ∣ m} μ(d)`. -/
theorem rosserSieve_le_siftIndicator_le (y z : ℝ) (m : ℕ) :
    rosserSieve true y z m ≤ siftIndicator z m ∧ siftIndicator z m ≤ rosserSieve false y z m := by
  induction z using primesLT_induction generalizing y with
  | h z ih =>
    constructor
    · rw [rosserSieve_eq, siftIndicator_eq, rosserPrimes_true]
      refine sub_le_sub_left (sum_le_sum fun p hp ↦ ?_) _
      exact (ih p (mem_filter.1 hp).1 (y / p)).2
    · rw [rosserSieve_eq, siftIndicator_eq]
      refine sub_le_sub_left ?_ _
      calc ∑ p ∈ (rosserPrimes false y z).filter (· ∣ m), rosserSieve (!false) (y / p) p m
          ≤ ∑ p ∈ (rosserPrimes false y z).filter (· ∣ m), siftIndicator p m :=
            sum_le_sum fun p hp ↦
              (ih p (rosserPrimes_subset (mem_filter.1 hp).1) (y / p)).1
        _ ≤ ∑ p ∈ (primesLT z).filter (· ∣ m), siftIndicator p m :=
            sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ rosserPrimes_subset)
              fun p _ _ ↦ siftIndicator_nonneg p m

/-- Lower-bound sieve property: `∑_{d ∈ D⁻, d ∣ m} μ(d) ≤ [no prime p < z divides m]`. -/
theorem sum_moebius_rosserSet_true_le (y z : ℝ) (m : ℕ) :
    ∑ d ∈ (rosserSet true y z).filter (· ∣ m), μ d ≤
      if ∀ p ∈ primesLT z, ¬ p ∣ m then 1 else 0 :=
  (rosserSieve_le_siftIndicator_le y z m).1

/-- Upper-bound sieve property: `[no prime p < z divides m] ≤ ∑_{d ∈ D⁺, d ∣ m} μ(d)`. -/
theorem le_sum_moebius_rosserSet_false (y z : ℝ) (m : ℕ) :
    (if ∀ p ∈ primesLT z, ¬ p ∣ m then 1 else 0) ≤
      ∑ d ∈ (rosserSet false y z).filter (· ∣ m), μ d :=
  (rosserSieve_le_siftIndicator_le y z m).2

/-- The sieve property for divisors of `P(z)`:
`∑_{d ∈ D⁻, d ∣ m} μ(d) ≤ [m = 1] ≤ ∑_{d ∈ D⁺, d ∣ m} μ(d)`. -/
theorem rosserSieve_of_dvd_primorialLT (y : ℝ) {m : ℕ} (hm : m ∣ primorialLT z) :
    ∑ d ∈ (rosserSet true y z).filter (· ∣ m), μ d ≤ (if m = 1 then 1 else 0) ∧
      (if m = 1 then 1 else 0) ≤ ∑ d ∈ (rosserSet false y z).filter (· ∣ m), μ d := by
  rw [← siftIndicator_of_dvd_primorialLT hm]
  exact rosserSieve_le_siftIndicator_le y z m

/-! ### The deficits `R(z) - ∑_{D⁻} μ(d)/d` and `∑_{D⁺} μ(d)/d - R(z)` -/

/-- Depth-truncated deficits ([I71, (2.9), (2.10)] with `k = 1`): `fail true r y z` and
`fail false r y z` are `R(z) - ∑_{d ∈ D⁻} μ(d)/d` and `∑_{d ∈ D⁺} μ(d)/d - R(z)` computed to
depth `r`. -/
noncomputable def fail : Bool → ℕ → ℝ → ℝ → ℝ
  | _, 0, _, _ => 0
  | true, r + 1, y, z => ∑ p ∈ primesLT z, fail false r (y / p) p / p
  | false, r + 1, y, z => ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p +
      ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p

@[simp] theorem fail_zero (lower : Bool) (y z : ℝ) : fail lower 0 y z = 0 := by
  cases lower <;> rfl

theorem fail_true_succ (r : ℕ) (y z : ℝ) :
    fail true (r + 1) y z = ∑ p ∈ primesLT z, fail false r (y / p) p / p := rfl

theorem fail_false_succ (r : ℕ) (y z : ℝ) :
    fail false (r + 1) y z = ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p +
      ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p := rfl

theorem fail_nonneg (lower : Bool) (r : ℕ) (y z : ℝ) : 0 ≤ fail lower r y z := by
  induction r generalizing lower y z with
  | zero => simp
  | succ r ih =>
    cases lower
    · rw [fail_false_succ]
      exact add_nonneg (sum_nonneg fun p _ ↦ div_nonneg (ih _ _ _) p.cast_nonneg)
        (sum_nonneg fun p _ ↦ div_nonneg (R_nonneg _) p.cast_nonneg)
    · rw [fail_true_succ]
      exact sum_nonneg fun p _ ↦ div_nonneg (ih _ _ _) p.cast_nonneg

theorem fail_le_fail_succ (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower r y z ≤ fail lower (r + 1) y z := by
  induction r generalizing lower y z with
  | zero => simpa using fail_nonneg lower 1 y z
  | succ r ih =>
    cases lower
    · rw [fail_false_succ, fail_false_succ]
      gcongr with p
      exact ih _ _ _
    · rw [fail_true_succ, fail_true_succ]
      gcongr with p
      exact ih _ _ _

theorem fail_mono (lower : Bool) (y z : ℝ) : Monotone fun r ↦ fail lower r y z :=
  monotone_nat_of_le_succ fun r ↦ fail_le_fail_succ lower r y z

/-- Once `r` exceeds the possible depth of the recursion, `fail` computes the deficits exactly
([I71, Lemma 2]). -/
theorem fail_eq_of_card_lt {r : ℕ} (hr : #(primesLT z) < r) (y : ℝ) :
    fail true r y z = R z - rosserMain true y z ∧
      fail false r y z = rosserMain false y z - R z := by
  induction r generalizing y z with
  | zero => simp at hr
  | succ r ih =>
    have ih' : ∀ p ∈ primesLT z, ∀ y, fail true r y p = R p - rosserMain true y p ∧
        fail false r y p = rosserMain false y p - R p := fun p hp y ↦
      ih ((card_lt_card (primesLT_natCast_ssubset hp)).trans_le (Nat.lt_succ_iff.1 hr)) y
    constructor
    · rw [fail_true_succ, rosserMain_eq, R_eq z, rosserPrimes_true]
      simp only [Bool.not_true]
      rw [sub_sub_sub_cancel_left, ← sum_sub_distrib]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [(ih' p hp _).2, sub_div]
    · rw [fail_false_succ, rosserMain_eq, R_eq z, rosserPrimes_false,
        ← sum_filter_add_sum_filter_not (primesLT z) (fun p : ℕ ↦ (p : ℝ) ^ 3 < y)
          (fun p ↦ R p / p)]
      simp only [Bool.not_false, ← rosserPrimes_false]
      have : ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p =
          ∑ p ∈ rosserPrimes false y z, R p / p -
            ∑ p ∈ rosserPrimes false y z, rosserMain true (y / p) p / p := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [(ih' p (rosserPrimes_subset hp) _).1, sub_div]
      rw [this]
      ring

/-- `∑_{d ∈ D⁻} μ(d)/d = R(z) - fail true r y z` for `r` large. -/
theorem rosserMain_true_eq {r : ℕ} (hr : #(primesLT z) < r) (y : ℝ) :
    rosserMain true y z = R z - fail true r y z := by
  rw [(fail_eq_of_card_lt hr y).1]
  ring

/-- `∑_{d ∈ D⁺} μ(d)/d = R(z) + fail false r y z` for `r` large. -/
theorem rosserMain_false_eq {r : ℕ} (hr : #(primesLT z) < r) (y : ℝ) :
    rosserMain false y z = R z + fail false r y z := by
  rw [(fail_eq_of_card_lt hr y).2]
  ring

theorem rosserMain_true_le_R (y z : ℝ) : rosserMain true y z ≤ R z := by
  rw [rosserMain_true_eq (Nat.lt_succ_self _) y]
  linarith [fail_nonneg true (#(primesLT z) + 1) y z]

theorem R_le_rosserMain_false (y z : ℝ) : R z ≤ rosserMain false y z := by
  rw [rosserMain_false_eq (Nat.lt_succ_self _) y]
  linarith [fail_nonneg false (#(primesLT z) + 1) y z]

end IwaniecLinearSieve
