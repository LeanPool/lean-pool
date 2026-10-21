/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Rosser
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Tactic.Polynomial.Basic

/-!
# Iwaniec's shifted sieve ([I78, Lemma 1])

Let `S` be any set of `r = π(z)` primes, and match `S` with the primes below `z` in increasing
order, `l : S → primesLT z`, so that `l(q) ≤ q`. Rosser's lower-bound weights `λ_d = μ(d)` on
`d ∈ D⁻` (supported on divisors of `P(z)`) are pulled back along `l` to divisors of
`Q = ∏_{q ∈ S} q`. Writing divisors of squarefree numbers as sets of primes, the weights are
`rosserWeight y z A` for `A ⊆ primesLT z`.

* `sum_powerset_div_prod`: `∑_{A ⊆ T} w(A)/∏_A g = ∏_T (1 - 1/g) ∑_{B ⊆ T} σ(B)/∏_B (g - 1)`.
* `prod_mul_sum_div_le_sum`: the comparison of main terms under condition (−).
* `shiftedSieve`: [I78, Lemma 1] for `X` consecutive integers.
* `R_le_prod_of_card_eq`: `R(z) ≤ ∏_{q ∈ S} (1 - 1/q)`.
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace IwaniecLinearSieve

/-! ### Matching an arbitrary set of primes with the first primes -/

/-- If every element of `S` lying below some element of `T` belongs to `T` (e.g. `T` is the set of
the first `r` primes and `S` is any set of primes), then the `i`-th element of `T` is at most the
`i`-th element of `S`. -/
theorem orderEmbOfFin_le_orderEmbOfFin {T S : Finset ℕ} {r : ℕ} (hT : #T = r) (hS : #S = r)
    (hdown : ∀ q ∈ S, ∀ t ∈ T, q < t → q ∈ T) (i : Fin r) :
    T.orderEmbOfFin hT i ≤ S.orderEmbOfFin hS i := by
  by_contra h
  push Not at h
  set t := T.orderEmbOfFin hT i
  have h1 : (Iic i).map (S.orderEmbOfFin hS).toEmbedding ⊆ T.filter (· < t) := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := mem_map.1 hu
    have hlt : S.orderEmbOfFin hS j < t :=
      lt_of_le_of_lt ((S.orderEmbOfFin hS).monotone (mem_Iic.1 hj)) h
    exact mem_filter.2 ⟨hdown _ (S.orderEmbOfFin_mem hS j) t (T.orderEmbOfFin_mem hT i) hlt, hlt⟩
  have h2 : T.filter (· < t) ⊆ (Iio i).map (T.orderEmbOfFin hT).toEmbedding := by
    intro u hu
    obtain ⟨huT, hut⟩ := mem_filter.1 hu
    have : u ∈ Set.range (T.orderEmbOfFin hT) := by
      rw [range_orderEmbOfFin]
      exact huT
    obtain ⟨j, rfl⟩ := this
    exact mem_map.2 ⟨j, mem_Iio.2 ((T.orderEmbOfFin hT).lt_iff_lt.1 hut), rfl⟩
  have := card_le_card (h1.trans h2)
  simp [Fin.card_Iic, Fin.card_Iio] at this

/-- The order-preserving bijection between two finite sets of the same size moves every element
of `T` upwards, provided every element of `S` below an element of `T` lies in `T`. -/
theorem exists_bijOn_le {T S : Finset ℕ} (hcard : #S = #T)
    (hdown : ∀ q ∈ S, ∀ t ∈ T, q < t → q ∈ T) :
    ∃ e : ℕ → ℕ, Set.BijOn e T S ∧ ∀ p ∈ T, p ≤ e p := by
  classical
  let iT := T.orderIsoOfFin rfl
  let iS := S.orderIsoOfFin hcard
  refine ⟨fun p ↦ if hp : p ∈ T then (iS (iT.symm ⟨p, hp⟩) : ℕ) else p, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [mem_coe] at hp
    simp only [hp, dite_true, mem_coe]
    exact (iS _).2
  · intro p hp q hq hpq
    simp only [mem_coe] at hp hq
    simp only [hp, hq, dite_true] at hpq
    have := iT.symm.injective (iS.injective (Subtype.ext hpq))
    exact congrArg Subtype.val this
  · intro q hq
    simp only [mem_coe] at hq
    refine ⟨iT (iS.symm ⟨q, hq⟩), (iT _).2, ?_⟩
    simp
  · intro p hp
    simp only [hp, dite_true]
    have h1 : p = T.orderEmbOfFin rfl (iT.symm ⟨p, hp⟩) := by
      rw [← coe_orderIsoOfFin_apply]
      simp [iT]
    have h2 : (iS (iT.symm ⟨p, hp⟩) : ℕ) = S.orderEmbOfFin hcard (iT.symm ⟨p, hp⟩) :=
      coe_orderIsoOfFin_apply _ _ _
    conv_lhs => rw [h1]
    rw [h2]
    exact orderEmbOfFin_le_orderEmbOfFin rfl hcard hdown _


/-! ### Möbius inversion over subsets -/
theorem sum_powerset_filter_superset_prod {T A : Finset ℕ} (hA : A ⊆ T) (h : ℕ → ℝ) :
    ∑ B ∈ T.powerset with A ⊆ B, ∏ p ∈ B, h p = (∏ p ∈ A, h p) * ∏ p ∈ T \ A, (1 + h p) := by
  rw [prod_one_add, mul_sum]
  refine sum_nbij' (fun B ↦ B \ A) (fun C ↦ A ∪ C) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB ⊢
    exact sdiff_subset_sdiff hB.1 le_rfl
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨union_subset hA (hC.trans sdiff_subset), subset_union_left⟩
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB
    exact union_sdiff_of_subset hB.2
  · intro C hC
    simp only [mem_powerset] at hC
    exact union_sdiff_cancel_left (disjoint_of_subset_right hC disjoint_sdiff)
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB
    rw [← prod_union disjoint_sdiff, union_sdiff_of_subset hB.2]

/-- The identity behind [I78, Lemma 1]: for weights `w` on the subsets of `T` (i.e. on the
divisors of `∏_{p ∈ T} p`) with partial sums `σ(B) = ∑_{A ⊆ B} w(A)`,
`∑_{A ⊆ T} w(A) / ∏_{p ∈ A} g(p) = ∏_{p ∈ T} (1 - 1/g(p)) ∑_{B ⊆ T} σ(B) / ∏_{p ∈ B} (g(p) - 1)`. -/
theorem sum_powerset_div_prod (T : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ T, g p ≠ 0 ∧ g p ≠ 1)
    (w : Finset ℕ → ℝ) :
    ∑ A ∈ T.powerset, w A / ∏ p ∈ A, g p =
      (∏ p ∈ T, (1 - (g p)⁻¹)) *
        ∑ B ∈ T.powerset, (∑ A ∈ B.powerset, w A) / ∏ p ∈ B, (g p - 1) := by
  simp_rw [mul_sum, sum_div, mul_sum, div_eq_mul_inv, ← prod_inv_distrib]
  rw [sum_comm' (t' := T.powerset) (s' := fun A ↦ T.powerset.filter (A ⊆ ·))]
  swap
  · intro B A
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨hB, hA⟩
      exact ⟨⟨hB, hA⟩, hA.trans hB⟩
    · rintro ⟨⟨hB, hA⟩, -⟩
      exact ⟨hB, hA⟩
  refine sum_congr rfl fun A hA ↦ ?_
  rw [mem_powerset] at hA
  rw [← mul_sum, ← mul_sum, sum_powerset_filter_superset_prod hA, mul_left_comm]
  congr 1
  rw [← prod_sdiff hA, show ∀ a b c d : ℝ, a * b * (c * d) = c * b * (a * d) by intros; ring,
    ← prod_mul_distrib, ← prod_mul_distrib]
  rw [prod_congr rfl (s₁ := T \ A) (g := fun _ ↦ (1 : ℝ)), prod_const_one, mul_one]
  · refine prod_congr rfl fun p hp ↦ ?_
    obtain ⟨h0, h1⟩ := hg p (hA hp)
    have : g p - 1 ≠ 0 := sub_ne_zero.2 h1
    field_simp
  · intro p hp
    obtain ⟨h0, h1⟩ := hg p (sdiff_subset hp)
    have : g p - 1 ≠ 0 := sub_ne_zero.2 h1
    field_simp
    ring


/-- The main-term comparison in [I78, Lemma 1]: if the partial sums of `w` are `≤ 0` on nonempty
sets ("condition (−)") and `1 < g ≤ f` on `T`, then
`∏ (1 - 1/f) · (∑_A w(A) / ∏_A g) / ∏ (1 - 1/g) ≤ ∑_A w(A) / ∏_A f`. -/
theorem prod_mul_sum_div_le_sum (T : Finset ℕ) (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f p) (w : Finset ℕ → ℝ)
    (hw : ∀ B ⊆ T, B.Nonempty → ∑ A ∈ B.powerset, w A ≤ 0) :
    (∏ p ∈ T, (1 - (f p)⁻¹)) *
        ((∑ A ∈ T.powerset, w A / ∏ p ∈ A, g p) / ∏ p ∈ T, (1 - (g p)⁻¹)) ≤
      ∑ A ∈ T.powerset, w A / ∏ p ∈ A, f p := by
  have hf : ∀ p ∈ T, 1 < f p := fun p hp ↦ (hg p hp).trans_le (hgf p hp)
  have hne : ∀ {h : ℕ → ℝ}, (∀ p ∈ T, 1 < h p) → ∀ p ∈ T, h p ≠ 0 ∧ h p ≠ 1 :=
    fun hh p hp ↦ ⟨(zero_lt_one.trans (hh p hp)).ne', (hh p hp).ne'⟩
  have hpos : ∀ {h : ℕ → ℝ}, (∀ p ∈ T, 1 < h p) → 0 < ∏ p ∈ T, (1 - (h p)⁻¹) :=
    fun hh ↦ prod_pos fun p hp ↦ sub_pos.2 (inv_lt_one_of_one_lt₀ (hh p hp))
  rw [sum_powerset_div_prod T g (hne hg), sum_powerset_div_prod T f (hne hf),
    mul_div_cancel_left₀ _ (hpos hg).ne']
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun B hB ↦ ?_) (hpos hf).le
  rw [mem_powerset] at hB
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp
  have h0 : 0 < ∏ p ∈ B, (g p - 1) := prod_pos fun p hp ↦ sub_pos.2 (hg p (hB hp))
  have h1 : ∏ p ∈ B, (g p - 1) ≤ ∏ p ∈ B, (f p - 1) :=
    prod_le_prod₀ (fun p hp ↦ (sub_pos.2 (hg p (hB hp))).le)
      fun p hp ↦ sub_le_sub_right (hgf p (hB hp)) 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonpos_left (inv_anti₀ h0 h1) (hw B hB hBne)

/-! ### Rosser's weights on subsets of the primes below `z` -/

/-- Sums over `rosserSet` as sums over sets of primes below `z`. -/
theorem sum_rosserSet_eq_sum_powerset {M : Type*} [AddCommMonoid M] (lower : Bool) (y z : ℝ)
    (F : Finset ℕ → M) :
    ∑ d ∈ rosserSet lower y z, F d.primeFactors =
      ∑ A ∈ (primesLT z).powerset, if ∏ p ∈ A, p ∈ rosserSet lower y z then F A else 0 := by
  rw [← sum_filter]
  have hprime : ∀ A ∈ (primesLT z).powerset, ∀ p ∈ A, p.Prime := fun A hA p hp ↦
    prime_of_mem_primesLT (mem_powerset.1 hA hp)
  refine sum_nbij' Nat.primeFactors (fun A ↦ ∏ p ∈ A, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    refine mem_filter.2 ⟨mem_powerset.2 (primeFactors_subset_of_mem_rosserSet hd), ?_⟩
    rwa [Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
  · intro A hA
    exact (mem_filter.1 hA).2
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)
  · intro A hA
    exact Nat.primeFactors_prod (hprime A (mem_filter.1 hA).1)
  · intro d _
    rfl

theorem sum_rosserSet_eq_sum_powerset' {M : Type*} [AddCommMonoid M] (lower : Bool) (y z : ℝ)
    (G : ℕ → M) :
    ∑ d ∈ rosserSet lower y z, G d =
      ∑ A ∈ (primesLT z).powerset,
        if ∏ p ∈ A, p ∈ rosserSet lower y z then G (∏ p ∈ A, p) else 0 := by
  rw [← sum_rosserSet_eq_sum_powerset lower y z (fun A ↦ G (∏ p ∈ A, p))]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]

/-- `λ_A = μ(∏_{p ∈ A} p)` if `∏_{p ∈ A} p ∈ D⁻`, and `0` otherwise. -/
noncomputable def rosserWeight (y z : ℝ) (A : Finset ℕ) : ℝ :=
  if ∏ p ∈ A, p ∈ rosserSet true y z then (μ (∏ p ∈ A, p) : ℝ) else 0

theorem sum_moebius_rosserSet_eq (y z : ℝ) (F : ℕ → ℝ) :
    ∑ d ∈ rosserSet true y z, (μ d : ℝ) * F d =
      ∑ A ∈ (primesLT z).powerset, rosserWeight y z A * F (∏ p ∈ A, p) := by
  rw [sum_rosserSet_eq_sum_powerset']
  refine sum_congr rfl fun A _ ↦ ?_
  rw [rosserWeight]
  split_ifs <;> simp

theorem rosserMain_eq_sum_rosserWeight (y z : ℝ) :
    rosserMain true y z =
      ∑ A ∈ (primesLT z).powerset, rosserWeight y z A / ∏ p ∈ A, (p : ℝ) := by
  have := sum_moebius_rosserSet_eq y z (fun d ↦ (d : ℝ)⁻¹)
  simp only [Nat.cast_prod] at this
  simp_rw [rosserMain, div_eq_mul_inv]
  exact this

theorem sum_abs_rosserWeight_le (y z : ℝ) :
    ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| ≤ #(rosserSet true y z) := by
  have : ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| =
      ∑ d ∈ rosserSet true y z, |(μ d : ℝ)| := by
    rw [sum_rosserSet_eq_sum_powerset']
    refine sum_congr rfl fun A _ ↦ ?_
    rw [rosserWeight]
    split_ifs <;> simp
  rw [this, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_le_sum fun d _ ↦ ?_
  exact_mod_cast abs_moebius_le_one


theorem prod_dvd_prod_iff_subset {A B : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hB : ∀ p ∈ B, p.Prime) : ∏ p ∈ A, p ∣ ∏ p ∈ B, p ↔ A ⊆ B := by
  refine ⟨fun h ↦ ?_, fun h ↦ prod_dvd_prod_of_subset _ _ _ h⟩
  have := Nat.primeFactors_mono h (prod_ne_zero_iff.2 fun p hp ↦ (hB p hp).ne_zero)
  rwa [Nat.primeFactors_prod hA, Nat.primeFactors_prod hB] at this

/-- The sieve property in terms of subsets ("condition (−)" of [I78, Lemma 1]):
`∑_{A ⊆ B} λ_A ≤ [B = ∅]`. -/
theorem sum_powerset_rosserWeight_le (y : ℝ) {z : ℝ} {B : Finset ℕ} (hB : B ⊆ primesLT z) :
    ∑ A ∈ B.powerset, rosserWeight y z A ≤ if B = ∅ then 1 else 0 := by
  have hBp : ∀ p ∈ B, p.Prime := fun p hp ↦ prime_of_mem_primesLT (hB hp)
  have h1 : ∑ A ∈ B.powerset, rosserWeight y z A =
      ∑ A ∈ (primesLT z).powerset,
        rosserWeight y z A * (if ∏ p ∈ A, p ∣ ∏ p ∈ B, p then 1 else 0) := by
    have : B.powerset = (primesLT z).powerset.filter (· ⊆ B) := by
      ext A
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hB, h⟩, fun h ↦ h.2⟩
    rw [this, sum_filter]
    refine sum_congr rfl fun A hA ↦ ?_
    simp only [prod_dvd_prod_iff_subset (fun p hp ↦ prime_of_mem_primesLT (mem_powerset.1 hA hp))
      hBp]
    split_ifs <;> simp
  have h2 : ∑ A ∈ (primesLT z).powerset,
        rosserWeight y z A * (if ∏ p ∈ A, p ∣ ∏ p ∈ B, p then 1 else 0) =
      ((∑ d ∈ (rosserSet true y z).filter (· ∣ ∏ p ∈ B, p), μ d : ℤ) : ℝ) := by
    rw [← sum_moebius_rosserSet_eq y z (fun d ↦ if d ∣ ∏ p ∈ B, p then 1 else 0), sum_filter,
      Int.cast_sum]
    refine sum_congr rfl fun d _ ↦ ?_
    split_ifs <;> simp
  have h3 := (rosserSieve_of_dvd_primorialLT (z := z) y
    (prod_dvd_prod_of_subset _ _ _ hB : ∏ p ∈ B, p ∣ primorialLT z)).1
  have h4 : (∏ p ∈ B, p = 1) ↔ B = ∅ := by
    constructor
    · intro h
      have := Nat.primeFactors_prod hBp
      rw [h, Nat.primeFactors_one] at this
      exact this.symm
    · rintro rfl
      simp
  rw [h1, h2]
  simp only [h4] at h3
  exact_mod_cast h3

/-! ### Counting multiples in an interval -/

/-- `|#{k < X : d ∣ x + k} - X / d| ≤ 1`. -/
theorem abs_card_filter_dvd_sub_le (x : ℤ) (X : ℕ) {d : ℕ} (hd : 0 < d) :
    |(#((range X).filter fun k : ℕ ↦ (d : ℤ) ∣ x + k) : ℝ) - X / d| ≤ 1 := by
  have hcard : #((range X).filter fun k : ℕ ↦ (d : ℤ) ∣ x + k) =
      #((Ico x (x + X)).filter ((d : ℤ) ∣ ·)) := by
    refine card_nbij' (fun k ↦ x + k) (fun t ↦ (t - x).toNat) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_Ico] at hk ⊢
      exact ⟨⟨by omega, by omega⟩, hk.2⟩
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_Ico] at ht ⊢
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      simpa using ht.2
    · intro k _
      simp
    · intro t ht
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at ht
      simp only
      omega
  have h := Int.Ico_filter_dvd_card x (x + X) (r := d) (by exact_mod_cast hd)
  set u : ℚ := x / (d : ℤ)
  set v : ℚ := (x + X : ℤ) / (d : ℤ)
  have hdq : (0 : ℚ) < (d : ℤ) := by exact_mod_cast hd
  have hvu : v = u + X / d := by
    simp only [v, u]
    push_cast
    ring
  have hX : (0 : ℚ) ≤ X / d := by positivity
  have hle : ⌈u⌉ ≤ ⌈v⌉ := Int.ceil_mono (by rw [hvu]; linarith)
  rw [max_eq_left (sub_nonneg.2 hle)] at h
  have hq : |((⌈v⌉ - ⌈u⌉ : ℤ) : ℚ) - X / d| ≤ 1 := by
    have h1 := Int.le_ceil v
    have h2 := Int.ceil_lt_add_one v
    have h3 := Int.le_ceil u
    have h4 := Int.ceil_lt_add_one u
    rw [abs_le]
    push_cast
    constructor <;> linarith
  rw [hcard]
  have : (#((Ico x (x + X)).filter ((d : ℤ) ∣ ·)) : ℝ) = ((⌈v⌉ - ⌈u⌉ : ℤ) : ℝ) := by
    exact_mod_cast h
  rw [this]
  have hq' := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at hq' ⊢
  exact hq'


/-! ### The shifted sieve -/

variable {z : ℝ}

/-- [I78, Lemma 1] for an interval of `X` consecutive integers, with an explicit matching `e`
of the primes below `z` with `S` such that `p ≤ e p`. -/
theorem shiftedSieve_of_bijOn (y : ℝ) {S : Finset ℕ} {e : ℕ → ℕ}
    (he : Set.BijOn e (primesLT z) S) (hle : ∀ p ∈ primesLT z, p ≤ e p)
    (hS : ∀ q ∈ S, q.Prime) (x : ℤ) (X : ℕ) :
    (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) -
        #(rosserSet true y z) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  set T := primesLT z
  set w := rosserWeight y z
  set n : Finset ℕ → ℕ := fun A ↦ ∏ p ∈ A, e p
  have heS : ∀ p ∈ T, e p ∈ S := fun p hp ↦ he.mapsTo hp
  have hePrime : ∀ p ∈ T, (e p).Prime := fun p hp ↦ hS _ (heS p hp)
  have hn : ∀ A ∈ T.powerset, 0 < n A := fun A hA ↦
    prod_pos fun p hp ↦ (hePrime p (mem_powerset.1 hA hp)).pos
  -- the sieve inequality for a single integer
  have ha : ∀ k : ℕ, ∑ A ∈ T.powerset, w A * (if (n A : ℤ) ∣ x + k then 1 else 0) ≤
      if ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k then 1 else 0 := by
    intro k
    set B := T.filter fun p ↦ (e p : ℤ) ∣ x + k
    have hB : B ⊆ T := filter_subset _ _
    have h1 : ∀ A ∈ T.powerset, ((n A : ℤ) ∣ x + k ↔ A ⊆ B) := by
      intro A hA
      rw [mem_powerset] at hA
      constructor
      · intro h p hp
        refine mem_filter.2 ⟨hA hp, (Int.natCast_dvd_natCast.2 ?_).trans h⟩
        exact dvd_prod_of_mem _ hp
      · intro h
        simp only [n, Nat.cast_prod]
        refine prod_dvd_of_coprime ?_ fun p hp ↦ (mem_filter.1 (h hp)).2
        intro p hp q hq hpq
        refine Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hePrime p (hA hp))
          (hePrime q (hA hq))).2 fun h' ↦ hpq (he.injOn (hA hp) (hA hq) h'))
    have h2 : B = ∅ ↔ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k := by
      rw [filter_eq_empty_iff]
      constructor
      · intro h q hq hqk
        obtain ⟨p, hp, rfl⟩ := he.surjOn hq
        exact h hp hqk
      · intro h p hp
        exact h _ (heS p hp)
    have h3 : B.powerset = T.powerset.filter (· ⊆ B) := by
      ext A
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hB, h⟩, fun h ↦ h.2⟩
    calc ∑ A ∈ T.powerset, w A * (if (n A : ℤ) ∣ x + k then 1 else 0)
        = ∑ A ∈ B.powerset, w A := by
          rw [h3, sum_filter]
          refine sum_congr rfl fun A hA ↦ ?_
          simp only [h1 A hA]
          split_ifs <;> simp
      _ ≤ if B = ∅ then 1 else 0 := sum_powerset_rosserWeight_le y hB
      _ = _ := by simp only [h2]
  -- summing over the interval
  have hb : ∑ A ∈ T.powerset, w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
    simp_rw [natCast_card_filter, mul_sum]
    rw [sum_comm]
    exact sum_le_sum fun k _ ↦ ha k
  -- the remainder
  have hc : ∀ A ∈ T.powerset, w A * X / n A - |w A| ≤
      w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) := by
    intro A hA
    have h := abs_card_filter_dvd_sub_le x X (hn A hA)
    have h' : |w A * (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) - X / n A)| ≤ |w A| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) h
    have := neg_abs_le (w A * (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) - X / n A))
    rw [mul_div_assoc]
    linarith [mul_sub (w A) (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) : ℝ) (X / n A)]
  -- the main term
  have hd : (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) ≤
      ∑ A ∈ T.powerset, w A * X / n A := by
    have hprodS : ∏ q ∈ S, (1 - (q : ℝ)⁻¹) = ∏ p ∈ T, (1 - (e p : ℝ)⁻¹) :=
      (prod_nbij e heS he.injOn he.surjOn fun p _ ↦ rfl).symm
    have hmain := prod_mul_sum_div_le_sum T (fun p ↦ (e p : ℝ)) (fun p ↦ (p : ℝ))
      (fun p hp ↦ by exact_mod_cast (prime_of_mem_primesLT hp).one_lt)
      (fun p hp ↦ by exact_mod_cast hle p hp) w
      (fun B hB hBne ↦ by
        simpa [hBne.ne_empty] using sum_powerset_rosserWeight_le y hB)
    rw [← rosserMain_eq_sum_rosserWeight] at hmain
    simp_rw [mul_div_right_comm _ (X : ℝ), ← sum_mul, mul_comm _ (X : ℝ)]
    rw [mul_assoc, hprodS]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg X)
    simpa [n, R, T] using hmain
  have he' := sum_abs_rosserWeight_le y z
  have hsum : ∑ A ∈ T.powerset, w A * X / n A - ∑ A ∈ T.powerset, |w A| ≤
      ∑ A ∈ T.powerset, w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) := by
    rw [← sum_sub_distrib]
    exact sum_le_sum hc
  linarith


/-- Any `π(z)` primes can be matched with the primes below `z` so that each prime below `z` is
matched with a prime at least as large. -/
theorem exists_bijOn_primesLT_le {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) :
    ∃ e : ℕ → ℕ, Set.BijOn e (primesLT z) S ∧ ∀ p ∈ primesLT z, p ≤ e p :=
  exists_bijOn_le hcard fun q hq _ ht hqt ↦
    mem_primesLT.2 ⟨hS q hq, (Nat.cast_lt.2 hqt).trans (lt_of_mem_primesLT ht)⟩

/-- [I78, Lemma 1] (the shifted sieve) for an interval of `X` consecutive integers `x + k`,
`0 ≤ k < X`, sifted by an arbitrary set `S` of `π(z)` primes, with Rosser's lower-bound weights:
`#{k < X : (x + k, ∏_{q ∈ S} q) = 1} ≥ X ∏_{q ∈ S} (1 - 1/q) · (∑_{d ∈ D⁻} μ(d)/d) / R(z) - |D⁻|`.
-/
theorem shiftedSieve (y : ℝ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) (x : ℤ) (X : ℕ) :
    (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) -
        #(rosserSet true y z) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  obtain ⟨e, he, hle⟩ := exists_bijOn_primesLT_le hS hcard
  exact shiftedSieve_of_bijOn y he hle hS x X

/-- `R(z) ≤ ∏_{q ∈ S} (1 - 1/q)` for any set `S` of `π(z)` primes. -/
theorem R_le_prod_of_card_eq {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) : R z ≤ ∏ q ∈ S, (1 - (q : ℝ)⁻¹) := by
  obtain ⟨e, he, hle⟩ := exists_bijOn_primesLT_le hS hcard
  rw [← prod_nbij e (fun p hp ↦ he.mapsTo hp) he.injOn he.surjOn fun p _ ↦ rfl, R]
  refine prod_le_prod₀ (fun p hp ↦ sub_nonneg.2 (inv_le_one_of_one_le₀ ?_)) fun p hp ↦ ?_
  · exact_mod_cast (prime_of_mem_primesLT hp).one_lt.le
  · have h1 : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
    have h2 : (p : ℝ) ≤ e p := by exact_mod_cast hle p hp
    exact sub_le_sub_left (inv_anti₀ h1 h2) 1

end IwaniecLinearSieve
