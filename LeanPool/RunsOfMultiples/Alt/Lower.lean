/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.BlockLower
public import LeanPool.RunsOfMultiples.LowerEstimates
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Runs of multiples: the lower bound via the "matching construction"

This file formalises §3 ("A matching construction") of `docs/first-missing-multiple.pdf`.

For `y ≥ 2` let
* `small y` = primes `p ≤ √y` (encoded as `p * p ≤ y`), `q = #small y`;
* `large y` = primes in `(√y, y]` (encoded as `y < p * p`, `p ≤ y`), `m = #large y`;
* `L = ⌊log₂ y⌋ = Nat.log 2 y`, `H = 2 q L`.

`S_y` is the set of integers `∏_{p ≤ √y} p ^ u_p * ∏_{√y < p ≤ y} p ^ v_p` with
`0 ≤ u_p ≤ H` and `∑ v_p ≤ m`. We represent exponent vectors as finsupps `ℕ →₀ ℕ` and
the number as `f.prod (· ^ ·)`. The small-prime part ranges over `smallExp y H`
(`Finset.finsupp`), the large-prime part over `largeExp y m`: finsupps supported on
`insert 1 (large y)` with total sum exactly `m`, the coordinate at `1` being a slack
variable (`1 ^ v = 1`), so that these give exactly the products with `∑ v_p ≤ m`
(stars and bars with a slack variable; `Finset.card_finsuppAntidiag_nat_eq_choose`).

The good elements (`u_p ≤ H - L`, `∑ v_p ≤ m - 1`) have all first `y` multiples in `S_y`,
at least a quarter of `S_y` is good, and `|S_y| ≤ (H + 1) ^ q * C(2m, m) ≤ exp (C y / log y)`.
The padding step is the same as in `RunsOfMultiples.Replication` (`replicate`).
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

namespace Alt

/-- Primes `p` with `p ≤ √y`, i.e. `p * p ≤ y`. -/
def small (y : ℕ) : Finset ℕ := (y + 1).primesBelow.filter (fun p => p * p ≤ y)

/-- Primes `p` with `√y < p ≤ y`. -/
def large (y : ℕ) : Finset ℕ := (y + 1).primesBelow.filter (fun p => y < p * p)

/-- `q = π(√y)`. -/
def qq (y : ℕ) : ℕ := (small y).card

/-- `m = π(y) - π(√y)`. -/
def mm (y : ℕ) : ℕ := (large y).card

/-- `L = ⌊log₂ y⌋`. -/
def LL (y : ℕ) : ℕ := Nat.log 2 y

/-- `H = 2 q L`. -/
def HH (y : ℕ) : ℕ := 2 * qq y * LL y

/-- Index set for the large-prime exponents, with a slack coordinate at `1`. -/
def slack (y : ℕ) : Finset ℕ := insert 1 (large y)

/-- The number with exponent vector `f`. -/
noncomputable def pw (f : ℕ →₀ ℕ) : ℕ := f.prod (· ^ ·)

/-- Small-prime exponent vectors with all entries `≤ e`. -/
noncomputable def smallExp (y e : ℕ) : Finset (ℕ →₀ ℕ) :=
  (small y).finsupp (fun _ => range (e + 1))

/-- Large-prime exponent vectors (plus slack at `1`) with total sum `k`. -/
noncomputable def largeExp (y k : ℕ) : Finset (ℕ →₀ ℕ) := (slack y).finsuppAntidiag k

/-- Small parts `∏_{p ≤ √y} p ^ u_p`, `u_p ≤ e`. -/
noncomputable def smallPart (y e : ℕ) : Finset ℕ := (smallExp y e).image pw

/-- Large parts `∏_{√y < p ≤ y} p ^ v_p`, `∑ v_p ≤ k`. -/
noncomputable def largePart (y k : ℕ) : Finset ℕ := (largeExp y k).image pw

/-- The block `S_y`. -/
noncomputable def Sy (y : ℕ) : Finset ℕ :=
  (smallPart y (HH y) ×ˢ largePart y (mm y)).image (fun x => x.1 * x.2)

/-- The good elements of `S_y`: `u_p ≤ H - L`, `∑ v_p ≤ m - 1`. -/
noncomputable def Gy (y : ℕ) : Finset ℕ :=
  (smallPart y (HH y - LL y) ×ˢ largePart y (mm y - 1)).image (fun x => x.1 * x.2)

/-! ### Basic facts -/

lemma pw_add (f g : ℕ →₀ ℕ) : pw (f + g) = pw f * pw g :=
  Finsupp.prod_add_index' (fun a => pow_zero a) (fun a b c => pow_add a b c)

lemma pw_single (a k : ℕ) : pw (Finsupp.single a k) = a ^ k :=
  Finsupp.prod_single_index (pow_zero a)

lemma pw_pos (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, 0 < p) : 0 < pw f :=
  Finset.prod_pos fun p hp => pow_pos (hf p hp) _

lemma mem_small {y p : ℕ} : p ∈ small y ↔ p.Prime ∧ p ≤ y ∧ p * p ≤ y := by
  simp only [small, mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h3⟩

lemma mem_large {y p : ℕ} : p ∈ large y ↔ p.Prime ∧ p ≤ y ∧ y < p * p := by
  simp only [large, mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h3⟩

lemma one_notMem_large (y : ℕ) : 1 ∉ large y := fun h => Nat.not_prime_one (mem_large.1 h).1

lemma card_largeExp (y k : ℕ) : (largeExp y k).card = (mm y + k).choose k := by
  rw [largeExp, card_finsuppAntidiag_nat_eq_choose, slack,
    card_insert_of_notMem (one_notMem_large y)]
  rw [show (large y).card + 1 + k - 1 = mm y + k by unfold mm; omega]

lemma card_smallExp (y e : ℕ) : (smallExp y e).card = (e + 1) ^ qq y := by
  rw [smallExp, card_finsupp]
  simp [qq]

lemma pw_injOn_smallExp (y e : ℕ) : Set.InjOn pw (smallExp y e : Set (ℕ →₀ ℕ)) := by
  intro f hf g hg h
  have hpr : ∀ f ∈ (smallExp y e : Set (ℕ →₀ ℕ)), ∀ p ∈ f.support, p.Prime := by
    intro f hf p hp
    rw [mem_coe, smallExp, mem_finsupp_iff] at hf
    exact (mem_small.1 (hf.1 hp)).1
  rw [← Nat.prod_pow_factorization_eq_self (hpr f hf),
    ← Nat.prod_pow_factorization_eq_self (hpr g hg)]
  exact congrArg Nat.factorization h

lemma pw_erase_one (f : ℕ →₀ ℕ) : pw f = pw (f.erase 1) := by
  conv_lhs => rw [← Finsupp.single_add_erase 1 f]
  rw [pw_add, pw_single, one_pow, one_mul]

lemma pw_injOn_largeExp (y k : ℕ) : Set.InjOn pw (largeExp y k : Set (ℕ →₀ ℕ)) := by
  intro f hf g hg h
  rw [mem_coe, largeExp, mem_finsuppAntidiag] at hf hg
  have hpr : ∀ f : ℕ →₀ ℕ, f.support ⊆ slack y → ∀ p ∈ (f.erase 1).support, p.Prime := by
    intro f hf p hp
    rw [Finsupp.support_erase, mem_erase] at hp
    have := hf hp.2
    rw [slack, mem_insert] at this
    rcases this with h1 | h1
    · exact absurd h1 hp.1
    · exact (mem_large.1 h1).1
  have he : f.erase 1 = g.erase 1 := by
    rw [← Nat.prod_pow_factorization_eq_self (hpr f hf.2),
      ← Nat.prod_pow_factorization_eq_self (hpr g hg.2)]
    have := h
    rw [pw_erase_one f, pw_erase_one g] at this
    exact congrArg Nat.factorization this
  have hsum : ∀ f : ℕ →₀ ℕ, (slack y).sum f = f 1 + ∑ p ∈ large y, (f.erase 1) p := by
    intro f
    rw [slack, sum_insert (one_notMem_large y)]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    rw [Finsupp.erase_ne (fun h : p = 1 => one_notMem_large y (h ▸ hp))]
  have h1 : f 1 = g 1 := by
    have h2 := hsum f
    have h3 := hsum g
    rw [hf.1, he] at h2
    rw [hg.1] at h3
    omega
  ext p
  by_cases hp : p = 1
  · rw [hp, h1]
  · rw [← Finsupp.erase_ne hp, he, Finsupp.erase_ne hp]

/-! ### Unique factorisation: the parts and their product are injective -/

lemma prime_dvd_pw {f : ℕ →₀ ℕ} {p : ℕ} (hp : p.Prime) (h : p ∣ pw f) :
    ∃ r ∈ f.support, p ∣ r := by
  unfold pw Finsupp.prod at h
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  exact ⟨r, hr, hp.dvd_of_dvd_pow hpr⟩

lemma prime_dvd_smallPart {y e a p : ℕ} (ha : a ∈ smallPart y e) (hp : p.Prime) (h : p ∣ a) :
    p ∈ small y := by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 ha
  obtain ⟨r, hr, hpr⟩ := prime_dvd_pw hp h
  rw [smallExp, mem_finsupp_iff] at hf
  have hrs := hf.1 hr
  rwa [(Nat.prime_dvd_prime_iff_eq hp (mem_small.1 hrs).1).1 hpr]

lemma prime_dvd_largePart {y k a p : ℕ} (ha : a ∈ largePart y k) (hp : p.Prime) (h : p ∣ a) :
    p ∈ large y := by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 ha
  obtain ⟨r, hr, hpr⟩ := prime_dvd_pw hp h
  rw [largeExp, mem_finsuppAntidiag] at hf
  have hrs := hf.2 hr
  rw [slack, mem_insert] at hrs
  rcases hrs with rfl | hrs
  · exact absurd (Nat.eq_one_of_dvd_one hpr) hp.one_lt.ne'
  · rwa [(Nat.prime_dvd_prime_iff_eq hp (mem_large.1 hrs).1).1 hpr]

lemma coprime_parts {y e k a b : ℕ} (ha : a ∈ smallPart y e) (hb : b ∈ largePart y k) :
    Nat.Coprime a b :=
  Nat.coprime_of_dvd fun p hp hpa hpb => by
    have h1 := (mem_small.1 (prime_dvd_smallPart ha hp hpa)).2.2
    have h2 := (mem_large.1 (prime_dvd_largePart hb hp hpb)).2.2
    omega

lemma smallPart_pos {y e a : ℕ} (ha : a ∈ smallPart y e) : 0 < a := by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 ha
  refine pw_pos f fun p hp => ?_
  rw [smallExp, mem_finsupp_iff] at hf
  exact (mem_small.1 (hf.1 hp)).1.pos

lemma largePart_pos {y k b : ℕ} (hb : b ∈ largePart y k) : 0 < b := by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 hb
  refine pw_pos f fun p hp => ?_
  rw [largeExp, mem_finsuppAntidiag] at hf
  have := hf.2 hp
  rw [slack, mem_insert] at this
  rcases this with rfl | h
  · exact one_pos
  · exact (mem_large.1 h).1.pos

lemma mul_injOn_parts (y e k : ℕ) : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
    (↑(smallPart y e ×ˢ largePart y k) : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [coe_product, Set.mem_prod, mem_coe] at hab hab' h
  have h1 : a ∣ a' := (coprime_parts hab.1 hab'.2).dvd_of_dvd_mul_right ⟨b, h.symm⟩
  have h2 : a' ∣ a := (coprime_parts hab'.1 hab.2).dvd_of_dvd_mul_right ⟨b', h⟩
  have h3 : a = a' := Nat.dvd_antisymm h1 h2
  subst h3
  have h4 : b = b' := Nat.eq_of_mul_eq_mul_left (smallPart_pos hab.1) h
  rw [h4]

lemma card_smallPart (y e : ℕ) : (smallPart y e).card = (e + 1) ^ qq y := by
  rw [smallPart, card_image_of_injOn (pw_injOn_smallExp y e), card_smallExp]

lemma card_largePart (y k : ℕ) : (largePart y k).card = (mm y + k).choose k := by
  rw [largePart, card_image_of_injOn (pw_injOn_largeExp y k), card_largeExp]

/-- `|S_y| = (H + 1) ^ q * C(2m, m)` (equation (9)). -/
lemma card_Sy (y : ℕ) : (Sy y).card = (HH y + 1) ^ qq y * (mm y + mm y).choose (mm y) := by
  rw [Sy, card_image_of_injOn (mul_injOn_parts _ _ _), card_product, card_smallPart,
    card_largePart]

lemma card_Gy (y : ℕ) :
    (Gy y).card = (HH y - LL y + 1) ^ qq y * (mm y + (mm y - 1)).choose (mm y - 1) := by
  rw [Gy, card_image_of_injOn (mul_injOn_parts _ _ _), card_product, card_smallPart,
    card_largePart]

/-! ### At least a quarter of `S_y` is good -/

/-- Bernoulli: `(H + 1) ^ q ≤ 2 (H - L + 1) ^ q` for `H = 2 q L`. -/
lemma bernoulli_aux (q L : ℕ) : (2 * q * L + 1) ^ q ≤ 2 * (2 * q * L - L + 1) ^ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hLe : L ≤ 2 * q * L := by nlinarith
  set N : ℝ := ((2 * q * L + 1 : ℕ) : ℝ) with hNdef
  have hN : 0 < N := by positivity
  have hLN : (L : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast (by omega : L ≤ 2 * q * L + 1)
  have hx : (-2 : ℝ) ≤ -(L / N) := by
    have : (L : ℝ) / N ≤ 1 := (div_le_one hN).2 hLN
    linarith
  have hb := one_add_mul_le_pow hx q
  have hcast : ((2 * q * L - L + 1 : ℕ) : ℝ) = N * (1 + -(L / N)) := by
    rw [hNdef, Nat.cast_add, Nat.cast_sub hLe]; push_cast; field_simp; ring
  have h2 : (1 : ℝ) / 2 ≤ 1 + q * -(L / N) := by
    have h3 : (q : ℝ) * L / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hN, hNdef]; push_cast; linarith
    have h4 : (q : ℝ) * -(L / N) = -((q : ℝ) * L / N) := by ring
    linarith
  have key : N ^ q ≤ 2 * (N * (1 + -(L / N))) ^ q := by
    rw [mul_pow]
    have hNq : 0 < N ^ q := pow_pos hN q
    have := mul_le_mul_of_nonneg_left (h2.trans hb) hNq.le
    linarith
  rw [← hcast, hNdef] at key
  exact_mod_cast key

/-- `C(2m, m) = 2 C(2m - 1, m - 1)` (for `m ≥ 1`; for `m = 0` both sides are `1`). -/
lemma choose_le_two_mul (m : ℕ) : (m + m).choose m ≤ 2 * (m + (m - 1)).choose (m - 1) := by
  rcases m with _ | m
  · simp
  · rw [Nat.add_sub_cancel, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring,
      show m + 1 + m = 2 * m + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
    omega

/-- At least a quarter of `S_y` is good. -/
lemma card_Sy_le (y : ℕ) : (Sy y).card ≤ 4 * (Gy y).card := by
  rw [card_Sy, card_Gy]
  have h1 := bernoulli_aux (qq y) (LL y)
  have h2 := choose_le_two_mul (mm y)
  rw [show HH y = 2 * qq y * LL y from rfl]
  calc (2 * qq y * LL y + 1) ^ qq y * (mm y + mm y).choose (mm y)
      ≤ (2 * (2 * qq y * LL y - LL y + 1) ^ qq y) *
          (2 * (mm y + (mm y - 1)).choose (mm y - 1)) := Nat.mul_le_mul h1 h2
    _ = _ := by ring

/-! ### Good elements have their first `y` multiples in `S_y` -/

/-- If `1 ≤ j ≤ y` has no prime factor `> √y`, its exponent vector lies in `smallExp y L`:
each small-prime exponent of `j` is at most `L = ⌊log₂ y⌋`. -/
lemma factorization_mem_smallExp {y j : ℕ} (hj1 : 1 ≤ j) (hjy : j ≤ y)
    (h : ∀ p, p.Prime → p ∣ j → p * p ≤ y) : j.factorization ∈ smallExp y (LL y) := by
  rw [smallExp, mem_finsupp_iff]
  have hj0 : j ≠ 0 := by omega
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact mem_small.2 ⟨hp.1, (Nat.le_of_dvd (by omega) hp.2.1).trans hjy, h p hp.1 hp.2.1⟩
  · rw [mem_range, Nat.lt_succ_iff]
    have hp2 : 1 < p := (mem_small.1 hp).1.one_lt
    have h1 : p ^ j.factorization p ≤ j := Nat.ordProj_le p hj0
    have h2 : y < 2 ^ (LL y).succ := Nat.lt_pow_succ_log_self (by norm_num) y
    have h3 : 2 ^ (LL y).succ ≤ p ^ (LL y).succ :=
      Nat.pow_le_pow_left (mem_small.1 hp).1.two_le _
    have h4 : p ^ j.factorization p < p ^ (LL y).succ := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h4
    omega

/-- Every `1 ≤ j ≤ y` is `js * jl` with `js` having small-prime exponents `≤ L` and
`jl ∈ {1} ∪ (√y, y]` (at most one prime factor `> √y`, counted with multiplicity). -/
lemma decomp {y j : ℕ} (hj1 : 1 ≤ j) (hjy : j ≤ y) :
    ∃ js jl, j = js * jl ∧ js.factorization ∈ smallExp y (LL y) ∧ 1 ≤ js ∧ jl ∈ slack y := by
  by_cases h : ∃ p, p.Prime ∧ p ∣ j ∧ y < p * p
  · obtain ⟨p, hp, ⟨j', rfl⟩, hpy⟩ := h
    have hj' : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · rw [h0, mul_zero] at hj1; omega
      · exact h0
    have hpj' : p ≤ p * j' := Nat.le_mul_of_pos_right p hj'
    have hj'y : j' ≤ y := (Nat.le_mul_of_pos_left j' hp.pos).trans hjy
    refine ⟨j', p, by ring, factorization_mem_smallExp hj' hj'y ?_, hj', ?_⟩
    · intro r hr hrj
      by_contra hry
      push Not at hry
      have h5 : p * r ≤ y :=
        (Nat.le_of_dvd (by omega) (Nat.mul_dvd_mul_left p hrj)).trans hjy
      have h6 : y * y < p * p * (r * r) := Nat.mul_lt_mul'' hpy hry
      have h7 : p * r * (p * r) ≤ y * y := Nat.mul_le_mul h5 h5
      have h8 : p * p * (r * r) = p * r * (p * r) := by ring
      omega
    · rw [slack, mem_insert]; exact Or.inr (mem_large.2 ⟨hp, hpj'.trans hjy, hpy⟩)
  · push Not at h
    exact ⟨j, 1, by ring, factorization_mem_smallExp hj1 hjy fun p hp hpj => h p hp hpj, hj1,
      mem_insert_self _ _⟩

lemma add_mem_smallExp {y : ℕ} {g e : ℕ →₀ ℕ} (hg : g ∈ smallExp y (LL y))
    (he : e ∈ smallExp y (HH y - LL y)) : g + e ∈ smallExp y (HH y) := by
  rw [smallExp, mem_finsupp_iff] at hg he ⊢
  refine ⟨Finsupp.support_add.trans (union_subset hg.1 he.1), fun i hi => ?_⟩
  have h1 := hg.2 i hi
  have h2 := he.2 i hi
  rw [mem_range] at h1 h2 ⊢
  have hq : 0 < qq y := card_pos.2 ⟨i, hi⟩
  have hLH : LL y ≤ HH y := Nat.le_mul_of_pos_left (LL y) (by omega)
  rw [Finsupp.add_apply]
  omega

lemma add_single_mem_largeExp {y k x c : ℕ} {f : ℕ →₀ ℕ} (hf : f ∈ largeExp y k)
    (hx : x ∈ slack y) : f + Finsupp.single x c ∈ largeExp y (k + c) := by
  rw [largeExp, mem_finsuppAntidiag] at hf ⊢
  refine ⟨?_, Finsupp.support_add.trans
    (union_subset hf.2 (Finsupp.support_single_subset.trans (singleton_subset_iff.2 hx)))⟩
  change ∑ i ∈ slack y, (f + Finsupp.single x c) i = k + c
  simp only [Finsupp.add_apply, sum_add_distrib, Finsupp.single_apply, sum_ite_eq, hx, ↓reduceIte]
  rw [← hf.1]

/-- Sanity check of the slack encoding: `largePart y k` is exactly the set of
`∏_{√y < p ≤ y} p ^ v_p` with `∑ v_p ≤ k`, as in (8). -/
lemma mem_largePart_iff {y k b : ℕ} : b ∈ largePart y k ↔
    ∃ v : ℕ →₀ ℕ, v.support ⊆ large y ∧ ∑ p ∈ large y, v p ≤ k ∧ pw v = b := by
  constructor
  · rintro hb
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hb
    rw [largeExp, mem_finsuppAntidiag] at hf
    refine ⟨f.erase 1, fun p hp => ?_, ?_, (pw_erase_one f).symm⟩
    · rw [Finsupp.support_erase, mem_erase] at hp
      have := hf.2 hp.2
      rw [slack, mem_insert] at this
      exact this.resolve_left hp.1
    · have h1 : (slack y).sum f = f 1 + ∑ p ∈ large y, (f.erase 1) p := by
        rw [slack, sum_insert (one_notMem_large y)]
        congr 1
        refine sum_congr rfl fun p hp => ?_
        rw [Finsupp.erase_ne (fun h : p = 1 => one_notMem_large y (h ▸ hp))]
      omega
  · rintro ⟨v, hv, hsum, rfl⟩
    have hv1 : v 1 = 0 := Finsupp.notMem_support_iff.1 fun h => one_notMem_large y (hv h)
    have hvL : v ∈ largeExp y (∑ p ∈ large y, v p) := by
      rw [largeExp, mem_finsuppAntidiag, slack, sum_insert (one_notMem_large y), hv1, zero_add]
      exact ⟨rfl, hv.trans (subset_insert _ _)⟩
    have h := add_single_mem_largeExp (c := k - ∑ p ∈ large y, v p) hvL (mem_insert_self 1 _)
    rw [show ∑ p ∈ large y, v p + (k - ∑ p ∈ large y, v p) = k by omega] at h
    refine mem_image.2 ⟨_, h, ?_⟩
    rw [pw_add, pw_single, one_pow, mul_one]

/-- If `a` is good and `1 ≤ j ≤ y`, then `j a ∈ S_y`. -/
lemma mul_mem_Sy {y a j : ℕ} (ha : a ∈ Gy y) (hj1 : 1 ≤ j) (hjy : j ≤ y) : j * a ∈ Sy y := by
  obtain ⟨⟨α, β⟩, hab, rfl⟩ := mem_image.1 ha
  rw [mem_product] at hab
  obtain ⟨e, he, rfl⟩ := mem_image.1 hab.1
  obtain ⟨f, hf, rfl⟩ := mem_image.1 hab.2
  obtain ⟨js, jl, rfl, hjs, hjs1, hjl⟩ := decomp hj1 hjy
  have hjs' : pw js.factorization = js := Nat.prod_factorization_pow_eq_self (by omega)
  have hsm := add_mem_smallExp hjs he
  have hjl' := hjl
  rw [slack, mem_insert] at hjl'
  rcases hjl' with rfl | hjl'
  · have hl := add_single_mem_largeExp (c := mm y - (mm y - 1)) hf hjl
    rw [show mm y - 1 + (mm y - (mm y - 1)) = mm y by omega] at hl
    refine mem_image.2 ⟨(pw (js.factorization + e), pw (f + Finsupp.single 1 (mm y - (mm y - 1)))),
      mem_product.2 ⟨mem_image_of_mem _ hsm, mem_image_of_mem _ hl⟩, ?_⟩
    simp only [pw_add, pw_single, one_pow, hjs']
    ring
  · have hm : 0 < mm y := card_pos.2 ⟨jl, hjl'⟩
    have hl := add_single_mem_largeExp (c := 1) hf hjl
    rw [show mm y - 1 + 1 = mm y by omega] at hl
    refine mem_image.2 ⟨(pw (js.factorization + e), pw (f + Finsupp.single jl 1)),
      mem_product.2 ⟨mem_image_of_mem _ hsm, mem_image_of_mem _ hl⟩, ?_⟩
    simp only [pw_add, pw_single, pow_one, hjs']
    ring

lemma Gy_subset_Sy {y : ℕ} (hy : 1 ≤ y) : Gy y ⊆ Sy y := fun a ha => by
  simpa using mul_mem_Sy ha le_rfl hy

lemma pos_of_mem_Sy {y a : ℕ} (ha : a ∈ Sy y) : 0 < a := by
  obtain ⟨⟨α, β⟩, hab, rfl⟩ := mem_image.1 ha
  rw [mem_product] at hab
  exact Nat.mul_pos (smallPart_pos hab.1) (largePart_pos hab.2)

lemma card_Sy_pos (y : ℕ) : 0 < (Sy y).card := by
  rw [card_Sy]
  exact Nat.mul_pos (pow_pos (by omega) _) (Nat.choose_pos (by omega))

/-! ### Size of `S_y`: `log |S_y| = O(y / log y)` (upper half of (12)) -/

lemma qq_le_sqrt (y : ℕ) : qq y ≤ Nat.sqrt y := by
  calc qq y ≤ (Icc 1 (Nat.sqrt y)).card := by
        refine card_le_card fun p hp => ?_
        have hp' := mem_small.1 hp
        exact mem_Icc.2 ⟨hp'.1.one_lt.le, Nat.le_sqrt.2 hp'.2.2⟩
    _ = Nat.sqrt y := by simp

lemma mm_le (y : ℕ) : mm y ≤ (y + 1).primesBelow.card := card_le_card (filter_subset _ _)

lemma HH_add_one_le {y : ℕ} (hy : 2 ≤ y) : HH y + 1 ≤ y ^ 4 := by
  have hq : qq y ≤ y := (qq_le_sqrt y).trans (Nat.sqrt_le_self y)
  have hL : LL y ≤ y := Nat.log_le_self 2 y
  have h1 : HH y ≤ 2 * (y * y) := by
    unfold HH
    calc 2 * qq y * LL y ≤ 2 * y * y := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hq) hL
      _ = 2 * (y * y) := by ring
  have h2 : 2 * 2 ≤ y * y := Nat.mul_le_mul hy hy
  have h3 : 2 * 2 * (y * y) ≤ y * y * (y * y) := Nat.mul_le_mul_right _ h2
  have h4 : y ^ 4 = y * y * (y * y) := by ring
  omega

/-- The constant in `|S_y| ≤ exp (C₃ y / log y)`. -/
noncomputable def C₃ : ℝ := 64 + log 4 * (2 * log 4 + 2)

lemma C₃_pos : 0 < C₃ := by
  have : 0 < log (4 : ℝ) := log_pos (by norm_num)
  unfold C₃; positivity

/-- `|S_y| ≤ (H + 1) ^ q * 4 ^ m ≤ exp (C₃ y / log y)`, using `q ≤ √y`, `H + 1 ≤ y ^ 4`
and Chebyshev's bound for `m ≤ π(y)`. -/
lemma card_Sy_le_exp {y : ℕ} (hy : 2 ≤ y) : ((Sy y).card : ℝ) ≤ exp (C₃ * (y / log y)) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hy0 : (0 : ℝ) < y := by linarith
  have hly : 0 < log (y : ℝ) := log_pos hy1
  have hl4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hN : (Sy y).card ≤ (y ^ 4) ^ qq y * 4 ^ mm y := by
    rw [card_Sy]
    refine Nat.mul_le_mul (Nat.pow_le_pow_left (HH_add_one_le hy) _) ?_
    calc (mm y + mm y).choose (mm y) ≤ 2 ^ (mm y + mm y) := Nat.choose_le_two_pow _ _
      _ = 4 ^ mm y := by rw [← two_mul, pow_mul]; norm_num
  have hR : ((Sy y).card : ℝ) ≤ ((y : ℝ) ^ 4) ^ qq y * 4 ^ mm y := by exact_mod_cast hN
  have e1 : ((y : ℝ) ^ 4) ^ qq y = exp (((4 * qq y : ℕ) : ℝ) * log y) := by
    rw [exp_nat_mul, exp_log hy0, ← pow_mul]
  have e2 : (4 : ℝ) ^ mm y = exp ((mm y : ℝ) * log 4) := by
    rw [exp_nat_mul, exp_log (by norm_num)]
  rw [e1, e2, ← exp_add] at hR
  refine hR.trans (exp_le_exp.2 ?_)
  have hq : (qq y : ℝ) ≤ √(y : ℝ) :=
    (Nat.cast_le.2 (qq_le_sqrt y)).trans Real.nat_sqrt_le_real_sqrt
  have hm : (mm y : ℝ) ≤ (2 * log 4 + 2) * (y / log y) :=
    (Nat.cast_le.2 (mm_le y)).trans (card_primesBelow_le y hy)
  have hs := sqrt_mul_log_le hy1
  have h1 : ((4 * qq y : ℕ) : ℝ) * log y ≤ 64 * (y / log y) := by
    push_cast
    have := mul_le_mul_of_nonneg_right hq hly.le
    linarith
  have h2 : (mm y : ℝ) * log 4 ≤ log 4 * (2 * log 4 + 2) * (y / log y) := by
    have := mul_le_mul_of_nonneg_right hm hl4.le
    linarith
  unfold C₃
  linarith

/-- The block of §3: `B = S_y`, `G` = good elements, `|G| ≥ |B| / 4`,
`|B| ≤ exp (C₃ y / log y)`. Same shape as `RunsOfMultiples.block`. -/
theorem block_alt : ∃ δ : ℝ, 0 < δ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ y : ℕ, 2 ≤ y → ∃ B G : Finset ℕ,
    (∀ a ∈ B, 0 < a) ∧ G ⊆ B ∧ (∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) ∧ 0 < B.card ∧
      δ * B.card ≤ G.card ∧ (B.card : ℝ) ≤ exp (C₂ * (y / log y)) := by
  refine ⟨1 / 4, by norm_num, C₃, C₃_pos, fun y hy => ⟨Sy y, Gy y, fun a ha => pos_of_mem_Sy ha,
    Gy_subset_Sy (by omega), fun a ha j hj1 hjy => mul_mem_Sy ha hj1 hjy, card_Sy_pos y, ?_,
    card_Sy_le_exp hy⟩⟩
  have : ((Sy y).card : ℝ) ≤ 4 * (Gy y).card := by exact_mod_cast card_Sy_le y
  linarith

end Alt

/-! ### Padding to every `n` (end of §3)

`y = ⌊ε log n log log n⌋` with `ε = 1 / (2 C₂)`, so `|S_y| ≤ exp (L / 2) ≤ n / 2`; take
`⌊n / |S_y|⌋` disjoint dilates `M ^ i • S_y` and pad (`replicate` from
`RunsOfMultiples.Replication`). The argument below is the one of `lower_bound`, applied to the
block `block_alt` of §3. -/

/-- **Lower bound (alternative construction, §3).** -/
theorem lower_bound_alt : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ,
    (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
  obtain ⟨δ, hδ, C₂, hC₂, hblock⟩ := Alt.block_alt
  exact lower_bound_of_block hδ hC₂ hblock

end RunsOfMultiples
