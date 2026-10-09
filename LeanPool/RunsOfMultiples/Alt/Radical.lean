/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Alt.Defs
public import LeanPool.RunsOfMultiples.PrimeEstimates
public import Mathlib.Data.Nat.Squarefree

/-!
# Radical bound and double counting (Lemma 3 and equation (7))

For a finite set `T` of positive integers that is closed under divisors (`DivClosed`) and under
replacing a prime factor by a smaller prime (`ShiftClosed`), we show

  `∑_{a ∈ T} L T a = O(n log n log log n)`,   `n = |T|`.

* Lemma 3: for `b ∈ T` with `m` distinct prime factors, `2 ^ m ≤ n`, and every product
  `∏_{p ∣ b} g p` with `g p ≤ p` prime lies in `T`. Each such product has at most `m ^ m`
  preimages `g`, so `∏_{p ∣ b} π(p) ≤ n m ^ m`. With `log p ≤ 2 log π(p) + C` this gives
  `∑_{p ∣ b} log p = O(log n log log n)`. (`docs/first-missing-multiple.pdf` uses `m!` preimages;
  `m ^ m` suffices.)
* Equation (7): `∑_{a ∈ T} θ(L T a) ≤ ∑_{b ∈ T} ∑_{p ∣ b} log p`, via `(a, p) ↦ (p a, p)`.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-- Replacing the prime factors `p ∈ s` of `c * ∏ s` by smaller primes `g p` stays inside a
shift-closed set. -/
lemma box_mem {T : Finset ℕ} (hshift : ShiftClosed T) (g : ℕ → ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (g p).Prime ∧ g p ≤ p) :
    ∀ c, c * ∏ p ∈ s, p ∈ T → c * ∏ p ∈ s, g p ∈ T := by
  induction s using Finset.induction_on with
  | empty => intro c hc; simpa using hc
  | insert q s hq ih =>
    intro c hc
    have hs' : ∀ p ∈ s, p.Prime ∧ (g p).Prime ∧ g p ≤ p := fun p hp => hs p (mem_insert_of_mem hp)
    obtain ⟨hqp, hgq, hgqle⟩ := hs q (mem_insert_self q s)
    rw [prod_insert hq] at hc ⊢
    have h1 : (c * q) * ∏ p ∈ s, g p ∈ T := ih hs' (c * q) (by rw [mul_assoc]; exact hc)
    rcases hgqle.lt_or_eq with hlt | heq
    · have h2 := hshift _ h1 (g q) q hgq hqp hlt ⟨c * ∏ p ∈ s, g p, by ring⟩
      have h3 : (c * q * ∏ p ∈ s, g p) / q = c * ∏ p ∈ s, g p :=
        Nat.div_eq_of_eq_mul_left hqp.pos (by ring)
      rw [h3] at h2
      convert h2 using 1
      ring
    · rw [heq]
      convert h1 using 1
      ring

/-- Products of prime factors of `b ∈ T` lie in a divisor-closed `T`. -/
lemma prod_primeFactors_mem {T : Finset ℕ} (hdiv : DivClosed T) {b : ℕ} (hb : b ∈ T)
    {s : Finset ℕ} (hs : s ⊆ b.primeFactors) : ∏ p ∈ s, p ∈ T :=
  hdiv b hb _ ((prod_dvd_prod_of_subset s b.primeFactors id hs).trans (Nat.prod_primeFactors_dvd b))

/-- (5): the squarefree divisors of `b` are distinct elements of `T`, so `2 ^ m ≤ |T|`. -/
lemma two_pow_card_primeFactors_le {T : Finset ℕ} (hdiv : DivClosed T) {b : ℕ} (hb : b ∈ T) :
    2 ^ b.primeFactors.card ≤ T.card := by
  rw [← card_powerset]
  refine card_le_card_of_injOn (fun s => ∏ p ∈ s, p)
    (fun s hs => prod_primeFactors_mem hdiv hb (mem_powerset.1 hs)) ?_
  intro s hs t ht hst
  have hs' : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.1 (mem_coe.1 hs) hp)
  have ht' : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.1 (mem_coe.1 ht) hp)
  rw [← Nat.primeFactors_prod hs', ← Nat.primeFactors_prod ht']
  exact congrArg _ hst

/-- (6), with `m ^ m` in place of `m!`: the box of index tuples has at most `|T| m ^ m`
elements. -/
lemma prod_card_primesUpTo_le {T : Finset ℕ} (hdiv : DivClosed T) (hshift : ShiftClosed T)
    {b : ℕ} (hb : b ∈ T) :
    ∏ p ∈ b.primeFactors, (primesUpTo p).card ≤
      T.card * b.primeFactors.card ^ b.primeFactors.card := by
  classical
  set P := b.primeFactors with hP
  let G : Finset (P → ℕ) := Fintype.piFinset (fun p : P => primesUpTo p.1)
  let Φ : (P → ℕ) → ℕ := fun g => ∏ p : P, g p
  have hG : G.card = ∏ p ∈ P, (primesUpTo p).card := by
    simp only [G, Fintype.card_piFinset]
    exact prod_coe_sort P (fun p => (primesUpTo p).card)
  have hmem : ∀ g ∈ G, ∀ p : P, (g p).Prime ∧ g p ≤ p := by
    intro g hg p
    have := Fintype.mem_piFinset.1 hg p
    simp only [primesUpTo, mem_filter, mem_range] at this
    exact ⟨this.2, by omega⟩
  have hmaps : ∀ g ∈ G, Φ g ∈ T := by
    intro g hg
    let g' : ℕ → ℕ := fun x => if h : x ∈ P then g ⟨x, h⟩ else x
    have hΦ : Φ g = 1 * ∏ p ∈ P, g' p := by
      rw [one_mul, ← prod_coe_sort P g']
      refine prod_congr rfl fun p _ => ?_
      simp [g', p.2]
    rw [hΦ]
    refine box_mem hshift g' P (fun p hp => ?_) 1
      (by rw [one_mul]; exact prod_primeFactors_mem hdiv hb subset_rfl)
    have := hmem g hg ⟨p, hp⟩
    simp only [g', hp, ↓reduceDIte]
    exact ⟨Nat.prime_of_mem_primeFactors hp, this⟩
  have hfib : ∀ x ∈ T, (G.filter (fun g => Φ g = x)).card ≤ P.card ^ P.card := by
    intro x _
    rcases (G.filter (fun g => Φ g = x)).eq_empty_or_nonempty with he | ⟨g₀, hg₀⟩
    · rw [he, card_empty]; exact Nat.zero_le _
    rw [mem_filter] at hg₀
    have hsub : G.filter (fun g => Φ g = x) ⊆ Fintype.piFinset (fun _ : P => x.primeFactors) := by
      intro g hg
      rw [mem_filter] at hg
      rw [Fintype.mem_piFinset]
      intro p
      have hp := (hmem g hg.1 p).1
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, ?_⟩
      · rw [← hg.2]; exact dvd_prod_of_mem _ (mem_univ p)
      · rw [← hg.2]; exact (prod_pos fun q _ => (hmem g hg.1 q).1.pos).ne'
    have hx : x.primeFactors.card ≤ P.card := by
      have : x.primeFactors ⊆ univ.image g₀ := by
        intro q hq
        rw [Nat.mem_primeFactors] at hq
        rw [← hg₀.2] at hq
        obtain ⟨p, _, hqp⟩ := (Nat.Prime.prime hq.1).dvd_finsetProd_iff _ |>.1 hq.2.1
        rw [mem_image]
        exact ⟨p, mem_univ p, ((Nat.prime_dvd_prime_iff_eq hq.1 (hmem g₀ hg₀.1 p).1).1 hqp).symm⟩
      refine (card_le_card this).trans (card_image_le.trans ?_)
      simp
    refine (card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_coe]
    exact Nat.pow_le_pow_left hx _
  have := card_le_mul_card_image_of_maps_to hmaps (P.card ^ P.card) hfib
  rw [← hG, mul_comm]
  exact this

/-- `log p ≤ 2 log π(p) + C` for all primes `p`, from `π(4q) - π(q) ≥ q^(3/4)` for large `q`
(this is `π(x) ≥ √x` for large `x`, up to constants). -/
lemma log_le_two_log_card_primesUpTo : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime →
    log (p : ℝ) ≤ 2 * log ((primesUpTo p).card : ℝ) + C := by
  obtain ⟨q₀, hq₀⟩ := many_primes
  set P₀ : ℕ := 8 * (q₀ + 1) with hP₀
  have hP₀1 : (1 : ℝ) ≤ P₀ := by norm_cast; omega
  have hl8 : 0 ≤ log (8 : ℝ) := log_nonneg (by norm_num)
  refine ⟨log P₀ + log 8, add_nonneg (log_nonneg hP₀1) hl8, fun p hp => ?_⟩
  have hcard1 : 1 ≤ (primesUpTo p).card :=
    card_pos.2 ⟨p, by simp [primesUpTo, hp]⟩
  have hlogc : 0 ≤ log ((primesUpTo p).card : ℝ) := log_nonneg (by exact_mod_cast hcard1)
  by_cases hpP : p < P₀
  · have : log (p : ℝ) ≤ log P₀ :=
      log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpP.le)
    linarith
  push Not at hpP
  set q := p / 4 with hq
  have hqq₀ : q₀ ≤ q := by omega
  have hq0 : 0 < q := by omega
  have h8q : p ≤ 8 * q := by omega
  have hsub : (Ioc q (4 * q)).filter Nat.Prime ⊆ primesUpTo p := by
    intro x hx
    simp only [mem_filter, mem_Ioc, primesUpTo, mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (primesUpTo p).card :=
    (hq₀ q hqq₀).trans (by exact_mod_cast card_le_card hsub)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have h2 : (3 / 4 : ℝ) * log q ≤ log (primesUpTo p).card := by
    rw [← log_rpow hqpos]
    exact log_le_log (rpow_pos_of_pos hqpos _) h1
  have h3 : log (p : ℝ) ≤ log 8 + log q := by
    rw [← log_mul (by norm_num) hqpos.ne']
    exact log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h8q)
  have := log_nonneg hP₀1
  have hlq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq0)
  linarith

/-- Lemma 3, explicit form: `∑_{p ∣ b} log p ≤ 2 log n + 2 m log m + C m`. -/
lemma sum_log_primeFactors_le {C : ℝ}
    (hC : ∀ p : ℕ, p.Prime → log (p : ℝ) ≤ 2 * log ((primesUpTo p).card : ℝ) + C)
    {T : Finset ℕ} (hdiv : DivClosed T) (hshift : ShiftClosed T) {b : ℕ} (hb : b ∈ T) :
    ∑ p ∈ b.primeFactors, log (p : ℝ) ≤ 2 * log (T.card : ℝ) +
      2 * ((b.primeFactors.card : ℝ) * log (b.primeFactors.card : ℝ)) +
      C * b.primeFactors.card := by
  set P := b.primeFactors with hP
  set m := P.card with hm
  have hn : (0 : ℝ) < T.card := by exact_mod_cast card_pos.2 ⟨b, hb⟩
  have h1 : ∑ p ∈ P, log (p : ℝ) ≤ ∑ p ∈ P, (2 * log ((primesUpTo p).card : ℝ) + C) :=
    sum_le_sum fun p hp => hC p (Nat.prime_of_mem_primeFactors hp)
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h1
  have hpos : ∀ p ∈ P, ((primesUpTo p).card : ℝ) ≠ 0 := fun p hp => by
    have : 0 < (primesUpTo p).card :=
      card_pos.2 ⟨p, by simp [primesUpTo, Nat.prime_of_mem_primeFactors hp]⟩
    positivity
  have h2 : ∑ p ∈ P, log ((primesUpTo p).card : ℝ) ≤ log (T.card : ℝ) + m * log m := by
    rw [← log_prod hpos]
    have hcast : (∏ p ∈ P, ((primesUpTo p).card : ℝ)) ≤ (T.card : ℝ) * (m : ℝ) ^ m := by
      exact_mod_cast prod_card_primesUpTo_le hdiv hshift hb
    have hprod : 0 < ∏ p ∈ P, ((primesUpTo p).card : ℝ) :=
      prod_pos fun p hp => lt_of_le_of_ne (Nat.cast_nonneg _) (hpos p hp).symm
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0] at hcast ⊢
      simp only [pow_zero, mul_one, CharP.cast_eq_zero, zero_mul, add_zero] at hcast ⊢
      exact log_le_log hprod hcast
    · have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
      refine (log_le_log hprod hcast).trans_eq ?_
      rw [log_mul hn.ne' (by positivity), log_pow]
  linarith

/-- **Lemma 3.** `∑_{p ∣ b} log p = O(log n log log n)` for `b ∈ T`, once `log log n ≥ 1`. -/
theorem radical_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ T : Finset ℕ, DivClosed T → ShiftClosed T →
    1 ≤ log (log (T.card : ℝ)) → ∀ b ∈ T,
      ∑ p ∈ b.primeFactors, log (p : ℝ) ≤ K * log (T.card : ℝ) * log (log (T.card : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := log_le_two_log_card_primesUpTo
  have hl2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  set c₂ : ℝ := (log 2)⁻¹ with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨2 + 2 * (c₂ * (c₂ + 1)) + C * c₂, by positivity, fun T hdiv hshift hℓℓ b hb => ?_⟩
  set m := b.primeFactors.card with hm
  have hn1 : (1 : ℝ) ≤ T.card := by exact_mod_cast card_pos.2 ⟨b, hb⟩
  set ℓ := log (T.card : ℝ) with hℓdef
  have hℓ0 : 0 ≤ ℓ := log_nonneg hn1
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h
    push Not at h
    linarith [log_nonpos hℓ0 h.le]
  set ℓℓ := log ℓ with hℓℓdef
  -- m ≤ c₂ ℓ
  have hmℓ : (m : ℝ) ≤ c₂ * ℓ := by
    have h2m : ((2 ^ m : ℕ) : ℝ) ≤ T.card := by exact_mod_cast two_pow_card_primeFactors_le hdiv hb
    have : (m : ℝ) * log 2 ≤ ℓ := by
      rw [← log_pow]
      push_cast at h2m
      exact log_le_log (by positivity) h2m
    rw [hc₂, inv_mul_eq_div, le_div_iff₀ hl2]
    exact this
  -- m log m ≤ c₂ (c₂ + 1) ℓ ℓℓ
  have hmlog : (m : ℝ) * log m ≤ c₂ * (c₂ + 1) * (ℓ * ℓℓ) := by
    have hrhs : 0 ≤ c₂ * (c₂ + 1) * (ℓ * ℓℓ) := by
      have : 0 ≤ ℓℓ := by linarith
      positivity
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0]; simpa using hrhs
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hlogm : log (m : ℝ) ≤ (c₂ + 1) * ℓℓ := by
      have h1 : log (m : ℝ) ≤ log (c₂ * ℓ) := log_le_log (by linarith) hmℓ
      have hc₂pos : 0 < c₂ := by positivity
      rw [log_mul hc₂pos.ne' (by linarith)] at h1
      have h2 : log c₂ ≤ c₂ := by linarith [log_le_sub_one_of_pos hc₂pos]
      have h3 : c₂ ≤ c₂ * ℓℓ := le_mul_of_one_le_right hc₂0 hℓℓ
      linarith
    have hlogm0 : 0 ≤ log (m : ℝ) := log_nonneg hmr
    calc (m : ℝ) * log m ≤ (c₂ * ℓ) * ((c₂ + 1) * ℓℓ) :=
          mul_le_mul hmℓ hlogm hlogm0 (by positivity)
      _ = c₂ * (c₂ + 1) * (ℓ * ℓℓ) := by ring
  have hmain := sum_log_primeFactors_le hC hdiv hshift hb
  rw [← hm, ← hℓdef] at hmain
  have hℓℓ' : ℓ ≤ ℓ * ℓℓ := le_mul_of_one_le_right hℓ0 hℓℓ
  have hCm : C * m ≤ C * c₂ * (ℓ * ℓℓ) := by
    have : C * m ≤ C * (c₂ * ℓ) := mul_le_mul_of_nonneg_left hmℓ hC0
    have h' : C * (c₂ * ℓ) ≤ C * (c₂ * (ℓ * ℓℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓℓ' hc₂0) hC0
    linarith
  calc ∑ p ∈ b.primeFactors, log (p : ℝ) ≤ 2 * ℓ + 2 * (m * log m) + C * m := hmain
    _ ≤ 2 * (ℓ * ℓℓ) + 2 * (c₂ * (c₂ + 1) * (ℓ * ℓℓ)) + C * c₂ * (ℓ * ℓℓ) := by linarith
    _ = (2 + 2 * (c₂ * (c₂ + 1)) + C * c₂) * ℓ * ℓℓ := by ring

/-- **Double counting (7).** `∑_{a ∈ T} θ(L T a) ≤ ∑_{b ∈ T} ∑_{p ∣ b} log p`, via the injection
`(a, p) ↦ (p a, p)`: if `p ≤ L T a` then `p a ∈ T`. -/
theorem sum_theta_L_le (T : Finset ℕ) (hpos : ∀ a ∈ T, 0 < a) :
    ∑ a ∈ T, ∑ p ∈ primesUpTo (L T a), log (p : ℝ) ≤
      ∑ b ∈ T, ∑ p ∈ b.primeFactors, log (p : ℝ) := by
  classical
  rw [sum_sigma', sum_sigma']
  refine sum_le_sum_of_injOn (fun x => (⟨x.2 * x.1, x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
    (fun _ _ => le_rfl) (fun y _ _ => log_natCast_nonneg _)
  · rintro ⟨a, p⟩ ha ⟨a', p'⟩ ha' h
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨h1, rfl⟩ := h
    have hp : 0 < p := by
      have := (mem_sigma.1 (mem_coe.1 ha)).2
      simp only [primesUpTo, mem_filter] at this
      exact this.2.pos
    rw [Nat.eq_of_mul_eq_mul_left hp h1]
  · intro y hy
    rw [mem_image] at hy
    obtain ⟨⟨a, p⟩, hx, rfl⟩ := hy
    rw [mem_sigma] at hx ⊢
    obtain ⟨haT, hpa⟩ := hx
    simp only [primesUpTo, mem_filter, mem_range] at hpa
    have hA : a ∈ A T (L T a) := (mem_A_iff T hpos).2 ⟨haT, le_rfl⟩
    have hmem : p * a ∈ T := mul_mem_of_mem_A hA hpa.2.one_lt.le (by omega)
    refine ⟨hmem, ?_⟩
    rw [Nat.mem_primeFactors]
    exact ⟨hpa.2, dvd_mul_right p a, (Nat.mul_pos hpa.2.pos (hpos a haT)).ne'⟩

/-- **Upper bound for closed sets.** If `T` is closed under divisors and prime shifts, then
`∑_{a ∈ T} L T a = O(n log n log log n)` with `n = |T|`. -/
theorem sum_L_le_of_closed : ∃ C : ℝ, ∃ N : ℕ, ∀ T : Finset ℕ, (∀ a ∈ T, 0 < a) →
    DivClosed T → ShiftClosed T → N ≤ T.card →
    (∑ a ∈ T, (L T a : ℝ)) ≤ C * T.card * Real.log T.card * Real.log (Real.log T.card) := by
  obtain ⟨K, hK0, hK⟩ := radical_bound
  obtain ⟨C₀, hC₀, hθ⟩ := theta_lower
  set c : ℝ := log 2 / 2 with hcdef
  have hc : 0 < c := by have := log_pos (one_lt_two : (1 : ℝ) < 2); positivity
  refine ⟨(K + C₀) / c, ⌈exp (exp 1)⌉₊, fun T hpos hdiv hshift hN => ?_⟩
  set n : ℝ := (T.card : ℝ) with hndef
  have hnexp : exp (exp 1) ≤ n := (Nat.le_ceil _).trans (by rw [hndef]; exact_mod_cast hN)
  have hn0 : 0 < n := (exp_pos _).trans_le hnexp
  have hℓ : exp 1 ≤ log n := (le_log_iff_exp_le hn0).2 hnexp
  have hℓ0 : 0 < log n := (exp_pos 1).trans_le hℓ
  have hℓℓ : 1 ≤ log (log n) := (le_log_iff_exp_le hℓ0).2 hℓ
  have hℓ1 : 1 ≤ log n := by linarith [add_one_le_exp (1 : ℝ)]
  -- θ(L a) ≥ c L a - C₀
  have h1 : ∀ a ∈ T, c * (L T a : ℝ) - C₀ ≤ ∑ p ∈ primesUpTo (L T a), log (p : ℝ) :=
    fun a _ => by rw [sum_primesUpTo_eq_theta]; exact hθ _
  have h2 := sum_le_sum h1
  rw [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← hndef] at h2
  have h3 := sum_theta_L_le T hpos
  have h4 : ∑ b ∈ T, ∑ p ∈ b.primeFactors, log (p : ℝ) ≤
      ∑ _b ∈ T, K * log n * log (log n) :=
    sum_le_sum fun b hb => hK T hdiv hshift hℓℓ b hb
  rw [sum_const, nsmul_eq_mul, ← hndef] at h4
  have h5 : n ≤ n * log n * log (log n) := by
    have : 1 ≤ log n * log (log n) := one_le_mul_of_one_le_of_one_le hℓ1 hℓℓ
    calc n = n * 1 := (mul_one n).symm
      _ ≤ n * (log n * log (log n)) := mul_le_mul_of_nonneg_left this hn0.le
      _ = n * log n * log (log n) := by ring
  have h6 : C₀ * n ≤ C₀ * (n * log n * log (log n)) := mul_le_mul_of_nonneg_left h5 hC₀
  rw [show (K + C₀) / c * n * log n * log (log n) =
      ((K + C₀) * (n * log n * log (log n))) / c by ring, le_div_iff₀ hc]
  linarith

end RunsOfMultiples
