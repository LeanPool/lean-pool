/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Edges
public import LeanPool.RunsOfMultiples.PrimeInput
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The upper bound

The main argument, with the two prime-number inputs (a Chebyshev lower bound for `θ` and a
lower bound for the number of primes in `(q, K q]`) taken as the hypothesis `PrimeInput`.
These are discharged from Mathlib's `Chebyshev` file in `Primes.lean`.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

lemma card_le_sup (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) : S.card ≤ S.sup id := by
  have : S ⊆ Icc 1 (S.sup id) := fun a ha =>
    mem_Icc.2 ⟨hS a ha, le_sup (f := id) ha⟩
  simpa using card_le_card this

lemma card_mul_log_le {T S : Finset ℕ} (hTS : T ⊆ S) :
    (T.card : ℝ) * log T.card ≤ T.card * log S.card := by
  rcases Nat.eq_zero_or_pos T.card with h | h
  · simp [h]
  · have h' : (0 : ℝ) < T.card := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left (log_le_log h' (by exact_mod_cast card_le_card hTS)) h'.le

/-- The per-fibre estimate: weight `log q` on the pairs `(a, q)` with `a ∈ A (K q)`. -/
lemma fibre_bound (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {K : ℕ} (hK : 1 ≤ K) {q₀ : ℕ}
    (hgap : ∀ q : ℕ, q₀ ≤ q →
      (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (((Ioc q (K * q)).filter Nat.Prime).card : ℝ))
    {Q₀ : ℝ} (hQ₀1 : 1 ≤ Q₀) (hQ₀q₀ : (q₀ : ℝ) ≤ Q₀)
    (hQ₀ : ∀ q : ℕ, Q₀ ≤ q → log q * log S.card ≤ (q : ℝ) ^ ((1 : ℝ) / 4))
    {q : ℕ} (hq : q.Prime) (c : ℕ →₀ ℕ) :
    log q * ((A S (K * q)).filter (fun m => key q m = c)).card ≤
      (log Q₀ + 2 / log 2) * ((A S q).filter (fun m => key q m = c)).card +
        4 * ent (S.filter (fun m => key q m = c)) (fun m => m.factorization q) := by
  set T := S.filter (fun m => key q m = c) with hTdef
  set G := (A S q).filter (fun m => key q m = c) with hGdef
  set H := (A S (K * q)).filter (fun m => key q m = c) with hHdef
  have hTpos : ∀ m ∈ T, 0 < m := fun m hm => hS m (mem_filter.1 hm).1
  have hHG : H ⊆ G := filter_subset_filter _ (A_anti S (Nat.le_mul_of_pos_left q hK))
  have hGT : G ⊆ T := filter_subset_filter _ (A_subset S q)
  have hmapG : ∀ m ∈ G, q * m ∈ T ∧ (q * m).factorization q = m.factorization q + 1 := by
    intro m hm
    rw [mem_filter] at hm
    have hmS : m ∈ S := A_subset S q hm.1
    refine ⟨?_, factorization_prime_mul_self hq (hS m hmS).ne'⟩
    rw [mem_filter]
    exact ⟨mul_mem_of_mem_A hm.1 hq.one_le le_rfl,
      by rw [key_prime_mul hq le_rfl (hS m hmS).ne', hm.2]⟩
  have hent : 0 ≤ ent T (fun m => m.factorization q) := ent_nonneg _ _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  have hlogQ₀ : 0 ≤ log Q₀ := log_nonneg hQ₀1
  have hHGc : (H.card : ℝ) ≤ G.card := by exact_mod_cast card_le_card hHG
  have hc2 : 0 ≤ 2 / log (2 : ℝ) := by positivity
  have hGc : (0 : ℝ) ≤ G.card := by positivity
  by_cases hsmall : (q : ℝ) < Q₀
  · -- small primes
    have : log (q : ℝ) ≤ log Q₀ := log_le_log hqpos hsmall.le
    calc log q * (H.card : ℝ) ≤ log Q₀ * G.card :=
          mul_le_mul this hHGc (by positivity) hlogQ₀
      _ ≤ _ := by nlinarith only [mul_nonneg hc2 hGc, hent]
  push Not at hsmall
  by_cases hsparse : (G.card : ℝ) * √(q : ℝ) ≤ T.card
  · -- sparse fibre: pure entropy
    have := ent_ge_sparse T G (fun m => m.factorization q) q hq.pos hGT hmapG hsparse
    calc log q * (H.card : ℝ) ≤ log q * G.card := mul_le_mul_of_nonneg_left hHGc hlogq
      _ ≤ 4 * ent T (fun m => m.factorization q) := by linarith
      _ ≤ _ := by nlinarith only [mul_nonneg (add_nonneg hlogQ₀ hc2) hGc]
  · -- dense fibre: runs past `K q` are rare
    push Not at hsparse
    set P := (Ioc q (K * q)).filter Nat.Prime with hPdef
    have hedge := edge_bound T hTpos P (fun p hp => (mem_filter.1 hp).2) (fun _ => H)
      (fun _ _ => hHG.trans hGT) (by
        intro p hp m hm
        rw [mem_filter, mem_Ioc] at hp
        have hmS : m ∈ S := A_subset S _ (mem_filter.1 hm).1
        rw [mem_filter]
        refine ⟨mul_mem_of_mem_A (mem_filter.1 hm).1 hp.2.one_le hp.1.2, ?_⟩
        rw [key_prime_mul hp.2 hp.1.1.le (hS m hmS).ne', (mem_filter.1 hm).2])
    simp only [sum_const, nsmul_eq_mul] at hedge
    have hT1 := card_mul_log_le (filter_subset (fun m => key q m = c) S)
    have hq₀q : q₀ ≤ q := by
      have : (q₀ : ℝ) ≤ q := hQ₀q₀.trans hsmall
      exact_mod_cast this
    have hP := hgap q hq₀q
    have hlogn : 0 ≤ log (S.card : ℝ) := by
      rcases Nat.eq_zero_or_pos S.card with h | h
      · simp [h]
      · exact log_nonneg (by exact_mod_cast h)
    have hq34 : (0 : ℝ) < (q : ℝ) ^ ((3 : ℝ) / 4) := rpow_pos_of_pos hqpos _
    have hsq : √(q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 4) = (q : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [sqrt_eq_rpow, ← rpow_add hqpos]
      norm_num
    have hsqpos : 0 ≤ √(q : ℝ) := sqrt_nonneg _
    have hHc : (0 : ℝ) ≤ H.card := by positivity
    -- (log 2 / 2) q^(3/4) |H| ≤ √q |G| log n
    have key1 : log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * H.card) ≤
        G.card * √(q : ℝ) * log S.card := by
      calc log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * H.card)
          ≤ log 2 / 2 * ((P.card : ℝ) * H.card) := by gcongr
        _ ≤ T.card * log T.card := hedge
        _ ≤ T.card * log S.card := hT1
        _ ≤ G.card * √(q : ℝ) * log S.card := mul_le_mul_of_nonneg_right hsparse.le hlogn
    -- multiply by `log q` and use `log q log n ≤ q^(1/4)`
    have key2 : log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * (log q * H.card)) ≤
        G.card * (q : ℝ) ^ ((3 : ℝ) / 4) := by
      have h1 := mul_le_mul_of_nonneg_left key1 hlogq
      have h2 : G.card * √(q : ℝ) * (log q * log S.card) ≤
          G.card * √(q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (hQ₀ q hsmall) (by positivity)
      calc log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * (log q * H.card))
          = log q * (log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * H.card)) := by ring
        _ ≤ log q * (G.card * √(q : ℝ) * log S.card) := h1
        _ = G.card * √(q : ℝ) * (log q * log S.card) := by ring
        _ ≤ G.card * √(q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 4) := h2
        _ = G.card * (q : ℝ) ^ ((3 : ℝ) / 4) := by rw [mul_assoc, hsq]
    have key3 : log 2 / 2 * (log q * H.card) ≤ G.card := by
      have : (q : ℝ) ^ ((3 : ℝ) / 4) * (log 2 / 2 * (log q * H.card)) ≤
          (q : ℝ) ^ ((3 : ℝ) / 4) * G.card := by
        calc (q : ℝ) ^ ((3 : ℝ) / 4) * (log 2 / 2 * (log q * H.card))
            = log 2 / 2 * ((q : ℝ) ^ ((3 : ℝ) / 4) * (log q * H.card)) := by ring
          _ ≤ G.card * (q : ℝ) ^ ((3 : ℝ) / 4) := key2
          _ = (q : ℝ) ^ ((3 : ℝ) / 4) * G.card := by ring
      exact le_of_mul_le_mul_left this hq34
    have key4 : log q * (H.card : ℝ) ≤ 2 / log 2 * G.card := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith only [key3]
    nlinarith only [key4, hent, mul_nonneg hlogQ₀ hGc]

/-- Summing the fibre estimate over the fibres of the `q`-smooth part. -/
lemma prime_bound (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {K : ℕ} (hK : 1 ≤ K) {q₀ : ℕ}
    (hgap : ∀ q : ℕ, q₀ ≤ q →
      (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (((Ioc q (K * q)).filter Nat.Prime).card : ℝ))
    {Q₀ : ℝ} (hQ₀1 : 1 ≤ Q₀) (hQ₀q₀ : (q₀ : ℝ) ≤ Q₀)
    (hQ₀ : ∀ q : ℕ, Q₀ ≤ q → log q * log S.card ≤ (q : ℝ) ^ ((1 : ℝ) / 4))
    {q : ℕ} (hq : q.Prime) :
    log q * (A S (K * q)).card ≤ (log Q₀ + 2 / log 2) * (A S q).card + 4 * D S q := by
  have hfib : ∀ t : ℕ, ((A S t).card : ℝ) =
      ∑ c ∈ S.image (key q), (((A S t).filter (fun m => key q m = c)).card : ℝ) := by
    intro t
    rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := key q)]
    intro m hm
    exact mem_image_of_mem _ (A_subset S t hm)
  rw [hfib, hfib, D, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun c _ => fibre_bound S hS hK hgap hQ₀1 hQ₀q₀ hQ₀ hq c

/-- Double counting: `∑_q log q |A (K q)| = ∑_a θ(L a / K)`. -/
lemma double_count (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {K : ℕ} (hK : 0 < K) :
    ∑ q ∈ (range (S.sup id + 1)).filter Nat.Prime, log q * ((A S (K * q)).card : ℝ) =
      ∑ a ∈ S, ∑ p ∈ primesUpTo (L S a / K), log p := by
  have h1 : ∀ q : ℕ, log (q : ℝ) * ((A S (K * q)).card : ℝ) =
      ∑ a ∈ S, if a ∈ A S (K * q) then log (q : ℝ) else 0 := by
    intro q
    have hA : S.filter (fun a => a ∈ A S (K * q)) = A S (K * q) := by
      ext a
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨A_subset S _ h, h⟩⟩
    rw [← sum_filter, hA, sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_range, primesUpTo, mem_A_iff S hS]
  have hLn := L_le_card S hS ha
  have hnB := card_le_sup S hS
  constructor
  · rintro ⟨⟨_, hp⟩, -, hpL⟩
    exact ⟨by rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hK, mul_comm]; exact hpL, hp⟩
  · rintro ⟨hpL, hp⟩
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hK] at hpL
    refine ⟨⟨?_, hp⟩, ha, by rw [mul_comm]; exact hpL⟩
    have : p ≤ L S a := le_trans (Nat.le_mul_of_pos_right p hK) hpL
    omega

/-- The explicit form of the upper bound. -/
theorem upper_core (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {K q₀ : ℕ} {c₁ C₁ : ℝ}
    (hPI : PrimeInput K c₁ C₁ q₀) {Q₀ : ℝ} (hQ₀1 : 1 ≤ Q₀) (hQ₀q₀ : (q₀ : ℝ) ≤ Q₀)
    (hQ₀ : ∀ q : ℕ, Q₀ ≤ q → log q * log S.card ≤ (q : ℝ) ^ ((1 : ℝ) / 4)) :
    c₁ / K * ∑ a ∈ S, (L S a : ℝ) ≤
      (log Q₀ + 2 / log 2) * (2 / log 2) * (S.card * log S.card) +
        4 * (S.card * log S.card) + (c₁ + C₁) * S.card := by
  have hK : 1 ≤ K := hPI.K_pos
  set B := S.sup id + 1
  set PB := (range B).filter Nat.Prime
  have hSB : ∀ m ∈ S, m < B := fun m hm => Nat.lt_succ_of_le (le_sup (f := id) hm)
  have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  have hc : 0 ≤ log Q₀ + 2 / log 2 := by
    have := log_nonneg hQ₀1
    positivity
  -- ∑_q |A q| ≤ (2 / log 2) n log n
  have hedge := edge_bound S hS PB (fun p hp => (mem_filter.1 hp).2) (fun q => A S q)
    (fun q _ => A_subset S q)
    (fun q hq m hm => mul_mem_of_mem_A hm (mem_filter.1 hq).2.one_le le_rfl)
  have hsumA : ∑ q ∈ PB, ((A S q).card : ℝ) ≤ 2 / log 2 * (S.card * log S.card) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    linarith
  have hsumD : ∑ q ∈ PB, D S q ≤ S.card * log S.card :=
    sum_D_le S hS hSB PB (filter_subset _ _)
  -- the weighted sum
  have hPhi : ∑ q ∈ PB, log q * ((A S (K * q)).card : ℝ) ≤
      (log Q₀ + 2 / log 2) * (2 / log 2) * (S.card * log S.card) +
        4 * (S.card * log S.card) := by
    calc ∑ q ∈ PB, log q * ((A S (K * q)).card : ℝ)
        ≤ ∑ q ∈ PB, ((log Q₀ + 2 / log 2) * (A S q).card + 4 * D S q) :=
          sum_le_sum fun q hq => prime_bound S hS hK hPI.gap hQ₀1 hQ₀q₀ hQ₀ (mem_filter.1 hq).2
      _ = (log Q₀ + 2 / log 2) * ∑ q ∈ PB, ((A S q).card : ℝ) + 4 * ∑ q ∈ PB, D S q := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hsumA hc
          nlinarith
  rw [double_count S hS hPI.K_pos] at hPhi
  -- θ lower bound for each element
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hPI.K_pos
  have helt : ∀ a ∈ S, c₁ / K * (L S a : ℝ) - (c₁ + C₁) ≤
      ∑ p ∈ primesUpTo (L S a / K), log p := by
    intro a _
    have ht := hPI.theta (L S a / K)
    have hdiv : (L S a : ℝ) / K - 1 ≤ ((L S a / K : ℕ) : ℝ) := by
      have h := Nat.div_add_mod (L S a) K
      have hmod := Nat.mod_lt (L S a) hPI.K_pos
      have h' : (L S a : ℝ) = K * ((L S a / K : ℕ) : ℝ) + ((L S a % K : ℕ) : ℝ) := by
        exact_mod_cast h.symm
      have hmod' : ((L S a % K : ℕ) : ℝ) < K := by exact_mod_cast hmod
      rw [div_sub_one hKpos.ne', div_le_iff₀ hKpos]
      nlinarith
    have hc₁ := hPI.c₁_pos
    calc c₁ / K * (L S a : ℝ) - (c₁ + C₁) = c₁ * ((L S a : ℝ) / K - 1) - C₁ := by
          field_simp
          ring
      _ ≤ c₁ * ((L S a / K : ℕ) : ℝ) - C₁ := by gcongr
      _ ≤ _ := ht
  have hsum := sum_le_sum helt
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum] at hsum
  linarith

/-- The upper bound in asymptotic form, given the prime-number input. -/
theorem upper_of_primeInput {K q₀ : ℕ} {c₁ C₁ : ℝ} (hPI : PrimeInput K c₁ C₁ q₀) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
      ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤
        C * S.card * log S.card * log (log S.card) := by
  set M₀ : ℝ := max (q₀ : ℝ) ((2 : ℝ) ^ (64 : ℕ)) with hM₀
  -- eventually: (log n)^8 ≥ M₀ and log log n ≥ 1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, M₀ ≤ (log n) ^ (8 : ℕ) ∧ 1 ≤ log (log n) := by
    have hlog : Filter.Tendsto (fun n : ℕ => log (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h8 : Filter.Tendsto (fun n : ℕ => (log (n : ℝ)) ^ (8 : ℕ)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop (by norm_num)).comp hlog
    have hll : Filter.Tendsto (fun n : ℕ => log (log (n : ℝ))) Filter.atTop Filter.atTop :=
      tendsto_log_atTop.comp hlog
    exact (h8.eventually_ge_atTop M₀).and (hll.eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  have hc₁ := hPI.c₁_pos
  have hC₁ := hPI.C₁_nonneg
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hPI.K_pos
  refine ⟨1 + K / c₁ * ((8 + 2 / log 2) * (2 / log 2) + 4 + c₁ + C₁), N, fun S hS hSN => ?_⟩
  obtain ⟨hM, hLL⟩ := hN S.card hSN
  set n : ℝ := (S.card : ℝ) with hn
  set Lg := log n with hLg
  set LL := log Lg with hLL'
  have hLg0 : 0 ≤ Lg := by rw [hLg, hn]; exact log_natCast_nonneg _
  have hLg1 : 1 ≤ Lg := by
    by_contra h
    push Not at h
    have : log Lg ≤ 0 := log_nonpos hLg0 h.le
    linarith
  have hnpos : 1 ≤ n := by
    by_contra h
    push Not at h
    have : Lg ≤ 0 := log_nonpos (by positivity) h.le
    linarith
  -- choose Q₀ = (log n)^8
  set Q₀ : ℝ := Lg ^ (8 : ℕ) with hQ₀def
  have hQ₀1 : 1 ≤ Q₀ := one_le_pow₀ hLg1
  have hQ₀M : M₀ ≤ Q₀ := hM
  have hQ₀q₀ : (q₀ : ℝ) ≤ Q₀ := (le_max_left _ _).trans hQ₀M
  have hQ₀big : (2 : ℝ) ^ (64 : ℕ) ≤ Q₀ := (le_max_right _ _).trans hQ₀M
  have hQ₀ : ∀ q : ℕ, Q₀ ≤ q → log q * log S.card ≤ (q : ℝ) ^ ((1 : ℝ) / 4) := by
    intro q hq
    have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
    -- log q ≤ q^(1/8)
    have hlq : log (q : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 8) := by
      have h1 := log_le_rpow_div hqpos.le (show (0 : ℝ) < 1 / 16 by norm_num)
      have h2 : (16 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) := by
        have : (16 : ℝ) = ((2 : ℝ) ^ (64 : ℕ)) ^ ((1 : ℝ) / 16) := by
          rw [← rpow_natCast, ← rpow_mul (by norm_num)]
          norm_num
        calc (16 : ℝ) = ((2 : ℝ) ^ (64 : ℕ)) ^ ((1 : ℝ) / 16) := this
          _ ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
            rpow_le_rpow (by norm_num) (hQ₀big.trans hq) (by norm_num)
      have h3 : (q : ℝ) ^ ((1 : ℝ) / 8) = (q : ℝ) ^ ((1 : ℝ) / 16) * (q : ℝ) ^ ((1 : ℝ) / 16) := by
        rw [← rpow_add hqpos]
        norm_num
      have h4 : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / 16) := by positivity
      rw [h3]
      calc log (q : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) / (1 / 16) := h1
        _ = 16 * (q : ℝ) ^ ((1 : ℝ) / 16) := by ring
        _ ≤ _ := by nlinarith
    -- log n ≤ q^(1/8)
    have hln : log (S.card : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 8) := by
      have : Lg = (Lg ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := by
        rw [← rpow_natCast, ← rpow_mul (by linarith)]
        norm_num
      rw [← hn, ← hLg, this]
      exact rpow_le_rpow (by positivity) hq (by norm_num)
    have hlq0 : 0 ≤ log (q : ℝ) := by
      apply log_nonneg
      have : (1 : ℝ) ≤ Q₀ := hQ₀1
      linarith
    have hsplit : (q : ℝ) ^ ((1 : ℝ) / 4) =
        (q : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [← rpow_add hqpos]
      norm_num
    rw [hsplit]
    exact mul_le_mul hlq hln (by rw [← hn, ← hLg]; linarith) (by positivity)
  have hcore := upper_core S hS hPI hQ₀1 hQ₀q₀ hQ₀
  have hlogQ₀ : log Q₀ = 8 * LL := by
    rw [hQ₀def, log_pow, hLL']
    push_cast
    ring
  rw [hlogQ₀] at hcore
  -- ∑ kVal = n + ∑ L
  have hk := sum_kVal_eq S hS
  have hk' : ((∑ a ∈ S, kVal S a : ℕ) : ℝ) = n + ∑ a ∈ S, (L S a : ℝ) := by
    rw [hk]
    push_cast
    rfl
  rw [hk']
  have hsumL : ∑ a ∈ S, (L S a : ℝ) ≤ K / c₁ *
      ((8 * LL + 2 / log 2) * (2 / log 2) * (n * Lg) + 4 * (n * Lg) + (c₁ + C₁) * n) := by
    rw [← hn, ← hLg] at hcore
    calc ∑ a ∈ S, (L S a : ℝ) = K / c₁ * (c₁ / K * ∑ a ∈ S, (L S a : ℝ)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcore (by positivity)
  -- absorb everything into `n Lg LL`
  have hnLL : 0 ≤ n * Lg * LL := by positivity
  have hA : n ≤ n * Lg * LL := by
    have h := one_le_mul_of_one_le_of_one_le hLg1 hLL
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ n)
  have hB : (8 * LL + 2 / log 2) * (2 / log 2) * (n * Lg) ≤
      (8 + 2 / log 2) * (2 / log 2) * (n * Lg * LL) := by
    have h22 : 0 ≤ 2 / log (2 : ℝ) := by positivity
    have : (8 * LL + 2 / log 2) ≤ (8 + 2 / log 2) * LL := by
      nlinarith only [mul_le_mul_of_nonneg_left hLL h22]
    have hnL : 0 ≤ n * Lg := by positivity
    calc (8 * LL + 2 / log 2) * (2 / log 2) * (n * Lg)
        ≤ (8 + 2 / log 2) * LL * (2 / log 2) * (n * Lg) := by gcongr
      _ = _ := by ring
  have hC : 4 * (n * Lg) ≤ 4 * (n * Lg * LL) := by
    have h := mul_le_mul_of_nonneg_left hLL (show 0 ≤ 4 * (n * Lg) by positivity)
    simpa only [mul_one, mul_assoc] using h
  have hD : (c₁ + C₁) * n ≤ (c₁ + C₁) * (n * Lg * LL) := by
    apply mul_le_mul_of_nonneg_left hA
    linarith
  have hKc : 0 ≤ K / c₁ := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hB hC) hD) hKc
  calc n + ∑ a ∈ S, (L S a : ℝ)
      ≤ n * Lg * LL + K / c₁ * ((8 + 2 / log 2) * (2 / log 2) * (n * Lg * LL) +
          4 * (n * Lg * LL) + (c₁ + C₁) * (n * Lg * LL)) := by linarith
    _ = (1 + K / c₁ * ((8 + 2 / log 2) * (2 / log 2) + 4 + c₁ + C₁)) * n * Lg * LL := by ring

end RunsOfMultiples
