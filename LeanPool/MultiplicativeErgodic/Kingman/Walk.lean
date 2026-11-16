/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman.ZeroOne

/-!
# Steele's greedy walk

The combinatorial core: a greedy decomposition of `[0, n)` into blocks on which `f` decreases
fast, the count of positions left uncovered, and the transition argument that converts a
threshold statement about `liminf` into convergence.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-!
### The greedy walk

Steele's decomposition of `[0, n)`: at position `k`, take a good block of length `≤ N` if one
exists at `σᵏx`, else a singleton. `blockLen` is that choice and `walk` iterates it.
-/

open Classical in
/-- The greedy block length at position `k`: some good `l ≤ N` if one exists, else `1`.
Any good `l` will do, so this uses choice rather than `Nat.find` — no minimality is needed. -/
noncomputable def blockLen (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (k : ℕ) : ℕ :=
  if h : ∃ l, 1 ≤ l ∧ l ≤ N ∧ f l (σ^[k] x) ≤ c * l then h.choose else 1

omit [MeasurableSpace Ω] in
theorem blockLen_pos (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (k : ℕ) :
    1 ≤ blockLen σ f N c x k := by
  unfold blockLen
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_refl 1

omit [MeasurableSpace Ω] in
/-- At a *good* position the block achieves the threshold: `f_{blockLen} ≤ c · blockLen`, and
the block has length `≤ N`. -/
theorem blockLen_spec (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (k : ℕ)
    (hk : σ^[k] x ∉ SubadditiveFamily.badSet f N c) :
    blockLen σ f N c x k ≤ N ∧
      f (blockLen σ f N c x k) (σ^[k] x) ≤ c * (blockLen σ f N c x k) := by
  have hex : ∃ l, 1 ≤ l ∧ l ≤ N ∧ f l (σ^[k] x) ≤ c * l := by
    simp only [SubadditiveFamily.badSet, Set.mem_ofPred_eq, not_forall, not_lt] at hk
    obtain ⟨l, hl⟩ := hk
    exact ⟨l, by tauto⟩
  unfold blockLen
  rw [dite_eq_left hex]
  exact ⟨hex.choose_spec.2.1, hex.choose_spec.2.2⟩

/-- Positions visited by the greedy walk. -/
noncomputable def walk (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) : ℕ → ℕ
  | 0 => 0
  | i + 1 => walk σ f N c x i + blockLen σ f N c x (walk σ f N c x i)

omit [MeasurableSpace Ω] in
/-- The walk advances by at least one each step, so `i ≤ walk i`. -/
theorem le_walk (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) :
    ∀ i, i ≤ walk σ f N c x i := by
  intro i
  induction i with
  | zero => simp [walk]
  | succ i ih =>
    have := blockLen_pos σ f N c x (walk σ f N c x i)
    change i + 1 ≤ walk σ f N c x i + blockLen σ f N c x (walk σ f N c x i)
    omega

/-- **Chaining subadditivity along the greedy walk**: the variable-length analogue of
`le_sum_blocks`. -/
theorem le_sum_walk {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (N : ℕ) (c : ℝ) (x : Ω) :
    ∀ i, 1 ≤ i → f (walk σ f N c x i) x
      ≤ ∑ j ∈ Finset.range i, f (blockLen σ f N c x (walk σ f N c x j))
          (σ^[walk σ f N c x j] x) := by
  intro i
  induction i with
  | zero => omega
  | succ i ih =>
    intro _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [walk]
    · have hstep := hf.2 (blockLen σ f N c x (walk σ f N c x i)) (walk σ f N c x i) x
      have hrec := ih hi
      rw [Finset.sum_range_succ]
      change f (walk σ f N c x i + blockLen σ f N c x (walk σ f N c x i)) x ≤ _
      rw [add_comm (walk σ f N c x i)] at *
      linarith

open Classical in
/-- The number of bad times among the first `n` positions of the orbit of `x`. -/
noncomputable def badCount (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, if σ^[k] x ∈ SubadditiveFamily.badSet f N c then 1 else 0

open Classical in
omit [MeasurableSpace Ω] in
theorem badCount_succ (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (n : ℕ) :
    badCount σ f N c x (n + 1)
      = (if x ∈ SubadditiveFamily.badSet f N c then 1 else 0) + badCount σ f N c (σ x) n := by
  unfold badCount
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_zero, id_eq]
  rw [add_comm]
  congr 1

open Classical in
omit [MeasurableSpace Ω] in
theorem badCount_shift_le (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω) (l n : ℕ)
    (hl : l ≤ n) : badCount σ f N c (σ^[l] x) (n - l) ≤ badCount σ f N c x n := by
  unfold badCount
  have hshift : ∀ k, (if σ^[k] (σ^[l] x) ∈ SubadditiveFamily.badSet f N c then 1 else 0)
      = (if σ^[k + l] x ∈ SubadditiveFamily.badSet f N c then 1 else 0) := by
    intro k; rw [← Function.iterate_add_apply]
  simp only [hshift]
  conv_rhs => rw [show n = l + (n - l) by omega]
  rw [Finset.sum_range_add]
  refine le_trans (le_of_eq ?_) (Nat.le_add_left _ _)
  exact Finset.sum_congr rfl (fun k _ => by rw [add_comm k l])

open Classical in
omit [MeasurableSpace Ω] in
/-- `badCount` is the Birkhoff sum of the indicator of the bad set.

Stated at top level under `open Classical in` deliberately: `badCount`'s `if` uses the classical
decidability instance, and inside a proof that is *not* in that scope the `show` needed to unfold
it silently fails to match — Lean then recovers with `sorry` rather than reporting an error, and
the surrounding tactics become dead code. Keeping the unfolding in one lemma, elaborated in the
same instance scope as the definition, avoids that trap entirely. -/
theorem badCount_cast_eq_birkhoffSum (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) (x : Ω)
    (n : ℕ) :
    ((badCount σ f N c x n : ℕ) : ℝ)
      = birkhoffSum σ (Set.indicator (SubadditiveFamily.badSet f N c) 1) n x := by
  unfold badCount
  change ((∑ k ∈ Finset.range n,
      (if σ^[k] x ∈ SubadditiveFamily.badSet f N c then 1 else 0) : ℕ) : ℝ)
    = ∑ k ∈ Finset.range n, Set.indicator (SubadditiveFamily.badSet f N c) 1 (σ^[k] x)
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : σ^[k] x ∈ SubadditiveFamily.badSet f N c <;> simp [h]

/-- **Steele's greedy estimate.**

Assume the family is non-positive from index `1` (Steele's reduction) and the threshold `c ≤ 0`.
Then for every `n ≥ 1` there is a "good total" `G` with

* `n ≤ G + badCount(x,n) + N` — the good blocks cover everything but the bad singletons and the
  last `< N` positions; and
* `f n x ≤ c · G`.

Proved by strong induction on `n`, *without* reference to the greedy walk: at position `0`,
either `x` is good — take a block of length `l ≤ N`, recurse on `n - l` (or, if `l > n`, take
`G = 0`, which is fine because `n < l ≤ N`) — or `x` is bad, in which case drop the singleton
using `f 1 x ≤ 0` and recurse on `n - 1`, the lost position being paid for by the `+1` in
`badCount_succ`. -/
theorem SubadditiveFamily.exists_goodTotal {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N : ℕ) (hN : 1 ≤ N) (c : ℝ)
    (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0) (x : Ω) :
    ∀ n, 1 ≤ n → ∃ G : ℕ, G ≤ n ∧ n ≤ G + badCount σ f N c x n + N ∧ f n x ≤ c * G := by
  intro n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hn
    by_cases hbad : x ∈ SubadditiveFamily.badSet f N c
    · -- bad position: drop the singleton `f 1 x ≤ 0`
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        refine ⟨0, by omega, ?_, ?_⟩
        · have : badCount σ f N c x 1 = 1 := by
            rw [show (1 : ℕ) = 0 + 1 from rfl, badCount_succ, ite_eq_left hbad]
            simp [badCount]
          omega
        · simpa using hneg 1 le_rfl x
      · obtain ⟨G', hG'le, hG'count, hG'val⟩ := ih (n - 1) (by omega) (σ x) (by omega)
        refine ⟨G', by omega, ?_, ?_⟩
        · have hpeel : badCount σ f N c x n
              = 1 + badCount σ f N c (σ x) (n - 1) := by
            rw [show n = (n - 1) + 1 by omega, badCount_succ, ite_eq_left hbad]
            simp
          omega
        · have hsplit := hf.2 (n - 1) 1 x
          rw [show n - 1 + 1 = n by omega, Function.iterate_one] at hsplit
          have h1 := hneg 1 le_rfl x
          linarith
    · -- good position: take a block of length `l ≤ N`
      obtain ⟨hlN, hlval⟩ := blockLen_spec σ f N c x 0 (by simpa using hbad)
      set l : ℕ := blockLen σ f N c x 0 with hldef
      have hl1 : 1 ≤ l := blockLen_pos σ f N c x 0
      have hlval0 : f l x ≤ c * l := by simpa using hlval
      rcases Nat.lt_or_ge n l with hnl | hnl
      · -- the block overshoots: `n < l ≤ N`
        exact ⟨0, by omega, by omega, by simpa using hneg n hn x⟩
      · rcases Nat.eq_or_lt_of_le hnl with hEq | hlt
        · -- `n = l` exactly
          refine ⟨l, by omega, by omega, ?_⟩
          rw [← hEq]
          exact hlval0
        · obtain ⟨G', hG'le, hG'count, hG'val⟩ := ih (n - l) (by omega) (σ^[l] x) (by omega)
          refine ⟨G' + l, by omega, ?_, ?_⟩
          · have := badCount_shift_le σ f N c x l n (le_of_lt hlt)
            omega
          · have hsplit := hf.2 (n - l) l x
            rw [show n - l + l = n by omega] at hsplit
            have : c * (G' + l : ℕ) = c * G' + c * l := by push_cast; ring
            rw [this]
            linarith

/-- **Steele's estimate, divided by `n`.** The threshold is `d + ε` with `d ≤ 0` and `ε ≥ 0`:
this is the shape Steele actually uses (`d = G_M`, the truncated a.e.-constant `liminf`), and the
sum is split as

`(d + ε)·G = d·G + ε·G ≤ d·G + ε·n`

using `G ≤ n`, *before* the non-positive `d` reverses the good-total bound. Assuming `d + ε ≤ 0`
instead would be wrong: `d + ε` is positive whenever `d = 0`. -/
theorem SubadditiveFamily.div_le_of_goodTotal {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N : ℕ) (hN : 1 ≤ N) (d ε : ℝ) (hd : d ≤ 0) (hε : 0 ≤ ε)
    (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0) (x : Ω) (n : ℕ) (hn : 1 ≤ n) :
    f n x / n
      ≤ d * (1 - (badCount σ f N (d + ε) x n : ℝ) / n - (N : ℝ) / n) + ε := by
  obtain ⟨G, hGle, hGcount, hGval⟩ := hf.exists_goodTotal N hN (d + ε) hneg x n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hGn : (G : ℝ) ≤ (n : ℝ) := by exact_mod_cast hGle
  have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
  -- split the threshold
  have hsplit : (d + ε) * (G : ℝ) ≤ d * (G : ℝ) + ε * n := by nlinarith
  -- `d ≤ 0` reverses the good-total bound
  have hGreal : (n : ℝ) - (badCount σ f N (d + ε) x n : ℝ) - (N : ℝ) ≤ (G : ℝ) := by
    have : (n : ℝ) ≤ (G : ℝ) + (badCount σ f N (d + ε) x n : ℝ) + (N : ℝ) := by
      exact_mod_cast hGcount
    linarith
  have hmul : d * (G : ℝ) ≤ d * ((n : ℝ) - (badCount σ f N (d + ε) x n : ℝ) - (N : ℝ)) :=
    mul_le_mul_of_nonpos_left hGreal hd
  rw [div_le_iff₀ hn0]
  have hexpand : (d * (1 - (badCount σ f N (d + ε) x n : ℝ) / n - (N : ℝ) / n) + ε) * (n : ℝ)
      = d * ((n : ℝ) - (badCount σ f N (d + ε) x n : ℝ) - (N : ℝ)) + ε * n := by
    field_simp
  rw [hexpand]
  linarith

/-- **The Steele bound, in the limit.** Letting `n → ∞` in `div_le_of_goodTotal`: the bad density
tends to `μ(bad_{N,d+ε})` and `N/n → 0`. -/
theorem SubadditiveFamily.eventually_div_lt_of_badDensity (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (N : ℕ) (hN : 1 ≤ N) (d ε : ℝ) (hd : d ≤ 0) (hε : 0 ≤ ε)
    (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0) :
    ∀ᵐ x ∂μ, ∀ b : ℝ,
      d * (1 - μ.real (SubadditiveFamily.badSet f N (d + ε))) + ε < b →
        ∀ᶠ n in atTop, f n x / n < b := by
  filter_upwards [hf.ae_tendsto_badSet_density μ σ hσ f N (d + ε)] with x hdens
  intro b hb
  have hbc : ∀ n : ℕ, 1 ≤ n →
      (badCount σ f N (d + ε) x n : ℝ) / n
        = birkhoffAverage ℝ σ
            (Set.indicator (SubadditiveFamily.badSet f N (d + ε)) 1) n x := by
    intro n _
    rw [birkhoffAverage_real, badCount_cast_eq_birkhoffSum]
  have hlim : Tendsto (fun n : ℕ =>
      d * (1 - birkhoffAverage ℝ σ
              (Set.indicator (SubadditiveFamily.badSet f N (d + ε)) 1) n x
            - (N : ℝ) / n) + ε) atTop
      (nhds (d * (1 - μ.real (SubadditiveFamily.badSet f N (d + ε))) + ε)) := by
    have hN0 : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h1 := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hdens).sub hN0
    have h2 := (h1.const_mul d).add (tendsto_const_nhds (x := ε))
    simpa using h2
  filter_upwards [(tendsto_order.mp hlim).2 b hb, eventually_ge_atTop 1] with n hlt hn
  refine lt_of_le_of_lt ?_ hlt
  rw [← hbc n hn]
  exact hf.div_le_of_goodTotal N hN d ε hd hε hneg x n hn

omit [MeasurableSpace Ω] in
/-- The bad sets shrink as the scale `N` grows: a longer window is a stronger requirement. -/
theorem SubadditiveFamily.badSet_antitone (f : ℕ → Ω → ℝ) (c : ℝ) :
    Antitone (fun N => SubadditiveFamily.badSet f N c) := by
  intro M N hMN x hx l h1 hl
  exact hx l h1 (le_trans hl hMN)

/-- **The bad sets are eventually negligible.** If a.e. `x` has *some* block achieving the
threshold, then `μ(bad_{N,c}) → 0` as `N → ∞`.

This is the limiting step of Steele's outer argument: with `c` strictly above the a.e.-constant
`liminf f_l/l`, a.e. `x` admits such a block, so the good blocks eventually cover all but a
vanishing fraction. -/
theorem SubadditiveFamily.tendsto_measure_badSet (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω → Ω) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f) (c : ℝ)
    (hc : ∀ᵐ x ∂μ, ∃ l, 1 ≤ l ∧ f l x ≤ c * l) :
    Tendsto (fun N => μ (SubadditiveFamily.badSet f N c)) atTop (nhds 0) := by
  have hinter : μ (⋂ N, SubadditiveFamily.badSet f N c) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.mp hc)
    simp only [Set.mem_iInter] at hx
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le]
    intro l hl
    exact hx l l hl le_rfl
  have := tendsto_measure_iInter_atTop (μ := μ)
    (fun N => (hf.measurableSet_badSet N c).nullMeasurableSet)
    (SubadditiveFamily.badSet_antitone f c) ⟨0, measure_ne_top μ _⟩
  rwa [hinter] at this

/-- **Steele's bound with the bad set eliminated.** If a.e. `x` has some block achieving the
threshold `d + ε`, then `μ(bad_{N,d+ε}) → 0` as `N → ∞`, so the `N`-dependent bound
`d·(1 - μ(bad)) + ε` can be pushed down to `d + ε`:

for a.e. `x` and every `b > d + ε`, eventually `f n x / n < b`.

This is Steele's limiting bound after letting `N → ∞`. -/
theorem SubadditiveFamily.eventually_div_lt_of_threshold (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (d ε : ℝ) (hd : d ≤ 0) (hε : 0 ≤ ε)
    (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0)
    (hgood : ∀ᵐ x ∂μ, ∃ l, 1 ≤ l ∧ f l x ≤ (d + ε) * l) :
    ∀ᵐ x ∂μ, ∀ b : ℝ, d + ε < b → ∀ᶠ n in atTop, f n x / n < b := by
  -- Choose `N` making `d·μ(bad_{N,d+ε})` small enough that the `N`-bound drops below `b`.
  have hbad := SubadditiveFamily.tendsto_measure_badSet μ σ f hf (d + ε) hgood
  -- The bound as a function of `N`, at the real-valued level.
  have hbadR : Tendsto (fun N => μ.real (SubadditiveFamily.badSet f N (d + ε))) atTop
      (nhds 0) := by
    simp only [measureReal_def]
    have : Tendsto (fun N => (μ (SubadditiveFamily.badSet f N (d + ε))).toReal) atTop
        (nhds ((0 : ENNReal).toReal)) := (ENNReal.tendsto_toReal (by simp)).comp hbad
    simpa using this
  -- For each `N ≥ 1` we have the Steele bound; combine over a countable set of `N`.
  have hall : ∀ᵐ x ∂μ, ∀ N : ℕ, 1 ≤ N → ∀ b : ℝ,
      d * (1 - μ.real (SubadditiveFamily.badSet f N (d + ε))) + ε < b →
        ∀ᶠ n in atTop, f n x / n < b := by
    refine ae_all_iff.mpr (fun N => ?_)
    by_cases hN : 1 ≤ N
    · filter_upwards [hf.eventually_div_lt_of_badDensity μ σ hσ f N hN d ε hd hε hneg] with x hx
      intro _ b hb
      exact hx b hb
    · filter_upwards with x h; omega
  filter_upwards [hall] with x hx
  intro b hb
  -- pick `N` with the `N`-bound below `b`
  set r : ℝ := b - (d + ε) with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hsmall : ∀ᶠ N in atTop, |d| * μ.real (SubadditiveFamily.badSet f N (d + ε)) < r := by
    have := hbadR.const_mul |d|
    rw [mul_zero] at this
    exact (tendsto_order.mp this).2 r hr0
  obtain ⟨N, hNsmall, hN1⟩ := (hsmall.and (eventually_ge_atTop 1)).exists
  refine hx N hN1 b ?_
  have hm0 : 0 ≤ μ.real (SubadditiveFamily.badSet f N (d + ε)) := measureReal_nonneg
  set m : ℝ := μ.real (SubadditiveFamily.badSet f N (d + ε)) with hmdef
  -- `d·(1 - m) + ε = (d + ε) - d·m`, and `|d·m| ≤ |d|·m < r = b - (d + ε)`
  have hdm : d * m ≤ |d| * m := by nlinarith [le_abs_self d, hm0]
  have hdmneg : -(|d| * m) ≤ d * m := by nlinarith [neg_abs_le d, hm0]
  have hkey : d * (1 - m) + ε = (d + ε) - d * m := by ring
  rw [hkey, hr] at *
  linarith [hNsmall, hdm, hdmneg]

/-- **The zero-one transition.** Given the zero-one law for the threshold sets, together with
*one* conull threshold `L₀` and *one* null threshold `U₀`, there is a real `γ` with every
threshold above it null and every threshold below it conull.

`γ := sInf {q | μ(liminfGE a q) = 0}`. The set is non-empty (`U₀`) and bounded below by `L₀`:
below `L₀` the sets contain `liminfGE a L₀`, which is conull, so they cannot be null. Without the
lower bound this infimum would be `-∞`, which is exactly the degenerate case `bkingman`'s linear
lower bound rules out. -/
theorem exists_transition {μ : Measure Ω} {a : ℕ → Ω → ℝ}
    (hzo : ∀ q : ℝ, μ (liminfGE a q) = 0 ∨ μ (liminfGE a q) = 1)
    {L₀ U₀ : ℝ} (hlow : μ (liminfGE a L₀) = 1) (hhigh : μ (liminfGE a U₀) = 0) :
    ∃ γ : ℝ, (∀ c : ℝ, γ < c → μ (liminfGE a c) = 0) ∧
      (∀ c : ℝ, c < γ → μ (liminfGE a c) = 1) := by
  set S : Set ℝ := {q : ℝ | μ (liminfGE a q) = 0} with hS
  have hne : S.Nonempty := ⟨U₀, hhigh⟩
  have hbdd : BddBelow S := by
    refine ⟨L₀, fun q hq => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    -- `q < L₀` forces `liminfGE a L₀ ⊆ liminfGE a q`, so `μ (liminfGE a q) = 1 ≠ 0`
    have hsub : liminfGE a L₀ ⊆ liminfGE a q := liminfGE_antitone a hlt.le
    have : (1 : ℝ≥0∞) ≤ μ (liminfGE a q) := by
      rw [← hlow]; exact measure_mono hsub
    rw [hS, Set.mem_ofPred_eq] at hq
    rw [hq] at this
    simp at this
  refine ⟨sInf S, fun c hc => ?_, fun c hc => ?_⟩
  · -- above the infimum: some null threshold sits below `c`
    obtain ⟨q, hqS, hqc⟩ := exists_lt_of_csInf_lt hne hc
    refine measure_mono_null (liminfGE_antitone a hqc.le) hqS
  · -- below the infimum: `c ∉ S`, so by the zero-one law its threshold set is conull
    rcases hzo c with h | h
    · exact absurd (csInf_le hbdd h) (not_le.mpr hc)
    · exact h

/-- **From the zero-one law to the Steele bound.** If the threshold set `{liminf fₙ/n ≥ c}` is
null, then a.e. `x` has some block achieving `c`, and hence `limsup fₙ/n ≤ c`.

The link is that a point failing to have *any* good block — `∀ l ≥ 1, c·l < f_l x` — satisfies
`f_l/l > c` for every `l`, so its `liminf` is `≥ c`; that is, the "no good block" set is
contained in the threshold set. Taking `ε = 0` in `eventually_div_lt_of_threshold` then applies. -/
theorem SubadditiveFamily.eventually_div_lt_of_liminfGE_null (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0) (c : ℝ)
    (h0 : μ (liminfGE (fun n ω => f n ω / n) c) = 0) :
    ∀ᵐ x ∂μ, ∀ b : ℝ, c < b → ∀ᶠ n in atTop, f n x / n < b := by
  -- split `c = d + ε` with `d ≤ 0 ≤ ε`; no sign restriction on `c` is needed
  set d : ℝ := min c 0 with hddef
  set e : ℝ := c - d with hedef
  have hd : d ≤ 0 := min_le_right _ _
  have he : 0 ≤ e := by rw [hedef]; linarith [min_le_left c 0]
  have hde : d + e = c := by rw [hedef]; ring
  have hgood : ∀ᵐ x ∂μ, ∃ l, 1 ≤ l ∧ f l x ≤ (d + e) * l := by
    rw [hde]
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) h0
    -- `x` has no good block, so `f l x / l > c` for every `l ≥ 1`, hence `liminf ≥ c`
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hx
    simp only [liminfGE, Set.mem_ofPred_eq]
    intro ε hε
    refine ⟨1, fun n hn => ?_⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have := hx n hn
    have hε0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    rw [lt_div_iff₀ hn0]
    nlinarith [this]
  have := hf.eventually_div_lt_of_threshold μ σ hσ f d e hd he hneg hgood
  filter_upwards [this] with x hx
  intro b hb
  exact hx b (by rw [hde]; exact hb)

/-- The complementary direction: if the threshold set is conull, the averages are eventually
above `c - ε` for every `ε > 0`, i.e. `liminf fₙ/n ≥ c` a.e. This is just unfolding `liminfGE`. -/
theorem SubadditiveFamily.eventually_lt_div_of_liminfGE_full (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (hfm : ∀ n, Measurable (f n)) (c : ℝ)
    (h1 : μ (liminfGE (fun n ω => f n ω / n) c) = 1) :
    ∀ᵐ x ∂μ, ∀ b : ℝ, b < c → ∀ᶠ n in atTop, b < f n x / n := by
  have hmeas : MeasurableSet (liminfGE (fun n ω => f n ω / n) c) :=
    measurableSet_liminfGE (fun n => (hfm n).div_const _) c
  have hmem : ∀ᵐ x ∂μ, x ∈ liminfGE (fun n ω => f n ω / n) c := by
    rw [ae_iff]
    have : μ (liminfGE (fun n ω => f n ω / n) c)ᶜ = 0 := by
      rw [measure_compl hmeas (measure_ne_top μ _), h1, measure_univ, tsub_self]
    exact this
  filter_upwards [hmem] with x hx
  intro b hb
  obtain ⟨ε, hε0, hεlt⟩ : ∃ e : ℚ, 0 < e ∧ b < c - (e : ℝ) := by
    obtain ⟨e, he1, he2⟩ := exists_rat_btwn (show (0:ℝ) < c - b by linarith)
    exact ⟨e, by exact_mod_cast he1, by linarith⟩
  obtain ⟨N, hN⟩ := hx ε (by exact_mod_cast hε0)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact lt_of_lt_of_le hεlt (le_of_lt (hN n hn))

/-- **Steele's theorem for a non-positive family.** If `γ` sits at the transition of the
zero-one law — every threshold above `γ` null, every threshold below it conull — then the
averages converge to `γ` a.e.

`eventually_div_lt_of_liminfGE_null` gives `limsup ≤ γ` and
`eventually_lt_div_of_liminfGE_full` gives `liminf ≥ γ`. -/
theorem SubadditiveFamily.ae_tendsto_of_transition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (hneg : ∀ m, 1 ≤ m → ∀ y, f m y ≤ 0) (γ : ℝ)
    (habove : ∀ c : ℝ, γ < c → μ (liminfGE (fun n ω => f n ω / n) c) = 0)
    (hbelow : ∀ c : ℝ, c < γ → μ (liminfGE (fun n ω => f n ω / n) c) = 1) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / n) atTop (nhds γ) := by
  -- Quantify over the *rationals* on each side: `ae_all_iff` needs a countable index.
  have hupQ : ∀ᵐ x ∂μ, ∀ q : ℚ, γ < (q : ℝ) →
      ∀ᶠ n in atTop, f n x / n < (q : ℝ) := by
    refine ae_all_iff.mpr (fun q => ?_)
    by_cases hq : γ < (q : ℝ)
    · obtain ⟨c, hc1, hc2⟩ := exists_between hq
      filter_upwards [hf.eventually_div_lt_of_liminfGE_null μ σ hσ f hneg c
        (habove c hc1)] with x hx _
      exact hx (q : ℝ) hc2
    · filter_upwards with x h; exact absurd h hq
  have hlowQ : ∀ᵐ x ∂μ, ∀ q : ℚ, (q : ℝ) < γ →
      ∀ᶠ n in atTop, (q : ℝ) < f n x / n := by
    refine ae_all_iff.mpr (fun q => ?_)
    by_cases hq : (q : ℝ) < γ
    · obtain ⟨c, hc1, hc2⟩ := exists_between hq
      filter_upwards [SubadditiveFamily.eventually_lt_div_of_liminfGE_full μ f hf.1 c
        (hbelow c hc2)] with x hx _
      exact hx (q : ℝ) hc1
    · filter_upwards with x h; exact absurd h hq
  filter_upwards [hupQ, hlowQ] with x hu hl
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨qu, hqu1, hqu2⟩ := exists_rat_btwn (show γ < γ + δ by linarith)
  obtain ⟨ql, hql1, hql2⟩ := exists_rat_btwn (show γ - δ < γ by linarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hu qu hqu1)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hl ql hql2)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end MultiplicativeErgodic
