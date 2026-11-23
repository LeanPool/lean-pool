/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymptoticDefs
import Mathlib.Tactic.Positivity.Finset

/-!
# Comparison of infinite expansions

Source: Kovač and Tang, §4 of *Eventually greedy best Egyptian
underapproximations of rational numbers via optimal control*.
The prefix-versus-tail argument below adapts
`Erdos315.infinitely_often_ge_of_sum_le_sum_eq` of Aristotle and Boris Alexeev
in plby/lean-proofs (commit 236ba31f0d88d469e55e3798fce9744546e83bca),
file src/latest/ErdosProblems/Erdos315.lean. This argument
has been reworked for this project's definitions and eventual prefix bounds. The comparison uses the
extended real liminf so divergence to positive infinity is covered.
-/

@[expose] public section

namespace Egyptian

open Filter
open scoped Topology BigOperators

/-- The sum of reciprocals over the first n places, coerced into the reals. -/
theorem real_prefix_sum (a : ℕ → ℕ) (n : ℕ) :
    (recipSum (prefixTuple a n) : ℝ) = ∑ i ∈ Finset.range n, 1 / (a i : ℝ) := by
  induction n with
  | zero => simp [recipSum, prefixTuple]
  | succ n ih =>
    simpa [prefixTuple, recipSum, List.range_succ, unit, Finset.sum_range_succ]
      using congrArg (fun x : ℝ => x + 1 / (a n : ℝ)) ih

/-- A finite prefix of an expansion is a strict underapproximation, even
when denominators repeat. -/
theorem admissible_prefix {q : ℚ} {a : ℕ → ℕ} (h : Expansion q a) (n : ℕ) :
    Admissible .weak q n (prefixTuple a n) := by
  obtain ⟨ha, hmono, hs⟩ := h
  refine ⟨by simp [prefixTuple], ?_, ?_, ?_⟩
  · simp only [prefixTuple, List.mem_map, List.mem_range, forall_exists_index, and_imp]
    rintro d i _ rfl
    exact ha i
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp (fun hij => hmono hij.le))
  · have hpos (i : ℕ) : 0 < (1 / (a i : ℝ)) := by
      have := ha i
      positivity
    have hle := hs.summable.sum_le_tsum (Finset.range (n+1))
      (fun (i : ℕ) _ => (hpos i).le)
    rw [Finset.sum_range_succ, hs.tsum_eq] at hle
    have hlt : (recipSum (prefixTuple a n) : ℝ) < (q : ℝ) := by
      rw [real_prefix_sum]
      linarith [hpos n]
    exact_mod_cast hlt

/-- Removing a finite prefix leaves a positive rational with the required
nondecreasing expansion. In particular the Bellman theorem may be applied
to this exact residual when proving the truncation inequality. -/
theorem expansion_tail {q : ℚ} {a : ℕ → ℕ} (h : Expansion q a) (k : ℕ) :
    0 < q - recipSum (prefixTuple a k) ∧
    Expansion (q - recipSum (prefixTuple a k)) (fun j => a (k + j)) := by
  have hpos := (admissible_prefix h k).2.2.2
  refine ⟨sub_pos.2 hpos, fun j => h.1 _, fun _ _ hij => h.2.1 (by omega), ?_⟩
  have hs := (hasSum_nat_add_iff' (f := fun i => 1 / (a i : ℝ)) k).2 h.2.2
  rw [Rat.cast_sub, real_prefix_sum]
  simpa only [Nat.add_comm] using hs

/-- In the weak convention, two eventually optimal prefixes have equal sums;
taking first differences yields equality of the denominators at every later
place. This also proves independence of the choice of benchmark. -/
theorem benchmarks_eventually_equal {q : ℚ} {b c : ℕ → ℕ}
    (hb : Benchmark q b) (hc : Benchmark q c) :
    ∃ K, ∀ n, K ≤ n → b n = c n := by
  obtain ⟨_, N, _, _, _, _, _, hN⟩ := hb
  obtain ⟨_, M, _, _, _, _, _, hM⟩ := hc
  have heq (n : ℕ) (hn : max N M ≤ n) :
      (∑ i ∈ Finset.range n, 1 / (b i : ℝ)) = ∑ i ∈ Finset.range n, 1 / (c i : ℝ) := by
    have h₁ := hN n ((le_max_left _ _).trans hn)
    have h₂ := hM n ((le_max_right _ _).trans hn)
    have h := le_antisymm (h₂.2 _ h₁.1) (h₁.2 _ h₂.1)
    rw [← real_prefix_sum, ← real_prefix_sum]
    exact_mod_cast h
  refine ⟨max N M, fun n hn => ?_⟩
  have h := heq (n+1) (by omega)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, heq n hn] at h
  simpa using add_left_cancel h

/-- Equal total sums and eventual dominance of the prefix sums force
infinitely many reversed comparisons of the individual summands. -/
theorem frequently_term_ge_of_prefix_le {u v : ℕ → ℝ} {s : ℝ}
    (hu : HasSum u s) (hv : HasSum v s)
    (hprefix : ∀ᶠ n in atTop, ∑ i ∈ Finset.range n, v i ≤ ∑ i ∈ Finset.range n, u i) :
    ∃ᶠ n in atTop, u n ≤ v n := by
  by_contra h
  have hev : ∀ᶠ n in atTop, v n < u n := by simpa using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hprefix.and hev)
  have htail : (∑' j : ℕ, v (j+N)) < ∑' j : ℕ, u (j+N) := by
    apply Summable.tsum_lt_tsum (i := 0)
    · exact fun j => (hN (j+N) (by omega)).2.le
    · exact (hN (0+N) (by omega)).2
    · exact hv.summable.comp_injective (add_left_injective N)
    · exact hu.summable.comp_injective (add_left_injective N)
  have hlt := add_lt_add_of_le_of_lt (hN N le_rfl).1 htail
  rw [hv.summable.sum_add_tsum_nat_add, hu.summable.sum_add_tsum_nat_add,
    hv.tsum_eq, hu.tsum_eq] at hlt
  exact (lt_irrefl _ hlt)

/-- A convergent comparison sequence that dominates the competitor at
infinitely many places gives an upper bound on its extended-real liminf. -/
theorem lowerGrowth_le_of_frequently_le {a b : ℕ → ℕ} {L : ℝ}
    (hf : ∃ᶠ n in atTop, a n ≤ b n)
    (hL : Tendsto (growth b) atTop (𝓝 L)) :
    lowerGrowth a ≤ (L : EReal) := by
  have hconv : Tendsto (fun n => (growth b n : EReal)) atTop (𝓝 (L : EReal)) :=
    EReal.tendsto_coe.2 hL
  unfold lowerGrowth
  apply (liminf_le_iff (f := atTop) (u := fun n => (growth a n : EReal))).2
  intro t ht
  apply (hf.and_eventually (hconv.eventually_lt_const ht)).mono
  rintro n ⟨hab, hbt⟩
  apply lt_of_le_of_lt _ hbt
  apply EReal.coe_le_coe_iff.mpr
  exact Real.rpow_le_rpow (Nat.cast_nonneg (a n))
    (Nat.cast_le.mpr hab : (a n : ℝ) ≤ (b n : ℝ)) (by positivity : 0 ≤ ((2 : ℝ) ^ (n+1))⁻¹)

/-- Every nondecreasing expansion is bounded in lower growth by the growth
rate of a benchmark: the comparison in §4 with no terms removed. -/
theorem frequently_den_le_benchmark {q : ℚ} {a b : ℕ → ℕ}
    (ha : Expansion q a) (hb : Benchmark q b) :
    ∃ᶠ n in atTop, a n ≤ b n := by
  obtain ⟨hbexp, N, _, _, _, _, _, hbest⟩ := hb
  have hfreq := frequently_term_ge_of_prefix_le hbexp.2.2 ha.2.2 (by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← real_prefix_sum, ← real_prefix_sum]
    exact_mod_cast (hbest n hn).2 _ (admissible_prefix ha n))
  apply hfreq.mono
  intro n h
  by_contra! hn
  have hbpos : (0 : ℝ) < b n := by have := hbexp.1 n; positivity
  exact (not_lt_of_ge h) (one_div_lt_one_div_of_lt hbpos (by exact_mod_cast hn))

theorem lowerGrowth_le_benchmark {q : ℚ} {a b : ℕ → ℕ} {L : ℝ}
    (ha : Expansion q a) (hb : Benchmark q b) (hL : Tendsto (growth b) atTop (𝓝 L)) :
    lowerGrowth a ≤ (L : EReal) :=
  lowerGrowth_le_of_frequently_le (frequently_den_le_benchmark ha hb) hL

/-- The full truncation comparison. After sorting the first k denominators
with the replacement expansion d, the resulting c eventually satisfies
c(k + j) = d(j). Comparing a(k + j) and c(k + j) at the same global indices
avoids moving a real power through a liminf. -/
theorem truncation_comparison {μ : ℚ} {a c d : ℕ → ℕ} {k : ℕ} {L : ℝ}
    (ha : Expansion μ (fun j => a (k + j))) (hd : Benchmark μ d)
    (hshift : ∀ᶠ j in atTop, c (k + j) = d j)
    (hL : Tendsto (growth c) atTop (𝓝 L)) :
    lowerGrowth a ≤ (L : EReal) := by
  apply lowerGrowth_le_of_frequently_le _ hL
  have hf := (frequently_den_le_benchmark ha hd).and_eventually hshift
  apply frequently_atTop.2
  intro M
  obtain ⟨j, hj, h, heq⟩ := frequently_atTop.1 hf M
  exact ⟨k+j, by omega, heq.symm ▸ h⟩

/-- Sorted inclusion of all finite prefixes, along a cofinal family of
truncations, forces pointwise domination. Equal reciprocal sums then force
equality. The index comparison counts repeated denominators automatically. -/
theorem eq_of_cofinal_prefix_comparison {q : ℚ} {a c : ℕ → ℕ}
    (ha : Expansion q a) (hc : Expansion q c)
    (h : ∃ᶠ k in atTop, ∀ i < k, c i ≤ a i) : a = c := by
  have hden (i : ℕ) : c i ≤ a i := by
    obtain ⟨k, hk, hle⟩ := frequently_atTop.1 h (i+1)
    exact hle i (by omega)
  funext i
  by_contra! hne
  have hpos (j : ℕ) : (0 : ℝ) < c j := by have := hc.1 j; positivity
  have hle (j : ℕ) : 1 / (a j : ℝ) ≤ 1 / (c j : ℝ) :=
    one_div_le_one_div_of_le (hpos j) (by exact_mod_cast hden j)
  have hlt : 1 / (a i : ℝ) < 1 / (c i : ℝ) :=
    one_div_lt_one_div_of_lt (hpos i) (by exact_mod_cast lt_of_le_of_ne (hden i) (Ne.symm hne))
  have htotal := ha.2.2.summable.tsum_lt_tsum hle hlt hc.2.2.summable
  rw [ha.2.2.tsum_eq, hc.2.2.tsum_eq] at htotal
  exact (lt_irrefl _ htotal)

/-- The last pigeonhole step of §4. The family S is provided by the
finite-maximizing-rays part of the Bellman argument. -/
theorem eq_benchmark_of_finite_completions {q : ℚ} {a b : ℕ → ℕ}
    (ha : Expansion q a) (hb : Benchmark q b)
    {S : Set (ℕ → ℕ)} (hS : S.Finite)
    (hgood : ∀ c ∈ S, Benchmark q c)
    (hcover : ∀ k : ℕ, ∃ c ∈ S, ∀ i < k, c i ≤ a i) :
    ∃ K, ∀ n, K ≤ n → a n = b n := by
  obtain ⟨c, hc, hcofinal⟩ := hS.frequently_exists.1
    (Frequently.of_forall (f := atTop) hcover)
  have hbench := hgood c hc
  have heq := eq_of_cofinal_prefix_comparison ha hbench.1 hcofinal
  exact heq.symm ▸ benchmarks_eventually_equal hbench hb

end Egyptian
