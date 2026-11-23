/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymGrowth
public import LeanPool.Egyptian.AsymCompletion

/-!
# The reduction of Theorem 4 to finiteness of maximizing rays

Two greedy unit tails with equal normalized growth agree after the later
starting point. Section 4 proves, by induction on the cleared numerator,
that only finitely many maximizing rays occur. The final theorem of this
module isolates precisely that finiteness input and benchmark existence.
-/

@[expose] public section

namespace Egyptian

open Filter
open scoped Topology

/-- A greedy unit-fraction tail from an arbitrary stopping depth. -/
def HasUnitTail (b : ℕ → ℕ) : Prop :=
  ∃ N T : ℕ, 1 ≤ T ∧ ∀ j, b (N + j) = unitIter T j + 1

theorem benchmark_hasUnitTail {q : ℚ} {b : ℕ → ℕ} (h : Benchmark q b) : HasUnitTail b := by
  obtain ⟨_, N, T, _, hT, _, ht, _⟩ := h
  exact ⟨N, T, by omega, ht⟩

private theorem align_unit_tail {b : ℕ → ℕ} {N T K : ℕ} (hT : 1 ≤ T)
    (h : ∀ j, b (N + j) = unitIter T j + 1) (hk : N ≤ K) :
    ∃ U : ℕ, 1 ≤ U ∧ ∀ j, b (K+j) = unitIter U j + 1 := by
  refine ⟨unitIter T (K-N), unitIter_pos hT _, fun j => ?_⟩
  rw [← unitIter_add, ← h, show N+(K-N+j) = K+j by omega]

/-- A finite shift of an eventually equal terminal ray has a unit tail. -/
private theorem unitTail_of_shift {c d : ℕ → ℕ} {k : ℕ} (h : HasUnitTail d)
    (hshift : ∀ᶠ j in atTop, c (k + j) = d j) : HasUnitTail c := by
  obtain ⟨N,T,hT,ht⟩ := h
  obtain ⟨I,hI⟩ := eventually_atTop.1 hshift
  let K := max I N
  obtain ⟨U,hU,hu⟩ := align_unit_tail hT ht (le_max_right I N)
  refine ⟨k+K, U, hU, fun j => ?_⟩
  rw [Nat.add_assoc, hI _ (by dsimp [K]; omega), hu]

/-- Equal growth rates synchronize the two iterates after transporting both
terminals to the same stopping depth. -/
theorem terminal_tails_equal {b c : ℕ → ℕ} {L : ℝ}
    (hb : HasUnitTail b) (hc : HasUnitTail c)
    (hlb : Tendsto (growth b) atTop (𝓝 L)) (hlc : Tendsto (growth c) atTop (𝓝 L)) :
    ∃ K, ∀ n, K ≤ n → b n = c n := by
  obtain ⟨N,T,hT,ht⟩ := hb
  obtain ⟨M,U,hU,hu⟩ := hc
  let K := max N M
  obtain ⟨X,hX,hx⟩ := align_unit_tail hT ht (le_max_left N M)
  obtain ⟨Y,hY,hy⟩ := align_unit_tail hU hu (le_max_right N M)
  have eqexp := (tendsto_nhds_unique (terminal_growth hX hx) hlb).trans
    (tendsto_nhds_unique hlc (terminal_growth hY hy))
  have heq := Real.exp_injective eqexp
  have hV : Payoff.value (X : ℝ) = Payoff.value (Y : ℝ) :=
    (div_left_inj₀ (by positivity : (2 : ℝ)^(K+1) ≠ 0)).1 heq
  have hXY : (X : ℝ) = Y := Payoff.value_strictMonoOn.injOn
    (show (1 : ℝ) ≤ X by exact_mod_cast hX)
    (show (1 : ℝ) ≤ Y by exact_mod_cast hY) hV
  have hnat : X = Y := by exact_mod_cast hXY
  subst Y
  refine ⟨K, fun n hn => ?_⟩
  have h := (hx (n-K)).trans (hy (n-K)).symm
  simpa only [show max N M + (n-K) = n by dsimp [K] at *; omega] using h

/-- Every rational residual has a benchmark, and a fixed benchmark has only
finitely many expansions with the same eventual tail. The latter is the
finite maximizing-ray assertion of §4 in sequence notation. -/
theorem asymptoticRigidity_of_finite_rays
    (hex : ∀ q : ℚ, 0 < q → ∃ b, Benchmark q b)
    (hfinite : ∀ (q : ℚ) (b : ℕ → ℕ), 0 < q → Benchmark q b →
      Set.Finite {c : ℕ → ℕ | Expansion q c ∧ ∃ K, ∀ n, K ≤ n → c n = b n}) :
    AsymptoticRigidity := by
  intro q hq
  refine ⟨hex q hq, fun b hb => ?_⟩
  obtain ⟨L,hpos,hL⟩ := benchmark_growth_exists hb
  refine ⟨L,hpos,hL,fun a ha => ?_⟩
  by_cases hlt : lowerGrowth a < (L : EReal)
  · exact Or.inl hlt
  right
  let S := {c : ℕ → ℕ | Expansion q c ∧ ∃ K, ∀ n, K ≤ n → c n = b n}
  have hcover (k : ℕ) : ∃ c ∈ S, ∀ i < k, c i ≤ a i := by
    let μ := q - recipSum (prefixTuple a k)
    obtain ⟨hμ, hμa⟩ := expansion_tail ha k
    obtain ⟨d, hd⟩ := hex μ hμ
    obtain ⟨c, hcexp, hle, hshift⟩ := sorted_completion ha.1 ha.2.1 hd.1 k
    have hc : Expansion q c := by simpa [μ] using hcexp
    have htail := unitTail_of_shift (benchmark_hasUnitTail hd) hshift
    obtain ⟨M,U,hU,hu⟩ := htail
    have hlc := terminal_growth hU hu
    have hcmp := truncation_comparison hμa hd hshift hlc
    have hcb := lowerGrowth_le_benchmark hc hb hL
    have hlim : lowerGrowth c = (Real.exp (Payoff.value (U : ℝ)/2^(M+1)) : ℝ) :=
      (EReal.tendsto_coe.2 hlc).liminf_eq
    rw [hlim] at hcb
    have heq : Real.exp (Payoff.value (U : ℝ)/2^(M+1)) = L := by
      apply EReal.coe_eq_coe_iff.1
      exact le_antisymm hcb ((le_of_not_gt hlt).trans hcmp)
    rw [heq] at hlc
    exact ⟨c, ⟨hc, terminal_tails_equal ⟨M,U,hU,hu⟩ (benchmark_hasUnitTail hb) hlc hL⟩, hle⟩
  have haS : a ∈ S := mem_of_finite_prefix_comparisons ha (hfinite q b hq hb)
    (fun _ hc => hc.1) hcover
  exact haS.2

end Egyptian
