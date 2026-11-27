/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAcceptance
public import LeanPool.KLRandomness.PoolParameters
public import LeanPool.KLRandomness.PoolCoverage

/-!
# The computable pool lemma with fixed Borel partitions

For every countable family of total computable scans, one Borel partition per
scan can be fixed before all finite-stage parameters. For any protected
prefix, positive error tolerance and position cutoff, a positive rational
margin and one ordinary partial-recursive program are then fixed. That
program, given only the requested pool size, halts at every sufficiently large
size and returns a pool satisfying both of the paper's missed-position bounds.

The final theorem discharges weak-limit existence, finite advice, termination,
and soundness. None of them is a hypothesis of the pool lemma.
-/

@[expose] public section

namespace Klr.PoolConstruction

open Filter MeasureTheory PoolAdvice
open scoped Topology BigOperators symmDiff

/-- The paper's two pool bounds, stated with actual missed positions and their
cardinality. The high/low partition is represented by a set and its complement. -/
def GoodPool (π : ℕ → ScanRule) (H : ℕ → Set Cantor) (ℓ : ℕ) (η : ℝ)
    (z : ℕ) (τ : ℚ) (M : ℕ) (G : List ℕ) : Prop :=
  G.length = M ∧ G.Nodup ∧ (∀ b ∈ G, z ≤ b) ∧
    ∀ i < ℓ,
      fairCoin.real {Z | Z ∈ H i ∧ ∃ b ∈ G, ¬ PoolQuery.Reads (π i) b Z} < η ∧
      fairCoin.real {Z | Z ∈ (H i)ᶜ ∧
        (PoolQuery.missedCount (π i) G.toFinset Z : ℝ) < (τ : ℝ) * M} < η

namespace FixedParameters

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} {Q : Pool.QueryPartition π a}
  {ℓ : ℕ} {η : ℝ} {z : ℕ} (P : PoolAdvice.FixedParameters Q ℓ η z)

/-- Soundness in the paper's exact missed-position formulation holds for every
accepted output, not only for the pools used to prove termination. -/
theorem goodPool_of_accepted {M : ℕ} {C : Candidate}
    (h : Accepted P.rules P.advice M C) :
    GoodPool π Q.high ℓ η z P.margin M C.1 := by
  refine ⟨h.1, h.2.1, fun b hb => P.position_ge.trans (h.2.2.1 b hb), ?_⟩
  intro i hi
  have hbounds := P.accepted_measure_bounds h i hi
  refine ⟨?_, ?_⟩
  · apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) hbounds.1
    intro Z hZ
    refine ⟨hZ.1, PoolQuery.readFraction_lt_one_of_exists_missed (π i) Z ?_⟩
    obtain ⟨b, hb, hmiss⟩ := hZ.2
    exact ⟨b, List.mem_toFinset.mpr hb, hmiss⟩
  · apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) hbounds.2
    intro Z hZ
    refine ⟨hZ.1, PoolQuery.one_sub_lt_readFraction_of_missedCount_lt
      (π i) C.1.toFinset Z (P.margin : ℝ) ?_⟩
    rw [List.toFinset_card_of_nodup h.2.1, h.1]
    exact hZ.2

/-- Every value of the actual pool-producing partial function satisfies the
two measure bounds and the requested finite combinatorial conditions. -/
theorem goodPool_of_mem {M : ℕ} {G : List ℕ}
    (hG : G ∈ pool P.rules P.advice M) :
    GoodPool π Q.high ℓ η z P.margin M G := by
  obtain ⟨V, hV⟩ := pool_spec hG
  exact goodPool_of_accepted P hV

/-- The analytic witness and finite-horizon convergence prove eventual
termination for the chosen fixed advice. -/
theorem eventually_accepted
    (ha : Tendsto Q.position atTop atTop)
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop
      (𝓝 (Pool.weightedQueryLimsup π))) :
    ∀ᶠ M : ℕ in atTop, ∃ C, Accepted P.rules P.advice M C := by
  apply Q.eventually_exists_accepted ha P.rules ?_ P.advice P.protected_le_length
    P.error_real_pos ?_ ?_ (P.eventually_weighted_above hp)
  · intro i hi
    exact P.getElem?_rules (by simpa only [P.length_rules] using hi)
  · intro i hi
    exact P.high_approx i (by rwa [P.protected_eq] at hi)
  · intro i hi
    exact P.function_approx i (by rwa [P.protected_eq] at hi)

/-- One fixed program returns good pools at all sufficiently large sizes. -/
theorem exists_eventual_goodPool_program
    (ha : Tendsto Q.position atTop atTop)
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop
      (𝓝 (Pool.weightedQueryLimsup π))) :
    ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
      ∃ G : List ℕ, encodePool G ∈ e.eval M ∧ GoodPool π Q.high ℓ η z P.margin M G := by
  obtain ⟨e, he⟩ := exists_eventual_pool_program P.rules P.advice (eventually_accepted P ha hp)
  refine ⟨e, ?_⟩
  filter_upwards [he] with M hM
  obtain ⟨G, V, hcode, haccepted⟩ := hM
  exact ⟨G, hcode, goodPool_of_accepted P haccepted⟩

end FixedParameters

/-- Lemma 3: fixed Borel partitions and fixed-advice computable pools.

The order of quantifiers is essential. The sets `H` precede `ℓ`, `η` and `z`;
the rational margin and the program precede the varying input `M`. Only the
program's running time and its output pool depend on that input. -/
theorem exists_fixed_partitions_computable_pools (π : ℕ → ScanRule) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ (ℓ : ℕ) (η : ℝ), 0 < η → ∀ z : ℕ,
        ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
          ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
            ∃ G : List ℕ, encodePool G ∈ e.eval M ∧ GoodPool π H ℓ η z τ M G := by
  obtain ⟨a, Q, ha, hp, _⟩ := Pool.exists_weighted_queryPartition π
  refine ⟨Q.high, Q.measurableSet_high, ?_⟩
  intro ℓ η hη z
  obtain ⟨P⟩ := exists_fixedParameters Q ℓ hη z
  exact ⟨P.margin, P.margin_pos, P.margin_lt_quarter,
    FixedParameters.exists_eventual_goodPool_program P ha hp⟩

end Klr.PoolConstruction
