/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolWitness
import Mathlib.Tactic.Linarith

/-!
# Finite-horizon acceptance from actual limiting pools

Once the finite advice is fixed, actual eventual pool estimates imply that
some finite horizon passes all three rational tests.  The argument uses
convergence only to prove existence; no convergence modulus is an input to
the checker or to the exhaustive search.

Combining this bridge with weak-limit selection proves that accepted
candidates exist at every sufficiently large pool size.
-/

@[expose] public section

namespace Klr.PoolAdvice

open MeasureTheory Filter
open scoped Topology BigOperators symmDiff

/-- The finite weighted test converges to the actual eventual weighted mass
of its fixed pool. -/
theorem tendsto_weightedMass {π : ℕ → ScanRule} {rules : List ScanRule}
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (A : Advice) (G : List ℕ) (hG : G.Nodup) :
    Tendsto (fun V : ℕ => (weightedMass rules A G V : ℝ)) atTop
      (𝓝 (Pool.finitePoolMass π rules.length G.toFinset)) := by
  simp only [weightedMass_eq_sum_integral π hπ A G hG, Pool.advice_weight_cast,
    Pool.finitePoolMass]
  exact tendsto_finsetSum (Finset.range rules.length) fun i _ =>
    (PoolQuery.tendsto_integral_readFractionBy (π i) G.toFinset).const_mul (Pool.weight i)

/-- Final pool estimates with room below the acceptance thresholds give an
actual finite candidate accepted by the exact rational checker. -/
theorem exists_accepted_of_final_tests {π : ℕ → ScanRule} {rules : List ScanRule}
    (hπ : ∀ i < rules.length, rules[i]? = some (π i)) (A : Advice)
    (hℓ : A.protectedCount ≤ rules.length) (hε : 0 < (A.error : ℝ))
    {M : ℕ} {G : Finset ℕ} (hcard : G.card = M)
    (hposition : ∀ b ∈ G, A.positionBound ≤ b)
    (hhigh : ∀ i < A.protectedCount,
      fairCoin.real {Z | Z ∈ highSet A i ∧ PoolQuery.readFraction (π i) G Z < 1} <
        2 * (A.error : ℝ))
    (hdist : ∀ i < A.protectedCount,
      (∫ Z, |PoolQuery.readFraction (π i) G Z - approx A i Z| ∂fairCoin) <
        2 * (A.error : ℝ))
    (hweighted : (A.threshold : ℝ) < Pool.finitePoolMass π rules.length G) :
    ∃ C : Candidate, Accepted rules A M C := by
  classical
  have hevHigh : ∀ᶠ V : ℕ in atTop, ∀ i : Fin A.protectedCount,
      fairCoin.real {Z | Z ∈ highSet A i ∧ PoolQuery.readFractionBy (π i) G V Z < 1} <
        3 * (A.error : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (PoolQuery.tendsto_high_missBy (π i) G (measurableSet_highSet A i)).eventually
      (p := fun x => x < 3 * (A.error : ℝ)) (gt_mem_nhds (by linarith [hhigh i i.isLt]))
  have hevDist : ∀ᶠ V : ℕ in atTop, ∀ i : Fin A.protectedCount,
      (∫ Z, |PoolQuery.readFraction (π i) G Z -
        PoolQuery.readFractionBy (π i) G V Z| ∂fairCoin) < (A.error : ℝ) := by
    exact Filter.eventually_all.mpr fun i =>
      (PoolQuery.tendsto_readFractionBy_l1 (π i) G).eventually (gt_mem_nhds hε)
  have hwlim : Tendsto (fun V : ℕ => (weightedMass rules A G.toList V : ℝ)) atTop
      (𝓝 (Pool.finitePoolMass π rules.length G)) := by
    simpa only [Finset.toList_toFinset] using
      tendsto_weightedMass hπ A G.toList G.nodup_toList
  have hevWeight := hwlim.eventually (lt_mem_nhds hweighted)
  obtain ⟨V, hVhigh, hVdist, hVweighted⟩ := (hevHigh.and (hevDist.and hevWeight)).exists
  refine ⟨(G.toList, V), ?_⟩
  refine ⟨?_, G.nodup_toList, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.length_toList] using hcard
  · intro b hb
    exact hposition b (Finset.mem_toList.mp hb)
  · intro i hi
    have hreal : (highMiss rules A G.toList V i : ℝ) < 3 * (A.error : ℝ) := by
      rw [highMiss_eq_measureReal (hπ i (hi.trans_le hℓ)) A G.toList G.nodup_toList V,
        Finset.toList_toFinset]
      exact hVhigh ⟨i, hi⟩
    exact_mod_cast hreal
  · intro i hi
    have hsmall : (∫ Z, |PoolQuery.readFractionBy (π i) G V Z -
        PoolQuery.readFraction (π i) G Z| ∂fairCoin) < (A.error : ℝ) := by
      simpa only [abs_sub_comm] using hVdist ⟨i, hi⟩
    have htri := PoolSoundness.integral_abs_sub_le_add
      (PoolQuery.integrable_readFractionBy (π i) G V)
      (PoolQuery.integrable_readFraction (π i) G) (integrable_approx A i)
    have hfinal := hdist i hi
    have hreal : (distance rules A G.toList V i : ℝ) < 3 * (A.error : ℝ) := by
      rw [distance_eq_integral (hπ i (hi.trans_le hℓ)) A G.toList G.nodup_toList V,
        Finset.toList_toFinset]
      linarith
    exact_mod_cast hreal
  · exact_mod_cast hVweighted

end Klr.PoolAdvice

namespace Klr.Pool.QueryPartition

open MeasureTheory Filter
open scoped Topology BigOperators symmDiff

/-- Fixed Borel and rational advice, together with the actual query weak
limits, ensures that accepted finite candidates exist for every sufficiently
large size. -/
theorem eventually_exists_accepted {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (D : QueryPartition π a) (ha : Tendsto D.position atTop atTop)
    (rules : List ScanRule) (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (A : PoolAdvice.Advice) (hℓ : A.protectedCount ≤ rules.length)
    (hε : 0 < (A.error : ℝ))
    (hhigh : ∀ i < A.protectedCount,
      fairCoin.real (D.high i ∆ PoolAdvice.highSet A i) < (A.error : ℝ))
    (happrox : ∀ i < A.protectedCount,
      (∫ Z, |PoolAdvice.approx A i Z - D.representative i Z| ∂fairCoin) < (A.error : ℝ))
    (hweighted : ∀ᶠ n : ℕ in atTop,
      (A.threshold : ℝ) < ∑ i ∈ Finset.range rules.length,
        weight i * queryProbability (π i) (D.position n)) :
    ∀ᶠ M : ℕ in atTop, ∃ C : PoolAdvice.Candidate, PoolAdvice.Accepted rules A M C := by
  filter_upwards [D.eventually_exists_final_pool ha A.protectedCount rules.length
    A.positionBound hε hweighted] with M hM
  obtain ⟨G, hcard, hposition, hGhigh, hGdist, hGweighted⟩ := hM
  apply PoolAdvice.exists_accepted_of_final_tests hπ A hℓ hε hcard hposition
    (hweighted := hGweighted)
  · intro i hi
    have hsub : {Z | Z ∈ PoolAdvice.highSet A i ∧ PoolQuery.readFraction (π i) G Z < 1} ⊆
        (D.high i ∆ PoolAdvice.highSet A i) ∪
          {Z | Z ∈ D.high i ∧ PoolQuery.readFraction (π i) G Z < 1} := by
      intro Z hZ
      by_cases hz : Z ∈ D.high i
      · exact Or.inr ⟨hz, hZ.2⟩
      · exact Or.inl (Or.inr ⟨hZ.1, hz⟩)
    have hle := (measureReal_mono hsub (measure_ne_top fairCoin _)).trans
      (measureReal_union_le (μ := fairCoin) _ _)
    linarith [hhigh i hi, hGhigh i hi]
  · intro i hi
    have hrep : Integrable (D.representative i) fairCoin :=
      (integrable_L2 (D.limit i)).congr (D.representative_ae_eq i).symm
    have htri := PoolSoundness.integral_abs_sub_le_add
      (PoolQuery.integrable_readFraction (π i) G) hrep (PoolAdvice.integrable_approx A i)
    have happ : (∫ Z, |D.representative i Z - PoolAdvice.approx A i Z| ∂fairCoin) <
        (A.error : ℝ) := by simpa only [abs_sub_comm] using happrox i hi
    linarith [hGdist i hi]

end Klr.Pool.QueryPartition
