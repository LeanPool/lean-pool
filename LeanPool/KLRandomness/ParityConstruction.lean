/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.ParityPools
public import LeanPool.KLRandomness.ConfinedStageConstruction
public import LeanPool.KLRandomness.ParityDescription
public import LeanPool.KLRandomness.StageEnumeration

/-!
# Defeating pair-respecting strategies with two nonrandom halves

At stage `n` the affine block uses only coordinates congruent to `n` modulo
two. The common Borel partitions supply both kinds of pools. The resulting
block law defeats every pair-respecting strategy, while each coordinate
half fails its own genuine Martin-Löf test.
-/

@[expose] public section

noncomputable section

namespace Klr.ParityConstruction

open MeasureTheory

/-- The complete stage construction with alternating even and odd supports. -/
theorem exists_sequence (s : ℕ → BettingStrategy)
    (hs : ∀ i, (s i).PairRespecting) :
    ∃ (H : ℕ → Set Cantor) (B : ℕ → AffineBlock) (V : ℕ → ℕ),
      (∀ i, MeasurableSet (H i)) ∧
      Pairwise (fun i j => Disjoint (B i).support (B j).support) ∧
      (∀ n, ∀ p ∈ (B n).support, p % 2 = n % 2) ∧
      (∀ i, StageEstimates B (s i).normalize.scan
        (s i).normalize.capital.wager V (H i) i) ∧
      ∀ n : ℕ, ∃ (p : List Bool) (c : AffineCode.Data),
        c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
          2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = (B n).event := by
  obtain ⟨H, hH, hpools⟩ := ParityPools.exists_fixed_partitions_parity_pools
    (fun i => (s i).normalize.scan) (fun i => by
      rw [BettingStrategy.normalize_scan]
      exact hs i)
  have hp : ConfinedStageConstruction.PoolSupply s H
      (fun n p => p % 2 = n % 2) := by
    intro n η hη z
    exact hpools (n + 1) η hη z (n % 2) (Nat.mod_lt _ (by decide))
  obtain ⟨B, V, hd, hc, he, hp⟩ :=
    ConfinedStageConstruction.exists_sequence s H hH (fun n p => p % 2 = n % 2) hp
  exact ⟨H, B, V, hH, hd, hc, he, hp⟩

/-- Only a classical covering enumeration of the pair-respecting subtype is
used. No effective enumeration of all total strategies is required. -/
theorem exists_surjective :
    ∃ s : ℕ → {t : BettingStrategy // t.PairRespecting}, Function.Surjective s := by
  classical
  let : Encodable {t : BettingStrategy // t.PairRespecting} := Encodable.ofCountable _
  let idle : {t : BettingStrategy // t.PairRespecting} :=
    ⟨StageEnumeration.idle, ScanRule.monotone_pairRespecting⟩
  let s (n : ℕ) : {t : BettingStrategy // t.PairRespecting} :=
    (Encodable.decode n).getD idle
  refine ⟨s, fun t => ⟨Encodable.encode t, ?_⟩⟩
  simp [s]

/-- Alternating parity blocks yield a sequence resisting every pair-respecting
strategy while both halves fail Martin-Löf randomness. -/
theorem exists_pairRespectingRandom_halves_not_martinLofRandom :
    ∃ X : Cantor, PairRespectingRandom X ∧
      ¬MartinLofRandom (fun n => X (2 * n)) ∧
      ¬MartinLofRandom (fun n => X (2 * n + 1)) := by
  obtain ⟨s, hs⟩ := exists_surjective
  obtain ⟨H, B, V, _, hdis, hparity, hest, hprogram⟩ :=
    exists_sequence (fun i => (s i).val) (fun i => (s i).property)
  have hfail : ∀ i, ∀ᵐ X ∂BlockProduct.law B hdis,
      ¬(s i).val.normalize.Succeeds X := by
    intro i
    exact BlockRandomness.ae_not_succeeds B hdis (s i).val.normalize
      (s i).val.normalize_wager_abs_le_half ((hest i).ae_summable_forcedWager hdis)
  have hall : ∀ᵐ X ∂BlockProduct.law B hdis,
      ∀ i, ¬(s i).val.normalize.Succeeds X := ae_all_iff.mpr hfail
  have hboth : ∀ᵐ X ∂BlockProduct.law B hdis,
      PairRespectingRandom X ∧
        ¬MartinLofRandom (fun n => X (2 * n)) ∧
        ¬MartinLofRandom (fun n => X (2 * n + 1)) := by
    filter_upwards [hall, BlockProduct.ae_all_blocks B hdis] with X hX hblocks
    refine ⟨?_, ?_, ?_⟩
    · intro t ht hsuccess
      obtain ⟨i, hi⟩ := hs ⟨t, ht⟩
      have he : (s i).val = t := congrArg Subtype.val hi
      exact hX i (he ▸ t.normalize_preserves_success hsuccess)
    · have he : ParityDescription.half 0 X = (fun n => X (2 * n)) := by
        funext n
        simp [ParityDescription.half]
      rw [← he]
      exact ParityDescription.not_martinLofRandom_half_of_blocks
        B hparity hprogram X hblocks 0
    · exact ParityDescription.not_martinLofRandom_half_of_blocks
        B hparity hprogram X hblocks 1
  exact hboth.exists

end Klr.ParityConstruction
