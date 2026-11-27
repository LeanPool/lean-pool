/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineDescriptionSeparation

/-!
# The concrete relation between two successive construction stages

The relation records estimates for one actual new affine block under the
actual preceding finite-stage laws. The old sequence is only consulted
before `n`; later blocks may be empty padding. A successful step also
includes a short, successfully evaluated exact affine description.
-/

@[expose] public section

namespace Klr.StageRecursion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- One stage's complete mathematical output. The fixed Borel partition
is shared across all stages, and the protected strategies are `0, ..., n`. -/
structure Step (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (old : ℕ → AffineBlock) (n z : ℕ) (error : ℚ)
    (C : AffineBlock) (V : ℕ) : Prop where
  above : ∀ q ∈ C.support, z ≤ q
  early_and_partial : ∀ i, i ≤ n →
    (∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager (fun _ => C)
      (s i).normalize.scan (s i).normalize.capital.wager (fun _ => V) 0 X)
      ∂cond (PrefixStage.law old n) C.event) +
      cond (PrefixStage.law old n) C.event
        (LateDropBound.partialEvent C (s i).normalize.scan V) ≤
          ENNReal.ofReal (4 * (error : ℝ))
  first_drop_tail : ∀ i, i ≤ n →
    cond (PrefixStage.law old n) C.event
      (StoppingTranscript.rankDropTailEvent C (s i).normalize.scan V) ≤
        ENNReal.ofReal (2 * (error : ℝ))
  high_no_drop : ∀ i, i ≤ n →
    PrefixStage.law old n
      ((s i).normalize.scan.observationMap ⁻¹' H i ∩
        NoDrop.noDropEvent C (s i).normalize.scan) ≤ ENNReal.ofReal (error : ℝ)
  earlier_low_drop : ∀ a, a ≤ n → ∀ i, i ≤ n →
    PrefixStage.law old a
      ((s i).normalize.scan.observationMap ⁻¹' (H i)ᶜ ∩
        LateDropBound.hasDrop C (s i).normalize.scan) ≤ ENNReal.ofReal (error : ℝ)
  description : ∃ (p : List Bool) (c : AffineCode.Data),
    c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
      AffineCode.rank c = C.rank ∧
      2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = C.event

end Klr.StageRecursion
