/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Step
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Induction
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.ToCumulant
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Generator
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction

/-!
# BKL Theorem 4.1: the universal cumulant bound
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL.Localization

/--
**Lemma 5.1 discharges its named hypothesis**: `Lemma51Bound` holds, by
`generator_cumulantEnergy_ge`. -/
theorem lemma51Bound : Lemma51Bound := by
  unfold Lemma51Bound
  intro n μ hc hiso hLC h8 r hr u q hSym hQ
  exact generator_cumulantEnergy_ge μ hc hiso hLC h8 hr u q hSym hQ

/--
**BKL (95) in finite-horizon cutoff form, every order `d + 1 ≥ 2`**, at `K = 153`, conditional only
on the compact
Letwin bound. This is the single assembly of the induction: the step `cutoffEnergyClaim_succ` with
`lemma51Bound` and the
claim-to-bound passage `cumulantBoundCompact_of_cutoffEnergyClaim`. -/
theorem cutoffEnergyClaim_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim 153 d :=
  cutoffEnergyClaim_all hL (le_refl 153)
    (fun _ hm ih ihb => cutoffEnergyClaim_succ hL lemma51Bound (le_refl 153) hm ih ihb)
    (fun _ h => cumulantBoundCompact_of_cutoffEnergyClaim (by norm_num : (0 : ℝ) ≤ 153) h)

/--
**BKL Theorem 4.1 for compactly supported laws, orders `d + 1 ≥ 3`**, conditional only on the
compact Letwin bound (Lemma 4.2):
`∃ K ≥ 1, ∀ d ≥ 2, R^ν_{d+1} ≤ (d!)² K^d · Id` for all compactly supported isotropic log-concave
`ν`. -/
theorem exists_cumulantBoundCompact_of_letwinCompact
    (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ,
      1 ≤ K ∧
        ∀ d : ℕ,
          2 ≤ d →
            LogConcave.Suspension.CumulantBoundCompact d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  refine ⟨153, by norm_num, fun d hd => ?_⟩
  have h :=
    cumulantBoundCompact_of_cutoffEnergyClaim (by norm_num : (0 : ℝ) ≤ 153)
      (cutoffEnergyClaim_of_letwinCompact hL d (by omega))
  rwa [envelope_succ_eq] at h

/--
**BKL Theorem 4.1, orders `d + 1 ≥ 3`** (all isotropic log-concave laws), conditional only on the
compact Letwin bound:
the compact bound extends by the truncation argument of p. 19. The separate
`cumulantBound_of_letwinCompact` below also includes the base order `d + 1 = 2`. -/
theorem exists_cumulantBound_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ,
      1 ≤ K ∧
        ∀ d : ℕ,
          2 ≤ d → LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  obtain ⟨K, hK, hcompact⟩ := exists_cumulantBoundCompact_of_letwinCompact hL
  refine ⟨K, hK, ?_⟩
  intro d hd
  exact LogConcave.Suspension.cumulantBound_of_compact (by omega : 1 ≤ d) (hcompact d hd)

/--
**BKL Theorem 4.1 with the explicit constant `153`, every order `d + 1 ≥ 2`** (the base `d = 1`
included) and every
isotropic log-concave law, conditional only on the compact Letwin bound: the shared cutoff producer
gives the compact
bound, and the truncation argument `cumulantBound_of_compact` removes compactness. -/
theorem cumulantBound_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∀ d : ℕ,
      1 ≤ d → LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) := by
  intro d hd
  have h :=
    cumulantBoundCompact_of_cutoffEnergyClaim (by norm_num : (0 : ℝ) ≤ 153)
      (cutoffEnergyClaim_of_letwinCompact hL d hd)
  rw [envelope_succ_eq] at h
  exact LogConcave.Suspension.cumulantBound_of_compact hd h

end FunctionalInequalities.KLS.BKL.Localization
