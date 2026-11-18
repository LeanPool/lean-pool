/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Induction
public import LeanPool.KLS.FunctionalInequalities.KLS.Letwin.CompactBound

/-!
# BKL Theorem 4.1 and the cutoff (95), closed

The proved compact Letwin bound `LogConcave.Suspension.letwinCompactBound` discharges the explicit
hypothesis of the shared
producers `cutoffEnergyClaim_of_letwinCompact` and `cumulantBound_of_letwinCompact`
(`Induction.lean`), at `K = 153` for every
order `d + 1 ≥ 2`. These closed endpoints are consumed by the certificates of
`lem:bkl-cutoff-energy` and
`thm:bkl-cumulant-bound` and by the final Poincaré assembly. The uncut Eldan process and the literal
(68)–(73) are not
constructed.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.BKL.Localization

/--
**BKL (95), finite-horizon cutoff form, closed**: every order `d + 1 ≥ 2` at `K = 153`, from the
proved compact
Letwin bound. -/
theorem cutoffEnergyClaim_153 : ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim 153 d :=
  cutoffEnergyClaim_of_letwinCompact LogConcave.Suspension.letwinCompactBound

/--
**BKL Theorem 4.1 with the explicit constant 153, closed**: every order `d + 1 ≥ 2` and every
isotropic log-concave
law in every dimension. -/
theorem cumulantBound_153 :
    ∀ d : ℕ,
      1 ≤ d → LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) :=
  cumulantBound_of_letwinCompact LogConcave.Suspension.letwinCompactBound

end FunctionalInequalities.KLS.BKL.Localization
