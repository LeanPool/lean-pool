/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Reduction

/-!
# BKL Theorem 1.1 and the closed KLS producers
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL.Localization
/--
**BKL Theorem 1.1 conditional on the compact Letwin bound**: the dimension-free KLS bound
`KLS.Conjecture`
follows from Theorem 4.1 through the certified reduction `conjecture_of_cumulantBound`. -/
theorem conjecture_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    KLS.Conjecture := by
  exact
    FunctionalInequalities.KLS.conjecture_of_cumulantBound (hSource :=
      exists_cumulantBound_of_letwinCompact hL)

universe u

/--
**BKL Theorem 1.1** (arXiv:2610.05474v1, p. 2), closed: one universal constant `C > 0` bounds the
literature
Poincaré constant of every isotropic log-concave probability measure on every finite-dimensional
real inner product
space (universe `u`), with `K = 153` from the closed `cumulantBound_153`. -/
theorem exists_isotropicBound : ∃ C : NNReal, 0 < C ∧ KLS.IsotropicBound.{u} C := by
  obtain ⟨C, hC, hAll⟩ := FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all.{u}
  have hcb :
    ∀ d : ℕ,
      2 ≤ d → LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) :=
    fun d hd => cumulantBound_153 d (by omega)
  let B : NNReal := ⟨2 * C * 153, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * 153) := ENNReal.ofReal_coe_nnreal.symm
  refine ⟨B, ?_, ?_⟩
  · change (0 : ℝ) < 2 * C * 153
    positivity
  · intro E _ _ _ _ _ _ _ μ hLC hiso
    rw [hB]
    exact hAll 153 (by norm_num) hcb E μ hLC hiso

/-- **The dimension-free KLS bound**, closed: `KLS.Conjecture` from the conditional assembly
`conjecture_of_letwinCompact` and the proved compact Letwin bound. -/
theorem conjecture : KLS.Conjecture :=
  conjecture_of_letwinCompact LogConcave.Suspension.letwinCompactBound

end FunctionalInequalities.KLS.BKL.Localization
