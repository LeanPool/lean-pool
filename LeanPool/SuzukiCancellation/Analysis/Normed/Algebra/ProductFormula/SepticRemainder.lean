/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Positivity

/-!
# Scalar remainders retaining seventh-order cancellation

The uncapped local distance and centered remainder keep the complete fifth- and
seventh-degree coefficients and every nonlinear term produced by integration.

## Main definitions

* `FQFP.septicStepBound`: the ninth-order local distance bound.
* `FQFP.septicCenteredRemainder`: the exact centered remainder polynomial.
-/

@[expose] public noncomputable section

namespace FQFP

/-- The uncapped local distance bound retaining both leading coefficients. -/
def septicStepBound (ℓ μ C h : ℝ) : ℝ := h ^ 5 * ℓ + h ^ 7 * μ + h ^ 9 * C

/-- The centered remainder including all products of leading coefficients and tails. -/
def septicCenteredRemainder (ℓ μ C D h : ℝ) : ℝ :=
  h ^ 9 * D + 1 / 2 * h ^ 10 * ℓ ^ 2 + h ^ 12 * ℓ * μ +
    h ^ 14 / 14 * (5 * ℓ * C + 7 * μ ^ 2) + 7 / 16 * h ^ 16 * μ * C

/-- The local distance polynomial is nonnegative for nonnegative inputs. -/
lemma septicStepBound_nonneg {ℓ μ C h : ℝ} (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) : 0 ≤ septicStepBound ℓ μ C h := by
  unfold septicStepBound
  positivity

/-- The centered remainder polynomial is nonnegative for nonnegative inputs. -/
lemma septicCenteredRemainder_nonneg {ℓ μ C D h : ℝ} (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hh : 0 ≤ h) :
    0 ≤ septicCenteredRemainder ℓ μ C D h := by
  unfold septicCenteredRemainder
  positivity

end FQFP
