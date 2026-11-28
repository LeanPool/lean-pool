/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Process.Stopping

/-!
# Paths of a stopped process

Facts about `stoppedProcess X ρ t ω = X (min t (ρ ω)) ω` that are independent of what `X` and `ρ`
are: the stopped time `t ∧ ρ` read back in `ℝ≥0` (`coe_untopA_min`), its continuity and value at
`0`, the stopped process inheriting continuity of paths (`continuous_stoppedProcess`), and the
stopping indicator being inert when `ρ` is positive (`stoppedProcess_indicator_eq`).
`BoundedLocalMartingale`, `LevyCharacterization` and `ItoFormulaUnrestrictedLocMart` localise by
stopping, and share these.

## Main results

* `coe_untopA_min`: `min t ρ`, read back in `ℝ≥0`, is again `min t ρ` in `WithTop ℝ≥0`.
* `continuous_untopA_min`, `untopA_min_zero`: `t ↦ t ∧ ρ` is continuous and equals `0` at `t = 0`.
* `stoppedProcess_indicator_eq`: when every `ρ ω` is positive, the indicator `{⊥ < ρ}` inside a
  stopped process changes nothing.
* `continuous_stoppedProcess`: a stopped process has continuous paths when `X` does.

## Tags

stopped process, localisation, path continuity, stopping time, local martingale, MSC 60G40,
MSC 60G07
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

lemma coe_untopA (x : ℝ≥0) : ((x : WithTop ℝ≥0)).untopA = x := rfl

/-- `min t ρ`, read back in `ℝ≥0`, is again `min t ρ` in `WithTop ℝ≥0`. -/
theorem coe_untopA_min (t : ℝ≥0) (c : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) c).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) c := by
  induction c using WithTop.recTopCoe with
  | top => rw [min_top_right]; rfl
  | coe c => rw [← WithTop.coe_min, coe_untopA]

/-- `t ↦ (t ∧ ρ)` is continuous. -/
theorem continuous_untopA_min (c : WithTop ℝ≥0) :
    Continuous fun t : ℝ≥0 ↦ (min (t : WithTop ℝ≥0) c).untopA := by
  induction c using WithTop.recTopCoe with
  | top => simp only [min_top_right]; exact continuous_id
  | coe c =>
    simp only [← WithTop.coe_min, coe_untopA]
    exact continuous_id.min continuous_const

/-- At time `0` the stopped time is `0`. -/
theorem untopA_min_zero (c : WithTop ℝ≥0) : (min ((0 : ℝ≥0) : WithTop ℝ≥0) c).untopA = 0 := by
  induction c using WithTop.recTopCoe with
  | top => rw [min_top_right]; rfl
  | coe c => rw [← WithTop.coe_min, coe_untopA]; simp

/-- When every `ρ ω` is positive, the indicator in the stopped process is inert. -/
theorem stoppedProcess_indicator_eq {ρ : Ω → WithTop ℝ≥0} (hρ : ∀ ω, ⊥ < ρ ω)
    (X : ℝ≥0 → Ω → ℝ) :
    stoppedProcess (fun i ↦ {ω | ⊥ < ρ ω}.indicator (X i)) ρ = stoppedProcess X ρ := by
  funext t ω
  simp only [stoppedProcess]
  exact Set.indicator_of_mem (show ω ∈ {ω : Ω | ⊥ < ρ ω} from hρ ω) _

/-- The stopped process has continuous paths. -/
theorem continuous_stoppedProcess (hcont : ∀ ω, Continuous fun t ↦ X t ω)
    (ρ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Continuous fun t ↦ stoppedProcess X ρ t ω :=
  (hcont ω).comp (continuous_untopA_min (ρ ω))

end MathFin
