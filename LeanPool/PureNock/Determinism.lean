/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.PureCompleteHint
public import LeanPool.PureNock.PaperReferenceMod

/-!
# Output uniqueness for the executable machines

Public capstones stating that the small-step Nock machines compute *partial functions*: a
successful run's result is independent of the fuel budget.  Each composes the machine's
unconditional adequacy with the corresponding oracle's output uniqueness:

* `runProgram_output_unique`      via `runProgram_adequate_complete` + `evalPaper_deterministic`;
* `runHintProgram_output_unique`  via `runHint_adequate_complete` + `evalN_deterministic`;
* `evalPaperMod_deterministic`    directly from `evalPaperMod_mono`.

Fuel affects only whether a run *finishes*, never a finished run's *value*.  These are Lean
consistency theorems (a fuel-indexed shadow of `Thm:deterministic_Trace`, `main.tex:1156–1158`),
not numbered paper theorems.  In particular there is deliberately no claim that the fuel *numbers*
of `runProgram` and `evalPaper` coincide — the two count different quantities.
-/

@[expose] public section

namespace Nock
namespace Verb

/-- **`runProgram` output uniqueness.**  Any two successful small-step runs of `*[s f]`, at any
    fuel budgets, return the same noun. -/
theorem runProgram_output_unique {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runProgram fuel s f = some r₂) : r₁ = r₂ := by
  obtain ⟨n₁, hp₁⟩ := (runProgram_adequate_complete s f r₁).1 h₁
  obtain ⟨n₂, hp₂⟩ := (runProgram_adequate_complete s f r₂).1 h₂
  exact evalPaper_deterministic hp₁ hp₂

/-- **`runHintProgram` output uniqueness.**  Any two successful OP₁₁-extended runs of `*[s f]`, at
    any fuel budgets, return the same noun. -/
theorem runHintProgram_output_unique {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runHintProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runHintProgram fuel s f = some r₂) : r₁ = r₂ := by
  obtain ⟨n₁, hp₁⟩ := (runHint_adequate_complete s f r₁).1 h₁
  obtain ⟨n₂, hp₂⟩ := (runHint_adequate_complete s f r₂).1 h₂
  exact evalN_deterministic hp₁ hp₂

end Verb

/-- **`evalPaperMod q` is a partial function (output uniqueness).**  Two successful modular
    fragment evaluations of the same `subject`/`formula`, at any fuel budgets, agree. -/
theorem evalPaperMod_deterministic {q n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalPaperMod q n s form = some r₁) (h₂ : evalPaperMod q m s form = some r₂) : r₁ = r₂ :=
  Option.some.inj ((evalPaperMod_mono (Nat.le_max_left n m) h₁).symm.trans
    (evalPaperMod_mono (Nat.le_max_right n m) h₂))

end Nock
