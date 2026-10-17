/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineFinalEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseUnique
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePConversion

/-!
# HomSpineCloseClause

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the per-`ω` clause producer (C3 and C4 together)

## What this module is

`HomSpineFinalEndpoint`'s third conditional is `hclauses`, the per-`ω` clause
supplier.  Its body — for one admissible datum — is produced
here from ONE application of the transcribed printed proposition `hCG'`
(the general coarse-graining proposition at finite `p`), the Schauder external
(through `HomSpineFinalStepFour.exists_comparator_stepFourEnergy`), and the
Step-2b/3b data feed.

**Both clauses come from the SAME `hlevel`.**  That is the load-bearing
observation, and it is what makes one defect slot `D` serve both displays:

```text
  hlevel:  RHS_p  ≤  σ_m · (C_w · E_B · dataBracket)
```

* Step 4 consumes it through the two duality slots of `hCG'` and gives
  clause (C4) at `2 C_w C_sch E_B · energyBracket²`;
* Step 3c consumes it at `A:= σ_m⁻¹ · RHS_p`, which is exactly the level
  `hCG'`'s gradient leg gives, and `hlevel` makes
  `A ≤ C_w E_B dataBracket`; the `L^∞` conversion then gives clause
  (C3) at `96 d² γ_lift C_w E_B · dataBracket`.

So `D:= E_B` and the single absorbed constant is

```text
  K_abs:= 2 C_w C_sch + 96 d² · liftGeomFactor(s + d/p) · C_w   (`spineClauseConst`),
```

datum-independent, as the clause supplier requires.  This is the
hand-verified "`D = dataBracket` matches exactly", formalized.

## The comparator quantifier

`exists_comparator_stepFourEnergy` delivers (C4) at a PRODUCED comparator `v'`
while the root quantifies `∀ v`.  The uniqueness lemma
(`HomSpineCloseUnique.dirichletComparator_energyAverage_eq`) closes that gap:
the comparator's energy average is the same number for every solution of the
comparator problem.  Clause (C3) needs no transfer at all — the printed
proposition `hCG'` is itself `∀ v`, so the Step-3c chain is run directly at the
root's own `v`.

## The disclosed frame (per datum), and what it is

* `hCG'` — the one mathematical conditional, at THIS comparator;
* `hS` — the Step-2b energy-slot datum (see `HomSpineCloseRecut` for the
  `s₁ = s/4` pin the slot needs);
* `hlevel` — the single arithmetic condition, shared by both clauses;
* `hEB`, `hdom` — the defect and its `EthmB(m)` domination (the manuscript's
  "comparing to the definition of `EthmB(m)`");
* The Step-3c frame `hw`, `hwI`, `hwc`, `hGI`, `hGzero`, `hgc`, `hgw`,
  `hzero` — the rendering of `u - v ∈ H¹₀(□_m)` plus the `H¹₀` zero extension
  of the gradient, carried exactly as the `L^∞` conversion
  carries it;
* `hC4ex` — the output of the Step-4 comparator-energy producer at this
  datum.

Nothing is smuggled: the root's own five data binders (`hsol`, `hcomp`, `hKg`,
`hKh`, `hKhInf`) are the only data hypotheses, and the data-bracket
nonnegativity is DERIVED from them (`dataBracket_nonneg_of_binders`).
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The single absorbed constant -/

/-- **The absorbed constant of the two clause displays**, `K_abs`.

`2 C_w C_sch` is Step 4's (the Schauder external's constant times the level
constant), `96 d² · liftGeomFactor(s + d/p) · C_w` is Step 3c's (the finite-`p`
conversion's dimension-only factor times the same level constant).  Their SUM
dominates both, is datum-independent, and is the `K_abs` slot of
the clause supplier. -/
def spineClauseConst (d : ℕ) (s p Cw Csch : ℝ) : ℝ :=
  2 * Cw * Csch + 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw

end

end Algsuperdiff.Section4.Provider.Homogenization
