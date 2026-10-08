/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.ScaleSelection

/-!
# High-contrast homogenization: Entry.Statements.ScaleSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.scale.selection` — scale-selection alternatives

`p.scale.selection`, the paper's Proposition "Scale-selection alternatives", transcribed
from the printed display.

Reading of the display, stated here so that no divergence is silent:

* The shape of the statement is this: the printed constants `h(d,γ)`, `ε_0(d,γ)`, `c(d,γ)`,
  `L(ε,σ,d,γ)`, `B_0(ε,σ,d,γ)` are the fields of the `SelectionData`
  (`HCPoly/Entry/Setup/SelectionData.lean`), and everything the proposition asserts *about* them
  is the
  predicate `SelectionData.Selects`, added to that file by this same batch. The proposition is
  therefore `∃ S : SelectionData, S.Selects d γ`: "there exist constants in the printed ranges
  such that the printed conclusion holds".
* The whole content of the display — the hypotheses on `(𝔪,q,k,n)`, the geometry update, the
  containment, the five guarded clauses of the three alternatives, and the two conclusions "in
  every alternative" — lives in `SelectionData.Selects`, whose docstring records its reading
  line by line. Nothing is stated here that is not stated there.
* `d ≥ 2` (`t.polynomial.entry`) and `γ ∈ [0,1)`  are the standing hypotheses of the
  manuscript, carried here exactly as the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean` carries
  them; every other hypothesis of the display is inside the predicate.
* **The source lower scale is a standing hypothesis.** The condition
  `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` of `e.source.lower.scale`, made standing near
  `e.source.lower.scale`
  ("From now on `j_*` satisfies `e.source.lower.scale`"), is carried inside
  `SelectionData.Selects`, with `C_src` existential in its outermost constant group; that reading
  applies
  to every statement whose type mentions `j_*`, whether or not its display restates the
  condition and whether or not its proof uses the source estimate.

The proof is one application of `HCPolySupport.HighContrast.Entry.scale_selection`
(`HCPoly/Entry/ScaleSelection.lean`) to the binders of the statement.
-/

namespace HCPolySupport.HighContrast

/-- **Proposition `p.scale.selection`**. There exist `h(d,γ) ∈ ℕ`
and `ε_0(d,γ), c(d,γ) ∈ (0,1)` such that, for every `ε ∈ (0,ε_0]` and `σ ∈ (0,ε]`, there exist
`L(ε,σ,d,γ) ∈ ℕ` and `B_0(ε,σ,d,γ) ≥ 1` such that the printed alternatives hold for every
`B ≥ B_0` — that is, selection data satisfying `SelectionData.Selects` exist. -/
theorem scale_selection
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ S : SelectionData, S.Selects d γ := by
  exact HCPolySupport.HighContrast.Entry.scale_selection d hd γ hγ


end HCPolySupport.HighContrast
