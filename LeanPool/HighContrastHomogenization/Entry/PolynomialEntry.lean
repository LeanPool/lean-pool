/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.PolynomialEntry.Assembly
public import LeanPool.HighContrastHomogenization.Entry.ResponseTransfer

/-!
# High-contrast homogenization: Entry.PolynomialEntry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `t.polynomial.entry`

`HCPolySupport.HighContrast.Entry.polynomial_entry` is the statement of
`HCPolySupport.HighContrast.polynomial_entry` (`HCPoly/Entry/Statements/PolynomialEntry.lean`),
the paper's
Theorem A.  Its statement is the one, character for character; the statement file's body
is one `by exact` application of this theorem to that statement's binders.

The proof is the assembly
`HCPolySupport.HighContrast.Multiscale.polynomial_entry_of_response_transfer`
(`HCPoly/Entry/Multiscale/PolynomialEntry/Assembly.lean`) fed with
`p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace annealedContrast aspectRatio)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory

/-- **Theorem `t.polynomial.entry`.** For every `d ≥ 2`, `γ ∈ [0,1)` and `σ ∈ (0,1]` there is
`C(σ,d,γ) > 0` such that, under the standing assumptions, `Θ_m ≤ 1 + σ` for every scale
`m ≥ ⌈C log₃(2 + Π K)⌉`.

The entry theorem is the assembly of `t.polynomial.entry` over `p.scale.selection`,
`p.global.selection` and `p.response.transfer`; the last is supplied here by
`response_transfer`. -/
theorem polynomial_entry
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
          annealedContrast P m ≤ 1 + σ :=
  Multiscale.polynomial_entry_of_response_transfer d hd γ hγ
    (fun S hS => response_transfer d hd γ hγ S hS) σ hσ

end HCPolySupport.HighContrast.Entry
