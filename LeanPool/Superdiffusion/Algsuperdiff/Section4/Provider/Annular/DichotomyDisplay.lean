/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseTwo

/-!
# DichotomyDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `[0,∞]` dichotomy that removes `𝒢₂` from the clause-(i) display

ABK26, Section 4.1.  The proved clause-(i) chain reaches the representative
display through `ClauseOne.clauseOne_bound`, whose binder `hsumE` asks for
**real** summability of the weighted annular double family `3^{−s(m−n)} ·
annularErrorLatticeMax`.  `EventReading` supplies that binder from a `𝒢₂`
membership.  That is the only place `𝒢₂` enters clause (i), and it is a genuine
divergence from the printed statement: the clause-(i) indicator of the Section
4.1 display is `𝒢₀ ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})` and carries **no** `𝒢₂`.

This module removes the dependence, with no event and no probability at all.

## The dichotomy

The display's own first term

```
clauseOneTermOne M m s ω = Σ_{j ≤ m} Σ_{n ≤ j−1} ofReal(3^{−s(m−n)}) ·
                             sup_{v ∈ 3^n Z^d ∩ (□_j ∖ □_{j−1})} ofReal(𝓔²)
```

is an `[0,∞]`-valued object that is always defined.  For each `ω` separately:

* if `clauseOneTermOne M m s ω = ⊤`, the display is **trivially true**: the
  coefficient `ofReal(C s)` is nonzero whenever `0 < C` (and `s > 0` by typing),
  so `ofReal(C s) · ⊤ = ⊤` absorbs the whole right-hand side
  (`clauseOneDisplayRhs_eq_top_of_termOne_top`);
* if `clauseOneTermOne M m s ω ≠ ⊤`, then `hsumE` follows **eventlessly**:
  `DisplaySlots.ofReal_annularErrorLatticeMax_le` dominates the real finite
  lattice maximum by the display's `[0,∞]`-valued lattice supremum term by term,
  so the `[0,∞]` sum of the real family is below `clauseOneTermOne` and hence
  finite, and `EventReading.summable_annFam_of_ennreal_ne_top` converts finiteness
  into `Summable` (`summable_annFam_error_of_clauseOneTermOne_ne_top`).

Note that this route is *sharper* than the `𝒢₂` route, which spent the factor
`3^{−(3/4)s(m−n)}` of slack between the event weight `3^{−(s/4)(m−n)}` and the
display weight `3^{−s(m−n)}`: here the comparison is against the display's own
term, at the display's own weight, with no slack at all.

The packaged consequence is `clauseOne_representative_display_dichotomy`: the
A5b representative display with `hbound` **gated on finiteness of the first
term**, so a producer of `hbound` never has to exhibit `hsumE` from an event.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the eventless `hsumE` -/

/-- The `[0,∞]` sum of the **real** weighted annular family of squared `(2,2)`
error maxima is below the display's own first term.  Termwise:
`ofReal(3^{−s(m−n)} · max) = ofReal(3^{−s(m−n)}) · ofReal(max)` and the finite
lattice maximum is below the `[0,∞]`-valued lattice supremum
(`DisplaySlots.ofReal_annularErrorLatticeMax_le`).  No event, no weight slack. -/
theorem ofReal_annFamError_tsum_le_clauseOneTermOne (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
        ENNReal.ofReal ((3 : ℝ) ^ (-((s : ℝ) * ((m - n.1 : ℤ) : ℝ)))
          * annularErrorLatticeMax M s omega j.1 n.1))
      ≤ clauseOneTermOne M m s omega := by
  refine ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun n => ?_
  have hnj : n.1 ≤ j.1 := by
    have hn := n.2
    omega
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    show -((s : ℝ) * ((m - n.1 : ℤ) : ℝ)) = -(s : ℝ) * ((m - n.1 : ℤ) : ℝ) from by ring]
  exact mul_le_mul_right (ofReal_annularErrorLatticeMax_le M s omega hnj) _

/-- **The `hsumE` binder of `ClauseOne.clauseOne_bound`, eventlessly.**

If the display's first term is finite at `ω`, the real weighted annular family of
squared `(2,2)` error maxima is summable at `ω`.  This replaces the
`𝒢₂`-conditioned reading of that binder: no `𝒢₂`, no probability, no
threshold. -/
theorem summable_annFam_error_of_clauseOneTermOne_ne_top (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    (hfin : clauseOneTermOne M m s omega ≠ ⊤) :
    Summable (annFam m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
      * annularErrorLatticeMax M s omega j n)) :=
  summable_annFam_of_ennreal_ne_top
    (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (annularErrorLatticeMax_nonneg M s omega j n))
    (ne_top_of_le_ne_top hfin
      (ofReal_annFamError_tsum_le_clauseOneTermOne M m s omega))

/-! ## Part B -- the trivial half of the dichotomy -/

/-- **The `⊤` branch.**  When the display's first term is infinite the whole
right-hand side is `⊤`, because its coefficient `ofReal(C s)` is nonzero: this is
exactly where the frozen statement's `0 < C` is consumed. -/
theorem clauseOneDisplayRhs_eq_top_of_termOne_top (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {C : ℝ} (hC : 0 < C)
    (htop : clauseOneTermOne M m s omega = ⊤) :
    clauseOneDisplayRhs M m s C omega = ⊤ := by
  have hne : ENNReal.ofReal (C * (s : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hC s.2
  rw [clauseOneDisplayRhs_eq, htop, ENNReal.mul_top hne, top_add, top_add, top_add]

/-! ## Part C -- the display with `hbound` gated on finiteness -/

/-- **The clause-(i) representative display, by the `[0,∞]` dichotomy.**

Identical to `DisplaySlots.clauseOne_representative_display_latticeMax` except
that the pointwise chain `hbound` is only required **where the display's first
term is finite**.  On the complementary set the display holds because its
right-hand side is `⊤`.

The gain is that a producer of `hbound` may discharge the `hsumE` binder of
`ClauseOne.clauseOne_bound` from `summable_annFam_error_of_clauseOneTermOne_ne_top`
instead of from a `𝒢₂` membership, which is what lets the endpoint be stated at
the honest frozen clause-(i) event `𝒢₀ ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})`.

The hypothesis `0 < C` (rather than `0 ≤ C`) is the only cost, and it is the
positivity the frozen statement already carries.

The remaining hypothesis is a conditional A obligation, not a source premise;
no source node is claimed, realized or closed. -/
theorem clauseOne_representative_display_dichotomy (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (Event : Set (Cutoff.CutoffSample d)) {C : ℝ}
    (hC0 : 0 < C)
    (hbound : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Event → clauseOneTermOne M m s omega ≠ ⊤ → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
              * annularErrorLatticeMax M s omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma C) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Set.indicator Event (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ clauseOneDisplayRhs M m s C omega := by
  classical
  have hgated : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Event ∩ {omega | clauseOneTermOne M m s omega ≠ ⊤} → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
              * annularErrorLatticeMax M s omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma C := by
    filter_upwards [hbound] with omega hb hmem
    exact hb hmem.1 hmem.2
  filter_upwards [clauseOne_representative_display_latticeMax M m s
    (Event ∩ {omega | clauseOneTermOne M m s omega ≠ ⊤}) hC0.le hgated] with omega hom
  have hom' : Set.indicator (Event ∩ {omega | clauseOneTermOne M m s omega ≠ ⊤})
      (Support.fluxCorrectedErrorObservableSqSup M m s) omega
      ≤ clauseOneDisplayRhs M m s C omega := by
    rw [clauseOneDisplayRhs_eq]
    exact hom
  by_cases htop : clauseOneTermOne M m s omega = ⊤
  · rw [clauseOneDisplayRhs_eq_top_of_termOne_top M m s omega hC0 htop]
    exact le_top
  · refine le_trans (le_of_eq ?_) hom'
    by_cases hmem : omega ∈ Event
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show omega ∈ Event ∩ {omega | clauseOneTermOne M m s omega ≠ ⊤}
          from ⟨hmem, htop⟩)]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (fun hc : omega ∈ Event ∩
          {omega | clauseOneTermOne M m s omega ≠ ⊤} => hmem hc.1)]

end

end Algsuperdiff.Section4.Provider.Annular
