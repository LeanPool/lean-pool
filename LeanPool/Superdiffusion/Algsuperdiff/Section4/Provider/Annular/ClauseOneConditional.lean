/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.EventReading
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ShomContinuityUngated

/-!
# ClauseOneConditional

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The conditional clause-(i) endpoint of the annular decomposition

This module composes the proved clause-(i) chain into a single **conditional**
endpoint: the almost-sure, `[0,∞]`-valued, representative-side display of
`DisplaySlots.clauseOne_representative_display_latticeMax`, carrying *exactly*
the four remaining inputs as named hypotheses and nothing else.

## What is discharged here

Starting from `ClauseOne.clauseOne_bound` (18 binders + two event memberships
after the A5c feed), this module closes:

* the **good-event plumbing** — the two event memberships `hG1` / `hG2` and the
  threshold nonnegativity `0 ≤ T`, from a single membership `ω ∈
  Support.goodEventBase M Ccg m s ε` through the proved projections
  `Support.goodEventBase_subset_eventG1` / `…_subset_eventG2`, at the
  `e.lambda.good.events` amplitude `T = s ε √c⋆ γ^{−1/2}`;
* the **σ-continuity slot** `hshom` (with its companion `hsig0`), from A5a's
  `exists_shomSlot_ge` at the floor `6`, so the endpoint's regime hypothesis is
  the printed `γ ≤ C^{−1} c⋆^{10}` with `C = C_shom^{10}`;
* the **constant bookkeeping** at the pinned family `C_bf = 1`, `K_L2 = 1`,
  `K_gn = 81`, with the two output constants given by the explicit formulas
  `clauseOneLegConstant` and `clauseOneOutConstant`;
* the **`∀ L` / `Eventually` wrapper**: the pointwise chain holds for *every*
  `L ≥ m`, with no `m ≤ L` side condition beyond the one the display carries.

## What remains, and why

* `hpref` / `hpret` — the Step-1 annular cover at the concrete grids
  `AssemblyFeed.jLegField` / `AssemblyFeed.jLegTranspose`; the covering and
  centering subadditivity (`hcov` / `hcen`) is not established here;
* `huglyf` — the per-cube ugly estimate at the pinned carriers
  `DisplaySlots.annularErrorLatticeMax`, `EventBudgets.annularL2Block`,
  `EventBudgets.annularGradBlock`; the unit-cube-to-lattice-cube transport is
  not established here;
* `huglyt` — its transpose leg, likewise open (CoarseGraining has no
  transpose-invariance theorem for the error functionals).

Together with the printed ranges (`s ≤ 1`, `8γ ≤ s`, `c⋆^4 ≤ 6`,
`1 ≤ |log γ|`, `0 ≤ ε`) and the good-event membership, these are the *only*
inputs of the endpoint.

## Wrinkle  of the graph's clause-(ii) route, recorded

`goodEventBase_subset_annularEvent` is the containment the manuscript leaves
unstated: `𝒢(m; s, ε) ⊆ 𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})`, i.e. the event of the
printed clause-(i) display, valid because `s ε ≤ 1`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the `𝒢₁` amplitude of `e.lambda.good.events` -/

/-- The `𝒢₁` amplitude carried by `Support.goodEventBase`, `T = s ε √c⋆ γ^{-1/2}`,
is nonnegative. -/
theorem goodEventAmplitude_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {ep : ℝ}
    (hep : 0 ≤ ep) :
    (0 : ℝ) ≤ (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
  mul_nonneg (mul_nonneg (mul_nonneg s.2.le hep) (Real.sqrt_nonneg _))
    (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- The square of the `𝒢₁` amplitude, in the form the third and fourth
right-hand terms of clause (i) consume: `T² = s² ε² c⋆ γ^{-1}`. -/
theorem goodEventAmplitude_sq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = (s : ℝ) ^ 2 * ep ^ 2 * Disorder.cstar M * (M.gamma)⁻¹ := by
  have hc : Real.sqrt (Disorder.cstar M) ^ 2 = Disorder.cstar M :=
    Real.sq_sqrt (Disorder.cstar_characterization M).1.le
  have hg : Real.sqrt M.gamma ^ 2 = M.gamma :=
    Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexp : ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = (s : ℝ) ^ 2 * ep ^ 2 * (Real.sqrt (Disorder.cstar M) ^ 2)
        * ((Real.sqrt M.gamma) ^ 2)⁻¹ := by
    rw [← inv_pow]
    ring
  rw [hexp, hc, hg]

/-- **Wrinkle  of the clause-(ii) route, made explicit.**  The good event `𝒢(m; s,
ε)` of `e.lambda.good.events` sits inside the event of the printed clause-(i)
display, whose `𝒢₁` amplitude is the larger `√c⋆ γ^{-1/2}`.  The manuscript
uses this containment without stating it. -/
theorem goodEventBase_subset_annularEvent (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {ep : ℝ} (hep0 : 0 ≤ ep) (hsep : (s : ℝ) * ep ≤ 1) :
    Support.goodEventBase M Ccg m s ep ⊆
      Support.eventG0 M Ccg m ∩
        Support.eventG1 M m (s : ℝ)
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
  intro omega homega
  refine ⟨Support.goodEventBase_subset_eventG0 M Ccg m s ep homega, ?_⟩
  refine Support.eventG1_subset_of_le M m (s : ℝ)
    (goodEventAmplitude_nonneg M s hep0) ?_
    (Support.goodEventBase_subset_eventG1 M Ccg m s ep homega)
  have hnn : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  calc (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
      = ((s : ℝ) * ep) * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
        ring
    _ ≤ 1 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) :=
        mul_le_mul_of_nonneg_right hsep hnn
    _ = Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := one_mul _

/-! ## Part B -- the two output constants at the pinned family -/

/-- The per-leg constant of `ClauseOne.clauseOne_bound`'s `hCleg` binder at the
pinned `C_bf = 1`: `C_leg = 24 C₁ (1 + K_tail) C₂`. -/
def clauseOneLegConstant (C₁ C₂ Ktail : ℝ) : ℝ := 24 * C₁ * ((1 + Ktail) * C₂)

/-- The output constant of the clause-(i) composite at the pinned family
`C_bf = 1`, `K_L2 = 1`, `K_gn = 81`:
`C_out = 2 C_leg · 7000 C_shom²`.

Because A5a delivers `C_shom ≥ 6`, this single value dominates all three
`hCout` binders: `7000 C_shom² ≥ 252000 ≥ 51264 = 4608 K_L2 + 576 K_gn ≥ 1`. -/
def clauseOneOutConstant (C₁ C₂ Ktail Cshom : ℝ) : ℝ :=
  2 * clauseOneLegConstant C₁ C₂ Ktail * (7000 * Cshom ^ 2)

theorem clauseOneLegConstant_nonneg {C₁ C₂ Ktail : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hKtail : 0 ≤ Ktail) : 0 ≤ clauseOneLegConstant C₁ C₂ Ktail := by
  have h1 : (0 : ℝ) ≤ 1 + Ktail := by linarith only [hKtail]
  exact mul_nonneg (mul_nonneg (by norm_num) hC₁) (mul_nonneg h1 hC₂)

end

end Algsuperdiff.Section4.Provider.Annular
