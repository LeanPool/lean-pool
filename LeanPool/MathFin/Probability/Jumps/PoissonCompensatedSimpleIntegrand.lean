/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedIsometryAdapted

/-!
# The marked simple integrand as a vector space

The source module for the compensated-Poisson (Itô–Lévy) integral operator: finite formal sums
`∑ᵢ φᵢ · 𝟙_{(sᵢ, tᵢ] × Aᵢ}` of space-time boxes, each coefficient `φᵢ` bounded and adapted at its
box's start `sᵢ`, each mark `Aᵢ` measurable with finite intensity.

Encoded as the submodule `levySimpleModule` of the `Finsupp` module `(ℝ × ℝ × Set E) →₀ (Ω → ℝ)`
(index `b = (s, t, A)` ↦ coefficient), carved by the predicate `IsLevySimple`. This is the marked
analogue of Degenne's `ProbabilityTheory.SimpleProcess` (time-indexed; no space-time version exists
in Mathlib or BrownianMotion). Adding two integrands concatenates their box families (`Finsupp`
add), scaling scales the coefficients, and adaptedness / finite marks / a uniform bound are each
preserved under `0`, `+`, `•` — so the marked integrands are a genuine submodule and inherit the
`Module ℝ` structure, with no bespoke instance.

The elementary integral, the two `L²` embeddings, the isometry (summing the overlapping-box bilinear
pairing `integral_bilinear_pairing`), and the `extendOfNorm` CLM are built on this source in the
sibling modules.

## Provenance

Structure shape mirrors `ProbabilityTheory.SimpleProcess` (Degenne, BrownianMotion — a `Finsupp` of
interval coefficients); the compensated-integral content is our own. The PRM field shape is
consulted from `cgarryZA/LevyStochCalc` (Apache-2.0, cited).

## Main definitions

* `indexBox`: the space-time box `(s, t] × A` of an index `b = (s, t, A)`.
* `IsLevySimple`: a finitely supported family `V` of coefficients indexed by boxes is a marked
  simple integrand when each `V b` is adapted at the box start, each mark is measurable with
  finite `ν`-intensity, and the coefficients are uniformly bounded.
* `levySimpleModule`: the marked simple integrands as a submodule of
  `(ℝ × ℝ × Set E) →₀ (Ω → ℝ)`.

## Main results

* `mem_levySimpleModule`: membership in `levySimpleModule N` is `IsLevySimple N`.
* `IsLevySimple.measurable_coe`: every coefficient of a marked simple integrand is adapted at its
  index's start, since off the support it is `0`.
* `IsLevySimple.bound_coe`: a marked simple integrand has a nonnegative uniform bound `C` at every
  index.

## Tags

marked simple integrand, space-time boxes, Lévy integrand, predictable simple process,
Poisson integral domain, MSC 60G51, MSC 60H05, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The space-time box of an index `b = (s, t, A)`: the rectangle `(s, t] × A`. -/
def indexBox (b : ℝ × ℝ × Set E) : Set (ℝ × E) := Set.Ioc b.1 b.2.1 ×ˢ b.2.2

/-- **The marked-simple predicate.** A `Finsupp` `V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)` is a marked simple
integrand when, on each box `b = (s, t, A)` in its (finite) support, the coefficient `V b` is
adapted at the start `s = b.1`, the mark `A = b.2.2` is measurable with finite `ν`-intensity, and
the coefficients are uniformly bounded. -/
structure IsLevySimple (N : PoissonRandomMeasure P ν)
    (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) : Prop where
  /-- Each coefficient is adapted at its box's start. -/
  adapted : ∀ b ∈ V.support, Measurable[N.pastFiltration b.1] (V b)
  /-- Each box's mark is measurable. -/
  markMeasurable : ∀ b ∈ V.support, MeasurableSet b.2.2
  /-- Each box's mark has finite intensity. -/
  markFinite : ∀ b ∈ V.support, ν b.2.2 ≠ ⊤
  /-- The coefficients are uniformly bounded. -/
  bounded : ∃ C : ℝ, ∀ b ∈ V.support, ∀ ω, |V b ω| ≤ C

namespace IsLevySimple

/-- Off its support a coefficient is `0`, so a marked simple integrand's coefficient is adapted at
`b.1` for **every** index `b`. -/
lemma measurable_coe {N : PoissonRandomMeasure P ν} {V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)}
    (hV : IsLevySimple N V) (b : ℝ × ℝ × Set E) : Measurable[N.pastFiltration b.1] (V b) := by
  by_cases hb : b ∈ V.support
  · exact hV.adapted b hb
  · rw [Finsupp.notMem_support_iff.mp hb]; exact measurable_const

/-- A nonnegative uniform bound holding at **every** index `b` (off the support the coefficient is
`0`). -/
lemma bound_coe {N : PoissonRandomMeasure P ν} {V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)}
    (hV : IsLevySimple N V) : ∃ C : ℝ, 0 ≤ C ∧ ∀ b ω, |V b ω| ≤ C := by
  obtain ⟨C, hC⟩ := hV.bounded
  refine ⟨max 0 C, le_max_left _ _, fun b ω => ?_⟩
  by_cases hb : b ∈ V.support
  · exact (hC b hb ω).trans (le_max_right _ _)
  · rw [Finsupp.notMem_support_iff.mp hb]; simp

end IsLevySimple

/-- **The marked simple integrands as a submodule** of the `Finsupp` module. The zero integrand has
empty support (all conditions vacuous); a sum's support lies in the union of the two supports so its
marks stay valid, its coefficients add (adaptedness closed under `+`, bound `Cᵥ + C_w`); a scalar
multiple keeps the support and scales the bound by `|c|`. -/
def levySimpleModule (N : PoissonRandomMeasure P ν) :
    Submodule ℝ ((ℝ × ℝ × Set E) →₀ (Ω → ℝ)) where
  carrier := {V | IsLevySimple N V}
  zero_mem' := by
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, 0, fun b hb => ?_⟩ <;> simp at hb
  add_mem' := by
    intro V W hV hW
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, ?_⟩
    · rw [Finsupp.add_apply]; exact (hV.measurable_coe b).add (hW.measurable_coe b)
    · rcases Finset.mem_union.mp (Finsupp.support_add hb) with h | h
      · exact hV.markMeasurable b h
      · exact hW.markMeasurable b h
    · rcases Finset.mem_union.mp (Finsupp.support_add hb) with h | h
      · exact hV.markFinite b h
      · exact hW.markFinite b h
    · obtain ⟨Cv, _, hCv⟩ := hV.bound_coe
      obtain ⟨Cw, _, hCw⟩ := hW.bound_coe
      refine ⟨Cv + Cw, fun b _ ω => ?_⟩
      rw [Finsupp.add_apply, Pi.add_apply, abs_le]
      have hx := abs_le.mp (hCv b ω); have hy := abs_le.mp (hCw b ω)
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  smul_mem' := by
    intro c V hV
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, ?_⟩
    · rw [Finsupp.smul_apply]; exact (hV.measurable_coe b).const_smul c
    · exact hV.markMeasurable b (Finsupp.support_smul hb)
    · exact hV.markFinite b (Finsupp.support_smul hb)
    · obtain ⟨C, _, hC⟩ := hV.bound_coe
      refine ⟨|c| * C, fun b _ ω => ?_⟩
      rw [Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC b ω) (abs_nonneg c)

@[simp] lemma mem_levySimpleModule {N : PoissonRandomMeasure P ν}
    {V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)} : V ∈ levySimpleModule N ↔ IsLevySimple N V := Iff.rfl

end MathFin
