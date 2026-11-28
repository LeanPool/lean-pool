/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Duality.ConvexDuality
public import LeanPool.MathFin.Risk.Coherent
public import Mathlib.Algebra.Order.Star.Real

/-!
# Coherent risk measures: the Artzner–Delbaen–Eber–Heath representation (finite state)

A coherent risk measure `ρ` of losses on a finite state space `ι` (`IsCoherentRiskMeasure`) is, by
its four ADEH axioms, the supremum of expected loss `∑ qᵢ Lᵢ` over a set of representing
probability vectors `q`. The geometric content is convex duality: the **acceptance cone**
`{L | ρ L ≤ 0}` is a closed convex cone, and a rejected loss is separated from it by a representing
density — the *same* Hahn–Banach separation that gives the FTAP its equivalent martingale measure
(here via the point-from-cone primitive `MathFin.exists_separating_of_not_mem_cone`). This is the
risk-side face of the convex-duality unification.

The representation is stated as `IsLUB` (ρ L is the least upper bound of the expected losses), which
is the precise "ρ = sup over measures" statement without the conditionally-complete-lattice `iSup`
overhead.

The state space carries any finite measure `P`: the axioms are required on `P`-integrable losses
and almost surely, and on a finite space that implies the pointwise order, which is all the
separation uses. The representing vectors `q` are scenarios and need not be absolutely continuous
with respect to `P` in any sense the statement tracks.

## Main definitions

* `representingSet`: the probability vectors `q` (`qᵢ ≥ 0`, `∑ qᵢ = 1`) with `∑ qᵢ Zᵢ ≤ 0` for
  every acceptable loss `Z` (`ρ Z ≤ 0`), the densities that separate the acceptance cone.

## Main results

* `MathFin.IsCoherentRiskMeasure.acceptance_closed`, `.convex_acceptance`, `.cone`: the acceptance
  set `{L | ρ L ≤ 0}` is a closed convex cone.
* `MathFin.coherentRisk_isLUB` — the representation

## References

* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]

## Tags

coherent risk measure, Artzner-Delbaen-Eber-Heath, acceptance set, dual representation,
Hahn-Banach separation, representing measures, MSC 91G70, MSC 91G80, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

namespace IsCoherentRiskMeasure
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {P : Measure ι} [IsFiniteMeasure P] {ρ : (ι → ℝ) → ℝ}

omit [Fintype ι] in
/-- The acceptance set `{L | ρ L ≤ 0}` is closed (ρ is continuous). -/
lemma acceptance_closed [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) :
    IsClosed {L : ι → ℝ | ρ L ≤ 0} :=
  isClosed_le hρ.continuous continuous_const

omit [Fintype ι] [MeasurableSingletonClass ι] [IsFiniteMeasure P] in
/-- `0` is acceptable. -/
lemma zero_mem (hρ : IsCoherentRiskMeasure P ρ) : (0 : ι → ℝ) ∈ {L : ι → ℝ | ρ L ≤ 0} :=
  hρ.rho_zero.le

omit [Fintype ι] in
/-- The acceptance set is a cone (positive homogeneity). -/
lemma cone [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) :
    ∀ ⦃L⦄, L ∈ {L : ι → ℝ | ρ L ≤ 0} → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • L ∈ {L : ι → ℝ | ρ L ≤ 0} :=
  fun _ hL _ hc ↦ (hρ.const_mul .of_finite hc).trans_le (mul_nonpos_of_nonneg_of_nonpos hc hL)

omit [Fintype ι] in
/-- The acceptance set is convex. -/
lemma convex_acceptance [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) :
    Convex ℝ {L : ι → ℝ | ρ L ≤ 0} := by
  simpa using hρ.convexOn_univ.convex_le 0

omit [Fintype ι] in
/-- Every nonpositive loss (a gain in every state) is acceptable (monotonicity). -/
lemma nonpos_mem [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) {L : ι → ℝ} (hL : L ≤ 0) :
    L ∈ {L : ι → ℝ | ρ L ≤ 0} :=
  (hρ.mono_of_le hL).trans_eq hρ.rho_zero

end IsCoherentRiskMeasure

/-- The representing set: probability vectors that price every acceptable loss nonpositively
(the densities separating the acceptance cone). -/
def representingSet {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ ∀ Z ∈ {Y : ι → ℝ | ρ Y ≤ 0}, ∑ i, q i * Z i ≤ 0}

/-- **Coherent-risk representation (Artzner–Delbaen–Eber–Heath, finite state).** A coherent risk
measure `ρ` of losses is the supremum of expected loss over its representing probability vectors:
`ρ L` is the least upper bound of `{∑ qᵢ Lᵢ | q ∈ representingSet ρ}`. The upper bound is
cash-invariance; the least-upper-bound is the point-from-cone separation of the rejected loss
`L − b`, for an upper bound `b < ρ L`, from the acceptance cone, normalised to a representing
density. -/
theorem coherentRisk_isLUB {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {P : Measure ι} [IsFiniteMeasure P] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRiskMeasure P ρ) (L : ι → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * L i) '' representingSet ρ) (ρ L) := by
  classical
  -- a probability vector prices a shifted loss at the shifted price
  have hshift {q : ι → ℝ} (hq : ∑ i, q i = 1) (L : ι → ℝ) (m : ℝ) :
      ∑ i, q i * (L i + m) = ∑ i, q i * L i + m := by
    simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hq]
  constructor
  · rintro _ ⟨q, ⟨-, hq₁, hq⟩, rfl⟩
    have hmem : (fun i ↦ L i + -ρ L) ∈ {Y : ι → ℝ | ρ Y ≤ 0} :=
      ((hρ.add_const .of_finite _).trans (add_neg_cancel _)).le
    have := hq _ hmem
    rw [hshift hq₁] at this
    linarith
  · intro b hb
    by_contra hlt
    rw [not_le] at hlt
    have hL' : (fun i ↦ L i + -b) ∉ {Y : ι → ℝ | ρ Y ≤ 0} := by
      change ¬ ρ _ ≤ 0
      rw [hρ.add_const .of_finite, not_le]; linarith
    obtain ⟨p, hp_le, hp_pos⟩ := exists_separating_of_not_mem_cone _ hρ.convex_acceptance
      hρ.acceptance_closed hρ.cone hρ.zero_mem hL'
    have hp_nonneg (i : ι) : 0 ≤ p i := by
      have hle := hp_le _ (hρ.nonpos_mem (L := -Pi.single i 1) fun j ↦ by
        simp only [Pi.neg_apply, Pi.single_apply, Pi.zero_apply]
        split_ifs <;> norm_num)
      simpa [Pi.single_apply] using hle
    have hS : 0 < ∑ i, p i := by
      refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ hp_nonneg i) fun h0 ↦ ?_
      have hp0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hp_nonneg i).1 h0.symm
      simp [hp0] at hp_pos
    set S := ∑ i, p i
    have hq_mem : (fun i ↦ p i / S) ∈ representingSet ρ :=
      ⟨fun i ↦ div_nonneg (hp_nonneg i) hS.le, by rw [← Finset.sum_div, div_self hS.ne'],
        fun Z hZ ↦ by
          simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
          exact div_nonpos_of_nonpos_of_nonneg (hp_le Z hZ) hS.le⟩
    have hle := hb ⟨_, hq_mem, rfl⟩
    have hq₁ : ∑ i, p i / S = 1 := hq_mem.2.1
    have hpos : 0 < ∑ i, p i / S * (L i + -b) := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      exact div_pos hp_pos hS
    rw [hshift hq₁] at hpos
    linarith

end MathFin
