/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Scheme
public import LeanPool.FunctionSpaces.Analysis.Lp.BoundedContinuous
public import Mathlib.Analysis.Complex.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation schemes of functions

A **scheme of functions** on a topological space `Ω` is an approximation scheme in the Banach
space `Ω →ᵇ ℂ` of bounded continuous complex functions with the sup norm
(`FunctionScheme Ω`).  Examples: trigonometric polynomials of degree `< n` on the torus,
algebraic polynomials on a compact set, splines, eigenfunctions of a Laplacian.

For a finite measure `μ` on `Ω`, every bounded continuous function defines an element of
`L_p(μ)` for every `p`, and the scheme is transported to `L_p(μ)` by Mathlib's bounded linear
map `BoundedContinuousFunction.toLp` (`FunctionScheme.toLp`).  One scheme thus yields a scheme
in every `L_p(μ)`, and these are compatible with the inclusions `L_r ↪ L_p`: the inclusion
maps the scheme in `L_r` onto the scheme in `L_p` (`image_toLp_of_le`), and the preimage of
the scheme in `L_p` is the scheme in `L_r` (`comap_toLp_of_le`).  These two facts are the only
input the transfer theorems need.

**Why bounded continuous functions.** The alternative, bounded measurable functions, would
add the proof obligation "bounded and measurable" to every element of every scheme, and
`C(Ω)` would restrict to compact `Ω`.  Haar functions, which are not continuous, are handled by
a scheme directly in `L_p`.
-/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction
open scoped ENNReal

/-- A **scheme of functions** on `Ω`: an approximation scheme of bounded continuous complex
functions. -/
abbrev FunctionScheme (Ω : Type*) [TopologicalSpace Ω] := ApproximationScheme (Ω →ᵇ ℂ)

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (S : FunctionScheme Ω) (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The scheme `S` transported to `L_p(μ)`: the `L_p` classes of the functions in `S n`. -/
noncomputable def toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : ApproximationScheme (Lp ℂ p μ) :=
  S.map (BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ).toLinearMap

variable {S μ} {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- `g ∈ S^(p)_n` iff `g` is the class in `L_p` of some `a ∈ S_n`. -/
theorem mem_toLp {n : ℕ} {g : Lp ℂ p μ} :
    g ∈ S.toLp μ p n ↔ ∃ a ∈ S n, BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a = g :=
  Iff.rfl

/-- The class in `L_p` of `a ∈ S_n` lies in `S^(p)_n`. -/
theorem toLp_mem_toLp {n : ℕ} {a : Ω →ᵇ ℂ} (ha : a ∈ S n) :
    BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a ∈ S.toLp μ p n :=
  ⟨a, ha, rfl⟩

/-- The inclusion `L_r ↪ L_p` maps the scheme in `L_r` into the scheme in `L_p`. -/
theorem inclusion_mem_toLp (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ r μ} (hg : g ∈ S.toLp μ r n) :
    Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g ∈ S.toLp μ p n := by
  obtain ⟨a, ha, rfl⟩ := hg
  change Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr
    (BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a) ∈ _
  rw [BoundedContinuousFunction.inclusionOfExponentLe_toLp]
  exact toLp_mem_toLp ha

/-- The inclusion `L_r ↪ L_p` maps the scheme in `L_r` onto the scheme in `L_p`. -/
theorem image_toLp_of_le (hpr : p ≤ r) (n : ℕ) :
    Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr '' S.toLp μ r n = S.toLp μ p n := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩; exact inclusion_mem_toLp hpr hg'
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, toLp_mem_toLp ha, BoundedContinuousFunction.inclusionOfExponentLe_toLp hpr a⟩

/-- An `L_r` function whose `L_p` class is an approximant is itself an approximant. -/
theorem mem_toLp_of_inclusion_mem (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ r μ}
    (hg : Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g ∈ S.toLp μ p n) : g ∈ S.toLp μ r n := by
  obtain ⟨a, ha, h⟩ := hg
  have : g = BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a :=
    Lp.inclusionOfExponentLe_injective (𝕜 := ℝ) hpr
      (by rw [BoundedContinuousFunction.inclusionOfExponentLe_toLp]; exact h.symm)
  exact this ▸ toLp_mem_toLp ha

/-- The preimage of the scheme in `L_p` under `L_r ↪ L_p` is the scheme in `L_r`. -/
theorem comap_toLp_of_le (hpr : p ≤ r) :
    (S.toLp μ p).comap (Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr).toLinearMap
      (Lp.inclusionOfExponentLe_injective hpr) = S.toLp μ r := by
  ext n g
  exact ⟨mem_toLp_of_inclusion_mem hpr, inclusion_mem_toLp hpr⟩

/-- Every approximant of the scheme in `L_p` is the inclusion of one in `L_r`. -/
theorem exists_toLp_of_mem (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ p μ} (hg : g ∈ S.toLp μ p n) :
    ∃ g' ∈ S.toLp μ r n, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g' = g := by
  rw [← image_toLp_of_le hpr] at hg
  exact hg

end FunctionScheme
