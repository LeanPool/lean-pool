/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Jackson
public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Embeddings

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Embedding theorems for Sobolev spaces

A **Sobolev space** of order `s` inside `L_p(μ)` is, for this library, a smoothness space for
the scheme `S` in `L_p`: a Banach space `W` with an injective bounded map `ι : W → L_p(μ)` and
Jackson's and Bernstein's inequalities of order `s` (`FunctionScheme.SobolevSpace`). It is a
hypothesis structure whose fields are the embedding, the order and Jackson's and Bernstein's
inequalities with their constants; its instances in this library are the spaces `H^s` with
`p = 2` on the torus (`Torus.sobolevSpace`) and for a continuous spectral basis
(`ContinuousSpectralBasis.sobolevSpace`).

If the scheme has the Nikolskii property of dimension `D` (the hypothesis
`FunctionScheme.HasNikolskii`, proved on the torus), then:

* **the Sobolev embedding** `W^s_p ↪ W^t_r` for `p ≤ r` and `t < s - D(1/p - 1/r)`
  (`SobolevSpace.exists_eq_inclusion`): every element of `W` is, as an `L_p` function, the
  inclusion of an element of `W'`;
* **the embedding into bounded continuous functions** for `s > D/p`
  (`SobolevSpace.exists_boundedContinuous`), when `μ` charges every nonempty open set.

The proof is the chain

`W^s_p ⊆ B^s_{p,∞} ⊆ B^{s-α}_{r,∞} ⊆ B^t_{r,1} ⊆ W^t_r`,   `α = D(1/p - 1/r)`,

by Jackson, the Besov embedding, the embedding `A^{s-α}_∞ ⊆ A^t_1` for `t < s - α`, and
Bernstein.

**Limiting cases.** The chain loses the fine index at both ends (`W ⊆ B_{·,∞}` and
`B_{·,1} ⊆ W`), and the Besov embedding needs a strict inequality.  The sharp cases
`t = s - D(1/p - 1/r)` (for instance `W^1_1(𝕋^d) ↪ L_{d/(d-1)}`) and `s = D/p` for continuity
are therefore not provable by this method; they need tools of harmonic analysis.
-/

@[expose] public section

open MeasureTheory ApproximationScheme
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {S : FunctionScheme Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {D : ℝ} {p r : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ r)]

variable (S μ p) in
/-- A **Sobolev space** inside `L_p(μ)` for the scheme `S`: a smoothness space for `S` in
`L_p(μ)`, that is, a normed space `W` with an injective bounded linear map into `L_p(μ)` and
Jackson's and Bernstein's inequalities of some order. It is a hypothesis structure; the instances
are `Torus.sobolevSpace` and `ContinuousSpectralBasis.sobolevSpace`, both for `p = 2`. -/
abbrev SobolevSpace (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  SmoothnessSpace (S.toLp μ p) W

variable {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W']
  [NormedSpace ℝ W'] [CompleteSpace W']

/-- **The Sobolev embedding** `W^s_p ↪ W^t_r`: for a scheme with the Nikolskii property of
dimension `D ≥ 0`, Sobolev spaces `V` of order `s` in `L_p` and `V'` of order `t` in `L_r`,
`p ≤ r`, and `t < s - D(1/p - 1/r)`, every element of `V` is, as an `L_p` function, the
inclusion of an element of `V'`. -/
theorem SobolevSpace.exists_eq_inclusion (h : S.HasNikolskii μ D) (hD : 0 ≤ D)
    (V : S.SobolevSpace μ p W) (V' : S.SobolevSpace μ r W') (hpr : p ≤ r)
    (hst : V'.order < V.order - nikolskiiExponent D p r) (y : W) :
    ∃ y' : W', Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr (V'.incl y') = V.incl y := by
  have hα : nikolskiiExponent D p r < V.order := by linarith [V'.order_pos]
  obtain ⟨g, hg, hmem⟩ :=
    MemBesov.exists_inclusion_eq_of_nikolskii h hD hpr hα le_top (V.memApprox_top y)
  obtain ⟨y', hy'⟩ := V'.exists_eq_of_lt hst le_top hmem
  exact ⟨y', by rw [hy', hg]⟩

/-- **The Sobolev embedding** in the classical form of the exponents: `t - D/r < s - D/p`. -/
theorem SobolevSpace.exists_eq_inclusion' (h : S.HasNikolskii μ D) (hD : 0 ≤ D)
    (V : S.SobolevSpace μ p W) (V' : S.SobolevSpace μ r W') (hpr : p ≤ r)
    (hst : V'.order - D * r.toReal⁻¹ < V.order - D * p.toReal⁻¹) (y : W) :
    ∃ y' : W', Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr (V'.incl y') = V.incl y :=
  V.exists_eq_inclusion h hD V' hpr (by unfold nikolskiiExponent; linarith) y

/-- **Embedding of a Sobolev space into bounded continuous functions**: for `s > D/p` and a
measure charging every nonempty open set, every element of a Sobolev space of order `s` in
`L_p` has a bounded continuous representative. -/
theorem SobolevSpace.exists_boundedContinuous [μ.IsOpenPosMeasure] (h : S.HasNikolskii μ D)
    (hD : 0 ≤ D) (V : S.SobolevSpace μ p W) (hs : D * p.toReal⁻¹ < V.order) (y : W) :
    ∃ a : Ω →ᵇ ℂ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ le_top
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ a) = V.incl y :=
  MemBesov.exists_boundedContinuous h hD hs le_top (V.memApprox_top y)

end FunctionScheme
