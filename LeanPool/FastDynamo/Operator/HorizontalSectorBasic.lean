/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.HorizontalSector
public import LeanPool.FastDynamo.Operator.FixedSectorLowerOrderDecay
public import LeanPool.FastDynamo.Operator.CompactBaseFredholm

/-!
# `lem:torus-sector-basic` for the horizontal torus operator

This module proves, clause by clause, Paper Lemma 5.1 (`lem:torus-sector-basic`) for the
horizontal operator `A_{ε,K}` of `FastDynamo/Operator/HorizontalSector.lean`.  The paper's
lemma reads

> Let `ε > 0`, `K ∈ ℤ` and `w = (w⊥, w₃) ∈ W^{1,∞}(T²; ℝ³)` satisfy `Div⊥ w⊥ = 0`.  We denote
> by `A_{ε,K}[w]` the operator in equation `eq:torus-sector` with `u` replaced by `w`.  Then
> `A_{ε,K}[w]` is closed and has non-empty resolvent set.  Its graph norm is equivalent to the
> `H²`-norm, and its resolvent is compact.  Moreover, the map
> `z - A_{ε,K}[w] : H²(T²; ℂ²) → L²(T²; ℂ²)` is Fredholm of index zero for every `z ∈ ℂ`.

**Lean drops the hypothesis `Div⊥ w⊥ = 0`** and quantifies over an arbitrary
`u : TransverseRealW1Inf`, because the route below never uses it; the paper's lemma is the
instance `u := w` with the hypothesis discarded.

Everything below is an instantiation at the two-component fibre of the fibre-generic machinery
of the `FixedSector*` and `CompactBaseFredholm` modules:

* the exact pencil splitting `z - A_{ε,K} = (diffusion pencil) - (lower order)`;
* the two fibre-blind decay estimates along the exponential ray `σ = eᵗ`
  (`tendsto_norm_transverseH2Embedding_comp_transverseVecDiffusionInverseRay_zero`, of order
  `σ⁻¹`, and `tendsto_norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverseRay_zero`,
  of order `σ^{-1/2}`), which dominate the transport, axial transport and stretching terms
  because those are bounded `L∞` multipliers of `H¹` resp. `L²` data;
* the Neumann resolvent step `eventually_hasResolventOn_of_transverseVecDiffusionSplitting`;
* the velocity-free graph clauses `transverseGraphOperator_isClosedGraph_of_hasResolventOn`,
  `norm_transverseVecH2_le_graph_of_hasResolventOn` and
  `isCompactOperator_transverseGraphOperator_stateResolvent`, the last resting on the
  two-component Rellich embedding;
* the ambient-sided Fredholm bridge
  `CompactBaseFredholm.PencilFredholmIndexZeroOn.ofCompactAmbientBase`, which is the only
  available route because `TransverseC2H2` is a closed submodule of a sup-normed product and
  therefore carries no `InnerProductSpace ℂ` instance.

**Deviation from the paper's proof**, recorded also in the blueprint node
`lem:torus-sector-basic`.  The paper (proof of `lem:torus-sector-basic`) gets the Fredholm
property from the fact that `z - A_{ε,K}[w]` differs from
`id - εΔ⊥` by an operator bounded `H¹ → L²`, hence compact `H² → L²`, and gets injectivity at
a large real `z₀ > ‖∇⊥w⊥‖_∞` from a coercivity estimate that uses `Div⊥ w⊥ = 0`; surjectivity
is then index zero, and the bounded inverse theorem gives the graph-norm equivalence.  Lean
reverses the order and uses neither ingredient: it inverts the diffusion part exactly as a
Fourier multiplier on the graph space, a Neumann series along the real ray `z → +∞` gives a
resolvent point directly, and the factorisation
`z - A = [id + (z - z₀)(z₀ - A)⁻¹](z₀ - A)` — identity-plus-compact on the *ambient* Hilbert
space `L²(T²; ℂ²)` — gives Fredholm index zero at every `z`.  The ambient side is forced:
`TransverseC2H2` is a closed submodule of a sup-normed product and carries no inner product,
so Atkinson's theorem is unavailable on it, and the paper's form — index zero for `T + K`
with `T` an isomorphism between two *different* spaces — is not in Mathlib.  The conclusions
proved are the paper's (up to the one-directional bundling of the graph-norm clause, see
`HorizontalTorusSectorBasic`), and the Lean statement is *stronger*, since it does not assume
`Div⊥ w⊥ = 0`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The lower-order part and the exact pencil splitting -/

/--
All first- and zeroth-order terms of the horizontal induction action: transport, axial
transport and stretching, with the signs they carry in `eq:torus-sector`.
-/
def horizontalInductionLowerOrder (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  -horizontalInductionTransport u - horizontalInductionAxialTransport u K +
    horizontalInductionStretching u

/-- The full horizontal pencil is exactly its diffusion pencil minus the lower-order
perturbation. -/
theorem horizontalInductionPencil_eq_diffusionPencil_sub_lowerOrder
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ) :
    (horizontalInductionOperator u ε K).pencil z =
      transverseVecDiffusionPencil (Fin 2) ε K z - horizontalInductionLowerOrder u K := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [DomainOperator.pencil, horizontalInductionOperator,
    horizontalInductionAction, horizontalInductionDiffusion,
    transverseVecDiffusionPencil, horizontalInductionLowerOrder,
    add_apply, sub_apply, neg_apply, smul_apply]
  module

/-! ## Relative decay of the lower-order terms along the exponential ray -/

section Decay

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Composing on the left with a fixed bounded map preserves operator-norm decay. -/
theorem tendsto_norm_comp_zero_of_tendsto_norm_zero
    (L : F →L[ℂ] G) (S : ℝ → E →L[ℂ] F)
    (h : Filter.Tendsto (fun t ↦ ‖S t‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t ↦ ‖L.comp (S t)‖) Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun t ↦ ContinuousLinearMap.opNorm_comp_le _ _
  · have hconst := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ ↦ ‖L‖) Filter.atTop (nhds ‖L‖)).mul h
    simpa using hconst

end Decay

/--
Clause (i) for the transport term: `u⊥·∇⊥` composed with the diffusion inverse tends to zero
along the exponential ray `σ = eᵗ`.  The velocity coefficients are bounded `L∞` multipliers, so
the whole term is dominated by the fibre-blind `O(σ^{-1/2})` first-derivative estimate.
-/
theorem tendsto_norm_horizontalInductionTransport_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(horizontalInductionTransport u).comp
        (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  have hfac : ∀ t : ℝ, (horizontalInductionTransport u).comp
      (transverseVecDiffusionInverseRay (Fin 2) ε K hε t) =
      ∑ j : Fin 2,
        (scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
            ((transverseVecDerivFromH2 (Fin 2) j).comp
              (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)) := by
    intro t
    ext f
    simp [horizontalInductionTransport, ContinuousLinearMap.comp_assoc]
  simp only [hfac]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun t ↦ norm_sum_le Finset.univ _
  · have hterm : ∀ j : Fin 2, Filter.Tendsto
        (fun t : ℝ ↦ ‖(scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
            ((transverseVecDerivFromH2 (Fin 2) j).comp
              (transverseVecDiffusionInverseRay (Fin 2) ε K hε t))‖)
        Filter.atTop (nhds 0) := fun j ↦
      tendsto_norm_comp_zero_of_tendsto_norm_zero _ _
        (tendsto_norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverseRay_zero
          (Fin 2) j ε K hε)
    have hsum : Filter.Tendsto
        (fun t : ℝ ↦ ∑ j : Fin 2, ‖(scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
            ((transverseVecDerivFromH2 (Fin 2) j).comp
              (transverseVecDiffusionInverseRay (Fin 2) ε K hε t))‖)
        Filter.atTop (nhds (∑ _j : Fin 2, (0 : ℝ))) :=
      tendsto_finsetSum Finset.univ fun j _ ↦ hterm j
    simpa using hsum

/--
Clause (i) for the axial transport term: `2π i K u₃` composed with the diffusion inverse tends
to zero along the exponential ray.  It is a zeroth-order multiplier, dominated by the
fibre-blind `O(σ⁻¹)` physical estimate.
-/
theorem tendsto_norm_horizontalInductionAxialTransport_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(horizontalInductionAxialTransport u K).comp
        (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  have hfac : ∀ t : ℝ, (horizontalInductionAxialTransport u K).comp
      (transverseVecDiffusionInverseRay (Fin 2) ε K hε t) =
      axialMultiplier K •
        (scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf 2 u)).comp
            ((transverseH2Embedding (ι := Fin 2)).comp
              (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)) := by
    intro t
    ext f
    simp [horizontalInductionAxialTransport, ContinuousLinearMap.comp_assoc]
  simp only [hfac, norm_smul]
  have hphysical := tendsto_norm_comp_zero_of_tendsto_norm_zero
    (scalarVectorMulTransverseC2 (transverseW1InfComplexValueCoordLInf 2 u))
    (fun t : ℝ ↦ (transverseH2Embedding (ι := Fin 2)).comp
      (transverseVecDiffusionInverseRay (Fin 2) ε K hε t))
    (tendsto_norm_transverseH2Embedding_comp_transverseVecDiffusionInverseRay_zero
      (Fin 2) ε K hε)
  have hmul := (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℝ ↦ ‖axialMultiplier K‖) Filter.atTop
      (nhds ‖axialMultiplier K‖)).mul hphysical
  simpa using hmul

/--
Clause (i) for the stretching term: `∑_{j<2} h_j (∂_j u)⊥` composed with the diffusion inverse
tends to zero along the exponential ray.  Reading one coordinate and multiplying by a bounded
gradient coefficient are both bounded, so the term is again dominated by the `O(σ⁻¹)` physical
estimate.
-/
theorem tendsto_norm_horizontalInductionStretching_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(horizontalInductionStretching u).comp
        (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  have hfac : ∀ t : ℝ, (horizontalInductionStretching u).comp
      (transverseVecDiffusionInverseRay (Fin 2) ε K hε t) =
      ∑ j : Fin 2,
        (vectorScalarMulTransverseC2
          (transverseW1InfHorizontalDerivLInf j u)).comp
            ((transverseCoordL2 (ι := Fin 2) j).comp
              ((transverseH2Embedding (ι := Fin 2)).comp
                (transverseVecDiffusionInverseRay (Fin 2) ε K hε t))) := by
    intro t
    ext f
    simp [horizontalInductionStretching, ContinuousLinearMap.comp_assoc]
  simp only [hfac]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun t ↦ norm_sum_le Finset.univ _
  · have hembedding :=
      tendsto_norm_transverseH2Embedding_comp_transverseVecDiffusionInverseRay_zero
        (Fin 2) ε K hε
    have hterm : ∀ j : Fin 2, Filter.Tendsto
        (fun t : ℝ ↦ ‖(vectorScalarMulTransverseC2
          (transverseW1InfHorizontalDerivLInf j u)).comp
            ((transverseCoordL2 (ι := Fin 2) j).comp
              ((transverseH2Embedding (ι := Fin 2)).comp
                (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)))‖)
        Filter.atTop (nhds 0) := fun j ↦
      tendsto_norm_comp_zero_of_tendsto_norm_zero _ _
        (tendsto_norm_comp_zero_of_tendsto_norm_zero _ _ hembedding)
    have hsum : Filter.Tendsto
        (fun t : ℝ ↦ ∑ j : Fin 2, ‖(vectorScalarMulTransverseC2
          (transverseW1InfHorizontalDerivLInf j u)).comp
            ((transverseCoordL2 (ι := Fin 2) j).comp
              ((transverseH2Embedding (ι := Fin 2)).comp
                (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)))‖)
        Filter.atTop (nhds (∑ _j : Fin 2, (0 : ℝ))) :=
      tendsto_finsetSum Finset.univ fun j _ ↦ hterm j
    simpa using hsum

/-- Triangle inequality in the shape `‖-a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`, matching the sign
pattern of `horizontalInductionLowerOrder`. -/
private theorem norm_neg_sub_add_le' {E : Type*} [SeminormedAddCommGroup E]
    (a b c : E) : ‖-a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖-a - b + c‖ ≤ ‖-a - b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖-a‖ + ‖b‖) + ‖c‖ := add_le_add (norm_sub_le _ _) (le_refl ‖c‖)
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by rw [norm_neg]

/-- The normalized lower-order correction is bounded by the sum of its three terms. -/
theorem norm_horizontalInductionLowerOrder_comp_le
    (u : TransverseRealW1Inf) (K : ℤ)
    (T : TransverseC2L2 →L[ℂ] TransverseC2H2) :
    ‖(horizontalInductionLowerOrder u K).comp T‖ ≤
      ‖(horizontalInductionTransport u).comp T‖ +
        ‖(horizontalInductionAxialTransport u K).comp T‖ +
          ‖(horizontalInductionStretching u).comp T‖ := by
  have heq : (horizontalInductionLowerOrder u K).comp T =
      -((horizontalInductionTransport u).comp T) -
        (horizontalInductionAxialTransport u K).comp T +
          (horizontalInductionStretching u).comp T := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [heq]
  exact norm_neg_sub_add_le' ((horizontalInductionTransport u).comp T)
    ((horizontalInductionAxialTransport u K).comp T)
    ((horizontalInductionStretching u).comp T)

/--
**Clause (i) for `lem:torus-sector-basic`** (an auxiliary step, not a clause of the paper's
statement).  The complete lower-order part of `A_{ε,K}`,
composed with the explicit diffusion inverse, tends to zero along the positive exponential ray
`σ = eᵗ`.  This is the quantitative input to the Neumann construction of a resolvent point.
-/
theorem tendsto_norm_horizontalInductionLowerOrder_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(horizontalInductionLowerOrder u K).comp
        (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun t ↦
      norm_horizontalInductionLowerOrder_comp_le u K
        (transverseVecDiffusionInverseRay (Fin 2) ε K hε t)
  · have hsum :=
      ((tendsto_norm_horizontalInductionTransport_comp_diffusionInverseRay_zero u ε K hε).add
        (tendsto_norm_horizontalInductionAxialTransport_comp_diffusionInverseRay_zero
          u ε K hε)).add
      (tendsto_norm_horizontalInductionStretching_comp_diffusionInverseRay_zero u ε K hε)
    simpa using hsum

/-! ## Clause (ii): a non-empty resolvent set -/

/--
**Clause (ii) of `lem:torus-sector-basic`** (non-empty resolvent set).  Every sufficiently
far point of the positive real exponential ray `σ = eᵗ` is a resolvent point of `A_{ε,K}`, with
a bounded ambient-to-`H²` inverse of the pencil.
-/
theorem eventually_hasResolventOn_horizontalInductionOperator_expRay
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Nonempty (HasResolventOn
        (horizontalInductionOperator u ε K) {((Real.exp t : ℝ) : ℂ)}) :=
  eventually_hasResolventOn_of_transverseVecDiffusionSplitting
    (horizontalInductionOperator u ε K) ε K hε (horizontalInductionLowerOrder u K)
    (fun t ↦ horizontalInductionPencil_eq_diffusionPencil_sub_lowerOrder
      u ε K ((Real.exp t : ℝ) : ℂ))
    (tendsto_norm_horizontalInductionLowerOrder_comp_diffusionInverseRay_zero u ε K hε)

/-- `A_{ε,K}` has an actual positive-real resolvent point at every positive diffusivity. -/
theorem exists_positiveReal_hasResolventOn_horizontalInductionOperator
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∃ t : ℝ, Nonempty (HasResolventOn
      (horizontalInductionOperator u ε K) {((Real.exp t : ℝ) : ℂ)}) :=
  (eventually_hasResolventOn_horizontalInductionOperator_expRay u ε K hε).exists

/-- In particular the resolvent set of `A_{ε,K}` is non-empty. -/
theorem horizontalInductionOperator_hasNonemptyResolvent
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    (horizontalInductionOperator u ε K).HasNonemptyResolvent := by
  obtain ⟨t, ht⟩ :=
    exists_positiveReal_hasResolventOn_horizontalInductionOperator u ε K hε
  exact (DomainOperator.hasNonemptyResolvent_iff_exists_singleton
    (horizontalInductionOperator u ε K)).2 ⟨((Real.exp t : ℝ) : ℂ), ht⟩

/-! ## Clauses (iii)–(v): closed graph, graph norm, compact resolvent -/

/-- **Clause (iii) of `lem:torus-sector-basic`** (closedness), conditional form: one bounded
resolvent closes the ordinary unbounded graph of `A_{ε,K}` in `L² × L²`. -/
theorem horizontalInductionOperator_isClosedGraph_of_hasResolventOn
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ)
    {S : Set ℂ} (h : HasResolventOn (horizontalInductionOperator u ε K) S)
    (z : ℂ) (hz : z ∈ S) :
    (horizontalInductionOperator u ε K).IsClosedGraph :=
  transverseGraphOperator_isClosedGraph_of_hasResolventOn
    (horizontalInductionOperator u ε K) h z hz

/-- **Clause (iii) of `lem:torus-sector-basic`**: `A_{ε,K}` is closed. -/
theorem horizontalInductionOperator_isClosedGraph
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    (horizontalInductionOperator u ε K).IsClosedGraph := by
  obtain ⟨t, ht⟩ :=
    exists_positiveReal_hasResolventOn_horizontalInductionOperator u ε K hε
  rcases ht with ⟨h⟩
  exact horizontalInductionOperator_isClosedGraph_of_hasResolventOn
    u ε K h ((Real.exp t : ℝ) : ℂ) (by simp)

/--
**Clause (iv) of `lem:torus-sector-basic`**: the graph norm of `A_{ε,K}` is
equivalent to the `H²` norm.  Only the nontrivial direction needs proof: the `H²` norm is
dominated by `C(‖z‖ ‖h‖_{L²} + ‖A_{ε,K} h‖_{L²})` with `C = ‖(z - A_{ε,K})⁻¹‖`.  The reverse
bound `‖h‖_{L²} + ‖A_{ε,K} h‖_{L²} ≤ (‖ι‖ + ‖A‖) ‖h‖_{H²}` holds for every domain operator.
-/
theorem norm_transverseC2H2_le_horizontalInduction_graph_of_hasResolventOn
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ)
    {S : Set ℂ} (h : HasResolventOn (horizontalInductionOperator u ε K) S)
    (z : ℂ) (hz : z ∈ S) (b : TransverseC2H2) :
    ‖b‖ ≤ ‖h.inv z‖ *
      (‖z‖ * ‖transverseH2Embedding b‖ + ‖horizontalInductionAction u ε K b‖) :=
  norm_transverseVecH2_le_graph_of_hasResolventOn
    (horizontalInductionOperator u ε K) h z hz b

/--
**Clause (v) of `lem:torus-sector-basic`**: the resolvent of `A_{ε,K}` is compact.
Wherever a resolvent is available it maps `L²` continuously into `H²`, and the two-component
transverse `H² → L²` embedding is compact.
-/
theorem isCompactOperator_horizontalInduction_stateResolvent
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ)
    {S : Set ℂ} (h : HasResolventOn (horizontalInductionOperator u ε K) S)
    (z : ℂ) :
    IsCompactOperator (h.stateResolvent z) :=
  isCompactOperator_transverseGraphOperator_stateResolvent
    (horizontalInductionOperator u ε K) rfl h z

/-- At one of the concrete positive-real resolvent points, the state resolvent of `A_{ε,K}` is
compact.  This is the input of the Fredholm bridge. -/
theorem exists_positiveReal_compactStateResolvent_horizontalInductionOperator
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∃ (t : ℝ) (h : HasResolventOn
      (horizontalInductionOperator u ε K) {((Real.exp t : ℝ) : ℂ)}),
      IsCompactOperator (h.stateResolvent ((Real.exp t : ℝ) : ℂ)) := by
  obtain ⟨t, ht⟩ :=
    exists_positiveReal_hasResolventOn_horizontalInductionOperator u ε K hε
  rcases ht with ⟨h⟩
  exact ⟨t, h, isCompactOperator_horizontalInduction_stateResolvent
    u ε K h ((Real.exp t : ℝ) : ℂ)⟩

/-! ## Clause (vi): Fredholm of index zero at every `z ∈ ℂ` -/

/--
**Clause (vi) of `lem:torus-sector-basic`**: the map
`z - A_{ε,K} : H²(T²; ℂ²) → L²(T²; ℂ²)` is Fredholm of index zero for **every** `z ∈ ℂ`.

The route is *not* the paper's: the paper compares `z - A_{ε,K}[w]` with
`id - εΔ⊥` (proof of `lem:torus-sector-basic`, see the module docstring).  Here the pencil
is factored instead as `z - A = [1 + (z - z₀)(z₀ - A)⁻¹](z₀ - A)` with `z₀` a resolvent
point, the first factor identity-plus-compact on the ambient Hilbert space `L²(T²; ℂ²)` and
the second an isomorphism `H² → L²`.  It is realized by
`CompactBaseFredholm.PencilFredholmIndexZeroOn.ofCompactAmbientBase`, which asks for an inner
product on the **ambient** space only — essential here, since `TransverseC2H2` carries none.
-/
theorem pencilFredholmIndexZeroOn_horizontalInductionOperator
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) (S : Set ℂ) :
    CompactBaseFredholm.PencilFredholmIndexZeroOn
      (horizontalInductionOperator u ε K) S := by
  obtain ⟨_t, h₀, hcompact⟩ :=
    exists_positiveReal_compactStateResolvent_horizontalInductionOperator u ε K hε
  exact CompactBaseFredholm.PencilFredholmIndexZeroOn.ofCompactAmbientBase
    (horizontalInductionOperator u ε K) h₀ hcompact S

/-- Every value of the horizontal pencil is Fredholm. -/
theorem isFredholm_horizontalInductionPencil
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) (z : ℂ) :
    ContinuousLinearMap.IsFredholm ((horizontalInductionOperator u ε K).pencil z) :=
  (pencilFredholmIndexZeroOn_horizontalInductionOperator u ε K hε Set.univ).isFredholm
    z (Set.mem_univ z)

/-- Every value of the horizontal pencil has Fredholm index zero. -/
theorem index_horizontalInductionPencil_eq_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) (z : ℂ) :
    ((horizontalInductionOperator u ε K).pencil z).toLinearMap.index = 0 :=
  (pencilFredholmIndexZeroOn_horizontalInductionOperator u ε K hε Set.univ).index_eq_zero
    z (Set.mem_univ z)

/-! ## The bundled lemma -/

/--
The five clauses of Paper Lemma 5.1 (`lem:torus-sector-basic`) for the horizontal torus
operator `A_{ε,K}`.  The paper's lemma reads

> Let `ε > 0`, `K ∈ ℤ` and `w = (w⊥, w₃) ∈ W^{1,∞}(T²; ℝ³)` satisfy `Div⊥ w⊥ = 0`.  We denote
> by `A_{ε,K}[w]` the operator in equation `eq:torus-sector` with `u` replaced by `w`.  Then
> `A_{ε,K}[w]` is closed and has non-empty resolvent set.  Its graph norm is equivalent to the
> `H²`-norm, and its resolvent is compact.  Moreover, the map
> `z - A_{ε,K}[w] : H²(T²; ℂ²) → L²(T²; ℂ²)` is Fredholm of index zero for every `z ∈ ℂ`.

Two differences from that quotation, both in the direction of a stronger Lean statement.

* **The hypothesis `Div⊥ w⊥ = 0` is dropped**: `u : TransverseRealW1Inf` is
  arbitrary, since the route of this module never uses it.
* **The graph-norm clause is one-directional.**  The field `norm_domain_le` records only
  `‖b‖_{H²} ≤ ‖(z - A)⁻¹‖ (‖z‖ ‖b‖_{L²} + ‖A b‖_{L²})`, the half that carries content.  The
  other half, `‖b‖_{L²} + ‖A b‖_{L²} ≤ (‖ι‖ + ‖A‖) ‖b‖_{H²}`, is the continuity of the
  embedding `transverseH2Embedding` and of the action `horizontalInductionAction`, both
  `ContinuousLinearMap`s, so it holds for every `DomainOperator` and is not bundled here.
-/
structure HorizontalTorusSectorBasic
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) : Prop where
  /-- `A_{ε,K}` is closed. -/
  isClosedGraph : (horizontalInductionOperator u ε K).IsClosedGraph
  /-- `A_{ε,K}` has non-empty resolvent set. -/
  hasNonemptyResolvent : (horizontalInductionOperator u ε K).HasNonemptyResolvent
  /-- The graph norm of `A_{ε,K}` dominates the `H²` norm at every resolvent point. -/
  norm_domain_le : ∀ (S : Set ℂ)
    (h : HasResolventOn (horizontalInductionOperator u ε K) S) (z : ℂ), z ∈ S →
      ∀ b : TransverseC2H2, ‖b‖ ≤ ‖h.inv z‖ *
        (‖z‖ * ‖transverseH2Embedding b‖ + ‖horizontalInductionAction u ε K b‖)
  /-- Every available state resolvent of `A_{ε,K}` is compact. -/
  isCompactOperator_stateResolvent : ∀ (S : Set ℂ)
    (h : HasResolventOn (horizontalInductionOperator u ε K) S) (z : ℂ), z ∈ S →
      IsCompactOperator (h.stateResolvent z)
  /-- `z - A_{ε,K}` is Fredholm of index zero for every `z ∈ ℂ`. -/
  pencilFredholmIndexZero : ∀ S : Set ℂ,
    CompactBaseFredholm.PencilFredholmIndexZeroOn (horizontalInductionOperator u ε K) S

/--
**Paper Lemma 5.1** (`lem:torus-sector-basic`): for every `ε > 0` and every `K ∈ ℤ`, the
horizontal torus operator `A_{ε,K}` of `eq:torus-sector` is closed, has non-empty resolvent
set, dominates the `H²(T²; ℂ²)` norm by its graph norm, has compact resolvent, and its pencil
`z - A_{ε,K} : H²(T²; ℂ²) → L²(T²; ℂ²)` is Fredholm of index zero for every `z ∈ ℂ`.

The paper says "graph norm is equivalent to the `H²`-norm"; `HorizontalTorusSectorBasic`
bundles only the nontrivial direction of that equivalence, the converse being the continuity
of `transverseH2Embedding` and of `horizontalInductionAction`.  The paper's hypothesis
`Div⊥ w⊥ = 0` is absent here: `u` is an arbitrary `TransverseRealW1Inf`.
See the structure's docstring.
-/
theorem horizontalInductionOperator_basic
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    HorizontalTorusSectorBasic u ε K where
  isClosedGraph := horizontalInductionOperator_isClosedGraph u ε K hε
  hasNonemptyResolvent := horizontalInductionOperator_hasNonemptyResolvent u ε K hε
  norm_domain_le := fun _S h z hz b ↦
    norm_transverseC2H2_le_horizontalInduction_graph_of_hasResolventOn u ε K h z hz b
  isCompactOperator_stateResolvent := fun _S h z _ ↦
    isCompactOperator_horizontalInduction_stateResolvent u ε K h z
  pencilFredholmIndexZero := fun S ↦
    pencilFredholmIndexZeroOn_horizontalInductionOperator u ε K hε S

end

end FastDynamo
