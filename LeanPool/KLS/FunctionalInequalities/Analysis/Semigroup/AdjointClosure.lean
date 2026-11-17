/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.AdjointComp
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Weak identities pass to the closure, and into the adjoint

Let `T : H₀ →ₗ.[ℝ] H₁` be a closable operator between real Hilbert spaces. If two fixed vectors
`w : H₀` and `v : H₁` satisfy the weak identity `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)`, the same
identity holds for every `x ∈ D(Tbar)` with `Tbar x` in place of `T x`: the set of pairs
`(x, y)` with
`⟪w, x⟫ = ⟪v, y⟫` is closed and contains the graph of `T`, hence its closure, which is the graph
of `Tbar` (`LinearPMap.IsClosable.graph_closure_eq_closure_graph`).

Consequently `v ∈ D(Tbar†)` and, when `D(Tbar)` is dense, `Tbar† v = w`
(`LinearPMap.mem_adjoint_domain_of_exists`, `LinearPMap.adjoint_apply_eq`). Combined with
`adjointComp` this is the tool that puts a vector `x ∈ D(Tbar)` into `D(Tbar†Tbar)` and computes
`Tbar†Tbar x` from a weak identity verified on the unclosed domain only.

The module also records two witness-level tools: `apply_sub_of_eq_sub`, which evaluates `S` on a
difference with the three membership witnesses supplied separately, and the graph-limit tool
`exists_mem_domain_apply_eq_of_tendsto`: a
**closed** operator absorbs limits of its graph points, so a vector reached by `x n ∈ D(S)` with
`S (x n)` convergent lies in `D(S)`, with the expected value. Together with a Cauchy estimate this
is how an identity or bound proved on a smaller domain is transported to the closure.

Pure Hilbert-space material: no measure, no differential operator, no semigroup.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]

/-- `S` on a difference, with all three membership witnesses supplied separately.  Only proof
irrelevance and `LinearPMap.map_sub` are involved; the value is given by a hypothesis `z = x - y`
so that it can be produced by a rewrite without disturbing the witnesses. -/
theorem apply_sub_of_eq_sub {S : H₀ →ₗ.[ℝ] H₁} {x y z : H₀} (hx : x ∈ S.domain)
    (hy : y ∈ S.domain) (hz : z ∈ S.domain) (h : z = x - y) :
    S ⟨z, hz⟩ = S ⟨x, hx⟩ - S ⟨y, hy⟩ := by
  subst h
  exact S.map_sub ⟨x, hx⟩ ⟨y, hy⟩

/-- A closed operator absorbs graph limits: if `x n ∈ D(S)` for every `n`, `x n → a` in `H₀` and
`S (x n) → b` in `H₁`, then `a ∈ D(S)` and `S a = b`.

`LinearPMap.IsClosed` is closedness of the graph as a subset of `H₀ × H₁`, so this is
`IsClosed.mem_of_tendsto` applied to the pair sequence, followed by `LinearPMap.mem_graph_iff`
and proof irrelevance of the membership witness. Completeness is not used: the limits are
hypotheses. -/
theorem exists_mem_domain_apply_eq_of_tendsto {S : H₀ →ₗ.[ℝ] H₁} (hS : S.IsClosed)
    {x : ℕ → H₀} (hx : ∀ n, x n ∈ S.domain) {a : H₀} {b : H₁}
    (hxa : Filter.Tendsto x Filter.atTop (nhds a))
    (hSb : Filter.Tendsto (fun n => S ⟨x n, hx n⟩) Filter.atTop (nhds b)) :
    ∃ h : a ∈ S.domain, S ⟨a, h⟩ = b := by
  have hgraph : (a, b) ∈ S.graph :=
    hS.mem_of_tendsto (hxa.prodMk_nhds hSb)
      (Filter.Eventually.of_forall fun n => S.mem_graph ⟨x n, hx n⟩)
  obtain ⟨y, hy1, hy2⟩ := S.mem_graph_iff.mp hgraph
  have hy1' : (y : H₀) = a := hy1
  have hy2' : S y = b := hy2
  have hmem : a ∈ S.domain := by rw [← hy1']; exact y.2
  refine ⟨hmem, ?_⟩
  rw [show (⟨a, hmem⟩ : S.domain) = y from Subtype.ext hy1'.symm]
  exact hy2'

/-- A weak identity `⟪w, x⟫ = ⟪v, T x⟫` valid on the domain of a closable operator `T` persists on
the domain of its closure. -/
theorem inner_eq_inner_closure_apply {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable) {w : H₀} {v : H₁}
    (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) (x : T.closure.domain) :
    ⟪w, (x : H₀)⟫ = ⟪v, T.closure x⟫ := by
  have hmem : ((x : H₀), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hclosed : IsClosed {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : (T.graph : Set (H₀ × H₁)) ⊆ {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} := by
    intro p hp
    obtain ⟨y, rfl⟩ := T.mem_graph_iff'.mp hp
    exact h y
  have hcl := closure_minimal hsub hclosed
  rw [← Submodule.topologicalClosure_coe] at hcl
  exact hcl hmem

variable [CompleteSpace H₀]

/-- If `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)` and `T` is closable, then `v ∈ D(Tbar†)`. -/
theorem mem_adjoint_domain_closure_of_forall {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable) {w : H₀}
    {v : H₁} (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) : v ∈ T.closure†.domain :=
  LinearPMap.mem_adjoint_domain_of_exists v ⟨w, inner_eq_inner_closure_apply hT h⟩

/-- If `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)`, `T` is closable and `D(Tbar)` is dense, then
`Tbar† v = w`. -/
theorem adjoint_closure_apply_eq_of_forall {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable)
    (hd : Dense (T.closure.domain : Set H₀)) {w : H₀} {v : H₁}
    (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) :
    T.closure† ⟨v, mem_adjoint_domain_closure_of_forall hT h⟩ = w :=
  LinearPMap.adjoint_apply_eq hd _ (inner_eq_inner_closure_apply hT h)

end FunctionalInequalities.Analysis.Semigroup
