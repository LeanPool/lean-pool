/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Definitions for Graph Minors XIX: Well-quasi-ordering on a surface

This file formalizes the definitions that the statement of (2.1) of N. Robertson and
P. D. Seymour, *Graph Minors. XIX. Well-quasi-ordering on a surface*, J. Combin. Theory Ser. B 90
(2004) 325–385, needs, from Section 2 (pages 327–328): paintings (`Painting`, a triple
`(U, V, γ)`), the 1-skeleton (`Painting.skAdj`), inflations (`IsInflation`), linear inflations
(`IsLinearInflation`) and internally 3-connected paintings (`Painting.IsInternallyThreeConnected`).

It also defines orientations of a cuff and the order of points on a cuff, which Graph Minors XVII,
XIX and XX all use: an orientation is a homeomorphism from the unit circle, and "in order" and
"immediately precedes" are read through such a homeomorphism (`cuffPoint`, `InOrderOn`,
`ImmediatelyPrecedes`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ### Order on a cuff -/

/-- The point of angle `t` under a parametrization `f` of an `O`-arc `Θ` by the circle. -/
noncomputable def cuffPoint {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) : S :=
  (f (Circle.exp t)).1

/-- `n₁, n₂, n₃, n₄` occur in order on the `O`-arc `Θ` (Graph Minors XVII, Section 2, page 166:
"here and later in the paper, refers to the order of occurrence around the cuff"): for
some parametrization of `Θ` by the circle they have angles `t₁ ≤ t₂ ≤ t₃ ≤ t₄ ≤ t₁ + 2π`. -/
def InOrderOn (Θ : Set S) (n₁ n₂ n₃ n₄ : S) : Prop :=
  ∃ (f : Circle ≃ₜ Θ) (t₁ t₂ t₃ t₄ : ℝ), t₁ ≤ t₂ ∧ t₂ ≤ t₃ ∧ t₃ ≤ t₄ ∧ t₄ ≤ t₁ + 2 * Real.pi ∧
    cuffPoint f t₁ = n₁ ∧ cuffPoint f t₂ = n₂ ∧ cuffPoint f t₃ = n₃ ∧ cuffPoint f t₄ = n₄

/-- Under the orientation of `Θ` given by `f`, the point `n` immediately precedes the open segment
`A` of `Θ` (Graph Minors XIX, Section 2, page 328; Graph Minors XX, Section 8, page 348): `A` is the
set of points of angles strictly between `t₀` and `t₁`, where `n` has angle `t₀`. -/
def ImmediatelyPrecedes {Θ : Set S} (f : Circle ≃ₜ Θ) (n : S) (A : Set S) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ < t₁ ∧ t₁ ≤ t₀ + 2 * Real.pi ∧ cuffPoint f t₀ = n ∧
    A = cuffPoint f '' Ioo t₀ t₁

/-! ### Paintings -/

/-- A painting in a surface (Graph Minors XIX, Section 2, page 327): "A *painting* $\Gamma$ in
$\Sigma$ is a triple $(U, V, \gamma)$, where $U \subseteq \Sigma$ is closed and $V \subseteq U$ is
finite, such that
- $bd(\Sigma) \subseteq U$, and $U \setminus V$ has only finitely many arc-wise connected
  components, called *edges*,
- for each edge $e$, either $|\tilde{e}| = 2$ and $\bar{e}$ is a line with ends the two members of
  $\tilde{e}$, or $|\tilde{e}| = 3$ and $\bar{e}$ is a disc with $\tilde{e} \subseteq bd(\bar{e})$,
- $\gamma$ is a function assigning to each edge $e$ a march $\gamma(e)$ with
  $\bar{\gamma}(e) = \tilde{e}$; we call the $i$th term of $\gamma(e)$ the $i$th *end* of $e$, and
  the first and last terms of $\gamma(e)$ are the *tail* and *head* of $e$,
- every edge $e$ with $e \cap bd(\Sigma) \ne \emptyset$ satisfies $|\tilde{e}| = 2$ and
  $e \subseteq bd(\Sigma)$." -/
structure Painting (S : Type u) [TopologicalSpace S] where
  /-- The set `U(Γ)`. -/
  U : Set S
  /-- The set `V(Γ)` of vertices. -/
  V : Set S
  /-- The march `γ(e)` of an edge `e`. -/
  γ : Set S → List S
  isClosed_U : IsClosed U
  V_subset : V ⊆ U
  finite_V : V.Finite
  bd_subset : bd S ⊆ U
  finite_edges : (arcComponentsIn (U \ V)).Finite
  edge_shape : ∀ e ∈ arcComponentsIn (U \ V),
    ((tilde e).ncard = 2 ∧ (tilde e).Finite ∧ IsLine (closure e) ∧ lineEnds (closure e) = tilde e) ∨
      ((tilde e).ncard = 3 ∧ (tilde e).Finite ∧ IsClosedDisc (closure e) ∧
        tilde e ⊆ discBd (closure e))
  γ_nodup : ∀ e ∈ arcComponentsIn (U \ V), (γ e).Nodup
  γ_set : ∀ e ∈ arcComponentsIn (U \ V), {v | v ∈ γ e} = tilde e
  border_edge : ∀ e ∈ arcComponentsIn (U \ V), (e ∩ bd S).Nonempty →
    (tilde e).ncard = 2 ∧ e ⊆ bd S

namespace Painting

/-- The set `E(Γ)` of edges. -/
def E (Γ : Painting S) : Set (Set S) := arcComponentsIn (Γ.U \ Γ.V)

/-- `e` is a border edge if `e ∩ bd(Σ) ≠ ∅` (Graph Minors XIX, Section 2, page 327). -/
def IsBorder (e : Set S) : Prop := (e ∩ bd S).Nonempty

/-- Two vertices are adjacent in the 1-skeleton `sk(Γ)` when they are distinct and are ends of a
common edge (Graph Minors XIX, Section 2, page 327). For a subdrawing `σ(v)` that is induced, only
its vertex set matters, so the skeleton is recorded as a simple graph. -/
def skAdj (Γ : Painting S) : SimpleGraph S where
  Adj x y := x ≠ y ∧ x ∈ Γ.V ∧ y ∈ Γ.V ∧ ∃ e ∈ Γ.E, x ∈ tilde e ∧ y ∈ tilde e
  symm := ⟨fun _ _ ⟨h, hx, hy, e, he, hxe, hye⟩ ↦ ⟨h.symm, hy, hx, e, he, hye, hxe⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- `Γ` is internally 3-connected (Graph Minors XIX, Section 2, page 328): "$E(\Gamma) \ne
\emptyset$ and every $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $$|F
\cap V(\Gamma)| + |F \cap bd(\Sigma)| \le 2$$ bounds a disc $\Delta \subseteq \Sigma$ with
$\Delta \cap V(\Gamma) \subseteq F$." -/
def IsInternallyThreeConnected (Γ : Painting S) : Prop :=
  Γ.E.Nonempty ∧ ∀ F : Set S, IsOArc F → F ∩ Γ.U ⊆ Γ.V → (F ∩ bd S).Finite →
    (F ∩ Γ.V).ncard + (F ∩ bd S).ncard ≤ 2 →
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ Γ.V ⊆ F

end Painting

/-- An inflation of `Γ` in `Γ'` (Graph Minors XIX, Section 2, page 328): "a function $\sigma$ with
domain $V(\Gamma) \cup E(\Gamma)$, satisfying
- $\sigma(e) \in E(\Gamma')$ and has the same size as $e$, for each $e \in E(\Gamma)$, and if
  $e_1, e_2 \in E(\Gamma)$ are distinct then $\sigma(e_1) \ne \sigma(e_2)$,
- $\sigma(v)$ is a non-null connected induced subdrawing of $sk(\Gamma')$, for each
  $v \in V(\Gamma)$; and if $v_1, v_2 \in V(\Gamma)$ are distinct then $\sigma(v_1), \sigma(v_2)$
  are disjoint,
- for each $e \in E(\Gamma)$ and $1 \le i \le |\tilde{e}|$, if $v$ is the $i$th end of $e$ then
  $\sigma(v)$ contains the $i$th end of $\sigma(e)$."
An induced subdrawing is given by its vertex set `σv v`. -/
structure IsInflation (Γ Γ' : Painting S) (σv : S → Set S) (σe : Set S → Set S) : Prop where
  edge_mem : ∀ e ∈ Γ.E, σe e ∈ Γ'.E
  edge_size : ∀ e ∈ Γ.E, (tilde (σe e)).ncard = (tilde e).ncard
  edge_injOn : InjOn σe Γ.E
  vertex_nonempty : ∀ v ∈ Γ.V, (σv v).Nonempty
  vertex_subset : ∀ v ∈ Γ.V, σv v ⊆ Γ'.V
  vertex_connected : ∀ v ∈ Γ.V, (Γ'.skAdj.induce (σv v)).Preconnected
  vertex_disjoint : ∀ v₁ ∈ Γ.V, ∀ v₂ ∈ Γ.V, v₁ ≠ v₂ → Disjoint (σv v₁) (σv v₂)
  ends : ∀ e ∈ Γ.E, ∀ (i : ℕ) (hi : i < (Γ.γ e).length) (hi' : i < (Γ'.γ (σe e)).length),
    (Γ'.γ (σe e))[i] ∈ σv (Γ.γ e)[i]

/-- An inflation is linear (Graph Minors XIX, Section 2, page 328): "An inflation $\sigma$ of
$\Gamma$ in $\Gamma'$ is *linear* if
- for each $e \in E(\Gamma)$ and for each cuff $\Theta$, $e$ borders $\Theta$ if and only if
  $\sigma(e)$ borders $\Theta$ (and so $e$ is internal if and only if $\sigma(e)$ is internal),
- for each border edge $e'$ of $\Gamma'$, if $e' \notin \sigma(E(\Gamma))$ then $e'$ is an edge of
  $\sigma(v)$ for some $v \in V(\Gamma)$,
- for each $e \in E(\Gamma)$ bordering a cuff $\Theta$, if we orient $\Theta$ such that the tail of
  $e$ immediately precedes $e$ under this orientation, then the tail of $\sigma(e)$ immediately
  precedes $\sigma(e)$ under the same orientation of $\Theta$." -/
structure IsLinearInflation (Γ Γ' : Painting S) (σv : S → Set S) (σe : Set S → Set S) : Prop
    extends IsInflation Γ Γ' σv σe where
  borders_iff : ∀ e ∈ Γ.E, ∀ Θ ∈ cuffs S, (e ∩ Θ).Nonempty ↔ (σe e ∩ Θ).Nonempty
  border_edge : ∀ e' ∈ Γ'.E, Painting.IsBorder e' → e' ∉ σe '' Γ.E →
    ∃ v ∈ Γ.V, tilde e' ⊆ σv v
  orientation : ∀ e ∈ Γ.E, ∀ Θ ∈ cuffs S, (e ∩ Θ).Nonempty → ∀ f : Circle ≃ₜ Θ,
    ∀ n n', (Γ.γ e).head? = some n → (Γ'.γ (σe e)).head? = some n' →
      ImmediatelyPrecedes f n e → ImmediatelyPrecedes f n' (σe e)

end GraphMinor.GM19
