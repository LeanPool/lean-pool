/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section2Count
public import LeanPool.GraphMinor.GM06.DiscRegions
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.Graph.Lattice

/-!
# Graph Minors VI, Section 3: Duality Symmetry, Reductions (3.3), and Dual Chains (3.5)

This file proves the foundational results of Section 3 of Robertson and Seymour,
*Graph Minors. VI. Disjoint paths across a disc*, J. Combin. Theory Ser. B **41** (1986),
115–138 (pages 119–122):
- `theorem_3_1`: **Graph Minors VI, (3.1)** ($G^{**} = G$ for a connected proper drawing on a disc).
- `theorem_3_3_i`: **Graph Minors VI, (3.3)(i)** (deleting a singleton member $\{v\} \in \Delta$).
- `theorem_3_3_ii`: **Graph Minors VI, (3.3)(ii)** (deleting a component disjoint from
  $\operatorname{bd}(\Sigma)$).
- `theorem_3_3_iii`: **Graph Minors VI, (3.3)(iii)** (infeasibility when $\delta \in \Delta$ meets
  two components).
- `theorem_3_3_iv`: **Graph Minors VI, (3.3)(iv)** (decomposing across components of $G$).
- `theorem_3_5`: **Graph Minors VI, (3.5)** (correspondence between $(x, y)$-chains of $G^*$ and $G$
  preserving redundancy).
-/

@[expose] public section

namespace GraphMinor.Surface.GraphWalk

open Set Graph

universe u v

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-- Lift a walk along a subgraph inclusion `H ≤ G`. -/
def mono {u v : α} (hle : H ≤ G) : GraphWalk H u v → GraphWalk G u v
  | .nil hv => .nil (hle.vertexSet_mono hv)
  | .cons h rest => .cons (h.mono hle) (rest.mono hle)

@[simp]
theorem support_mono {u v : α} (hle : H ≤ G) (W : GraphWalk H u v) :
    (W.mono hle).support = W.support := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mono, support, ih]

@[simp]
theorem edges_mono {u v : α} (hle : H ≤ G) (W : GraphWalk H u v) :
    (W.mono hle).edges = W.edges := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mono, edges, ih]

@[simp]
theorem length_mono {u v : α} (hle : H ≤ G) (W : GraphWalk H u v) :
    (W.mono hle).length = W.length := by
  simp [length]

theorem isSimpleClosed_mono {u : α} {hle : H ≤ G} {W : GraphWalk H u u}
    (hW : W.IsSimpleClosed) : (W.mono hle).IsSimpleClosed :=
  ⟨by simpa using hW.1, by simpa using hW.2⟩

/-- Lift a walk in `G` to an induced subgraph `G.induce X` when all its vertices lie in `X`. -/
def toInduce {u v : α} {X : Set α} (W : GraphWalk G u v)
    (hX : ∀ x ∈ W.support, x ∈ X) : GraphWalk (G.induce X) u v :=
  match W with
  | .nil _ => .nil (hX u (by simp [support]))
  | .cons h rest =>
    have hu : u ∈ X := hX u (by simp [support])
    have hv : _ ∈ X := by
      apply hX
      cases rest <;> simp [support]
    .cons ⟨h, hu, hv⟩ (rest.toInduce fun x hx => hX x (by simp [support, hx]))

end GraphMinor.Surface.GraphWalk

namespace GraphMinor.GM06

open Set Function Topology Graph GraphMinor.Surface

universe u v

/-! ## 1. Forests and Connected Components of Multigraphs -/

theorem isGraphForest_of_le {α : Type u} {β : Type v} {H G : Graph α β}
    (hle : H ≤ G) (hG : IsGraphForest G) : IsGraphForest H := by
  intro u W hW
  rw [← W.length_mono hle]
  exact hG u (W.mono hle) (W.isSimpleClosed_mono hW)

/-- The set of vertices of `G` reachable by a walk from `x`. -/
def reachSet {α : Type u} {β : Type v} (G : Graph α β) (x : α) : Set α :=
  {y ∈ V(G) | Nonempty (GraphWalk G x y)}

/-- The canonical connected component of `G` containing `x`, defined as `G.induce (reachSet G x)`.
-/
def compOf {α : Type u} {β : Type v} (G : Graph α β) (x : α) : Graph α β :=
  G.induce (reachSet G x)

theorem reachSet_subset {α : Type u} {β : Type v} (G : Graph α β) (x : α) :
    reachSet G x ⊆ V(G) :=
  fun _ hy => hy.1

@[simp]
theorem vertexSet_compOf {α : Type u} {β : Type v} (G : Graph α β) (x : α) :
    V(compOf G x) = reachSet G x :=
  rfl

theorem compOf_le {α : Type u} {β : Type v} (G : Graph α β) (x : α) :
    compOf G x ≤ G :=
  G.induce_le (reachSet_subset G x)

theorem self_mem_reachSet {α : Type u} {β : Type v} {G : Graph α β} {x : α} (hx : x ∈ V(G)) :
    x ∈ reachSet G x :=
  ⟨hx, ⟨.nil hx⟩⟩

theorem reachSet_step {α : Type u} {β : Type v} {G : Graph α β} {x u v : α} {e : β}
    (hu : u ∈ reachSet G x) (hlink : G.IsLink e u v) : v ∈ reachSet G x := by
  obtain ⟨_, ⟨W⟩⟩ := hu
  exact ⟨hlink.right_mem, ⟨W.append (.cons hlink (.nil hlink.right_mem))⟩⟩

theorem walk_support_subset_reachSet {α : Type u} {β : Type v} {G : Graph α β} {x u v : α}
    (hu : u ∈ reachSet G x) (W : GraphWalk G u v) :
    ∀ z ∈ W.support, z ∈ reachSet G x := by
  induction W with
  | nil _ =>
    intro z hz
    simp only [GraphWalk.support, List.mem_singleton] at hz
    exact hz ▸ hu
  | cons h rest ih =>
    intro z hz
    simp only [GraphWalk.support, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih (reachSet_step hu h) z hz

theorem isGraphConnected_compOf {α : Type u} {β : Type v} {G : Graph α β} {x : α}
    (hx : x ∈ V(G)) : IsGraphConnected (compOf G x) := by
  refine ⟨⟨x, self_mem_reachSet hx⟩, fun u hu v hv => ?_⟩
  rcases hu with ⟨huG, ⟨Wxu⟩⟩
  rcases hv with ⟨_, ⟨Wxv⟩⟩
  let Wuv : GraphWalk G u v := Wxu.reverse.append Wxv
  have hu' : u ∈ reachSet G x := ⟨huG, ⟨Wxu⟩⟩
  exact ⟨Wuv.toInduce (walk_support_subset_reachSet hu' Wuv)⟩

theorem le_compOf_of_isGraphConnected {α : Type u} {β : Type v} {G C : Graph α β} {x : α}
    (hCG : C ≤ G) (hConn : IsGraphConnected C) (hx : x ∈ V(C)) :
    C ≤ compOf G x := by
  have hsub : V(C) ⊆ reachSet G x := by
    intro y hy
    obtain ⟨W⟩ := hConn.2 x hx y hy
    exact ⟨hCG.vertexSet_mono hy, ⟨W.mono hCG⟩⟩
  refine ⟨hsub, fun e u v hlink => ?_⟩
  exact ⟨hlink.mono hCG, hsub hlink.left_mem, hsub hlink.right_mem⟩

theorem isGraphComponent_compOf {α : Type u} {β : Type v} {G : Graph α β} {x : α}
    (hx : x ∈ V(G)) : IsGraphComponent (compOf G x) G := by
  refine ⟨compOf_le G x, isGraphConnected_compOf hx, fun C' hle hC'G hConn => ?_⟩
  have hxC' : x ∈ V(C') := hle.vertexSet_mono (self_mem_reachSet hx)
  exact le_antisymm (le_compOf_of_isGraphConnected hC'G hConn hxC') hle

theorem IsGraphComponent.eq_compOf_of_mem {α : Type u} {β : Type v} {G C : Graph α β}
    (hC : IsGraphComponent C G) {x : α} (hx : x ∈ V(C)) :
    C = compOf G x := by
  have hxG : x ∈ V(G) := hC.1.vertexSet_mono hx
  exact (hC.2.2 (compOf G x) (le_compOf_of_isGraphConnected hC.1 hC.2.1 hx)
    (compOf_le G x) (isGraphConnected_compOf hxG)).symm

theorem IsGraphComponent.eq_of_mem_mem {α : Type u} {β : Type v} {G C₁ C₂ : Graph α β}
    (h₁ : IsGraphComponent C₁ G) (h₂ : IsGraphComponent C₂ G) {x : α}
    (hx₁ : x ∈ V(C₁)) (hx₂ : x ∈ V(C₂)) : C₁ = C₂ := by
  rw [h₁.eq_compOf_of_mem hx₁, h₂.eq_compOf_of_mem hx₂]

theorem IsGraphComponent.disjoint_vertexSet_of_ne {α : Type u} {β : Type v} {G C₁ C₂ : Graph α β}
    (h₁ : IsGraphComponent C₁ G) (h₂ : IsGraphComponent C₂ G) (hne : C₁ ≠ C₂) :
    Disjoint V(C₁) V(C₂) :=
  disjoint_left.mpr fun _ hx₁ hx₂ => hne (h₁.eq_of_mem_mem h₂ hx₁ hx₂)

theorem IsGraphComponent.disjoint_edgeSet_of_ne {α : Type u} {β : Type v} {G C₁ C₂ : Graph α β}
    (h₁ : IsGraphComponent C₁ G) (h₂ : IsGraphComponent C₂ G) (hne : C₁ ≠ C₂) :
    Disjoint E(C₁) E(C₂) := by
  refine disjoint_left.mpr fun e he₁ he₂ => ?_
  obtain ⟨u, v, hl₁⟩ := C₁.exists_isLink_of_mem_edgeSet he₁
  obtain ⟨x, y, hl₂⟩ := C₂.exists_isLink_of_mem_edgeSet he₂
  have h1 := hl₁.mono h₁.1
  have h2 := hl₂.mono h₂.1
  rcases h1.left_eq_or_eq h2 with rfl | rfl
  · exact disjoint_left.mp (h₁.disjoint_vertexSet_of_ne h₂ hne) hl₁.left_mem hl₂.left_mem
  · exact disjoint_left.mp (h₁.disjoint_vertexSet_of_ne h₂ hne) hl₁.left_mem hl₂.right_mem

theorem IsGraphComponent.mem_iff_of_isLink {α : Type u} {β : Type v} {G C : Graph α β}
    (hC : IsGraphComponent C G) {e : β} {u v : α} (hlink : G.IsLink e u v) :
    u ∈ V(C) ↔ v ∈ V(C) := by
  constructor
  · intro hu
    rw [hC.eq_compOf_of_mem hu]
    exact reachSet_step (self_mem_reachSet (hC.1.vertexSet_mono hu)) hlink
  · intro hv
    rw [hC.eq_compOf_of_mem hv]
    exact reachSet_step (self_mem_reachSet (hC.1.vertexSet_mono hv)) hlink.symm

theorem IsGraphComponent.isLink_iff_of_mem {α : Type u} {β : Type v} {G C : Graph α β}
    (hC : IsGraphComponent C G) {e : β} {u v : α} (hu : u ∈ V(C)) :
    C.IsLink e u v ↔ G.IsLink e u v := by
  constructor
  · exact fun h => h.mono hC.1
  · intro hlink
    have hv : v ∈ V(C) := (hC.mem_iff_of_isLink hlink).mp hu
    have heq := hC.eq_compOf_of_mem hu
    rw [heq] at hu hv ⊢
    exact ⟨hlink, hu, hv⟩

theorem IsGraphComponent.le_of_isGraphConnected {α : Type u} {β : Type v} {G C K : Graph α β}
    (hC : IsGraphComponent C G) (hKG : K ≤ G) (hK : IsGraphConnected K)
    {x : α} (hxK : x ∈ V(K)) (hxC : x ∈ V(C)) : K ≤ C := by
  rw [hC.eq_compOf_of_mem hxC]
  exact le_compOf_of_isGraphConnected hKG hK hxK

/-! ## 2. Proof of Theorem (3.1) -/

/-- **Graph Minors VI, (3.1)** (page 120):
"If $G$ is connected and properly drawn on a disc $\Sigma$, then $G^{**} = G$. (More precisely, the
drawing of $G$ is a drawing of $G^{**}$.)" -/
theorem theorem_3_1_proof : Statement31.{u} := by
  intro S _ G G_dual hS hConn hDual
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  exact hDual.symm_of_connected hS hConn

/-! ## 3. Proofs of (3.3)(i)–(iv) -/

/-- Deleting the vertex set of a connected component `C` from `H` preserves all other connected
components of `H`. -/
private theorem isGraphComponent_deleteVerts_iff {α : Type u} {β : Type v}
    {H C K : Graph α β} (hC : IsGraphComponent C H) :
    IsGraphComponent K (H.deleteVerts V(C)) ↔ IsGraphComponent K H ∧ K ≠ C := by
  constructor
  · intro hK
    obtain ⟨x, hxK⟩ := hK.2.1.1
    have hx_del : x ∈ V(H) \ V(C) := by
      rw [← vertexSet_deleteVerts]
      exact hK.1.vertexSet_mono hxK
    have hCH : IsGraphComponent (compOf H x) H := isGraphComponent_compOf hx_del.1
    have hne : compOf H x ≠ C := by
      intro heq
      have hx_in : x ∈ V(compOf H x) := self_mem_reachSet hx_del.1
      rw [heq] at hx_in
      exact hx_del.2 hx_in
    have hdisj : Disjoint V(compOf H x) V(C) := hCH.disjoint_vertexSet_of_ne hC hne
    have hcomp_le : compOf H x ≤ H.deleteVerts V(C) := by
      refine ⟨?_, fun e u v hlink => ?_⟩
      · rw [vertexSet_deleteVerts]
        exact subset_sdiff.mpr ⟨reachSet_subset H x, hdisj⟩
      · rw [deleteVerts_isLink]
        exact ⟨hlink.1, disjoint_left.mp hdisj hlink.2.1, disjoint_left.mp hdisj hlink.2.2⟩
    have hK_le_H : K ≤ H := hK.1.trans deleteVerts_le
    have hK_le_comp : K ≤ compOf H x :=
      le_compOf_of_isGraphConnected hK_le_H hK.2.1 hxK
    have hK_eq : K = compOf H x :=
      (hK.2.2 (compOf H x) hK_le_comp hcomp_le (isGraphConnected_compOf hx_del.1)).symm
    rw [hK_eq]
    exact ⟨hCH, hne⟩
  · rintro ⟨hK, hne⟩
    have hdisj : Disjoint V(K) V(C) := hK.disjoint_vertexSet_of_ne hC hne
    have hK_le : K ≤ H.deleteVerts V(C) := by
      refine ⟨?_, fun e u v hlink => ?_⟩
      · rw [vertexSet_deleteVerts]
        exact subset_sdiff.mpr ⟨hK.1.vertexSet_mono, hdisj⟩
      · rw [deleteVerts_isLink]
        exact ⟨hlink.mono hK.1, disjoint_left.mp hdisj hlink.left_mem,
          disjoint_left.mp hdisj hlink.right_mem⟩
    refine ⟨hK_le, hK.2.1, fun K' hKK' hK'del hK'conn => ?_⟩
    exact hK.2.2 K' hKK' (hK'del.trans deleteVerts_le) hK'conn

/-- Adding an isolated vertex `v ∉ V(H')` to a graph `H'`. -/
private def addIsolatedVertex {α : Type u} {β : Type v} (H' : Graph α β) (v : α) : Graph α β where
  vertexSet := V(H') ∪ {v}
  edgeSet := E(H')
  IsLink e x y := H'.IsLink e x y
  isLink_symm _ he := H'.isLink_symm he
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := h1.left_eq_or_eq h2
  edge_mem_iff_exists_isLink e := H'.edge_mem_iff_exists_isLink e
  left_mem_of_isLink _ _ _ h := Or.inl h.left_mem

private theorem le_addIsolatedVertex {α : Type u} {β : Type v} (H' : Graph α β) (v : α) :
    H' ≤ addIsolatedVertex H' v :=
  ⟨subset_union_left, fun _ _ _ h => h⟩

private def walkToSub {α : Type u} {β : Type v} {H' : Graph α β} {v : α}
    {x y : α} (hx : x ∈ V(H')) :
    GraphWalk (addIsolatedVertex H' v) x y → GraphWalk H' x y
  | .nil _ => .nil hx
  | .cons h rest =>
    have h' : H'.IsLink _ _ _ := h
    .cons h' (walkToSub h'.right_mem rest)

@[simp]
private theorem support_walkToSub {α : Type u} {β : Type v} {H' : Graph α β} {v : α}
    {x y : α} (hx : x ∈ V(H')) (W : GraphWalk (addIsolatedVertex H' v) x y) :
    (walkToSub hx W).support = W.support := by
  induction W with
  | nil _ => rfl
  | cons h rest ih =>
    have h' : H'.IsLink _ _ _ := h
    simp [walkToSub, GraphWalk.support, ih h'.right_mem]

@[simp]
private theorem edges_walkToSub {α : Type u} {β : Type v} {H' : Graph α β} {v : α}
    {x y : α} (hx : x ∈ V(H')) (W : GraphWalk (addIsolatedVertex H' v) x y) :
    (walkToSub hx W).edges = W.edges := by
  induction W with
  | nil _ => rfl
  | cons h rest ih =>
    have h' : H'.IsLink _ _ _ := h
    simp [walkToSub, GraphWalk.edges, ih h'.right_mem]

private theorem isGraphForest_addIsolatedVertex {α : Type u} {β : Type v} {H' : Graph α β} {v : α}
    (hF : IsGraphForest H') : IsGraphForest (addIsolatedVertex H' v) := by
  intro u W hW
  cases W with
  | nil _ => rfl
  | cons h rest =>
    have h' : H'.IsLink _ _ _ := h
    have hu : u ∈ V(H') := h'.left_mem
    let W' : GraphWalk H' u u := walkToSub hu (.cons h rest)
    have hW' : W'.IsSimpleClosed := by
      refine ⟨?_, ?_⟩
      · rw [support_walkToSub]
        exact hW.1
      · rw [edges_walkToSub]
        exact hW.2
    have hlen : (GraphWalk.cons h rest).length = W'.length := by
      simp [GraphWalk.length, W']
    rw [hlen]
    exact hF u W' hW'

private theorem compOf_addIsolatedVertex_self {α : Type u} {β : Type v} {H' : Graph α β} {v : α}
    (hv : v ∉ V(H')) :
    compOf (addIsolatedVertex H' v) v = Graph.noEdge ({v} : Set α) β := by
  have hreach : reachSet (addIsolatedVertex H' v) v = {v} := by
    ext x
    simp only [reachSet, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨W⟩⟩
      cases W with
      | nil _ => rfl
      | cons h _ =>
        have h' : H'.IsLink _ _ _ := h
        exact absurd h'.left_mem hv
    · rintro rfl
      exact ⟨Or.inr rfl, ⟨.nil (Or.inr rfl)⟩⟩
  refine Graph.ext ?_ fun e x y => ?_
  · simp [compOf, hreach]
  · simp only [compOf, induce_isLink, hreach, mem_singleton_iff, noEdge_isLink, iff_false, not_and]
    intro hlink hx _
    have h' : H'.IsLink _ _ _ := hlink
    exact hv (hx ▸ h'.left_mem)

private theorem isGraphComponent_noEdge_addIsolatedVertex {α : Type u} {β : Type v}
    {H' : Graph α β} {v : α} (hv : v ∉ V(H')) :
    IsGraphComponent (Graph.noEdge ({v} : Set α) β) (addIsolatedVertex H' v) := by
  rw [← compOf_addIsolatedVertex_self hv]
  exact isGraphComponent_compOf (Or.inr rfl)

private theorem compOf_addIsolatedVertex_of_mem {α : Type u} {β : Type v}
    {H' : Graph α β} {v x : α} (hx : x ∈ V(H')) :
    compOf (addIsolatedVertex H' v) x = compOf H' x := by
  have hreach : reachSet (addIsolatedVertex H' v) x = reachSet H' x := by
    ext y
    simp only [reachSet, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨W⟩⟩
      let W' := walkToSub hx W
      exact ⟨W'.mem_vertexSet_of_mem_support W'.end_mem_support, ⟨W'⟩⟩
    · rintro ⟨hy, ⟨W⟩⟩
      exact ⟨Or.inl hy, ⟨W.mono (le_addIsolatedVertex H' v)⟩⟩
  refine Graph.ext ?_ fun e a b => ?_
  · simp [compOf, hreach]
  · rw [compOf, compOf, induce_isLink, induce_isLink, hreach]
    rfl

private theorem isGraphComponent_addIsolatedVertex_iff {α : Type u} {β : Type v}
    {H' K : Graph α β} {v : α} (hv : v ∉ V(H')) :
    IsGraphComponent K (addIsolatedVertex H' v) ↔
      K = Graph.noEdge ({v} : Set α) β ∨ IsGraphComponent K H' := by
  constructor
  · intro hK
    obtain ⟨x, hxK⟩ := hK.2.1.1
    have hx_mem : x ∈ V(H') ∪ {v} := hK.1.vertexSet_mono hxK
    rcases hx_mem with hxH' | rfl
    · right
      rw [hK.eq_compOf_of_mem hxK, compOf_addIsolatedVertex_of_mem hxH']
      exact isGraphComponent_compOf hxH'
    · left
      rw [hK.eq_compOf_of_mem hxK, compOf_addIsolatedVertex_self hv]
  · rintro (rfl | hK)
    · exact isGraphComponent_noEdge_addIsolatedVertex hv
    · obtain ⟨x, hxK⟩ := hK.2.1.1
      have hxH' : x ∈ V(H') := hK.1.vertexSet_mono hxK
      rw [hK.eq_compOf_of_mem hxK, ← compOf_addIsolatedVertex_of_mem hxH']
      exact isGraphComponent_compOf (Or.inl hxH')

/-- **Graph Minors VI, (3.3)(i)** (page 120):
"If $|\delta| = 1$ for some $\delta \in \Delta$, and $\delta = \{v\}$ say, then $\Delta$ is feasible
in $G$ if and only if $\Delta - \{\delta\}$ is feasible in the graph obtained from $G$ by deleting
$v$." -/
theorem theorem_3_3_i : Statement33i.{u, v} := by
  classical
  intro α β G Δ v hΔ hΔ_sub hv_mem
  have hv_in_G : v ∈ V(G) := hΔ_sub ⟨{v}, hv_mem, rfl⟩
  have hΔ'_div : IsDivision (Δ \ {{v}}) :=
    ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
  have hΔ'_sub : divisionUnion (Δ \ {{v}}) ⊆ V(G.deleteVerts {v}) := by
    rintro x ⟨δ, ⟨hδ, hδ_ne⟩, hxδ⟩
    rw [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
    refine ⟨hΔ_sub ⟨δ, hδ, hxδ⟩, ?_⟩
    rintro rfl
    exact (hΔ.2.2 hδ hv_mem hδ_ne).ne_of_mem hxδ rfl rfl
  constructor
  · rintro ⟨H, _, _, hHG, hF, H_comp, hinj, hcomp, hcomps_eq⟩
    let Cv := H_comp {v}
    have hCv_comp : IsGraphComponent Cv H := (hcomp {v} hv_mem).1
    have hv_in_Cv : v ∈ V(Cv) := (hcomp {v} hv_mem).2 rfl
    let H' := H.deleteVerts V(Cv)
    refine ⟨H', hΔ'_div, hΔ'_sub, ?_, isGraphForest_of_le deleteVerts_le hF, H_comp,
      hinj.mono sdiff_subset, ?_, ?_⟩
    · refine ⟨?_, fun e x y hlink => ?_⟩
      · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
        exact sdiff_subset_sdiff hHG.vertexSet_mono (singleton_subset_iff.mpr hv_in_Cv)
      · rw [deleteVerts_isLink] at hlink ⊢
        exact ⟨hlink.1.mono hHG, fun hxv => hlink.2.1 (mem_singleton_iff.mp hxv ▸ hv_in_Cv),
          fun hyv => hlink.2.2 (mem_singleton_iff.mp hyv ▸ hv_in_Cv)⟩
    · intro δ hδ
      have hne : H_comp δ ≠ Cv := fun heq => hδ.2 (hinj hδ.1 hv_mem heq)
      exact ⟨(isGraphComponent_deleteVerts_iff hCv_comp).mpr ⟨(hcomp δ hδ.1).1, hne⟩,
        (hcomp δ hδ.1).2⟩
    · ext K
      change IsGraphComponent K (H.deleteVerts V(Cv)) ↔ K ∈ H_comp '' (Δ \ {{v}})
      rw [isGraphComponent_deleteVerts_iff hCv_comp, mem_image]
      constructor
      · rintro ⟨hKH, hne⟩
        have hK_mem : K ∈ graphComponents H := hKH
        rw [hcomps_eq] at hK_mem
        obtain ⟨δ, hδ, rfl⟩ := hK_mem
        exact ⟨δ, ⟨hδ, fun h => hne (congrArg H_comp (mem_singleton_iff.mp h))⟩, rfl⟩
      · rintro ⟨δ, ⟨hδ, hδ_ne⟩, rfl⟩
        exact ⟨(hcomp δ hδ).1, fun heq => hδ_ne (hinj hδ hv_mem heq)⟩
  · rintro ⟨H', _, _, hH'G, hF', H'_comp, hinj', hcomp', hcomps'_eq⟩
    have hv_not_H' : v ∉ V(H') := by
      intro hvH'
      have := hH'G.vertexSet_mono hvH'
      rw [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] at this
      exact this.2 rfl
    let H := addIsolatedVertex H' v
    let H_comp : Set α → Graph α β := fun δ =>
      if δ = {v} then Graph.noEdge ({v} : Set α) β else H'_comp δ
    have hnoEdge_not_H' : ∀ δ ∈ Δ \ {{v}}, H'_comp δ ≠ Graph.noEdge ({v} : Set α) β := by
      intro δ hδ heq
      have hsub : V(H'_comp δ) ⊆ V(H') := (hcomp' δ hδ).1.1.vertexSet_mono
      have hv_in : v ∈ V(H'_comp δ) := by rw [heq]; exact rfl
      exact hv_not_H' (hsub hv_in)
    refine ⟨H, hΔ, hΔ_sub, ?_, isGraphForest_addIsolatedVertex hF', H_comp, ?_, ?_, ?_⟩
    · refine ⟨union_subset (hH'G.vertexSet_mono.trans ?_)
        (singleton_subset_iff.mpr hv_in_G), fun e x y hlink => ?_⟩
      · rw [vertexSet_deleteVerts]
        exact sdiff_subset
      · have h' : H'.IsLink e x y := hlink
        exact (h'.mono hH'G).mono deleteVerts_le
    · intro δ₁ hδ₁ δ₂ hδ₂ heq
      dsimp only [H_comp] at heq
      by_cases h1 : δ₁ = {v} <;> by_cases h2 : δ₂ = {v}
      · rw [h1, h2]
      · simp only [h1, h2, ↓reduceIte] at heq
        exact absurd heq.symm (hnoEdge_not_H' δ₂ ⟨hδ₂, h2⟩)
      · simp only [h1, h2, ↓reduceIte] at heq
        exact absurd heq (hnoEdge_not_H' δ₁ ⟨hδ₁, h1⟩)
      · simp only [h1, h2, ↓reduceIte] at heq
        exact hinj' ⟨hδ₁, h1⟩ ⟨hδ₂, h2⟩ heq
    · intro δ hδ
      dsimp only [H_comp]
      by_cases h : δ = {v}
      · subst h
        simp only [↓reduceIte]
        exact ⟨isGraphComponent_noEdge_addIsolatedVertex hv_not_H', subset_rfl⟩
      · simp only [h, ↓reduceIte]
        exact ⟨(isGraphComponent_addIsolatedVertex_iff hv_not_H').mpr
          (Or.inr (hcomp' δ ⟨hδ, h⟩).1), (hcomp' δ ⟨hδ, h⟩).2⟩
    · ext K
      change IsGraphComponent K (addIsolatedVertex H' v) ↔ K ∈ H_comp '' Δ
      rw [isGraphComponent_addIsolatedVertex_iff hv_not_H', mem_image]
      constructor
      · rintro (rfl | hKH')
        · refine ⟨{v}, hv_mem, ?_⟩
          simp [H_comp]
        · have hK_mem : K ∈ graphComponents H' := hKH'
          rw [hcomps'_eq] at hK_mem
          obtain ⟨δ, ⟨hδ, hδ_ne⟩, rfl⟩ := hK_mem
          refine ⟨δ, hδ, ?_⟩
          have hne : δ ≠ {v} := fun h => hδ_ne (mem_singleton_iff.mpr h)
          simp [H_comp, hne]
      · rintro ⟨δ, hδ, rfl⟩
        dsimp only [H_comp]
        by_cases h : δ = {v}
        · simp [h]
        · simp only [h, ↓reduceIte]
          exact Or.inr (hcomp' δ ⟨hδ, h⟩).1

/-- **Graph Minors VI, (3.3)(ii)** (page 120):
"If $G$ has a component $G'$ with no vertex in $\operatorname{bd}(\Sigma)$ then $\Delta$ is feasible
in $G$ if and only if it is feasible in the graph obtained from $G$ by deleting $V(G')$." -/
theorem theorem_3_3_ii : Statement33ii.{u} := by
  intro S _ G G' Δ hΔ hΔ_sub hG'_comp hdisj
  have hΔ_del : divisionUnion Δ ⊆ V(G.toGraph.deleteVerts V(G')) := by
    intro x hx
    have hx_bd : x ∈ G.V ∩ bd S := hΔ_sub hx
    rw [vertexSet_deleteVerts]
    exact ⟨hx_bd.1, disjoint_right.mp hdisj hx_bd.2⟩
  constructor
  · rintro ⟨H, _, _, hHG, hF, H_comp, hinj, hcomp, hcomps_eq⟩
    have hH_disj : Disjoint V(H) V(G') := by
      refine disjoint_left.mpr fun x hxH hxG' => ?_
      have hcomp_x : compOf H x ∈ graphComponents H := isGraphComponent_compOf hxH
      rw [hcomps_eq] at hcomp_x
      obtain ⟨δ, hδ, hcomp_eq⟩ := hcomp_x
      have hx_in_δcomp : x ∈ V(H_comp δ) := by
        rw [hcomp_eq]
        exact self_mem_reachSet hxH
      obtain ⟨y, hyδ⟩ := hΔ.2.1 δ hδ
      have hy_bd : y ∈ G.V ∩ bd S := hΔ_sub ⟨δ, hδ, hyδ⟩
      have hy_in_δcomp : y ∈ V(H_comp δ) := (hcomp δ hδ).2 hyδ
      have hle_G' : H_comp δ ≤ G' :=
        hG'_comp.le_of_isGraphConnected ((hcomp δ hδ).1.1.trans hHG) (hcomp δ hδ).1.2.1
          hx_in_δcomp hxG'
      exact disjoint_left.mp hdisj (hle_G'.vertexSet_mono hy_in_δcomp) hy_bd.2
    have hH_le : H ≤ G.toGraph.deleteVerts V(G') := by
      refine ⟨?_, fun e u v hlink => ?_⟩
      · rw [vertexSet_deleteVerts]
        exact subset_sdiff.mpr ⟨hHG.vertexSet_mono, hH_disj⟩
      · rw [deleteVerts_isLink]
        exact ⟨hlink.mono hHG, disjoint_left.mp hH_disj hlink.left_mem,
          disjoint_left.mp hH_disj hlink.right_mem⟩
    exact ⟨H, hΔ, hΔ_del, hH_le, hF, H_comp, hinj, hcomp, hcomps_eq⟩
  · rintro ⟨H, _, _, hH_del, hF, H_comp, hinj, hcomp, hcomps_eq⟩
    exact ⟨H, hΔ, hΔ_sub.trans inter_subset_left, hH_del.trans deleteVerts_le,
      hF, H_comp, hinj, hcomp, hcomps_eq⟩

/-- **Graph Minors VI, (3.3)(iii)** (page 121):
"If there exists $\delta \in \Delta$ which intersects more than one component of $G$ then $\Delta$
is not feasible in $G$." -/
theorem theorem_3_3_iii : Statement33iii.{u, v} := by
  intro α β G Δ δ G₁ G₂ hδ hG₁ hG₂ hne ⟨u, huδ, huG₁⟩ ⟨v, hvδ, hvG₂⟩ ⟨H, _, _, hHG, _, H_comp, _,
    hcomp, _⟩
  have hu_comp : u ∈ V(H_comp δ) := (hcomp δ hδ).2 huδ
  have hv_comp : v ∈ V(H_comp δ) := (hcomp δ hδ).2 hvδ
  have hle₁ : H_comp δ ≤ G₁ :=
    hG₁.le_of_isGraphConnected ((hcomp δ hδ).1.1.trans hHG) (hcomp δ hδ).1.2.1 hu_comp huG₁
  have hvG₁ : v ∈ V(G₁) := hle₁.vertexSet_mono hv_comp
  exact hne (hG₁.eq_of_mem_mem hG₂ hvG₁ hvG₂)

/-- Union of a finite family of pairwise vertex-disjoint and edge-disjoint subgraphs of `G`. -/
def graphUnionFamily {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (H_fam : Fin k → Graph α β) : Graph α β :=
  (G.restrict (⋃ i : Fin k, E(H_fam i))).induce (⋃ i : Fin k, V(H_fam i))

theorem graphUnionFamily_le {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (H_fam : Fin k → Graph α β) (hle : ∀ i : Fin k, H_fam i ≤ G) :
    graphUnionFamily G H_fam ≤ G := by
  refine (induce_le ?_).trans restrict_le
  exact iUnion_subset fun i => (hle i).vertexSet_mono

theorem le_graphUnionFamily {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (H_fam : Fin k → Graph α β) (hle : ∀ i : Fin k, H_fam i ≤ G) (i : Fin k) :
    H_fam i ≤ graphUnionFamily G H_fam := by
  refine ⟨subset_iUnion (fun j => V(H_fam j)) i, fun e x y hlink => ?_⟩
  simp only [graphUnionFamily, induce_isLink, restrict_isLink, mem_iUnion]
  exact ⟨⟨⟨i, hlink.edge_mem⟩, hlink.mono (hle i)⟩, ⟨i, hlink.left_mem⟩, ⟨i, hlink.right_mem⟩⟩

theorem graphUnionFamily_isLink_iff {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (H_fam : Fin k → Graph α β) (hle : ∀ i : Fin k, H_fam i ≤ G)
    (_hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {e : β} {x y : α} :
    (graphUnionFamily G H_fam).IsLink e x y ↔ ∃ i : Fin k, (H_fam i).IsLink e x y := by
  simp only [graphUnionFamily, induce_isLink, restrict_isLink, mem_iUnion]
  constructor
  · rintro ⟨⟨⟨i, hei⟩, hGlink⟩, _, _⟩
    exact ⟨i, ((hle i).isLink_iff hei).mpr hGlink⟩
  · rintro ⟨i, hlink⟩
    exact ⟨⟨⟨i, hlink.edge_mem⟩, hlink.mono (hle i)⟩,
      ⟨i, hlink.left_mem⟩, ⟨i, hlink.right_mem⟩⟩

private def walkUnionToMember {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {i : Fin k} {x y : α} (hx : x ∈ V(H_fam i)) :
    GraphWalk (graphUnionFamily G H_fam) x y → GraphWalk (H_fam i) x y
  | .nil _ => .nil hx
  | .cons h rest =>
    have hlink_i : (H_fam i).IsLink _ x _ := by
      obtain ⟨j, hj⟩ := (graphUnionFamily_isLink_iff G H_fam hle hE_disj).mp h
      rcases eq_or_ne i j with rfl | hne
      · exact hj
      · exact absurd hj.left_mem (disjoint_left.mp (hV_disj hne) hx)
    .cons hlink_i (walkUnionToMember hle hV_disj hE_disj hlink_i.right_mem rest)

@[simp]
private theorem support_walkUnionToMember {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {i : Fin k} {x y : α} (hx : x ∈ V(H_fam i))
    (W : GraphWalk (graphUnionFamily G H_fam) x y) :
    (walkUnionToMember hle hV_disj hE_disj hx W).support = W.support := by
  induction W with
  | nil _ => rfl
  | cons h rest ih =>
    simp [walkUnionToMember, GraphWalk.support, ih]

@[simp]
private theorem edges_walkUnionToMember {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {i : Fin k} {x y : α} (hx : x ∈ V(H_fam i))
    (W : GraphWalk (graphUnionFamily G H_fam) x y) :
    (walkUnionToMember hle hV_disj hE_disj hx W).edges = W.edges := by
  induction W with
  | nil _ => rfl
  | cons h rest ih =>
    simp [walkUnionToMember, GraphWalk.edges, ih]

theorem isGraphForest_graphUnionFamily {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    (hF : ∀ i : Fin k, IsGraphForest (H_fam i)) :
    IsGraphForest (graphUnionFamily G H_fam) := by
  intro u W hW
  cases W with
  | nil _ => rfl
  | cons h rest =>
    obtain ⟨i, hi⟩ := (graphUnionFamily_isLink_iff G H_fam hle hE_disj).mp h
    let W' := walkUnionToMember hle hV_disj hE_disj hi.left_mem (.cons h rest)
    have hW' : W'.IsSimpleClosed := by
      refine ⟨?_, ?_⟩
      · rw [support_walkUnionToMember]
        exact hW.1
      · rw [edges_walkUnionToMember]
        exact hW.2
    have hlen : (GraphWalk.cons h rest).length = W'.length := by
      simp [GraphWalk.length, W']
    rw [hlen]
    exact hF i u W' hW'

theorem compOf_graphUnionFamily_of_mem {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {i : Fin k} {x : α} (hx : x ∈ V(H_fam i)) :
    compOf (graphUnionFamily G H_fam) x = compOf (H_fam i) x := by
  have hreach : reachSet (graphUnionFamily G H_fam) x = reachSet (H_fam i) x := by
    ext y
    simp only [reachSet, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨W⟩⟩
      let W' := walkUnionToMember hle hV_disj hE_disj hx W
      exact ⟨W'.mem_vertexSet_of_mem_support W'.end_mem_support, ⟨W'⟩⟩
    · rintro ⟨hy, ⟨W⟩⟩
      exact ⟨mem_iUnion.mpr ⟨i, hy⟩, ⟨W.mono (le_graphUnionFamily G H_fam hle i)⟩⟩
  refine Graph.ext ?_ fun e a b => ?_
  · simp [compOf, hreach]
  · rw [compOf, compOf, induce_isLink, induce_isLink, hreach,
      graphUnionFamily_isLink_iff G H_fam hle hE_disj]
    constructor
    · rintro ⟨⟨j, hj⟩, ha, hb⟩
      rcases eq_or_ne i j with rfl | hne
      · exact ⟨hj, ha, hb⟩
      · exact absurd hj.left_mem (disjoint_left.mp (hV_disj hne) ha.1)
    · rintro ⟨hi, ha, hb⟩
      exact ⟨⟨i, hi⟩, ha, hb⟩

theorem isGraphComponent_graphUnionFamily_iff {α : Type u} {β : Type v} {k : ℕ}
    {G : Graph α β} {H_fam : Fin k → Graph α β} (hle : ∀ i : Fin k, H_fam i ≤ G)
    (hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j))
    (hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j))
    {K : Graph α β} :
    IsGraphComponent K (graphUnionFamily G H_fam) ↔
      ∃ i : Fin k, IsGraphComponent K (H_fam i) := by
  constructor
  · intro hK
    obtain ⟨x, hxK⟩ := hK.2.1.1
    have hxU : x ∈ ⋃ i : Fin k, V(H_fam i) := hK.1.vertexSet_mono hxK
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    refine ⟨i, ?_⟩
    rw [hK.eq_compOf_of_mem hxK, compOf_graphUnionFamily_of_mem hle hV_disj hE_disj hxi]
    exact isGraphComponent_compOf hxi
  · rintro ⟨i, hK⟩
    obtain ⟨x, hxK⟩ := hK.2.1.1
    have hxi : x ∈ V(H_fam i) := hK.1.vertexSet_mono hxK
    rw [hK.eq_compOf_of_mem hxK, ← compOf_graphUnionFamily_of_mem hle hV_disj hE_disj hxi]
    exact isGraphComponent_compOf (mem_iUnion.mpr ⟨i, hxi⟩)

/-- **Graph Minors VI, (3.3)(iv)** (page 121):
"If $G$ has components $G_1, \dots, G_k$ for $k \ge 2$, and (ii), (iii) do not apply, let
$(\Delta_1, \dots, \Delta_k)$ be the partition of $\Delta$ such that* $$\bigcup \Delta_i =
V(G_i) \cap bd(\Sigma) \qquad (1 \le i \le k);$$ *then $\Delta$ is feasible in $G$ if and
only if $\Delta_i$ is feasible in $G_i$ for each $i$." -/
theorem theorem_3_3_iv : Statement33iv.{u} := by
  classical
  intro S _ G Δ k G_comp Δ_part _hk hΔ hΔ_union hinj_G hG_comps hΔ_part hΔ_cov
  have hG_comp : ∀ i : Fin k, IsGraphComponent (G_comp i) G.toGraph := by
    intro i
    have hmem : G_comp i ∈ graphComponents G.toGraph := by
      rw [hG_comps]
      exact mem_range_self i
    exact hmem
  have hG_V_disj : Pairwise fun i j : Fin k => Disjoint V(G_comp i) V(G_comp j) :=
    fun _ _ hne => (hG_comp _).disjoint_vertexSet_of_ne (hG_comp _)
      (fun heq => hne (hinj_G trivial trivial heq))
  have hG_E_disj : Pairwise fun i j : Fin k => Disjoint E(G_comp i) E(G_comp j) :=
    fun _ _ hne => (hG_comp _).disjoint_edgeSet_of_ne (hG_comp _)
      (fun heq => hne (hinj_G trivial trivial heq))
  have hsub_part : ∀ i : Fin k, Δ_part i ⊆ Δ := by
    intro i δ hδ
    rw [hΔ_part i] at hδ
    exact hδ.1
  have hΔ_part_div : ∀ i : Fin k, IsDivision (Δ_part i) := by
    intro i
    exact ⟨hΔ.1.subset (hsub_part i), fun δ hδ => hΔ.2.1 δ (hsub_part i hδ),
      hΔ.2.2.subset (hsub_part i)⟩
  have hΔ_part_sub : ∀ i : Fin k, divisionUnion (Δ_part i) ⊆ V(G_comp i) := by
    intro i x ⟨δ, hδ, hxδ⟩
    rw [hΔ_part i] at hδ
    exact hδ.2 hxδ
  have hΔ_uniq_i : ∀ δ ∈ Δ, ∀ i j : Fin k, δ ⊆ V(G_comp i) → δ ⊆ V(G_comp j) → i = j := by
    intro δ hδ i j hi hj
    obtain ⟨x, hxδ⟩ := hΔ.2.1 δ hδ
    by_contra hne
    exact disjoint_left.mp (hG_V_disj hne) (hi hxδ) (hj hxδ)
  constructor
  · rintro ⟨H, _, _, hHG, hF, H_comp, hinj_H, hcomp_H, hcomps_H⟩ i
    have hH_comp_in_Gi : ∀ δ ∈ Δ, ∀ j : Fin k, δ ⊆ V(G_comp j) → H_comp δ ≤ G_comp j := by
      intro δ hδ j hsub
      obtain ⟨y, hyδ⟩ := hΔ.2.1 δ hδ
      exact (hG_comp j).le_of_isGraphConnected ((hcomp_H δ hδ).1.1.trans hHG)
        (hcomp_H δ hδ).1.2.1 ((hcomp_H δ hδ).2 hyδ) (hsub hyδ)
    let H_i := H.induce (V(H) ∩ V(G_comp i))
    have hHi_le_H : H_i ≤ H := H.induce_le inter_subset_left
    have hHi_le_Gi : H_i ≤ G_comp i := by
      refine ⟨inter_subset_right, fun e x y hlink => ?_⟩
      exact ((hG_comp i).isLink_iff_of_mem hlink.2.1.2).mpr (hlink.1.mono hHG)
    have hcomp_in_Hi : ∀ K : Graph S (Set S),
        IsGraphComponent K H_i ↔ ∃ δ ∈ Δ_part i, K = H_comp δ := by
      intro K
      constructor
      · intro hK
        obtain ⟨x, hxK⟩ := hK.2.1.1
        have hx_mem : x ∈ V(H) ∩ V(G_comp i) := hK.1.vertexSet_mono hxK
        have hcomp_x : compOf H x ∈ graphComponents H := isGraphComponent_compOf hx_mem.1
        rw [hcomps_H] at hcomp_x
        obtain ⟨δ, hδ, hcomp_eq⟩ := hcomp_x
        obtain ⟨j, hj⟩ := hΔ_cov δ hδ
        have hle_j : H_comp δ ≤ G_comp j := hH_comp_in_Gi δ hδ j hj
        have hx_in_δ : x ∈ V(H_comp δ) := by
          rw [hcomp_eq]
          exact self_mem_reachSet hx_mem.1
        have hij : i = j := by
          by_contra hne
          exact disjoint_left.mp (hG_V_disj hne) hx_mem.2 (hle_j.vertexSet_mono hx_in_δ)
        subst hij
        have hδ_in_part : δ ∈ Δ_part i := by
          rw [hΔ_part i]
          exact ⟨hδ, hj⟩
        have hδ_le_Hi : H_comp δ ≤ H_i := by
          refine ⟨subset_inter (hcomp_H δ hδ).1.1.vertexSet_mono hle_j.vertexSet_mono,
            fun e u v hlink => ?_⟩
          exact ⟨hlink.mono (hcomp_H δ hδ).1.1,
            ⟨(hcomp_H δ hδ).1.1.vertexSet_mono hlink.left_mem,
              hle_j.vertexSet_mono hlink.left_mem⟩,
            ⟨(hcomp_H δ hδ).1.1.vertexSet_mono hlink.right_mem,
              hle_j.vertexSet_mono hlink.right_mem⟩⟩
        have hK_le_δ : K ≤ H_comp δ :=
          (hcomp_H δ hδ).1.le_of_isGraphConnected (hK.1.trans hHi_le_H) hK.2.1 hxK hx_in_δ
        exact ⟨δ, hδ_in_part, (hK.2.2 (H_comp δ) hK_le_δ hδ_le_Hi (hcomp_H δ hδ).1.2.1).symm⟩
      · rintro ⟨δ, hδ_part, rfl⟩
        have hδ_part' := hδ_part
        rw [hΔ_part i] at hδ_part'
        have hle_i : H_comp δ ≤ G_comp i := hH_comp_in_Gi δ hδ_part'.1 i hδ_part'.2
        have hδ_le_Hi : H_comp δ ≤ H_i := by
          refine ⟨subset_inter (hcomp_H δ hδ_part'.1).1.1.vertexSet_mono hle_i.vertexSet_mono,
            fun e u v hlink => ?_⟩
          exact ⟨hlink.mono (hcomp_H δ hδ_part'.1).1.1,
            ⟨(hcomp_H δ hδ_part'.1).1.1.vertexSet_mono hlink.left_mem,
              hle_i.vertexSet_mono hlink.left_mem⟩,
            ⟨(hcomp_H δ hδ_part'.1).1.1.vertexSet_mono hlink.right_mem,
              hle_i.vertexSet_mono hlink.right_mem⟩⟩
        refine ⟨hδ_le_Hi, (hcomp_H δ hδ_part'.1).1.2.1, fun K' hle hK'Hi hK'conn => ?_⟩
        exact (hcomp_H δ hδ_part'.1).1.2.2 K' hle (hK'Hi.trans hHi_le_H) hK'conn
    refine ⟨H_i, hΔ_part_div i, hΔ_part_sub i, hHi_le_Gi, isGraphForest_of_le hHi_le_H hF,
      H_comp, hinj_H.mono (hsub_part i), ?_, ?_⟩
    · intro δ hδ
      exact ⟨(hcomp_in_Hi (H_comp δ)).mpr ⟨δ, hδ, rfl⟩, (hcomp_H δ (hsub_part i hδ)).2⟩
    · ext K
      change IsGraphComponent K H_i ↔ K ∈ H_comp '' Δ_part i
      rw [hcomp_in_Hi, mem_image]
      exact ⟨fun ⟨δ, hδ, heq⟩ => ⟨δ, hδ, heq.symm⟩, fun ⟨δ, hδ, heq⟩ => ⟨δ, hδ, heq.symm⟩⟩
  · intro hFeas
    choose H_fam hReal using hFeas
    have hle_G : ∀ i : Fin k, H_fam i ≤ G.toGraph :=
      fun i => (hReal i).2.2.1.trans (hG_comp i).1
    have hV_disj : Pairwise fun i j : Fin k => Disjoint V(H_fam i) V(H_fam j) :=
      fun i j hne => (hG_V_disj hne).mono (hReal i).2.2.1.vertexSet_mono
        (hReal j).2.2.1.vertexSet_mono
    have hE_disj : Pairwise fun i j : Fin k => Disjoint E(H_fam i) E(H_fam j) :=
      fun i j hne => (hG_E_disj hne).mono (hReal i).2.2.1.edgeSet_mono
        (hReal j).2.2.1.edgeSet_mono
    choose H_comp_fam hinj_fam hcomp_fam hcomps_fam using fun i => (hReal i).2.2.2.2
    have hΔ_cov_all : ∀ δ : Set S, ∃ i : Fin k, δ ∈ Δ → δ ⊆ V(G_comp i) := by
      intro δ
      by_cases hδ : δ ∈ Δ
      · obtain ⟨i, hi⟩ := hΔ_cov δ hδ
        exact ⟨i, fun _ => hi⟩
      · exact ⟨⟨0, by omega⟩, fun h => False.elim (hδ h)⟩
    choose idxOf hidxOf_sub using hΔ_cov_all
    have hidxOf_spec : ∀ δ ∈ Δ, δ ∈ Δ_part (idxOf δ) := by
      intro δ hδ
      rw [hΔ_part (idxOf δ)]
      exact ⟨hδ, hidxOf_sub δ hδ⟩
    have hidxOf_eq : ∀ δ ∈ Δ, ∀ i : Fin k, δ ∈ Δ_part i → idxOf δ = i := by
      intro δ hδ i hi
      rw [hΔ_part i] at hi
      exact hΔ_uniq_i δ hδ (idxOf δ) i (hidxOf_sub δ hδ) hi.2
    let H := graphUnionFamily G.toGraph H_fam
    let H_comp : Set S → Graph S (Set S) := fun δ => H_comp_fam (idxOf δ) δ
    have hΔ_sub_G : divisionUnion Δ ⊆ V(G.toGraph) := by
      rw [hΔ_union]
      exact inter_subset_left
    refine ⟨H, hΔ, hΔ_sub_G,
      graphUnionFamily_le G.toGraph H_fam hle_G,
      isGraphForest_graphUnionFamily hle_G hV_disj hE_disj (fun i => (hReal i).2.2.2.1),
      H_comp, ?_, ?_, ?_⟩
    · intro δ₁ hδ₁ δ₂ hδ₂ heq
      have h1 := hidxOf_spec δ₁ hδ₁
      have h2 := hidxOf_spec δ₂ hδ₂
      obtain ⟨x, hx⟩ := (hcomp_fam (idxOf δ₁) δ₁ h1).1.2.1.1
      have hx1 : x ∈ V(H_fam (idxOf δ₁)) :=
        (hcomp_fam (idxOf δ₁) δ₁ h1).1.1.vertexSet_mono hx
      have hx2 : x ∈ V(H_fam (idxOf δ₂)) := by
        have hx' : x ∈ V(H_comp δ₂) := heq ▸ hx
        exact (hcomp_fam (idxOf δ₂) δ₂ h2).1.1.vertexSet_mono hx'
      have hij : idxOf δ₁ = idxOf δ₂ := by
        by_contra hne
        exact disjoint_left.mp (hV_disj hne) hx1 hx2
      dsimp only [H_comp] at heq
      rw [← hij] at heq h2
      exact hinj_fam (idxOf δ₁) h1 h2 heq
    · intro δ hδ
      have h_part := hidxOf_spec δ hδ
      exact ⟨(isGraphComponent_graphUnionFamily_iff hle_G hV_disj hE_disj).mpr
        ⟨idxOf δ, (hcomp_fam (idxOf δ) δ h_part).1⟩,
        (hcomp_fam (idxOf δ) δ h_part).2⟩
    · ext K
      change IsGraphComponent K (graphUnionFamily G.toGraph H_fam) ↔ K ∈ H_comp '' Δ
      rw [isGraphComponent_graphUnionFamily_iff hle_G hV_disj hE_disj, mem_image]
      constructor
      · rintro ⟨i, hKi⟩
        have hK_mem : K ∈ graphComponents (H_fam i) := hKi
        rw [hcomps_fam i] at hK_mem
        obtain ⟨δ, hδ_i, rfl⟩ := hK_mem
        have hδ : δ ∈ Δ := by rw [hΔ_part i] at hδ_i; exact hδ_i.1
        refine ⟨δ, hδ, ?_⟩
        dsimp only [H_comp]
        rw [hidxOf_eq δ hδ i hδ_i]
      · rintro ⟨δ, hδ, rfl⟩
        exact ⟨idxOf δ, (hcomp_fam (idxOf δ) δ (hidxOf_spec δ hδ)).1⟩

/-- **Graph Minors VI, (3.3)** (pages 120–121):
"(3.3) (i) *If $|\delta| = 1$ for some $\delta \in \Delta$, and $\delta = \{v\}$ say, then $\Delta$
is feasible in $G$ if and only if $\Delta - \{\delta\}$ is feasible in the graph obtained from $G$
by deleting $v$.*
(ii) *If $G$ has a component $G'$ with no vertex in $bd(\Sigma)$ then $\Delta$ is feasible in $G$ if
and only if it is feasible in the graph obtained from $G$ by deleting $V(G')$.*
(iii) *If there exists $\delta \in \Delta$ which intersects more than one component of $G$ then
$\Delta$ is not feasible in $G$.*
(iv) *If $G$ has components $G_1, \dots, G_k$ for $k \ge 2$, and (ii), (iii) do not apply, let
$(\Delta_1, \dots, \Delta_k)$ be the partition of $\Delta$ such that* $$\bigcup \Delta_i = V(G_i)
\cap bd(\Sigma) \qquad (1 \le i \le k);$$ *then $\Delta$ is feasible in $G$ if and only if
$\Delta_i$
is feasible in $G_i$ for each $i$.*" -/
theorem theorem_3_3_proof :
    Statement33i.{u, v} ∧ Statement33ii.{u} ∧ Statement33iii.{u, v} ∧ Statement33iv.{u} :=
  ⟨theorem_3_3_i, theorem_3_3_ii, theorem_3_3_iii, theorem_3_3_iv⟩

/-! ## 4. Proof of Theorem (3.5) -/

private theorem not_compactSpace_Ioo : ¬ CompactSpace (Ioo (0 : ℝ) 1) := by
  intro h
  have hcomp : IsCompact (Ioo (0 : ℝ) 1) := isCompact_iff_compactSpace.mpr h
  have hcl : IsClosed (Ioo (0 : ℝ) 1) := hcomp.isClosed
  have hmem : (0 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    rw [← hcl.closure_eq, closure_Ioo zero_ne_one]
    exact left_mem_Icc.mpr zero_le_one
  exact lt_irrefl 0 hmem.1

theorem nonempty_of_mem_segmentsOf {S : Type u} [TopologicalSpace S] {C V seg : Set S}
    (hC : IsOArc C) (hseg : seg ∈ segmentsOf C V) : V.Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  subst hne
  obtain ⟨φ⟩ := hC
  have hEmpty : oArcMap φ '' (∅ : Set Circle) = ∅ := image_empty _
  rw [← hEmpty, segmentsOf_oArcMap] at hseg
  obtain ⟨seg₀, ⟨⟨z, _, rfl⟩, ⟨e⟩⟩, _⟩ := hseg
  have hseg₀_univ : connectedComponentIn ((univ : Set Circle) \ ∅) z = univ := by
    rw [sdiff_empty, connectedComponentIn_univ]
    exact PreconnectedSpace.connectedComponent_eq_univ z
  rw [hseg₀_univ] at e
  have hcomp : CompactSpace (Ioo (0 : ℝ) 1) :=
    (e.trans (Homeomorph.Set.univ Circle)).symm.compactSpace
  exact not_compactSpace_Ioo hcomp

theorem connectedComponentIn_mem_segmentsOf {S : Type u} [TopologicalSpace S]
    {C V : Set S} (hC : IsOArc C) (hV_fin : V.Finite) (hV_sub : V ⊆ C) (hV_ne : V.Nonempty)
    {w : S} (hw : w ∈ C \ V) :
    connectedComponentIn (C \ V) w ∈ segmentsOf C V := by
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  let V₀ := oArcMap φ ⁻¹' V
  have hV_eq : oArcMap φ '' V₀ = V :=
    image_preimage_eq_of_subset (hV_sub.trans (range_oArcMap φ).symm.subset)
  have hV₀_fin : V₀.Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rwa [hV_eq]
  have hV₀_ne : V₀.Nonempty := by
    obtain ⟨v, hv⟩ := hV_ne
    rw [← hV_eq] at hv
    obtain ⟨v₀, hv₀, _⟩ := hv
    exact ⟨v₀, hv₀⟩
  let w₀ := φ.symm ⟨w, hw.1⟩
  have hw₀_map : oArcMap φ w₀ = w := by simp [oArcMap, w₀]
  have hw₀_compl : w₀ ∈ V₀ᶜ := by
    intro h
    apply hw.2
    rw [← hV_eq, ← hw₀_map]
    exact mem_image_of_mem (oArcMap φ) h
  rw [← hV_eq, segmentsOf_oArcMap, diff_image_oArcMap]
  refine ⟨connectedComponentIn V₀ᶜ w₀, ?_, ?_⟩
  · obtain ⟨v₀, ⟨hv₀, hw₀v₀⟩, _⟩ := exists_unique_nextSegment_of_mem_compl hV₀_fin hV₀_ne hw₀_compl
    rw [connectedComponentIn_compl_eq_nextSegment hV₀_fin hv₀ hw₀v₀]
    exact nextSegment_mem_segmentsOf_univ hV₀_fin hv₀
  · rw [← hw₀_map, isEmbedding_image_connectedComponentIn hemb hw₀_compl]

/-- In a dual drawing pair `(G, G_dual)` on a closed disc `S`, a dual vertex `w ∈ r ∩ G_dual.V`
(for `r ∈ G.R`) lies in `bd S` if and only if `r` is peripheral in `G`. -/
private theorem dual_vertex_mem_bd_iff_peripheral {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hC : IsOArc (bd S)) (hDual : IsDiscDualDrawingPair G G_dual)
    {r : Set S} (hr : r ∈ G.R) {w : S} (hw : w ∈ r ∧ w ∈ G_dual.V) :
    w ∈ bd S ↔ ∃ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), seg ⊆ r := by
  have hG_prop : G.IsProper := hDual.1
  have hV_disj : G.V ∩ G_dual.V = ∅ := hDual.2.2.1
  have hR_uniq := hDual.2.2.2.1
  have hU1 : IsDualPointSet (bd S) (G.V ∩ bd S) (G_dual.V ∩ bd S) :=
    hDual.2.2.2.2.2.2.2.2.1
  have hbd_sub_compl : bd S \ (G.V ∩ bd S) ⊆ univ \ G.U := by
    rintro z ⟨hz_bd, hz_not⟩
    refine ⟨trivial, fun hzU => hz_not ⟨hG_prop ⟨hz_bd, hzU⟩, hz_bd⟩⟩
  have hr_eq : r = connectedComponentIn (univ \ G.U) w := by
    obtain ⟨z, hz, rfl⟩ := hr
    exact connectedComponentIn_eq hw.1
  constructor
  · intro hw_bd
    have hw_not_V : w ∉ G.V := fun hwV => by
      have : w ∈ G.V ∩ G_dual.V := ⟨hwV, hw.2⟩
      rw [hV_disj] at this
      exact this
    have hw_diff : w ∈ bd S \ (G.V ∩ bd S) := ⟨hw_bd, fun h => hw_not_V h.1⟩
    have hV_ne : (G.V ∩ bd S).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hEmpty := hU1.1 hne
      have hw_in : w ∈ G_dual.V ∩ bd S := ⟨hw.2, hw_bd⟩
      rw [hEmpty] at hw_in
      exact hw_in
    have hV_fin : (G.V ∩ bd S).Finite := G.finite_V.subset inter_subset_left
    refine ⟨connectedComponentIn (bd S \ (G.V ∩ bd S)) w,
      connectedComponentIn_mem_segmentsOf hC hV_fin inter_subset_right hV_ne hw_diff, ?_⟩
    rw [hr_eq]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hw_diff)
      ((connectedComponentIn_subset _ _).trans hbd_sub_compl)
  · rintro ⟨seg, hseg, hseg_sub⟩
    have hV_ne : (G.V ∩ bd S).Nonempty := nonempty_of_mem_segmentsOf hC hseg
    have hcard := (hU1.2 hV_ne).2 seg hseg
    obtain ⟨w', hw'_mem⟩ := nonempty_of_ncard_ne_zero (by omega : ((G_dual.V ∩ bd S) ∩ seg).ncard ≠
      0)
    have hw'_eq : w' = w :=
      (hR_uniq r hr).unique ⟨hseg_sub hw'_mem.2, hw'_mem.1.1⟩ hw
    exact hw'_eq ▸ hw'_mem.1.2

open Classical in
/-- Map a chain term of `G_dual` to the corresponding chain term of `G`. -/
private noncomputable def dualChainTerm {S : Type u} [TopologicalSpace S] (G : Drawing S) :
    ChainTerm S → ChainTerm S
  | .inl w => .inr (connectedComponentIn (univ \ G.U) w)
  | .inr r_dual =>
    if h : ∃ v, v ∈ r_dual ∧ v ∈ G.V then .inl (Classical.choose h) else .inr r_dual

private theorem dualChainTerm_inr_eq {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {r_dual : Set S} (hr : r_dual ∈ G_dual.R) {v : S} (hv : v ∈ r_dual ∧ v ∈ G.V) :
    dualChainTerm G (.inr r_dual) = .inl v := by
  have hex : ∃ v', v' ∈ r_dual ∧ v' ∈ G.V := ⟨v, hv⟩
  dsimp only [dualChainTerm]
  simp only [hex, ↓reduceDIte]
  congr 1
  exact (hDual.2.2.2.2.2.1 r_dual hr).unique (Classical.choose_spec hex) hv

private theorem dualChainTerm_valid {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {t : ChainTerm S} (ht : t.IsValid G_dual) :
    (dualChainTerm G t).IsValid G := by
  cases t with
  | inl w =>
    obtain ⟨r, hr, hwr⟩ := hDual.2.2.2.2.1 w ht
    obtain ⟨z, hz, rfl⟩ := hr
    have heq : connectedComponentIn (univ \ G.U) w = connectedComponentIn (univ \ G.U) z :=
      (connectedComponentIn_eq hwr).symm
    dsimp only [dualChainTerm, ChainTerm.IsValid]
    rw [heq]
    exact ⟨z, hz, rfl⟩
  | inr r_dual =>
    obtain ⟨v, hv, _⟩ := hDual.2.2.2.2.2.1 r_dual ht
    rw [dualChainTerm_inr_eq hDual ht hv]
    exact hv.2

private theorem dualChainTerm_isVertex_iff {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {t : ChainTerm S} (ht : t.IsValid G_dual) :
    (dualChainTerm G t).IsVertex ↔ ¬ t.IsVertex := by
  cases t with
  | inl w =>
    simp [dualChainTerm, ChainTerm.IsVertex]
  | inr r_dual =>
    obtain ⟨v, hv, _⟩ := hDual.2.2.2.2.2.1 r_dual ht
    rw [dualChainTerm_inr_eq hDual ht hv]
    simp [ChainTerm.IsVertex]

private theorem dualChainTerm_areIncident {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {t₁ t₂ : ChainTerm S} (hinc : ChainTerm.AreIncident G_dual t₁ t₂) :
    ChainTerm.AreIncident G (dualChainTerm G t₁) (dualChainTerm G t₂) := by
  cases t₁ with
  | inl w =>
    cases t₂ with
    | inl _ => exact False.elim hinc
    | inr r_dual =>
      rcases hinc with ⟨hw, hr_dual, hw_cl⟩
      obtain ⟨r, hr, hwr⟩ := hDual.2.2.2.2.1 w hw
      have hr_eq : connectedComponentIn (univ \ G.U) w = r := by
        obtain ⟨z, hz, rfl⟩ := hr
        exact (connectedComponentIn_eq hwr).symm
      obtain ⟨v, hv, _⟩ := hDual.2.2.2.2.2.1 r_dual hr_dual
      rw [dualChainTerm_inr_eq hDual hr_dual hv]
      dsimp only [dualChainTerm, ChainTerm.AreIncident]
      rw [hr_eq]
      exact ⟨hv.2, hr, (hDual.2.2.2.2.2.2.2.1 v hv.2 r hr w ⟨hwr, hw⟩ r_dual hr_dual hv.1).mpr
        hw_cl⟩
  | inr r_dual =>
    cases t₂ with
    | inl w =>
      rcases hinc with ⟨hw, hr_dual, hw_cl⟩
      obtain ⟨r, hr, hwr⟩ := hDual.2.2.2.2.1 w hw
      have hr_eq : connectedComponentIn (univ \ G.U) w = r := by
        obtain ⟨z, hz, rfl⟩ := hr
        exact (connectedComponentIn_eq hwr).symm
      obtain ⟨v, hv, _⟩ := hDual.2.2.2.2.2.1 r_dual hr_dual
      rw [dualChainTerm_inr_eq hDual hr_dual hv]
      dsimp only [dualChainTerm, ChainTerm.AreIncident]
      rw [hr_eq]
      exact ⟨hv.2, hr, (hDual.2.2.2.2.2.2.2.1 v hv.2 r hr w ⟨hwr, hw⟩ r_dual hr_dual hv.1).mpr
        hw_cl⟩
    | inr _ => exact False.elim hinc

private theorem dualChainTerm_isPeripheral_iff {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hC : IsOArc (bd S)) (hDual : IsDiscDualDrawingPair G G_dual)
    {t : ChainTerm S} (ht : t.IsValid G_dual) :
    (dualChainTerm G t).IsPeripheral G ↔ t.IsPeripheral G_dual := by
  cases t with
  | inl w =>
    obtain ⟨r, hr, hwr⟩ := hDual.2.2.2.2.1 w ht
    have hr_eq : connectedComponentIn (univ \ G.U) w = r := by
      obtain ⟨z, hz, rfl⟩ := hr
      exact (connectedComponentIn_eq hwr).symm
    dsimp only [dualChainTerm, ChainTerm.IsPeripheral]
    rw [hr_eq]
    exact ⟨fun ⟨_, hseg⟩ => ⟨ht, (dual_vertex_mem_bd_iff_peripheral hC hDual hr ⟨hwr, ht⟩).mpr
      hseg⟩,
      fun ⟨_, hw_bd⟩ => ⟨hr, (dual_vertex_mem_bd_iff_peripheral hC hDual hr ⟨hwr, ht⟩).mp hw_bd⟩⟩
  | inr r_dual =>
    obtain ⟨v, hv, _⟩ := hDual.2.2.2.2.2.1 r_dual ht
    rw [dualChainTerm_inr_eq hDual ht hv]
    dsimp only [ChainTerm.IsPeripheral]
    have hiff := dual_vertex_mem_bd_iff_peripheral hC hDual.symm ht hv
    exact ⟨fun ⟨_, hv_bd⟩ => ⟨ht, hiff.mp hv_bd⟩, fun ⟨_, hseg⟩ => ⟨hv.2, hiff.mpr hseg⟩⟩

private theorem dualChainTerm_matchesEnd {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {z : S} (hz : z ∈ G_dual.V ∪ G.V) {t : ChainTerm S} (ht : t.IsValid G_dual)
    (hm : t.MatchesEnd z) :
    (dualChainTerm G t).MatchesEnd z ∧ (z ∈ G_dual.V ↔ t.IsVertex) ∧ (z ∈ G.V ↔ ¬ t.IsVertex) := by
  have hV_disj : G.V ∩ G_dual.V = ∅ := hDual.2.2.1
  cases t with
  | inl w =>
    dsimp only [ChainTerm.MatchesEnd] at hm
    subst hm
    obtain ⟨r, hr, hwr⟩ := hDual.2.2.2.2.1 w ht
    have hw_compl : w ∈ univ \ G.U := by
      obtain ⟨x₀, _, rfl⟩ := hr
      exact connectedComponentIn_subset _ _ hwr
    have hw_not_GV : w ∉ G.V := fun hwG => by
      have : w ∈ G.V ∩ G_dual.V := ⟨hwG, ht⟩
      rw [hV_disj] at this
      exact this
    dsimp only [dualChainTerm, ChainTerm.MatchesEnd, ChainTerm.IsVertex]
    exact ⟨mem_connectedComponentIn hw_compl,
      ⟨fun _ => trivial, fun _ => ht⟩,
      ⟨fun h => False.elim (hw_not_GV h), fun h => False.elim (h trivial)⟩⟩
  | inr r_dual =>
    dsimp only [ChainTerm.MatchesEnd] at hm
    obtain ⟨v, hv, huniq⟩ := hDual.2.2.2.2.2.1 r_dual ht
    rw [dualChainTerm_inr_eq hDual ht hv]
    have hz_compl : z ∈ univ \ G_dual.U := by
      obtain ⟨x₀, _, rfl⟩ := ht
      exact connectedComponentIn_subset _ _ hm
    have hz_not_GdV : z ∉ G_dual.V := fun hzGd => hz_compl.2 (G_dual.V_subset_U hzGd)
    have hz_GV : z ∈ G.V := by
      rcases hz with hzGd | hzG
      · exact False.elim (hz_not_GdV hzGd)
      · exact hzG
    have hvz : v = z := (huniq z ⟨hm, hz_GV⟩).symm
    dsimp only [ChainTerm.MatchesEnd, ChainTerm.IsVertex]
    exact ⟨hvz,
      ⟨fun h => False.elim (hz_not_GdV h), fun h => False.elim h⟩,
      ⟨fun _ => not_false, fun _ => hz_GV⟩⟩

private def chainNonVertexLength {S : Type u} (A : List (ChainTerm S)) : ℕ :=
  (A.filter (fun t => !decide t.IsVertex)).length

private theorem chainLength_map_dualChainTerm {S : Type u} [TopologicalSpace S]
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawingPair G G_dual)
    {A_dual : List (ChainTerm S)} (hvalid : ∀ t ∈ A_dual, t.IsValid G_dual) :
    chainLength (A_dual.map (dualChainTerm G)) = chainNonVertexLength A_dual := by
  unfold chainLength chainNonVertexLength
  induction A_dual with
  | nil => rfl
  | cons a rest ih =>
    have ha : a.IsValid G_dual := hvalid a List.mem_cons_self
    have hrest : ∀ t ∈ rest, t.IsValid G_dual :=
      fun t ht => hvalid t (List.mem_cons_of_mem a ht)
    have hiff : decide (dualChainTerm G a).IsVertex = !decide a.IsVertex := by
      rw [← decide_not]
      exact decide_eq_decide.mpr (dualChainTerm_isVertex_iff hDual ha)
    simp only [List.map_cons, List.filter_cons, hiff]
    cases (!decide a.IsVertex) <;> simp [ih hrest]

private theorem isChain_map_of_imp {α β : Type*} {R₁ : α → α → Prop} {R₂ : β → β → Prop}
    (f : α → β) (himp : ∀ a b, R₁ a b → R₂ (f a) (f b)) :
    ∀ L : List α, L.IsChain R₁ → (L.map f).IsChain R₂
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: rest, h => by
    obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨himp a b hab, isChain_map_of_imp f himp (b :: rest) hrest⟩

private theorem alternating_chainLength_diff {S : Type u} :
    ∀ (L : List (ChainTerm S)) (hL : L ≠ []),
      L.IsChain (fun a b => (a.IsVertex ↔ ¬ b.IsVertex)) →
      (((L.head hL).IsVertex ∧ (L.getLast hL).IsVertex →
          (chainLength L : ℤ) - (chainNonVertexLength L : ℤ) = 1) ∧
       (¬ (L.head hL).IsVertex ∧ ¬ (L.getLast hL).IsVertex →
          (chainLength L : ℤ) - (chainNonVertexLength L : ℤ) = -1) ∧
       (¬ ((L.head hL).IsVertex ∧ (L.getLast hL).IsVertex) →
        ¬ (¬ (L.head hL).IsVertex ∧ ¬ (L.getLast hL).IsVertex) →
          (chainLength L : ℤ) - (chainNonVertexLength L : ℤ) = 0))
  | [], hL, _ => False.elim (hL rfl)
  | [a], _, _ => by
    by_cases ha : a.IsVertex <;>
      simp [chainLength, chainNonVertexLength, ha]
  | a :: b :: rest, _, hChain => by
    obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp hChain
    have hne : b :: rest ≠ [] := List.cons_ne_nil b rest
    have ih := alternating_chainLength_diff (b :: rest) hne hrest
    have hlast : (a :: b :: rest).getLast (List.cons_ne_nil a _) = (b :: rest).getLast hne :=
      List.getLast_cons hne
    have hhead_b : (b :: rest).head hne = b := rfl
    rw [hhead_b] at ih
    by_cases ha : a.IsVertex
    · have hb : ¬ b.IsVertex := hab.mp ha
      have hlen_v : chainLength (a :: b :: rest) = chainLength (b :: rest) + 1 := by
        simp [chainLength, ha]
      have hlen_r : chainNonVertexLength (a :: b :: rest) = chainNonVertexLength (b :: rest) := by
        simp [chainNonVertexLength, ha]
      by_cases hl : ((b :: rest).getLast hne).IsVertex
      · have ih0 := ih.2.2 (fun h => hb h.1) (fun h => h.2 hl)
        refine ⟨fun _ => by omega, fun h => False.elim (h.1 ha), fun h1 _ => ?_⟩
        exact False.elim (h1 ⟨ha, by rwa [hlast]⟩)
      · have ih1 := ih.2.1 ⟨hb, hl⟩
        refine ⟨fun h => False.elim (hl (hlast ▸ h.2)), fun h => False.elim (h.1 ha),
          fun _ _ => by omega⟩
    · have hb : b.IsVertex := by
        by_contra hnb
        exact ha (hab.mpr hnb)
      have hlen_v : chainLength (a :: b :: rest) = chainLength (b :: rest) := by
        simp [chainLength, ha]
      have hlen_r : chainNonVertexLength (a :: b :: rest) =
          chainNonVertexLength (b :: rest) + 1 := by
        simp [chainNonVertexLength, ha]
      by_cases hl : ((b :: rest).getLast hne).IsVertex
      · have ih1 := ih.1 ⟨hb, hl⟩
        refine ⟨fun h => False.elim (ha h.1), fun h => False.elim (h.2 (hlast ▸ hl)),
          fun _ _ => by omega⟩
      · have ih0 := ih.2.2 (fun h => hl h.2) (fun h => h.1 hb)
        refine ⟨fun h => False.elim (ha h.1), fun _ => by omega, fun _ h2 => ?_⟩
        exact False.elim (h2 ⟨ha, by rwa [hlast]⟩)

/-- **Graph Minors VI, (3.5)** (page 121):
"If $G$ is connected, any $(x, y)$-chain of $G^*$ corresponds to an $(x, y)$-chain of $G$, and if
$\Delta$ is cross-free the $\Delta^*$-redundancy of the first chain equals the $\Delta$-redundancy
of the second." -/
theorem theorem_3_5_proof : Statement35.{u} := by
  intro S _ G G_dual Δ x y A_dual hS hConn hΔ hΔ_union hCF hDual₀ hx hy hChain
  have hDual : IsDiscDualDrawingPair G G_dual := hDual₀.to_pair hS hConn
  have hC : IsOArc (bd S) := hS.isOArc_bd
  have hV_fin : (divisionUnion Δ).Finite := by
    rw [hΔ_union]
    exact G.finite_V.subset inter_subset_left
  have hV_sub : divisionUnion Δ ⊆ bd S := by
    rw [hΔ_union]
    exact inter_subset_right
  have hU1 : IsDualPointSet (bd S) (divisionUnion Δ) (G_dual.V ∩ bd S) := by
    rw [hΔ_union]
    exact hDual.2.2.2.2.2.2.2.2.1
  let A := A_dual.map (dualChainTerm G)
  have hA_ne : A ≠ [] := by
    simp [A, hChain.ne_nil]
  have hx_V : x ∈ G_dual.V ∪ G.V := by
    rw [hΔ_union] at hx
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hy_V : y ∈ G_dual.V ∪ G.V := by
    rw [hΔ_union] at hy
    rcases hy with hy | hy
    · exact Or.inl hy.1
    · exact Or.inr hy.1
  have hhead_valid : (A_dual.head hChain.ne_nil).IsValid G_dual :=
    hChain.valid _ (List.head_mem hChain.ne_nil)
  have hlast_valid : (A_dual.getLast hChain.ne_nil).IsValid G_dual :=
    hChain.valid _ (List.getLast_mem hChain.ne_nil)
  have hhead_match := dualChainTerm_matchesEnd hDual hx_V hhead_valid hChain.head_matches
  have hlast_match := dualChainTerm_matchesEnd hDual hy_V hlast_valid hChain.last_matches
  refine ⟨A, ?_, ?_⟩
  · refine ⟨hA_ne, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact dualChainTerm_valid hDual (hChain.valid t₀ ht₀)
    · exact isChain_map_of_imp (dualChainTerm G)
        (fun a b hab => dualChainTerm_areIncident hDual hab) A_dual hChain.isChain
    · rw [List.head_map]
      exact hhead_match.1
    · rw [List.getLast_map]
      exact hlast_match.1
    · intro i
      have hi_lt : i.1 < A_dual.length := by
        have := i.2
        simpa [A] using this
      let i₀ : Fin A_dual.length := ⟨i.1, hi_lt⟩
      have hget : A[i] = dualChainTerm G A_dual[i₀] := by simp [A, i₀]
      have hlen_iff : (i.1 = 0 ∨ i.1 + 1 = A.length) ↔ (i₀.1 = 0 ∨ i₀.1 + 1 = A_dual.length) := by
        simp [A, i₀]
      have hvalid_i₀ : A_dual[i₀].IsValid G_dual :=
        hChain.valid _ (List.getElem_mem i₀.2)
      rw [hget, hlen_iff, dualChainTerm_isPeripheral_iff hC hDual hvalid_i₀]
      exact hChain.peripheral_iff i₀
  · have hlen_A : chainLength A = chainNonVertexLength A_dual :=
      chainLength_map_dualChainTerm hDual hChain.valid
    have halt : A_dual.IsChain (fun a b => (a.IsVertex ↔ ¬ b.IsVertex)) := by
      refine hChain.isChain.imp fun a b hab => ?_
      cases a <;> cases b <;> simp [ChainTerm.AreIncident, ChainTerm.IsVertex] at hab ⊢
    have hdiff_L := alternating_chainLength_diff A_dual hChain.ne_nil halt
    have hx_W : x ∈ divisionUnion Δ ∪ (G_dual.V ∩ bd S) := hx.symm
    have hy_W : y ∈ divisionUnion Δ ∪ (G_dual.V ∩ bd S) := hy.symm
    have hdiff_Δ := theorem_2_4_proof (bd S) (G_dual.V ∩ bd S) Δ x y
      hC hΔ hV_fin hV_sub hU1 hCF hx_W hy_W
    have hx_bd : x ∈ bd S := by
      rw [hΔ_union] at hx
      rcases hx with hx | hx <;> exact hx.2
    have hy_bd : y ∈ bd S := by
      rw [hΔ_union] at hy
      rcases hy with hy | hy <;> exact hy.2
    have hx_U_iff : x ∈ G_dual.V ∩ bd S ↔ (A_dual.head hChain.ne_nil).IsVertex :=
      ⟨fun h => hhead_match.2.1.mp h.1, fun h => ⟨hhead_match.2.1.mpr h, hx_bd⟩⟩
    have hy_U_iff : y ∈ G_dual.V ∩ bd S ↔ (A_dual.getLast hChain.ne_nil).IsVertex :=
      ⟨fun h => hlast_match.2.1.mp h.1, fun h => ⟨hlast_match.2.1.mpr h, hy_bd⟩⟩
    have hx_V_iff : x ∈ divisionUnion Δ ↔ ¬ (A_dual.head hChain.ne_nil).IsVertex := by
      rw [hΔ_union]
      exact ⟨fun h => hhead_match.2.2.mp h.1, fun h => ⟨hhead_match.2.2.mpr h, hx_bd⟩⟩
    have hy_V_iff : y ∈ divisionUnion Δ ↔ ¬ (A_dual.getLast hChain.ne_nil).IsVertex := by
      rw [hΔ_union]
      exact ⟨fun h => hlast_match.2.2.mp h.1, fun h => ⟨hlast_match.2.2.mpr h, hy_bd⟩⟩
    unfold chainRedundancy
    rw [hlen_A]
    by_cases h1 : (A_dual.head hChain.ne_nil).IsVertex ∧ (A_dual.getLast hChain.ne_nil).IsVertex
    · have hL := hdiff_L.1 h1
      have hD := hdiff_Δ.2.1 ⟨hx_U_iff.mpr h1.1, hy_U_iff.mpr h1.2⟩
      omega
    · by_cases h2 : ¬ (A_dual.head hChain.ne_nil).IsVertex ∧ ¬ (A_dual.getLast
      hChain.ne_nil).IsVertex
      · have hL := hdiff_L.2.1 h2
        have hD := hdiff_Δ.1 ⟨hx_V_iff.mpr h2.1, hy_V_iff.mpr h2.2⟩
        omega
      · have hL := hdiff_L.2.2 h1 h2
        have hD := hdiff_Δ.2.2
          (fun h => h2 ⟨hx_V_iff.mp h.1, hy_V_iff.mp h.2⟩)
          (fun h => h1 ⟨hx_U_iff.mp h.1, hy_U_iff.mp h.2⟩)
        omega

end GraphMinor.GM06
