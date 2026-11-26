/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Axioms
public import LeanPool.GraphMinor.GM04.Patchwork.StarWQO
import LeanPool.GraphMinor.GM04.Patchwork.Menger
import LeanPool.GraphMinor.GM04.Patchwork.Expansion
import LeanPool.GraphMinor.GM04.Patchwork.Stars
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Verifying the axioms for robust patchworks (Graph Minors IV, Section 9)

This file formalizes Section 9 of Graph Minors IV (pages 251–252):
given a sequence `P : ℕ → Patchwork Ω α β` of mutually disjoint robust `Ω`-patchworks, we define
the class `ℛ` (`patchworkClass P`), the induced patchwork `P(G)` (`inducedPatchwork P G`), and the
simulation relation (`patchworkSim P`), verify `Axiom1`, `Axiom2`, `Axiom3`, and `Axiom4 ι` (for
every tree vertex type `ι`), and deduce (9.1) (`theorem_9_1`) from `(5.3)` (`Theorem53Statement`).
-/

@[expose] public section

namespace GraphMinor.GM04

open SimpleGraph _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

variable {Ω : Type w} [Preorder Ω] {α : Type u} {β : Type v} {ι : Type*}

/-! ### Restriction of a robust patchwork and `Patchwork.Agrees` equivalence -/

omit [Preorder Ω] in
open Classical in
theorem Patchwork.IsRobust.restrict {P : Patchwork Ω α β} (hP : P.IsRobust)
    (G' : RootedHypergraph α β) : (P.restrict G').IsRobust := by
  intro e he
  dsimp only [Patchwork.restrict]
  split_ifs with h
  · exact hP e h.1
  · have hfin : (G'.ends e).Finite :=
      G'.vertexSet_finite.subset fun _ hv ↦ G'.vertex_mem_of_inc hv
    exact Patch.IsFree.isRobust hfin (freePatch_isFree (G'.ends e))

omit [Preorder Ω] in
open Classical in
theorem Patchwork.Agrees.rfl (P : Patchwork Ω α β) : P.Agrees P :=
  ⟨Eq.refl _, Eq.refl _, fun _ _ ↦ Eq.refl _, fun _ _ ↦ Eq.refl _, fun _ _ ↦ Eq.refl _⟩

omit [Preorder Ω] in
open Classical in
theorem Patchwork.Agrees.trans {P₁ P₂ P₃ : Patchwork Ω α β}
    (h₁₂ : P₁.Agrees P₂) (h₂₃ : P₂.Agrees P₃) : P₁.Agrees P₃ :=
  ⟨h₁₂.G_eq.trans h₂₃.G_eq, h₁₂.dom_eq.trans h₂₃.dom_eq,
    fun e he ↦ (h₁₂.μ_eq e he).trans (h₂₃.μ_eq e (h₁₂.G_eq ▸ he)),
    fun e he ↦ (h₁₂.Δ_eq e he).trans (h₂₃.Δ_eq e (h₁₂.G_eq ▸ he)),
    fun e he ↦ (h₁₂.φ_eq e he).trans (h₂₃.φ_eq e (h₁₂.G_eq ▸ he))⟩

/-! ### The class `ℛ`, induced patchwork `P(G)`, and simulation relation (Section 9, page 251) -/

open Classical in
/-- Graph Minors IV, Section 9 (page 251):
"Let $\mathscr{R}$ be the set of all rooted hypergraphs $G$ such that $G^- \subseteq G_i^-$
for some $i$." -/
def patchworkClass (P : ℕ → Patchwork Ω α β) : Set (RootedHypergraph α β) :=
  {G | ∃ i, G.toHypergraph ≤ (P i).G.toHypergraph}

open Classical in
/-- Chosen index `i` with `G⁻ ⊆ Gᵢ⁻` when `G ∈ patchworkClass P` (and `0` otherwise). -/
noncomputable def inducedIndex (P : ℕ → Patchwork Ω α β) (G : RootedHypergraph α β) : ℕ :=
  if h : ∃ i, G.toHypergraph ≤ (P i).G.toHypergraph then h.choose else 0

open Classical in
/-- Graph Minors IV, Section 9 (page 251):
"For each $G \in \mathscr{R}$ we define $P(G)$ to be $P_i \mid G$ where $G^- \subseteq
G_i^-$. (This is well-defined since such a value of $i$ is unique unless $G$ is null.)" -/
noncomputable def inducedPatchwork (P : ℕ → Patchwork Ω α β) (G : RootedHypergraph α β) :
    Patchwork Ω α β :=
  (P (inducedIndex P G)).restrict G

open Classical in
/-- Graph Minors IV, Section 9 (page 251):
"Let us say that $G \in \mathscr{R}$ is simulated in $G' \in \mathscr{R}$ if $P(G)$ is
simulated in $P(G')$." -/
def patchworkSim (P : ℕ → Patchwork Ω α β) (G G' : RootedHypergraph α β) : Prop :=
  Simulated (inducedPatchwork P G) (inducedPatchwork P G')

omit [Preorder Ω] in
open Classical in
@[simp]
theorem inducedPatchwork_G (P : ℕ → Patchwork Ω α β) (G : RootedHypergraph α β) :
    (inducedPatchwork P G).G = G := rfl

omit [Preorder Ω] in
open Classical in
theorem inducedIndex_spec {P : ℕ → Patchwork Ω α β} {G : RootedHypergraph α β}
    (hG : G ∈ patchworkClass P) :
    G.toHypergraph ≤ (P (inducedIndex P G)).G.toHypergraph := by
  have hG' : ∃ i, G.toHypergraph ≤ (P i).G.toHypergraph := hG
  dsimp only [inducedIndex]
  rw [dite_eq_left_of_eq_true (eq_true hG')]
  exact hG'.choose_spec

omit [Preorder Ω] in
open Classical in
theorem inducedPatchwork_isRobust {P : ℕ → Patchwork Ω α β} (hrob : ∀ i, (P i).IsRobust)
    (G : RootedHypergraph α β) : (inducedPatchwork P G).IsRobust :=
  (hrob (inducedIndex P G)).restrict G

omit [Preorder Ω] in
open Classical in
theorem inducedPatchwork_isRemovable {P : ℕ → Patchwork Ω α β} (hrob : ∀ i, (P i).IsRobust)
    (G : RootedHypergraph α β) : (inducedPatchwork P G).IsRemovable :=
  (inducedPatchwork_isRobust hrob G).isRemovable

omit [Preorder Ω] in
open Classical in
theorem agrees_restrict_of_edgeSet_eq_empty (P₁ P₂ : Patchwork Ω α β)
    {G : RootedHypergraph α β} (hE : G.edgeSet = ∅) :
    (P₁.restrict G).Agrees (P₂.restrict G) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [Patchwork.restrict, hE]
  · intro e he
    have heE : e ∈ G.edgeSet := he
    rw [hE] at heE
    exact False.elim heE
  · intro e he
    have heE : e ∈ G.edgeSet := he
    rw [hE] at heE
    exact False.elim heE
  · intro e he
    have heE : e ∈ G.edgeSet := he
    rw [hE] at heE
    exact False.elim heE

omit [Preorder Ω] in
open Classical in
theorem inducedPatchwork_agrees {P : ℕ → Patchwork Ω α β}
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet)
    {i : ℕ} {G : RootedHypergraph α β} (hG : G.toHypergraph ≤ (P i).G.toHypergraph) :
    (inducedPatchwork P G).Agrees ((P i).restrict G) := by
  have hmem : G ∈ patchworkClass P := ⟨i, hG⟩
  let j := inducedIndex P G
  have hj : G.toHypergraph ≤ (P j).G.toHypergraph := inducedIndex_spec hmem
  by_cases hij : j = i
  · subst hij
    exact Patchwork.Agrees.rfl _
  · have hE : G.edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e he
      exact Set.disjoint_left.mp (hdisj hij) (hj.edgeSet_subset he) (hG.edgeSet_subset he)
    exact agrees_restrict_of_edgeSet_eq_empty (P j) (P i) hE

omit [Preorder Ω] in
open Classical in
theorem inducedPatchwork_self_agrees {P : ℕ → Patchwork Ω α β}
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet) (i : ℕ) :
    (inducedPatchwork P (P i).G).Agrees (P i) :=
  (inducedPatchwork_agrees hdisj (le_refl (P i).G.toHypergraph)).trans
    (Patchwork.agrees_restrict_self (P i))

omit [Preorder Ω] in
open Classical in
theorem inducedPatchwork_restrict_agrees {P : ℕ → Patchwork Ω α β}
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet)
    {G H : RootedHypergraph α β} (hG : G ∈ patchworkClass P)
    (hHG : H.toHypergraph ≤ G.toHypergraph) :
    (inducedPatchwork P H).Agrees ((inducedPatchwork P G).restrict H) := by
  let i := inducedIndex P G
  have hi : G.toHypergraph ≤ (P i).G.toHypergraph := inducedIndex_spec hG
  have hHi : H.toHypergraph ≤ (P i).G.toHypergraph := hHG.trans hi
  exact (inducedPatchwork_agrees hdisj hHi).trans
    (Patchwork.agrees_restrict_restrict hi hHG).symm

/-! ### Verification of Axioms 1 and 2 (Section 9, page 251) -/

omit [Preorder Ω] in
open Classical in
/-- Graph Minors IV, Section 9, Axiom 1 (page 251):
"Axiom 1. This is clear from the definition of $\mathscr{R}$." -/
theorem axiom1_patchwork (P : ℕ → Patchwork Ω α β) :
    Axiom1 (patchworkClass P) := by
  intro G ⟨i, hi⟩ H hHG
  exact ⟨i, hHG.trans hi⟩

open Classical in
/-- Graph Minors IV, Section 9, Axiom 2 (page 251):
"Axiom 2. This is immediate from (7.1)." -/
theorem axiom2_patchwork (P : ℕ → Patchwork Ω α β) :
    Axiom2 (patchworkClass P) (patchworkSim P) :=
  ⟨fun G _ ↦ Simulated.refl (inducedPatchwork P G),
    fun _ _ _ _ _ _ h₁₂ h₂₃ ↦ h₁₂.trans h₂₃⟩

/-! ### Verification of Axiom 3 (Section 9, pages 251–252) -/

omit [Preorder Ω] in
open Classical in
theorem sup_emptySubgraph_reachable_iff (H : (⊤ : SimpleGraph α).Subgraph) (V : Set α)
    (a b : (H ⊔ emptySubgraph V).verts) :
    (H ⊔ emptySubgraph V).coe.Reachable a b ↔
      a = b ∨ ∃ (ha : a.1 ∈ H.verts) (hb : b.1 ∈ H.verts), H.coe.Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩ := by
  rw [reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      have hyz_H : H.Adj y.1 z.1 := by
        rcases hyz with hyz | hyz
        · exact hyz
        · exact False.elim hyz
      have hy : y.1 ∈ H.verts := H.edge_vert hyz_H
      have hz : z.1 ∈ H.verts := H.edge_vert hyz_H.symm
      have hstep : H.coe.Reachable ⟨y.1, hy⟩ ⟨z.1, hz⟩ := Adj.reachable hyz_H
      rcases ih with rfl | ⟨ha, hy', hry⟩
      · exact Or.inr ⟨hy, hz, hstep⟩
      · exact Or.inr ⟨ha, hz, hry.trans hstep⟩
  · rintro (rfl | ⟨ha, hb, hr⟩)
    · exact Relation.ReflTransGen.refl
    · rw [reachable_iff_reflTransGen] at hr
      suffices ∀ (x y : H.verts), Relation.ReflTransGen H.coe.Adj x y →
          ∀ (hx : x.1 ∈ (H ⊔ emptySubgraph V).verts) (hy : y.1 ∈ (H ⊔ emptySubgraph V).verts),
          Relation.ReflTransGen (H ⊔ emptySubgraph V).coe.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩ from
        this ⟨a.1, ha⟩ ⟨b.1, hb⟩ hr a.2 b.2
      intro x y hxy
      induction hxy with
      | refl =>
        intro _ _
        exact Relation.ReflTransGen.refl
      | @tail u w _ huw ih =>
        intro hx hw
        have hu : u.1 ∈ (H ⊔ emptySubgraph V).verts := Or.inl u.2
        exact (ih hx hu).tail (Or.inl huw)

omit [Preorder Ω] in
open Classical in
theorem IsComponent.sup_emptySubgraph {H D : (⊤ : SimpleGraph α).Subgraph} (h : IsComponent H D)
    (V : Set α) : IsComponent (H ⊔ emptySubgraph V) D := by
  obtain ⟨x, rfl⟩ := h
  let x' : (H ⊔ emptySubgraph V).verts := ⟨x.1, Or.inl x.2⟩
  refine ⟨x', ?_⟩
  have hverts : componentVerts H x = componentVerts (H ⊔ emptySubgraph V) x' := by
    ext w
    simp only [mem_componentVerts_iff]
    constructor
    · rintro ⟨hw, hr⟩
      refine ⟨Or.inl hw, (sup_emptySubgraph_reachable_iff H V x' ⟨w, Or.inl hw⟩).mpr ?_⟩
      exact Or.inr ⟨x.2, hw, hr⟩
    · rintro ⟨hw, hr⟩
      rcases (sup_emptySubgraph_reachable_iff H V x' ⟨w, hw⟩).mp hr with hEq | ⟨_, hwH, hrH⟩
      · have hwx : w = x.1 := congrArg Subtype.val hEq.symm
        subst hwx
        exact ⟨x.2, Reachable.refl x⟩
      · exact ⟨hwH, hrH⟩
  ext u v
  · exact (congrArg (u ∈ ·) hverts).to_iff
  · simp [component, hverts, emptySubgraph]

omit [Preorder Ω] in
open Classical in
theorem component_sup_emptySubgraph_verts_of_notMem (H : (⊤ : SimpleGraph α).Subgraph)
    {V : Set α} {u : α} (huV : u ∈ V) (huH : u ∉ H.verts) :
    (component (H ⊔ emptySubgraph V) ⟨u, Or.inr huV⟩).verts = {u} := by
  ext w
  simp only [component_verts, mem_componentVerts_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hr⟩
    rcases (sup_emptySubgraph_reachable_iff H V ⟨u, Or.inr huV⟩ ⟨w, hw⟩).mp hr with hEq | ⟨huH', _,
      _⟩
    · exact congrArg Subtype.val hEq.symm
    · exact False.elim (huH huH')
  · rintro rfl
    exact ⟨Or.inr huV, Reachable.refl _⟩

omit [Preorder Ω] in
open Classical in
/-- Gluing a separation `(J₁, J₂)` of `G₂⁻` with `V(G₁⁻ ∩ G₂⁻) ⊆ V(J₁)` and `πBar(G₂) ⊆ V(J₂)` to
`G₁` yields a separation `(G₁⁻ ∪ J₁, J₂)` of `G` with the same order as `(J₁, J₂)`
(Graph Minors IV, Section 9, pages 251–252). -/
private theorem sep_G2_ge_of_min {G G₁ G₂ : RootedHypergraph α β}
    (hsep : G.IsSeparation G₁ G₂)
    (hmin : ¬ ∃ H₁ H₂ : RootedHypergraph α β, G.IsSeparation H₁ H₂ ∧
      G₁.toHypergraph ≤ H₁.toHypergraph ∧
      separationOrder H₁.toHypergraph H₂.toHypergraph < G.roots.length)
    {J₁ J₂ : Hypergraph α β} (hJ : G₂.toHypergraph.IsSeparation J₁ J₂)
    (hX_sub : (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet ⊆ J₁.vertexSet)
    (hY_sub : G₂.rootSet ⊆ J₂.vertexSet) :
    G.roots.length ≤ separationOrder J₁ J₂ := by
  by_contra! hlt
  have hle₁ : G₁.toHypergraph ∪ J₁ ≤ G.toHypergraph := by
    have hJ₁_G : J₁ ≤ G.toHypergraph := hJ.left_le.trans hsep.isSeparation.right_le
    refine ⟨Set.union_subset hsep.isSeparation.left_le.vertexSet_subset hJ₁_G.vertexSet_subset,
      Set.union_subset hsep.isSeparation.left_le.edgeSet_subset hJ₁_G.edgeSet_subset, ?_⟩
    rintro e (he₁ | heJ)
    · ext v
      simp only [Hypergraph.ends, Set.mem_ofPred_eq]
      constructor
      · intro hv
        left
        have hEq := hsep.isSeparation.left_le.ends_eq e he₁
        exact (congrArg (v ∈ ·) hEq).mp hv
      · rintro (hv₁ | hvJ)
        · have hEq := hsep.isSeparation.left_le.ends_eq e he₁
          exact (congrArg (v ∈ ·) hEq).mpr hv₁
        · have hEq := hJ₁_G.ends_eq e (J₁.edge_mem_of_inc hvJ)
          exact (congrArg (v ∈ ·) hEq).mpr hvJ
    · ext v
      simp only [Hypergraph.ends, Set.mem_ofPred_eq]
      constructor
      · intro hv
        right
        have hEq := hJ₁_G.ends_eq e heJ
        exact (congrArg (v ∈ ·) hEq).mp hv
      · rintro (hv₁ | hvJ)
        · have hEq := hsep.isSeparation.left_le.ends_eq e (G₁.edge_mem_of_inc hv₁)
          exact (congrArg (v ∈ ·) hEq).mpr hv₁
        · have hEq := hJ₁_G.ends_eq e heJ
          exact (congrArg (v ∈ ·) hEq).mpr hvJ
  have hle₂ : J₂ ≤ G.toHypergraph := hJ.right_le.trans hsep.isSeparation.right_le
  have hunion : (G₁.toHypergraph ∪ J₁) ∪ J₂ = G.toHypergraph := by
    have hassoc : (G₁.toHypergraph ∪ J₁) ∪ J₂ = G₁.toHypergraph ∪ (J₁ ∪ J₂) := by
      ext : 1
      · exact Set.union_assoc _ _ _
      · exact Set.union_assoc _ _ _
      · ext e v
        exact or_assoc
    rw [hassoc, hJ.union_eq, hsep.isSeparation.union_eq]
  have hedge_inter : ((G₁.toHypergraph ∪ J₁) ∩ J₂).edgeSet = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he₁ | heJ₁, heJ₂⟩
    · have he₂ : e ∈ G₂.edgeSet := hJ.right_le.edgeSet_subset heJ₂
      have he_inter : e ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).edgeSet := ⟨he₁, he₂⟩
      rw [hsep.isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter
    · have he_inter : e ∈ (J₁ ∩ J₂).edgeSet := ⟨heJ₁, heJ₂⟩
      rw [hJ.edgeSet_inter_eq] at he_inter
      exact he_inter
  have hvert_inter : ((G₁.toHypergraph ∪ J₁) ∩ J₂).vertexSet = (J₁ ∩ J₂).vertexSet := by
    ext v
    constructor
    · rintro ⟨hv₁ | hvJ₁, hvJ₂⟩
      · have hv₂ : v ∈ G₂.vertexSet := hJ.right_le.vertexSet_subset hvJ₂
        exact ⟨hX_sub ⟨hv₁, hv₂⟩, hvJ₂⟩
      · exact ⟨hvJ₁, hvJ₂⟩
    · rintro ⟨hvJ₁, hvJ₂⟩
      exact ⟨Or.inr hvJ₁, hvJ₂⟩
  let S := ((G₁.toHypergraph ∪ J₁) ∩ J₂).vertexSet
  have hS_fin : S.Finite := ((G₁.toHypergraph ∪ J₁) ∩ J₂).vertexSet_finite
  let H₁ : RootedHypergraph α β :=
    { toHypergraph := G₁.toHypergraph ∪ J₁
      roots := hS_fin.toFinset.toList
      roots_nodup := Finset.nodup_toList _
      roots_subset := fun v hv ↦ by
        rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
        exact hv.1 }
  let H₂ : RootedHypergraph α β :=
    { toHypergraph := J₂
      roots := G.roots
      roots_nodup := G.roots_nodup
      roots_subset := fun v hv ↦ by
        rw [← hsep.roots_right] at hv
        exact hY_sub hv }
  have hH_sep : G.IsSeparation H₁ H₂ := by
    refine ⟨⟨hle₁, hle₂, hunion, hedge_inter⟩, rfl, ?_⟩
    ext v
    simp [H₁, H₂, RootedHypergraph.rootSet, S]
  have hG₁_le_H₁ : G₁.toHypergraph ≤ H₁.toHypergraph := by
    refine ⟨Set.subset_union_left, Set.subset_union_left, fun e he ↦ ?_⟩
    ext v
    simp only [H₁, Hypergraph.ends, Set.mem_ofPred_eq]
    refine ⟨fun h ↦ ?_, Or.inl⟩
    rcases h with h | hJ₁
    · exact h
    · have hG := (hJ.left_le.trans hsep.isSeparation.right_le).ends_eq e (J₁.edge_mem_of_inc hJ₁)
      have hG₁ := hsep.isSeparation.left_le.ends_eq e he
      exact (congrArg (v ∈ ·) (hG₁.symm.trans hG)).mpr hJ₁
  have hord_eq : separationOrder H₁.toHypergraph H₂.toHypergraph = separationOrder J₁ J₂ := by
    dsimp only [separationOrder, H₁, H₂]
    rw [hvert_inter]
  exact hmin ⟨H₁, H₂, hH_sep, hG₁_le_H₁, hord_eq.symm ▸ hlt⟩

open Classical in
/-- Index the disjoint components by the roots they contain, retaining a vertex in the
separator for each component. -/
private theorem reindex_components_by_roots {G G₂ : RootedHypergraph α β}
    {H : (⊤ : SimpleGraph α).Subgraph} {X : Set α}
    {D : Fin G.roots.length → (⊤ : SimpleGraph α).Subgraph}
    (hroots : G₂.roots = G.roots) (hD_inj : Function.Injective D)
    (hD_spec : ∀ j, IsComponent H (D j) ∧
      ((D j).verts ∩ X).Nonempty ∧ ((D j).verts ∩ G₂.rootSet).Nonempty) :
    ∃ (C : Fin G.roots.length → (⊤ : SimpleGraph α).Subgraph)
      (v : Fin G.roots.length → α),
      (∀ i, IsComponent H (C i)) ∧ Function.Injective C ∧
      (∀ i, G.roots[i.1]'i.2 ∈ (C i).verts) ∧
      (∀ i, v i ∈ (C i).verts) ∧ (∀ i, v i ∈ X) := by
  let k := G.roots.length
  let yOf (j : Fin k) : α := ((hD_spec j).2.2).choose
  have hyOf_D : ∀ j : Fin k, yOf j ∈ (D j).verts := fun j ↦ ((hD_spec j).2.2).choose_spec.1
  have hyOf_Y : ∀ j : Fin k, yOf j ∈ G.roots := by
    intro j
    rw [← hroots]
    exact ((hD_spec j).2.2).choose_spec.2
  let idxOf (j : Fin k) : Fin k :=
    ⟨G.roots.idxOf (yOf j), List.idxOf_lt_length_of_mem (hyOf_Y j)⟩
  have hidxOf_get : ∀ j : Fin k, G.roots[(idxOf j).1]'(idxOf j).2 = yOf j :=
    fun j ↦ List.getElem_idxOf (idxOf j).2
  have hidxOf_inj : Function.Injective idxOf := by
    intro j₁ j₂ hEq
    have hyEq : yOf j₁ = yOf j₂ := by
      rw [← hidxOf_get j₁, ← hidxOf_get j₂]
      exact congrArg (fun m : Fin k ↦ G.roots[m.1]'m.2) hEq
    have hDEq : D j₁ = D j₂ :=
      (hD_spec j₁).1.eq_of_mem (hD_spec j₂).1 (hyOf_D j₁) (hyEq ▸ hyOf_D j₂)
    exact hD_inj hDEq
  have hidxOf_bij : Function.Bijective idxOf :=
    (Fintype.bijective_iff_injective_and_card idxOf).mpr ⟨hidxOf_inj, rfl⟩
  let eIdx : Fin k ≃ Fin k := Equiv.ofBijective idxOf hidxOf_bij
  let C (i : Fin k) : (⊤ : SimpleGraph α).Subgraph := D (eIdx.symm i)
  have hC_comp : ∀ i : Fin k, IsComponent H (C i) := fun i ↦ (hD_spec (eIdx.symm i)).1
  have hC_inj : Function.Injective C := hD_inj.comp eIdx.symm.injective
  have hC_root : ∀ i : Fin k, G.roots[i.1]'i.2 ∈ (C i).verts := by
    intro i
    have h1 : idxOf (eIdx.symm i) = i := eIdx.apply_symm_apply i
    have h2 : G.roots[i.1]'i.2 = yOf (eIdx.symm i) :=
      (congrArg (fun m : Fin k ↦ G.roots[m.1]'m.2) h1).symm.trans (hidxOf_get (eIdx.symm i))
    rw [h2]
    exact hyOf_D (eIdx.symm i)
  let v (i : Fin k) : α := ((hD_spec (eIdx.symm i)).2.1).choose
  have hv_C : ∀ i : Fin k, v i ∈ (C i).verts := fun i ↦ ((hD_spec (eIdx.symm i)).2.1).choose_spec.1
  have hv_X : ∀ i : Fin k, v i ∈ X := fun i ↦ ((hD_spec (eIdx.symm i)).2.1).choose_spec.2
  exact ⟨C, v, hC_comp, hC_inj, hC_root, hv_C, hv_X⟩

open Classical in
/-- Graph Minors IV, Section 9, Axiom 3 (pages 251–252):
verification of Axiom 3 for `patchworkClass P` and `patchworkSim P`. -/
theorem axiom3_patchwork (hM : MengerStatement.{u, v}) {P : ℕ → Patchwork Ω α β}
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet)
    (hrob : ∀ i, (P i).IsRobust) :
    Axiom3 (patchworkClass P) (patchworkSim P) := by
  intro G hG G₁ G₂ hsep hord hmin
  let Q := inducedPatchwork P G
  let Q₂ := Q.restrict G₂
  have hQ_rob : Q.IsRobust := inducedPatchwork_isRobust hrob G
  have hQ₂_rob : Q₂.IsRobust := hQ_rob.restrict G₂
  let X := (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet
  let Y := G₂.rootSet
  let k := G.roots.length
  have hX_sub : X ⊆ G₂.vertexSet := Set.inter_subset_right
  have hY_sub : Y ⊆ G₂.vertexSet := fun v hv ↦ G₂.roots_subset v hv
  have hcond1 : Theorem61Cond1 Q₂ X Y k :=
    fun J₁ J₂ hJ hJ₁ hJ₂ ↦ sep_G2_ge_of_min hsep hmin hJ hJ₁ hJ₂
  have hcond2 : Theorem61Cond2 Q₂ X Y k :=
    ((theorem_6_1_proof hM hQ₂_rob hX_sub hY_sub k).1.mp hcond1)
  obtain ⟨H, D, hH_real, hD_inj, hD_spec⟩ := hcond2
  have hH_verts : H.verts = G₂.vertexSet := hH_real.verts_eq
  obtain ⟨C, v, hC_comp, hC_inj, hC_root, hv_C, hv_X⟩ :=
    reindex_components_by_roots hsep.roots_right hD_inj hD_spec
  have hv_inj : Function.Injective v := by
    intro i₁ i₂ hEq
    have hCEq : C i₁ = C i₂ :=
      (hC_comp i₁).eq_of_mem (hC_comp i₂) (hv_C i₁) (hEq ▸ hv_C i₂)
    exact hC_inj hCEq
  have hrange_v : Set.range v = X := by
    have hsub : Set.range v ⊆ X := Set.range_subset_iff.mpr hv_X
    have hcard_range : (Set.range v).ncard = k := by
      rw [Set.ncard_range_of_injective hv_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hX_fin : X.Finite := (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet_finite
    have hX_le : X.ncard ≤ (Set.range v).ncard := by
      rw [hcard_range]
      exact hord.le
    exact Set.eq_of_subset_of_ncard_le hsub hX_le hX_fin
  let π₁ : List α := List.ofFn v
  have hπ₁_len : π₁.length = k := List.length_ofFn
  have hπ₁_nodup : π₁.Nodup := List.nodup_ofFn.mpr hv_inj
  have hπ₁_set : {w | w ∈ π₁} = X := by
    ext w
    simp [π₁, ← hrange_v]
  let H₁ : RootedHypergraph α β :=
    { toHypergraph := G₁.toHypergraph
      roots := π₁
      roots_nodup := hπ₁_nodup
      roots_subset := fun w hw ↦ by
        have hwX : w ∈ X := hπ₁_set ▸ hw
        exact hwX.1 }
  have hH₁_rootSet : H₁.rootSet = G₁.rootSet := by
    change {w | w ∈ π₁} = G₁.rootSet
    rw [hπ₁_set, hsep.rootSet_left]
  refine ⟨H₁, rfl, hH₁_rootSet, ?_⟩
  let Q₁ := Q.restrict H₁
  have hH₁_le : H₁.toHypergraph ≤ Q.G.toHypergraph := hsep.isSeparation.left_le
  have hQ₁_agrees : (inducedPatchwork P H₁).Agrees Q₁ :=
    inducedPatchwork_restrict_agrees hdisj hG hH₁_le
  have hQ_rfl : Q.Agrees Q := ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  let ηv (u : α) : Set α :=
    if h : ∃ i : Fin k, v i = u then (C h.choose).verts else {u}
  have hηv_v : ∀ i : Fin k, ηv (v i) = (C i).verts := by
    intro i
    have h : ∃ j : Fin k, v j = v i := ⟨i, rfl⟩
    dsimp only [ηv]
    rw [dite_eq_left_of_eq_true (eq_true h)]
    rw [hv_inj h.choose_spec]
  have hηv_not_X : ∀ u ∉ X, ηv u = {u} := by
    intro u hu
    have hnot : ¬∃ i : Fin k, v i = u := by
      rw [← Set.mem_range, hrange_v]
      exact hu
    dsimp only [ηv]
    exact dite_eq_right_of_eq_false (eq_false hnot)
  have hself_mem_ηv : ∀ u : α, u ∈ ηv u := by
    intro u
    by_cases h : ∃ i : Fin k, v i = u
    · obtain ⟨i, rfl⟩ := h
      rw [hηv_v i]
      exact hv_C i
    · dsimp only [ηv]
      rw [dite_eq_right_of_eq_false (eq_false h)]
      exact Set.mem_singleton u
  have hC_sub_G₂ : ∀ i : Fin k, (C i).verts ⊆ G₂.vertexSet :=
    fun i ↦ hH_verts ▸ (hC_comp i).le.1
  have hηv_sub_G : ∀ u ∈ G₁.vertexSet, ηv u ⊆ G.vertexSet := by
    intro u hu
    by_cases h : ∃ i : Fin k, v i = u
    · obtain ⟨i, rfl⟩ := h
      rw [hηv_v i]
      exact (hC_sub_G₂ i).trans hsep.isSeparation.right_le.vertexSet_subset
    · dsimp only [ηv]
      rw [dite_eq_right_of_eq_false (eq_false h)]
      exact Set.singleton_subset_iff.mpr (hsep.isSeparation.left_le.vertexSet_subset hu)
  have hηv_disj : ∀ u₁ ∈ G₁.vertexSet, ∀ u₂ ∈ G₁.vertexSet, u₁ ≠ u₂ →
      Disjoint (ηv u₁) (ηv u₂) := by
    intro u₁ hu₁ u₂ hu₂ hne
    by_cases h₁ : ∃ i : Fin k, v i = u₁ <;> by_cases h₂ : ∃ i : Fin k, v i = u₂
    · obtain ⟨i₁, rfl⟩ := h₁
      obtain ⟨i₂, rfl⟩ := h₂
      rw [hηv_v i₁, hηv_v i₂]
      have hne_i : i₁ ≠ i₂ := fun hEq ↦ hne (congrArg v hEq)
      exact (hC_comp i₁).disjoint_verts_of_ne (hC_comp i₂) (fun hCEq ↦ hne_i (hC_inj hCEq))
    · obtain ⟨i₁, rfl⟩ := h₁
      have hu₂_notX : u₂ ∉ X := by rwa [← hrange_v]
      rw [hηv_v i₁, hηv_not_X u₂ hu₂_notX, Set.disjoint_singleton_right]
      intro hu₂_C
      exact hu₂_notX ⟨hu₂, hC_sub_G₂ i₁ hu₂_C⟩
    · obtain ⟨i₂, rfl⟩ := h₂
      have hu₁_notX : u₁ ∉ X := by rwa [← hrange_v]
      rw [hηv_not_X u₁ hu₁_notX, hηv_v i₂, Set.disjoint_singleton_left]
      intro hu₁_C
      exact hu₁_notX ⟨hu₁, hC_sub_G₂ i₂ hu₁_C⟩
    · have hu₁_notX : u₁ ∉ X := by rwa [← hrange_v]
      have hu₂_notX : u₂ ∉ X := by rwa [← hrange_v]
      rw [hηv_not_X u₁ hu₁_notX, hηv_not_X u₂ hu₂_notX, Set.disjoint_singleton]
      exact hne
  have hexp : IsExpansion Q₁ Q ηv id := by
    refine ⟨fun u _ ↦ ⟨u, hself_mem_ηv u⟩, hηv_sub_G,
      fun e he ↦ hH₁_le.edgeSet_subset he, hηv_disj, Set.injOn_id _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [Q.restrict_dom hH₁_le]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he⟩⟩
    · intro e he _ u hu
      have hu' : Q.G.Inc e u := by
        have hEq := hH₁_le.ends_eq e he
        exact (congrArg (u ∈ ·) hEq).mpr hu
      exact ⟨u, hself_mem_ηv u, hu'⟩
    · intro e _
      rfl
    · intro e _ i hi₁ _
      exact hself_mem_ηv ((Q.μ e)[i]'hi₁)
    · exact hπ₁_len
    · intro i hi₁ hi'
      have hget : Q₁.G.roots[i]'hi₁ = v ⟨i, hi'⟩ := by simp [Q₁, Patchwork.restrict, H₁, π₁]
      rw [hget, hηv_v ⟨i, hi'⟩]
      exact hC_root ⟨i, hi'⟩
    · intro e hd δ hδ
      have hd_H₁ : e ∈ H₁.edgeSet := Q₁.dom_subset hd
      have hd_Q : e ∈ Q.dom := (Q.restrict_dom hH₁_le ▸ hd).1
      have hδ_Q : δ ∈ (Q.Δ e).groupings := by
        rwa [Q.restrict_Δ hH₁_le hd_H₁] at hδ
      have hverts : δ.verts ⊆ {w | w ∈ Q.μ e} := by
        rw [((Q.Δ e).verts_eq δ hδ_Q).trans (Q.Δ_verts e (Q.dom_subset hd_Q)), Q.μ_set e hd_Q]
      change marchMapSubgraph (Q.μ e) (Q.μ e) δ ∈ (Q.Δ e).groupings
      rwa [marchMapSubgraph_id hverts]
    · intro _ _
      exact le_rfl
  have hreal : Realizes Q₁ Q ηv id (H ⊔ emptySubgraph G₁.vertexSet) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨δ, hδ, hH_eq⟩ := hH_real
      have hE_diff : G.edgeSet \ (id '' H₁.edgeSet) = G₂.edgeSet := by
        rw [Set.image_id]
        ext e
        simp only [Set.mem_sdiff]
        constructor
        · rintro ⟨heG, he₁⟩
          have hunion : e ∈ G₁.edgeSet ∪ G₂.edgeSet := by
            change e ∈ (G₁.toHypergraph ∪ G₂.toHypergraph).edgeSet
            rwa [hsep.isSeparation.union_eq]
          exact hunion.resolve_left he₁
        · intro he₂
          refine ⟨hsep.isSeparation.right_le.edgeSet_subset he₂, fun he₁ ↦ ?_⟩
          have he_inter : e ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).edgeSet := ⟨he₁, he₂⟩
          rw [hsep.isSeparation.edgeSet_inter_eq] at he_inter
          exact he_inter
      have hδ' : ∀ e ∈ (Q.deleteEdges (id '' H₁.edgeSet)).G.edgeSet,
          δ e ∈ (Q.deleteEdges (id '' H₁.edgeSet)).Δ e := by
        intro e he
        have he₂ : e ∈ G₂.edgeSet := hE_diff ▸ he
        have hδe := hδ e he₂
        rwa [Q.restrict_Δ hsep.isSeparation.right_le he₂] at hδe
      have hreal' : (Q.deleteEdges (id '' H₁.edgeSet)).IsRealization
          (realizationOf (Q.deleteEdges (id '' H₁.edgeSet)).G.toHypergraph δ) :=
        ⟨δ, hδ', rfl⟩
      refine ⟨δ, hδ', ?_⟩
      ext x y
      · have hverts1 : (H ⊔ emptySubgraph G₁.vertexSet).verts = G.vertexSet := by
          rw [Subgraph.verts_sup, hH_verts, emptySubgraph_verts, Set.union_comm]
          exact isSeparation_vertexSet_union hsep.isSeparation
        have hverts2 : (realizationOf (Q.deleteEdges (id '' Q₁.G.edgeSet)).G.toHypergraph δ).verts =
            G.vertexSet := hreal'.verts_eq
        exact (congrArg (x ∈ ·) (hverts1.trans hverts2.symm)).to_iff
      · rw [hH_eq]
        change ((emptySubgraph G₂.vertexSet ⊔ ⨆ e ∈ G₂.edgeSet, δ e) ⊔
            emptySubgraph G₁.vertexSet).Adj x y ↔
          (emptySubgraph G.vertexSet ⊔ ⨆ e ∈ G.edgeSet \ (id '' H₁.edgeSet), δ e).Adj x y
        rw [hE_diff]
        simp [Subgraph.sup_adj, Subgraph.iSup_adj]
    · intro u hu
      have huG₁ : u ∈ G₁.vertexSet := hu
      by_cases h : ∃ i : Fin k, v i = u
      · obtain ⟨i, rfl⟩ := h
        exact ⟨C i, (hC_comp i).sup_emptySubgraph G₁.vertexSet, (hηv_v i).symm⟩
      · have hu_notX : u ∉ X := by rwa [← hrange_v]
        have hu_notH : u ∉ H.verts := by
          rw [hH_verts]
          intro hu₂
          exact hu_notX ⟨huG₁, hu₂⟩
        refine ⟨component (H ⊔ emptySubgraph G₁.vertexSet) ⟨u, Or.inr huG₁⟩, ⟨_, rfl⟩, ?_⟩
        rw [component_sup_emptySubgraph_verts_of_notMem H huG₁ hu_notH, hηv_not_X u hu_notX]
  exact ⟨ηv, id, IsRealizableExpansion.congr hQ₁_agrees.symm hQ_rfl ⟨hexp, _, hreal⟩⟩

/-! ### Verification of Axiom 4 (Section 9, page 252) -/

omit [Preorder Ω] in
open Classical in
private theorem index_le_of_starClass {P : ℕ → Patchwork Ω α β} {n : ℕ}
    {S : RootedTree ι} {σ : ι → RootedHypergraph α β}
    (hp : (S, σ) ∈ starClass ι (patchworkClass P) n) :
    index S σ ≤ n := by
  obtain ⟨⟨hstar, htd⟩, _, hcard⟩ := hp
  refine Finset.sup_le fun s hs ↦ ?_
  have hsub : ((σ s).roots.toFinset : Set α) ⊆ (σ S.root).vertexSet := by
    intro v hv
    rw [Finset.mem_coe, List.mem_toFinset] at hv
    by_cases hsr : s = S.root
    · subst hsr
      exact (σ S.root).roots_subset v hv
    · have hs_edge : s ∈ S.edges := Finset.mem_erase.mpr ⟨hsr, hs⟩
      have hv_rootSet : v ∈ (σ s).rootSet := hv
      rw [htd.rootSet_edge s hs_edge, hstar s hs_edge] at hv_rootSet
      exact hv_rootSet.2
  have hncard : ((σ s).roots.toFinset : Set α).ncard = (σ s).roots.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (σ s).roots_nodup]
  rw [← hncard]
  exact (Set.ncard_le_ncard hsub (σ S.root).vertexSet_finite).trans hcard

open Classical in
/-- Graph Minors IV, Section 9, Axiom 4 (page 252):
verification of `Axiom4 ι` for `patchworkClass P` and `patchworkSim P` for every tree vertex type
`ι`. -/
theorem axiom4_patchwork (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    {P : ℕ → Patchwork Ω α β}
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet)
    (hrob : ∀ i, (P i).IsRobust) (ι : Type*) :
    Axiom4 ι (patchworkClass P) (patchworkSim P) := by
  intro n
  refine ⟨fun _ hp ↦ hp.1, fun _ hp ↦ hp.2.1, ⟨n, fun _ hp ↦ index_le_of_starClass hp⟩, ?_⟩
  intro x hx hwqo_tips
  let S (i : ℕ) : RootedTree ι := (x i).1
  let σ (i : ℕ) : ι → RootedHypergraph α β := (x i).2
  let G (i : ℕ) : RootedHypergraph α β := cross (σ i) (S i).verts (S i).root
  let Q (i : ℕ) : Patchwork Ω α β := inducedPatchwork P (G i)
  have hrem : ∀ i, (Q i).IsRemovable := fun i ↦ inducedPatchwork_isRemovable hrob (G i)
  have hstar : ∀ i, (S i).IsStar := fun i ↦ (hx i).1.1
  have htd : ∀ i, IsTreeDecomposition (Q i).G (S i) (σ i) := fun i ↦ (hx i).1.2
  have hcard : ∀ i, (σ i (S i).root).vertexSet.ncard ≤ n := fun i ↦ (hx i).2.2
  have hwqo : ∀ T : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, T k = (Q i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (T j) (T j') := by
    intro T hT
    let ik (k : ℕ) : ℕ := (hT k).choose
    let sk (k : ℕ) : ι := (hT k).choose_spec.choose
    have hsk_edge : ∀ k, sk k ∈ (S (ik k)).edges :=
      fun k ↦ (hT k).choose_spec.choose_spec.1
    have hTk_eq : ∀ k, T k = (Q (ik k)).restrict (σ (ik k) (sk k)) :=
      fun k ↦ (hT k).choose_spec.choose_spec.2
    have hmem_tips : ∀ k, σ (ik k) (sk k) ∈ ⋃ i, tips (S i) (σ i) :=
      fun k ↦ Set.mem_iUnion.mpr ⟨ik k, sk k, hsk_edge k, rfl⟩
    obtain ⟨j, j', hlt, hsim⟩ := hwqo_tips (fun k ↦ σ (ik k) (sk k)) hmem_tips
    have h_agrees : ∀ k, (inducedPatchwork P (σ (ik k) (sk k))).Agrees (T k) := by
      intro k
      rw [hTk_eq k]
      have hle : (σ (ik k) (sk k)).toHypergraph ≤ (G (ik k)).toHypergraph :=
        (htd (ik k)).le (sk k) (Finset.mem_of_mem_erase (hsk_edge k))
      exact inducedPatchwork_restrict_agrees hdisj (hx (ik k)).2.1 hle
    obtain ⟨ηv, ηe, hη⟩ := hsim
    exact ⟨j, j', hlt, ηv, ηe, hη.congr (h_agrees j) (h_agrees j')⟩
  exact theorem_8_4_proof hH hΩ n Q hrem S σ hstar htd hcard hwqo

/-! ### Graph Minors IV, (9.1) (page 252) -/

open Classical in
/-- Graph Minors IV, (9.1) for a sequence of edge-disjoint robust `Ω`-patchworks. -/
theorem theorem_9_1_disjoint (h53 : Theorem53Statement.{u, v}) (hM : MengerStatement.{u, v})
    (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β)
    (hdisj : Pairwise fun i j ↦ Disjoint (P i).G.edgeSet (P j).G.edgeSet)
    (hrob : ∀ i, (P i).IsRobust)
    (htw : ∀ i, TreeWidthLE (P i).G n) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') := by
  have hmem : ∀ i, (P i).G ∈ patchworkClass P := fun i ↦ ⟨i, le_rfl⟩
  obtain ⟨i, i', hlt, ηv, ηe, hη⟩ := h53 (patchworkClass P) (patchworkSim P)
    (axiom1_patchwork P) (axiom2_patchwork P) (axiom3_patchwork hM hdisj hrob)
    (axiom4_patchwork hH hΩ hdisj hrob ℕ) n (fun i ↦ (P i).G) hmem htw
  exact ⟨i, i', hlt, ηv, ηe,
    hη.congr (inducedPatchwork_self_agrees hdisj i) (inducedPatchwork_self_agrees hdisj i')⟩

open Classical in
/-- Tagging the edges of a hypergraph `G` with an index `i : ℕ` so that a sequence of hypergraphs
becomes pairwise edge-disjoint while keeping the same vertex type `α`. -/
def tagEdgeHypergraph (i : ℕ) (G : Hypergraph α β) : Hypergraph α (ℕ × β) where
  vertexSet := G.vertexSet
  edgeSet := Prod.mk i '' G.edgeSet
  Inc p v := p.1 = i ∧ G.Inc p.2 v
  vertex_mem_of_inc _ _ h := G.vertex_mem_of_inc h.2
  edge_mem_of_inc p _ h := ⟨p.2, G.edge_mem_of_inc h.2, Prod.ext h.1.symm rfl⟩
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.image (Prod.mk i)

open Classical in
/-- Tagging the edges of a rooted hypergraph `G` with `i : ℕ`. -/
def tagEdgeRooted (i : ℕ) (G : RootedHypergraph α β) : RootedHypergraph α (ℕ × β) where
  toHypergraph := tagEdgeHypergraph i G.toHypergraph
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset := G.roots_subset

omit [Preorder Ω] in
open Classical in
@[simp]
theorem tagEdgeHypergraph_ends (i : ℕ) (G : Hypergraph α β) (e : β) :
    (tagEdgeHypergraph i G).ends (i, e) = G.ends e := by
  ext v
  simp [tagEdgeHypergraph, Hypergraph.ends]

open Classical in
/-- Tagging the edges of an `Ω`-patchwork `P` with `i : ℕ`. -/
def tagEdgePatchwork (i : ℕ) (P : Patchwork Ω α β) : Patchwork Ω α (ℕ × β) where
  G := tagEdgeRooted i P.G
  dom := Prod.mk i '' P.dom
  μ p := P.μ p.2
  Δ p := P.Δ p.2
  φ p := P.φ p.2
  dom_subset := Set.image_mono P.dom_subset
  μ_nodup := by
    rintro _ ⟨e, he, rfl⟩
    exact P.μ_nodup e he
  μ_set := by
    rintro _ ⟨e, he, rfl⟩
    rw [P.μ_set e he]
    exact (tagEdgeHypergraph_ends i P.G.toHypergraph e).symm
  Δ_verts := by
    rintro _ ⟨e, he, rfl⟩
    rw [P.Δ_verts e he]
    exact (tagEdgeHypergraph_ends i P.G.toHypergraph e).symm
  Δ_free := by
    rintro _ ⟨e, he, rfl⟩ hnd
    exact P.Δ_free e he fun hd ↦ hnd ⟨e, hd, rfl⟩

omit [Preorder Ω] in
open Classical in
theorem tagEdgePatchwork_disjoint (P : ℕ → Patchwork Ω α β) :
    Pairwise fun i j ↦
      Disjoint (tagEdgePatchwork i (P i)).G.edgeSet (tagEdgePatchwork j (P j)).G.edgeSet := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro _ ⟨e₁, _, rfl⟩ ⟨e₂, _, hEq⟩
  exact hij (congrArg Prod.fst hEq).symm

omit [Preorder Ω] in
open Classical in
theorem tagEdgePatchwork_isRobust {P : Patchwork Ω α β} (hrob : P.IsRobust) (i : ℕ) :
    (tagEdgePatchwork i P).IsRobust := by
  rintro _ ⟨e, he, rfl⟩
  exact hrob e he

omit [Preorder Ω] in
open Classical in
theorem tagEdgeRooted_treeWidthLE {G : RootedHypergraph α β} {n : ℕ}
    (htw : TreeWidthLE G n) (i : ℕ) :
    TreeWidthLE (tagEdgeRooted i G) n := by
  obtain ⟨T, τ, htd, hwidth⟩ := htw
  refine ⟨T, fun t ↦ tagEdgeRooted i (τ t), ⟨?_, ?_, ?_, ?_, htd.roots_root, htd.rootSet_edge⟩,
    hwidth⟩
  · intro t ht
    have hle := htd.le t ht
    refine ⟨hle.vertexSet_subset, Set.image_mono hle.edgeSet_subset, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simp only [tagEdgeRooted, tagEdgeHypergraph_ends]
    exact hle.ends_eq e he
  · ext : 1
    · change (Hypergraph.biUnion T.verts fun t ↦ (τ t).toHypergraph).vertexSet = G.vertexSet
      exact congrArg Hypergraph.vertexSet htd.biUnion_eq
    · simp only [Hypergraph.biUnion, tagEdgeRooted, tagEdgeHypergraph]
      rw [← Set.image_iUnion₂]
      exact congrArg (Prod.mk i '' ·) (congrArg Hypergraph.edgeSet htd.biUnion_eq)
    · ext ⟨j, e⟩ v
      simp only [Hypergraph.biUnion, tagEdgeRooted, tagEdgeHypergraph]
      constructor
      · rintro ⟨t, ht, rfl, hinc⟩
        refine ⟨rfl, ?_⟩
        have hEq := congrFun (congrFun (congrArg Hypergraph.Inc htd.biUnion_eq) e) v
        exact hEq.mp ⟨t, ht, hinc⟩
      · rintro ⟨rfl, hinc⟩
        have hEq := congrFun (congrFun (congrArg Hypergraph.Inc htd.biUnion_eq) e) v
        obtain ⟨t, ht, hinc'⟩ := hEq.mpr hinc
        exact ⟨t, ht, rfl, hinc'⟩
  · intro t₁ ht₁ t₂ ht₂ hne
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₂, he₂, hEq⟩⟩
    obtain rfl : e₁ = e₂ := congrArg Prod.snd hEq.symm
    have he_inter : e₁ ∈ ((τ t₁).toHypergraph ∩ (τ t₂).toHypergraph).edgeSet := ⟨he₁, he₂⟩
    rw [htd.edgeSet_inter_eq t₁ ht₁ t₂ ht₂ hne] at he_inter
    exact he_inter
  · intro t₁ ht₁ t₂ ht₂ t₃ ht₃ hpath
    have hle := htd.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hpath
    refine ⟨hle.vertexSet_subset, ?_, ?_⟩
    · rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₃, he₃, hEq⟩⟩
      obtain rfl : e₁ = e₃ := congrArg Prod.snd hEq.symm
      exact ⟨e₁, hle.edgeSet_subset ⟨he₁, he₃⟩, rfl⟩
    · rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₃, he₃, hEq⟩⟩
      obtain rfl : e₁ = e₃ := congrArg Prod.snd hEq.symm
      ext v
      have hends := congrArg (v ∈ ·) (hle.ends_eq e₁ ⟨he₁, he₃⟩)
      dsimp only [Hypergraph.ends, Inter.inter, tagEdgeRooted, tagEdgeHypergraph] at hends ⊢
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hends ⊢
      exact ⟨fun h ↦ ⟨⟨rfl, (hends.mp h.2).1⟩, ⟨rfl, (hends.mp h.2).2⟩⟩,
        fun ⟨h₁, h₃⟩ ↦ ⟨rfl, hends.mpr ⟨h₁.2, h₃.2⟩⟩⟩

open Classical in
theorem simulated_of_tagEdgePatchwork {P P' : Patchwork Ω α β} {i i' : ℕ}
    (hsim : Simulated (tagEdgePatchwork i P) (tagEdgePatchwork i' P')) :
    Simulated P P' := by
  obtain ⟨ηv, ηe', hexp', H, hreal'⟩ := hsim
  let ηe (e : β) : β := (ηe' (i, e)).2
  have hηe_eq : ∀ e ∈ P.G.edgeSet, ηe' (i, e) = (i', ηe e) := by
    intro e he
    obtain ⟨e', _, hEq⟩ := hexp'.edge_mem (i, e) ⟨e, he, rfl⟩
    exact Prod.ext (congrArg Prod.fst hEq).symm rfl
  have hηe_mem : ∀ e ∈ P.G.edgeSet, ηe e ∈ P'.G.edgeSet := by
    intro e he
    obtain ⟨e', he', hEq⟩ := hexp'.edge_mem (i, e) ⟨e, he, rfl⟩
    have hsnd : e' = ηe e := congrArg Prod.snd hEq
    exact hsnd ▸ he'
  have hexp : IsExpansion P P' ηv ηe := by
    refine ⟨hexp'.vertex_nonempty, hexp'.vertex_subset, hηe_mem, hexp'.vertex_disjoint,
      ?_, ?_, ?_, ?_, ?_, hexp'.roots_length, hexp'.roots_mem, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hEq
      have hEq' : ηe' (i, e₁) = ηe' (i, e₂) := by
        rw [hηe_eq e₁ he₁, hηe_eq e₂ he₂, hEq]
      have hinj := hexp'.edge_injOn ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩ hEq'
      exact congrArg Prod.snd hinj
    · intro e he
      have hdom := hexp'.mem_dom_iff (i, e) ⟨e, he, rfl⟩
      rw [hηe_eq e he] at hdom
      simp only [tagEdgePatchwork, Set.mem_image, Prod.mk.injEq, true_and, exists_eq_right] at hdom
      exact hdom
    · intro e he hnd v hv
      have hnd' : (i, e) ∉ (tagEdgePatchwork i P).dom := by
        rintro ⟨e₁, hd₁, hEq⟩
        obtain rfl : e₁ = e := congrArg Prod.snd hEq
        exact hnd hd₁
      obtain ⟨v', hv', hinc'⟩ := hexp'.ends_nonempty (i, e) ⟨e, he, rfl⟩ hnd' v ⟨rfl, hv⟩
      rw [hηe_eq e he] at hinc'
      exact ⟨v', hv', hinc'.2⟩
    · intro e hd
      exact hexp'.μ_length (i, e) ⟨e, hd, rfl⟩
    · intro e hd j hj₁ hj'
      exact hexp'.μ_mem (i, e) ⟨e, hd, rfl⟩ j hj₁ hj'
    · intro e hd
      exact hexp'.maps_Δ (i, e) ⟨e, hd, rfl⟩
    · intro e he
      exact hexp'.φ_le (i, e) ⟨e, he, rfl⟩
  have hreal : Realizes P P' ηv ηe H := by
    refine ⟨?_, hreal'.2⟩
    obtain ⟨δ', hδ', rfl⟩ := hreal'.1
    let δ (e' : β) : (⊤ : SimpleGraph α).Subgraph := δ' (i', e')
    have hmem_del : ∀ e' : β,
        e' ∈ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet ↔
          (i', e') ∈ ((tagEdgePatchwork i' P').deleteEdges
            (ηe' '' (tagEdgePatchwork i P).G.edgeSet)).G.edgeSet := by
      intro e'
      simp only [Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
        tagEdgePatchwork, tagEdgeRooted, tagEdgeHypergraph, Set.mem_sdiff, Set.mem_image,
        Prod.mk.injEq, true_and, exists_eq_right]
      refine and_congr_right fun _ ↦ not_congr ?_
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨(i, e), ⟨e, he, rfl⟩, hηe_eq e he⟩
      · rintro ⟨_, ⟨e, he, rfl⟩, hEq⟩
        rw [hηe_eq e he] at hEq
        exact ⟨e, he, congrArg Prod.snd hEq⟩
    refine ⟨δ, fun e' he' ↦ hδ' (i', e') ((hmem_del e').mp he'), ?_⟩
    ext x y
    · simp only [realizationOf, Patchwork.deleteEdges, RootedHypergraph.deleteEdges,
        Hypergraph.deleteEdges, Subgraph.verts_sup, Subgraph.verts_iSup, emptySubgraph_verts,
        tagEdgePatchwork, tagEdgeRooted, tagEdgeHypergraph]
      refine or_congr_right ?_
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨⟨j, e'⟩, hje', hxy⟩
        have hj : j = i' := by
          rcases hje'.1 with ⟨_, _, hEq⟩
          exact (congrArg Prod.fst hEq).symm
        subst hj
        exact ⟨e', (hmem_del e').mpr hje', hxy⟩
      · rintro ⟨e', he', hxy⟩
        exact ⟨(i', e'), (hmem_del e').mp he', hxy⟩
    · simp only [realizationOf, Subgraph.sup_adj, not_emptySubgraph_adj, false_or,
        Subgraph.iSup_adj]
      constructor
      · rintro ⟨⟨j, e'⟩, hje', hxy⟩
        have hj : j = i' := by
          rcases hje'.1 with ⟨_, _, hEq⟩
          exact (congrArg Prod.fst hEq).symm
        subst hj
        exact ⟨e', (hmem_del e').mpr hje', hxy⟩
      · rintro ⟨e', he', hxy⟩
        exact ⟨(i', e'), (hmem_del e').mp he', hxy⟩
  exact ⟨ηv, ηe, hexp, H, hreal⟩

open Classical in
/-- **Graph Minors IV, (9.1)** (page 252):
"Let $n \ge 0$, let $\Omega$ be a well-quasi-order, and let $P_i = (G_i, \mu_i, \Delta_i,
\phi_i)$ $(i = 1, 2, \dots)$ be a countable sequence of robust $\Omega$-patchworks, where
each $G_i$ has tree-width $\le n$. Then there exist $i' > i \ge 1$ such that there is a
realizable expansion of $P_i$ in $P_{i'}$."

Following the paper ("We may assume that $G_1, G_2, \dots$ are mutually disjoint, and hence we may
define
$\mathscr{R}$, etc. as at the start of this section; and the claim follows from (5.3)"), we tag the
edges of
each `Pᵢ` with `i` via `tagEdgePatchwork i (P i) : Patchwork Ω α (ℕ × β)` so that the hypergraphs
have pairwise disjoint edge sets without changing the universe `v`, apply `theorem_9_1_disjoint`,
and pull back the resulting simulation along `simulated_of_tagEdgePatchwork`. -/
theorem theorem_9_1_proof (h53 : Theorem53Statement.{u, v}) (hM : MengerStatement.{u, v})
    (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β)
    (hrob : ∀ i, (P i).IsRobust)
    (htw : ∀ i, TreeWidthLE (P i).G n) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') := by
  let P' (i : ℕ) : Patchwork Ω α (ℕ × β) := tagEdgePatchwork i (P i)
  obtain ⟨i, i', hlt, hsim⟩ := theorem_9_1_disjoint h53 hM hH hΩ n P'
    (tagEdgePatchwork_disjoint P)
    (fun i ↦ tagEdgePatchwork_isRobust (hrob i) i)
    (fun i ↦ tagEdgeRooted_treeWidthLE (htw i) i)
  exact ⟨i, i', hlt, simulated_of_tagEdgePatchwork hsim⟩

end GraphMinor.GM04
