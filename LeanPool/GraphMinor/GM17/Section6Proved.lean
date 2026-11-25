/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section6
import LeanPool.GraphMinor.GM17.Section5Proved

public import LeanPool.GraphMinor.GM17.Section5

import LeanPool.GraphMinor.Surface.Cuffs

import LeanPool.GraphMinor.GM17.ArcDisc

import LeanPool.GraphMinor.GM17.CutArcPaint

import LeanPool.GraphMinor.GM17.PasteCuff

import LeanPool.GraphMinor.GM17.PushNode

/-!
# Graph Minors XVII: proved deductions of Section6

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section6`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Quotient Hypergraphs and Graph Minors XVII, (6.1) (Page 174) -/

/-- **Graph Minors XVII, (6.3)** (page 174):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$, with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F
\subseteq \Sigma$ be a $\Gamma$-normal $I$-arc with ends $n_1, n_2$ and with $|F \cap
dom(\gamma)| \le z - 2p$. Then there is a disc $\Delta \subseteq \Sigma$ with $F \subseteq
bd(\Delta) \subseteq F \cup bd(\Sigma)$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_6_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ)
    {F : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFγ_le : 2 * p ≤ z ∧ (F ∩ π.domγ).ncard ≤ z - 2 * p) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hn₁_mem : n₁ ∈ F ∩ bd π.S := hFbd ▸ mem_insert _ _
  have hn₂_mem : n₂ ∈ F ∩ bd π.S := hFbd ▸ mem_insert_of_mem _ (mem_singleton _)
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S :=
    ⟨hnorm (show n₁ ∈ F ∩ π.Γ.U from ⟨hn₁_mem.1, π.Γ.bd_subset hn₁_mem.2⟩), hn₁_mem.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S :=
    ⟨hnorm (show n₂ ∈ F ∩ π.Γ.U from ⟨hn₂_mem.1, π.Γ.bd_subset hn₂_mem.2⟩), hn₂_mem.2⟩
  let Z : Set α := π.borderSet n₁ ∪ π.borderSet n₂ ∪ π.nodeVertex '' (F ∩ π.domγ)
  have hZ_sub : Z ⊆ G.vertexSet := by
    refine union_subset (union_subset (π.borderSet_subset n₁ hn₁_bd) (π.borderSet_subset n₂
      hn₂_bd)) ?_
    rintro _ ⟨n, ⟨_, hnγ⟩, rfl⟩
    exact π.nodeVertex_mem n hnγ
  have hn₁_card : (π.borderSet n₁).ncard ≤ p :=
    (π.ncard_borderSet_le_warp hn₁_bd).trans hwarp
  have hn₂_card : (π.borderSet n₂).ncard ≤ p :=
    (π.ncard_borderSet_le_warp hn₂_bd).trans hwarp
  have hFγ_fin : (F ∩ π.domγ).Finite :=
    (π.Γ.finite_N.subset π.domγ_subset).inter_of_right F
  have hZ_le : Z.ncard ≤ z := by
    have h1 : Z.ncard ≤ (π.borderSet n₁ ∪ π.borderSet n₂).ncard +
        (π.nodeVertex '' (F ∩ π.domγ)).ncard := ncard_union_le _ _
    have h2 : (π.borderSet n₁ ∪ π.borderSet n₂).ncard ≤
        (π.borderSet n₁).ncard + (π.borderSet n₂).ncard := ncard_union_le _ _
    have h3 : (π.nodeVertex '' (F ∩ π.domγ)).ncard ≤ (F ∩ π.domγ).ncard :=
      ncard_image_le hFγ_fin
    omega
  obtain ⟨hT', _, hred'⟩ :=
    π.quotientBy_resembles_and_isZeroRedundant h𝒯 hT hwarp hred hZ_sub hZ_le (by omega)
  have hTangle' : IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
    theorem_4_2_proof h𝒯 hZ_sub (by omega)
  have hβ₁' : (π.quotientBy Z).borderSet n₁ = ∅ := by
    ext v
    simp only [Portrayal.quotientBy, mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hv => Or.inl (Or.inl hv)
  have hβ₂' : (π.quotientBy Z).borderSet n₂ = ∅ := by
    ext v
    simp only [Portrayal.quotientBy, mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hv => Or.inl (Or.inr hv)
  have hFγ' : F ∩ (π.quotientBy Z).domγ = ∅ := by
    ext n
    simp only [Portrayal.quotientBy, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hnF hnγ => Or.inr ⟨n, ⟨hnF, hnγ⟩, rfl⟩
  have : CompactSpace (π.quotientBy Z).S := (π.quotientBy Z).isSurface.1
  have : T2Space (π.quotientBy Z).S := (π.quotientBy Z).isSurface.2.1
  obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hsmall'⟩ :=
    theorem_5_3_proof hTangle' (by omega) (π.quotientBy Z) hT' hred'
      hnorm hF hFbd hβ₁' hβ₂' hFγ'
  refine ⟨Δ, hΔ, hF_bd, hbd_sub, ?_⟩
  have hatt' := hsmall'.ncard_attachments_lt hTangle'
  rw [π.quotientBy_areaGraph Z Δ] at hsmall' hatt'
  exact (theorem_6_1_proof h𝒯 hZ_sub (by omega) (π.cellsUnion_le _) hatt').mpr hsmall'

/-- **Graph Minors XVII, (6.4)** (page 175):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$, with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F
\subseteq \Sigma$ be a $\Gamma$-normal $O$-arc with $|F \cap dom(\gamma)| \le z$. Then there
is a disc $\Delta \subseteq \Sigma$ with $bd(\Delta) = F$ such that $\alpha(\Delta)$ is
small." -/
theorem theorem_6_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ)
    {F : Set π.S} (hO : IsOArc F) (hnorm : π.Γ.IsNormal F)
    (hFγ_le : (F ∩ π.domγ).ncard ≤ z) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  let Z : Set α := π.nodeVertex '' (F ∩ π.domγ)
  have hZ_sub : Z ⊆ G.vertexSet := by
    rintro _ ⟨n, ⟨_, hnγ⟩, rfl⟩
    exact π.nodeVertex_mem n hnγ
  have hFγ_fin : (F ∩ π.domγ).Finite :=
    (π.Γ.finite_N.subset π.domγ_subset).inter_of_right F
  have hZ_le : Z.ncard ≤ z :=
    (ncard_image_le hFγ_fin).trans hFγ_le
  obtain ⟨hT', _, hred'⟩ :=
    π.quotientBy_resembles_and_isZeroRedundant h𝒯 hT hwarp hred hZ_sub hZ_le (by omega)
  have hTangle' : IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
    theorem_4_2_proof h𝒯 hZ_sub (by omega)
  have hFγ' : F ∩ (π.quotientBy Z).domγ = ∅ := by
    ext n
    simp only [Portrayal.quotientBy, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hnF hnγ => ⟨n, ⟨hnF, hnγ⟩, rfl⟩
  have : CompactSpace (π.quotientBy Z).S := (π.quotientBy Z).isSurface.1
  have : T2Space (π.quotientBy Z).S := (π.quotientBy Z).isSurface.2.1
  obtain ⟨Δ, hΔ, hbd_eq, hsmall'⟩ :=
    theorem_5_4_proof hTangle' (by omega) (π.quotientBy Z) hT' hred'
      hnorm hO hFγ'
  refine ⟨Δ, hΔ, hbd_eq, ?_⟩
  have hatt' := hsmall'.ncard_attachments_lt hTangle'
  rw [π.quotientBy_areaGraph Z Δ] at hsmall' hatt'
  exact (theorem_6_1_proof h𝒯 hZ_sub (by omega) (π.cellsUnion_le _) hatt').mpr hsmall'

/-! ## 3. Separation Restriction Portrayal and (6.5) (Pages 175–176) -/

private lemma walk_skeleton_mono {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (h : H₁ ≤ H₂) {u v : α}
    (W : H₁.skeleton.Walk u v) :
    ∃ W' : H₂.skeleton.Walk u v, W'.support = W.support := by
  induction W with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u w v hadj W ih =>
    obtain ⟨W', hsupp⟩ := ih
    rcases hadj with ⟨hne, e, heu, hew⟩
    have heH₁ : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc heu
    have hends := h.ends_eq e heH₁
    have heu' : H₂.Inc e u := by
      change u ∈ H₂.ends e; rw [hends]; exact heu
    have hew' : H₂.Inc e w := by
      change w ∈ H₂.ends e; rw [hends]; exact hew
    refine ⟨.cons ⟨hne, e, heu', hew'⟩ W', ?_⟩
    dsimp [SimpleGraph.Walk.support]
    rw [hsupp]

private lemma walk_skeleton_union_left_of_disjoint {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (hdisjV : Disjoint H₁.vertexSet H₂.vertexSet)
    (hdisjE : Disjoint H₁.edgeSet H₂.edgeSet)
    {u v : α} (hu : u ∈ H₁.vertexSet) (W : (H₁ ∪ H₂).skeleton.Walk u v) :
    ∃ W' : H₁.skeleton.Walk u v, W'.support = W.support := by
  induction W with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u w v hadj W ih =>
    rcases hadj with ⟨hne, e, heu, hew⟩
    have heu₁ : H₁.Inc e u := by
      rcases heu with heu₁ | heu₂
      · exact heu₁
      · exact (Set.disjoint_left.mp hdisjV hu (H₂.vertex_mem_of_inc heu₂)).elim
    have hew₁ : H₁.Inc e w := by
      rcases hew with hew₁ | hew₂
      · exact hew₁
      · exact (Set.disjoint_left.mp hdisjE (H₁.edge_mem_of_inc heu₁)
          (H₂.edge_mem_of_inc hew₂)).elim
    have hw : w ∈ H₁.vertexSet := H₁.vertex_mem_of_inc hew₁
    obtain ⟨W', hsupp⟩ := ih hw
    refine ⟨.cons ⟨hne, e, heu₁, hew₁⟩ W', ?_⟩
    dsimp [SimpleGraph.Walk.support]
    rw [hsupp]

private lemma walk_support_subset_vertexSet {α : Type u} {β : Type v}
    {H : Hypergraph α β} {u v : α} (hu : u ∈ H.vertexSet)
    (W : H.skeleton.Walk u v) :
    {z | z ∈ W.support} ⊆ H.vertexSet :=
  fun _ hz => Hypergraph.skeleton_walk_support_subset_vertexSet W hu _ hz

/-- Given a portrayal $\pi$ of $G$, a separation $(A, B)$ of $G$ with $Z = V(A \cap B)$, and a
cell $c' \in C(\Gamma)$, the portrayal $\pi' = (\Sigma, \Gamma, \alpha', \beta', \gamma')$ of
$G / Z$ constructed in the proof of (6.5) (page 175), where
$\alpha'(c') = ((\alpha(c') \cap B) / Z) \cup (A / Z)$,
$\alpha'(c) = (\alpha(c) \cap B) / Z$ for $c \ne c'$,
$\beta'(n) = \beta(n) \setminus V(A)$, and
$\gamma' = \gamma \mid \{n \in \operatorname{dom}(\gamma) : \gamma(n) \notin V(A)\}$. -/
theorem Portrayal.restrictQuotient_walk_lift {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) (hsep : IsSeparation G A B)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C) {c : Set π.S} (hc : c ∈ π.Γ.C)
    {u v : α} (hu : u ∈ (π.cellGraph c).vertexSet \ A.vertexSet)
    (W : ((π.restrictQuotient A B hsep c' hc').cellGraph c).skeleton.Walk u v) :
    ∃ W' : (π.cellGraph c ∩ B).skeleton.Walk u v,
      W'.support = W.support ∧ {z | z ∈ W'.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
  classical
  have huG : u ∈ G.vertexSet := (π.cellGraph_le c hc).1 hu.1
  have huAB : u ∈ A.vertexSet ∪ B.vertexSet := hsep.vertexSet_union ▸ huG
  have huB : u ∈ B.vertexSet := huAB.resolve_left hu.2
  have huZ : u ∉ A.vertexSet ∩ B.vertexSet := fun hZ => hu.2 hZ.1
  have huQB : u ∈ (quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩ B.vertexSet)).vertexSet :=
    ⟨⟨hu.1, huB⟩, huZ⟩
  have hW_QB : ∃ W₀ : (quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩
    B.vertexSet)).skeleton.Walk u v,
      W₀.support = W.support := by
    by_cases hcc' : c = c'
    · have hle : (π.restrictQuotient A B hsep c' hc').cellGraph c ≤
          quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩ B.vertexSet) ∪
          quotientVertices A (A.vertexSet ∩ B.vertexSet) := by
        change (if c = c' then _ else _) ≤ _
        rw [ite_eq_left hcc']
      obtain ⟨W₁, hsupp₁⟩ := walk_skeleton_mono hle W
      have hdisjV : Disjoint
          (quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩ B.vertexSet)).vertexSet
          (quotientVertices A (A.vertexSet ∩ B.vertexSet)).vertexSet := by
        refine Set.disjoint_left.mpr fun x ⟨⟨_, hxB⟩, hxZ⟩ ⟨hxA, _⟩ => hxZ ⟨hxA, hxB⟩
      have hdisjE : Disjoint
          (quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩ B.vertexSet)).edgeSet
          (quotientVertices A (A.vertexSet ∩ B.vertexSet)).edgeSet := by
        have hdisjAB : Disjoint A.edgeSet B.edgeSet :=
          Set.disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq
        refine Set.disjoint_left.mpr fun e ⟨_, heB⟩ heA => Set.disjoint_left.mp hdisjAB heA heB
      obtain ⟨W₀, hsupp₀⟩ := walk_skeleton_union_left_of_disjoint hdisjV hdisjE huQB W₁
      exact ⟨W₀, hsupp₀.trans hsupp₁⟩
    · have hle : (π.restrictQuotient A B hsep c' hc').cellGraph c ≤
          quotientVertices (π.cellGraph c ∩ B) (A.vertexSet ∩ B.vertexSet) := by
        change (if c = c' then _ else _) ≤ _
        rw [ite_eq_right hcc']
      exact walk_skeleton_mono hle W
  obtain ⟨W₀, hsupp₀⟩ := hW_QB
  have hsub_supp : {z | z ∈ W₀.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
    intro z hz
    have hzQB := walk_support_subset_vertexSet huQB W₀ hz
    exact ⟨hzQB.1.1, fun hzA => hzQB.2 ⟨hzA, hzQB.1.2⟩⟩
  obtain ⟨W', hsupp'⟩ := walk_skeleton_of_quotientVertices W₀
  exact ⟨W', hsupp'.trans hsupp₀, fun z hz => hsub_supp (by rwa [← hsupp'])⟩

theorem Portrayal.restrictQuotient_cellWarp_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) (hsep : IsSeparation G A B)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty) :
    (π.restrictQuotient A B hsep c' hc').cellWarp c ≤ π.cellWarp c := by
  apply Nat.sInf_le
  intro n₁ hn₁ n₂ hn₂ hne
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := π.Γ.border_cell_exists_ends hc hbd
  have hn₁' : n₁ ∈ ({u, v} : Set π.S) := htilde ▸ hn₁
  have hn₂' : n₂ ∈ ({u, v} : Set π.S) := htilde ▸ hn₂
  have hn₁_mem : n₁ ∈ π.Γ.N ∩ bd π.S := by rcases hn₁' with rfl | rfl <;> assumption
  have hn₂_mem : n₂ ∈ π.Γ.N ∩ bd π.S := by rcases hn₂' with rfl | rfl <;> assumption
  have hspec := π.cellWarp_spec hc hbd n₁ hn₁ n₂ hn₂ hne
  refine ⟨(ncard_le_ncard sdiff_subset (π.borderSet_finite hn₁_mem)).trans hspec.1,
    (ncard_le_ncard sdiff_subset (π.borderSet_finite hn₂_mem)).trans hspec.2.1,
    fun hcard₁ hcard₂ P hP_disj => ?_⟩
  have hbp₁ := π.restrictQuotient_borderPlus A B hsep c' hc' n₁
  have hbp₂ := π.restrictQuotient_borderPlus A B hsep c' hc' n₂
  have hcard₁₀ : (π.borderPlus n₁ \ A.vertexSet).ncard = π.cellWarp c + 1 := hbp₁ ▸ hcard₁
  have hcard₂₀ : (π.borderPlus n₂ \ A.vertexSet).ncard = π.cellWarp c + 1 := hbp₂ ▸ hcard₂
  have hle₁ : (π.borderPlus n₁).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hn₁_mem).trans (Nat.add_le_add_right hspec.1 1)
  have hle₂ : (π.borderPlus n₂).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hn₂_mem).trans (Nat.add_le_add_right hspec.2.1 1)
  have hcard₁' : (π.borderPlus n₁).ncard = π.cellWarp c + 1 := by
    have := ncard_le_ncard (sdiff_subset : π.borderPlus n₁ \ A.vertexSet ⊆ π.borderPlus n₁)
      (π.borderPlus_finite hn₁_mem)
    omega
  have hcard₂' : (π.borderPlus n₂).ncard = π.cellWarp c + 1 := by
    have := ncard_le_ncard (sdiff_subset : π.borderPlus n₂ \ A.vertexSet ⊆ π.borderPlus n₂)
      (π.borderPlus_finite hn₂_mem)
    omega
  have hlift : ∀ i : Fin (π.cellWarp c + 1),
      ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂),
        Q.first = (P i).first ∧ Q.last = (P i).last ∧ Q.walk.support = (P i).walk.support := by
    intro i
    have hfirst_bp : (P i).first ∈ π.borderPlus n₁ \ A.vertexSet :=
      (Set.ext_iff.mp hbp₁ (P i).first).mp (P i).first_mem
    have hlast_bp : (P i).last ∈ π.borderPlus n₂ \ A.vertexSet :=
      (Set.ext_iff.mp hbp₂ (P i).last).mp (P i).last_mem
    have hfirst_c : (P i).first ∈ (π.cellGraph c).vertexSet \ A.vertexSet :=
      ⟨π.borderPlus_subset_cellGraph hc hbd hn₁ hfirst_bp.1, hfirst_bp.2⟩
    obtain ⟨W₀, hsupp₀, _⟩ :=
      π.restrictQuotient_walk_lift A B hsep c' hc' hc hfirst_c (P i).walk
    have hle_c : π.cellGraph c ∩ B ≤ π.cellGraph c :=
      inter_le_left (π.cellGraph_le c hc) hsep.right_le
    obtain ⟨W', hsupp'⟩ := walk_skeleton_mono hle_c W₀
    have hsupp : W'.support = (P i).walk.support := hsupp'.trans hsupp₀
    have hisPath : W'.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hsupp]
      exact SimpleGraph.Walk.IsPath.support_nodup (P i).isPath
    exact ⟨⟨(P i).first, (P i).last, W', hisPath, hfirst_bp.1, hlast_bp.1⟩, rfl, rfl, hsupp⟩
  choose Q hQ_first hQ_last hQ_supp using hlift
  have hQ_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support} := by
    intro i j hij
    rw [hQ_supp i, hQ_supp j]
    exact hP_disj hij
  obtain ⟨i, hfirst, hlast⟩ := hspec.2.2 hcard₁' hcard₂' Q hQ_disj
  exact ⟨i, (hQ_first i).symm.trans hfirst, (hQ_last i).symm.trans hlast⟩

theorem Portrayal.restrictQuotient_warpAt_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) (hsep : IsSeparation G A B)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    (π.restrictQuotient A B hsep c' hc').warpAt Θ ≤ π.warpAt Θ := by
  refine ((π.restrictQuotient A B hsep c' hc').warpAt_le_iff (Θ := Θ)).mpr fun c hc hcΘ => ?_
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
  exact (π.restrictQuotient_cellWarp_le A B hsep c' hc' hc hbd).trans (π.cellWarp_le_warpAt hc hcΘ)

private theorem exists_not_cellWarpLE_pair
    {α β : Type*} {G : Hypergraph α β} {p : ℕ}
    (π : Portrayal G) (c : Set π.S) (hnot_le : ¬π.CellWarpLE c (p - 1)) :
    ∃ m₁ ∈ tilde c, ∃ m₂ ∈ tilde c, m₁ ≠ m₂ ∧
      ¬((π.borderSet m₁).ncard ≤ p - 1 ∧ (π.borderSet m₂).ncard ≤ p - 1 ∧
        ((π.borderPlus m₁).ncard = p - 1 + 1 → (π.borderPlus m₂).ncard = p - 1 + 1 →
          Portrayal.LinkagePairs (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂)
            (p - 1 + 1) (π.nodeVertex m₁) (π.nodeVertex m₂))) := by
  by_contra h_all
  apply hnot_le
  intro m₁ hm₁ m₂ hm₂ hm_ne
  by_contra h_neg
  exact h_all ⟨m₁, hm₁, m₂, hm₂, hm_ne, h_neg⟩

private theorem lift_restricted_linkage_paths
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {p : ℕ}
    (π : Portrayal G)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hsep : G.IsSeparation A B)
    (c : Set π.S)
    (hc : c ∈ (π.restrictQuotient A B hsep c' hc').Γ.C)
    (hbd : (c ∩ bd π.S).Nonempty)
    (m₁ : π.S)
    (hm₁_t : m₁ ∈ tilde c)
    (m₂ : π.S)
    (P : Fin p → PathFromTo ((π.restrictQuotient A B hsep c' hc').cellGraph c).skeleton
      ((π.restrictQuotient A B hsep c' hc').borderPlus m₁) ((π.restrictQuotient A B hsep c'
      hc').borderPlus m₂))
    (hbp₁ : (π.restrictQuotient A B hsep c' hc').borderPlus m₁ = π.borderPlus m₁ \ A.vertexSet)
    (hbp₂ : (π.restrictQuotient A B hsep c' hc').borderPlus m₂ = π.borderPlus m₂ \ A.vertexSet) :
    ∀ i : Fin p, ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
      Q.first = (P i).first ∧ Q.last = (P i).last ∧ Q.walk.support = (P i).walk.support ∧
        {z | z ∈ Q.walk.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
  intro i
  have hfirst_bp : (P i).first ∈ π.borderPlus m₁ \ A.vertexSet :=
    (Set.ext_iff.mp hbp₁ (P i).first).mp (P i).first_mem
  have hlast_bp : (P i).last ∈ π.borderPlus m₂ \ A.vertexSet :=
    (Set.ext_iff.mp hbp₂ (P i).last).mp (P i).last_mem
  have hfirst_c : (P i).first ∈ (π.cellGraph c).vertexSet \ A.vertexSet :=
    ⟨π.borderPlus_subset_cellGraph hc hbd hm₁_t hfirst_bp.1, hfirst_bp.2⟩
  obtain ⟨W₀, hsupp₀, hsub₀⟩ :=
    π.restrictQuotient_walk_lift A B hsep c' hc' hc hfirst_c (P i).walk
  have hle_Bc : π.cellGraph c ∩ B ≤ π.cellGraph c :=
    inter_le_left (π.cellGraph_le c hc) hsep.right_le
  obtain ⟨W', hsupp'⟩ := walk_skeleton_mono hle_Bc W₀
  have hsupp : W'.support = (P i).walk.support := hsupp'.trans hsupp₀
  have hisPath : W'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsupp]
    exact SimpleGraph.Walk.IsPath.support_nodup (P i).isPath
  refine ⟨⟨(P i).first, (P i).last, W', hisPath, hfirst_bp.1, hlast_bp.1⟩,
    rfl, rfl, hsupp, fun z hz => hsub₀ (by rwa [← hsupp'])⟩

private theorem disjoint_paths_with_one_extra {α : Type*} {g : SimpleGraph α}
    {U V A : Set α} {p : ℕ} (Q : Fin p → PathFromTo g U V)
    (Q_extra : PathFromTo g U V)
    (hQ_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support})
    (hQ_sub : ∀ i, {z | z ∈ (Q i).walk.support} ⊆ Aᶜ)
    (hQ_extra : {z | z ∈ Q_extra.walk.support} ⊆ A) :
    let Q_all : Fin (p + 1) → PathFromTo g U V :=
      fun i => if h : i.1 < p then Q ⟨i.1, h⟩ else Q_extra
    Pairwise fun i j => Disjoint {z | z ∈ (Q_all i).walk.support}
      {z | z ∈ (Q_all j).walk.support} := by
  dsimp only
  intro i j hij
  refine Set.disjoint_left.mpr fun z hzi hzj => ?_
  change z ∈ (if h : i.1 < p then Q ⟨i.1, h⟩ else Q_extra).walk.support at hzi
  change z ∈ (if h : j.1 < p then Q ⟨j.1, h⟩ else Q_extra).walk.support at hzj
  by_cases hi : i.1 < p <;> by_cases hj : j.1 < p
  · rw [dite_eq_left hi] at hzi
    rw [dite_eq_left hj] at hzj
    have hij' : (⟨i.1, hi⟩ : Fin p) ≠ ⟨j.1, hj⟩ :=
      fun h => hij (Fin.ext (Fin.mk.inj_iff.mp h))
    exact Set.disjoint_left.mp (hQ_disj hij') hzi hzj
  · rw [dite_eq_left hi] at hzi
    rw [dite_eq_right hj] at hzj
    exact hQ_sub ⟨i.1, hi⟩ hzi (hQ_extra hzj)
  · rw [dite_eq_right hi] at hzi
    rw [dite_eq_left hj] at hzj
    exact hQ_sub ⟨j.1, hj⟩ hzj (hQ_extra hzi)
  · exact hij (Fin.ext (by omega))

private theorem ncard_endsets_ge_of_disjoint_paths {α : Type*} {g : SimpleGraph α}
    {U V : Set α} {p : ℕ} (Q : Fin p → PathFromTo g U V)
    (hQ : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support})
    (hU : U.Finite) (hV : V.Finite) :
    p ≤ U.ncard ∧ p ≤ V.ncard := by
  have cardinal (B : Set α) (hB : B.Finite) (f : Fin p → α) (hf : ∀ i, f i ∈ B)
      (hsupp : ∀ i, f i ∈ (Q i).walk.support) : p ≤ B.ncard := by
    have hinj : Injective f := by
      intro i j h
      by_contra hne
      exact Set.disjoint_left.mp (hQ hne) (hsupp i) (h ▸ hsupp j)
    have hcard : (range f).ncard = p := by
      rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard ▸ ncard_le_ncard (range_subset_iff.mpr hf) hB
  exact ⟨cardinal U hU (fun i => (Q i).first) (fun i => (Q i).first_mem)
      (fun i => (Q i).walk.start_mem_support),
    cardinal V hV (fun i => (Q i).last) (fun i => (Q i).last_mem)
      (fun i => (Q i).walk.end_mem_support)⟩

private theorem exists_borderSet_disjoint_of_sdiff_card
    {α β : Type*} {G : Hypergraph α β} {π : Portrayal G}
    {A : Hypergraph α β} {Θ : Set π.S} {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S) (hΘ_arc : IsOArc Θ) (hp : π.warpAt Θ = p)
    (hΘ_bd : Θ ⊆ bd π.S)
    (hcard : ∃ n ∈ π.Γ.N ∩ Θ, p ≤ (π.borderSet n \ A.vertexSet).ncard) :
    ∃ n ∈ π.Γ.N ∩ Θ, (π.borderSet n).ncard = p ∧ Disjoint (π.borderSet n) A.vertexSet := by
  obtain ⟨n, hn, hle⟩ := hcard
  have hn_bd : n ∈ π.Γ.N ∩ bd π.S := ⟨hn.1, hΘ_bd hn.2⟩
  have hle_p : (π.borderSet n).ncard ≤ p := hp ▸ π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn
  have hsub_le : (π.borderSet n \ A.vertexSet).ncard ≤ (π.borderSet n).ncard :=
    ncard_le_ncard sdiff_subset (π.borderSet_finite hn_bd)
  have h_eq : π.borderSet n \ A.vertexSet = π.borderSet n :=
    eq_of_subset_of_ncard_le sdiff_subset (by omega) (π.borderSet_finite hn_bd)
  refine ⟨n, hn, by omega, Set.disjoint_left.mpr fun v hvn hvA => ?_⟩
  have hvn' : v ∈ π.borderSet n \ A.vertexSet := h_eq.symm ▸ hvn
  exact hvn'.2 hvA

/-- **Graph Minors XVII, (6.5)** (page 175):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$ with $warp \le q$, let $(A, B) \in \mathscr{T}$ have order
$\le z$, let $\Theta$ be a cuff of $\Sigma$, and let $\pi$ have warp $p$ at $\Theta$. Let
$ord(\mathscr{T}) > z + 2q + 2$. Then there exists either* (i) *a node $n$ bordering
$\Theta$ with $|\beta(n)| = p$ and $\beta(n) \cap V(A) = \emptyset$, or* (ii) *a cell $c$
bordering $\Theta$ with ends $n_1, n_2 \in dom(\gamma)$, such that $\gamma(n_1), \gamma(n_2)
\notin V(A)$, there is no path of $(A \cap \alpha(c))^*$ between $\beta(n_1)$ and
$\beta(n_2)$, and* $$|\beta(n_1) - V(A)| = |\beta(n_2) - V(A)| = p - 1 \ge 1.$$" -/
theorem theorem_6_5_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ q p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ q) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * q + 2) < θ)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hord : separationOrder A B ≤ z)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hp : π.warpAt Θ = p) :
    (∃ n ∈ π.Γ.N ∩ Θ, (π.borderSet n).ncard = p ∧ Disjoint (π.borderSet n) A.vertexSet) ∨
    (∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ ∃ n₁ n₂ : π.S, n₁ ≠ n₂ ∧ tilde c = {n₁, n₂} ∧
      n₁ ∈ π.domγ ∧ n₂ ∈ π.domγ ∧
      π.nodeVertex n₁ ∉ A.vertexSet ∧ π.nodeVertex n₂ ∉ A.vertexSet ∧
      (∀ u ∈ (A ∩ π.cellGraph c).vertexSet ∩ π.borderSet n₁,
       ∀ v ∈ (A ∩ π.cellGraph c).vertexSet ∩ π.borderSet n₂,
       IsEmpty ((A ∩ π.cellGraph c).skeleton.Walk u v)) ∧
      (π.borderSet n₁ \ A.vertexSet).ncard = p - 1 ∧
      (π.borderSet n₂ \ A.vertexSet).ncard = p - 1 ∧ 2 ≤ p) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hp_pos : 1 ≤ p := by
    rw [← hp]
    exact theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) hΘ
  obtain ⟨c', hc', hc'Θ, hc'warp⟩ := π.exists_cell_cellWarp_eq_warpAt hΘ hΘ_arc
  set Z := A.vertexSet ∩ B.vertexSet
  have hsep := h𝒯.isSeparation hAB
  have hZ_sub : Z ⊆ G.vertexSet := inter_subset_left.trans hsep.left_le.1
  have hZ_le : (A.vertexSet ∩ B.vertexSet).ncard ≤ z := by
    change (A ∩ B).vertexSet.ncard ≤ z
    exact hord
  let π' := π.restrictQuotient A B hsep c' hc'
  have hT' : π'.IsCentral (quotientTangle G 𝒯 Z) :=
    π.restrictQuotient_isCentral h𝒯 hT hwarp hAB (by omega) c' hc'
  have hnot_simp : ¬ π'.IsSimpler π := hred.2 Z hZ_sub hZ_le π' hT'
  have hwarpAt_eq : π'.warpAt Θ = p := by
    have hEq := Portrayal.warpAt_eq_of_warpAt_le_of_not_isSimpler (π' := π') (π := π)
      (Homeomorph.refl π.S)
      (fun Φ hΦ => by
        have hle := π.restrictQuotient_warpAt_le A B hsep c' hc' hΦ
        have himg : (Homeomorph.refl π.S : π.S → π.S) '' Φ = Φ := image_id Φ
        change π'.warpAt Φ ≤ π.warpAt ((Homeomorph.refl π.S : π.S → π.S) '' Φ)
        rw [himg]
        exact hle)
      hnot_simp Θ hΘ
    have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
    change π'.warpAt Θ = π.warpAt ((Homeomorph.refl π.S : π.S → π.S) '' Θ) at hEq
    rw [himg, hp] at hEq
    exact hEq
  by_cases hcase1 : ∃ n ∈ π.Γ.N ∩ Θ, p ≤ (π.borderSet n \ A.vertexSet).ncard
  · exact Or.inl (exists_borderSet_disjoint_of_sdiff_card hΘ hΘ_arc hp hΘ_bd hcase1)
  · refine Or.inr ?_
    have hcase1' : ∀ n ∈ π.Γ.N ∩ Θ, (π.borderSet n \ A.vertexSet).ncard < p := by
      intro n hn
      exact Nat.lt_of_not_ge fun hge => hcase1 ⟨n, hn, hge⟩
    obtain ⟨c : Set π.S, hc, hcΘ, hcw'⟩ := π'.exists_cell_cellWarp_eq_warpAt hΘ hΘ_arc
    rw [hwarpAt_eq] at hcw'
    have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
    have htilde_Θ : tilde c ⊆ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc hΘ hcΘ).2.2.2.1
    obtain ⟨n₁, n₂, hne, htilde, _, _, hn₁_bd, hn₂_bd⟩ := π.Γ.border_cell_exists_ends hc hbd
    have hn₁_t : n₁ ∈ tilde c := htilde ▸ mem_insert _ _
    have hn₂_t : n₂ ∈ tilde c := htilde ▸ mem_insert_of_mem _ (mem_singleton _)
    have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := htilde_Θ hn₁_t
    have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := htilde_Θ hn₂_t
    have hnot_le : ¬ π'.CellWarpLE c (p - 1) := by
      intro hle
      have := (π'.cellWarp_le_iff hc hbd).mpr hle
      omega
    have hm_exists : ∃ m₁ ∈ tilde c, ∃ m₂ ∈ tilde c, m₁ ≠ m₂ ∧
        ¬ ((π'.borderSet m₁).ncard ≤ p - 1 ∧ (π'.borderSet m₂).ncard ≤ p - 1 ∧
          ((π'.borderPlus m₁).ncard = p - 1 + 1 → (π'.borderPlus m₂).ncard = p - 1 + 1 →
            Portrayal.LinkagePairs (π'.cellGraph c).skeleton (π'.borderPlus m₁) (π'.borderPlus m₂)
              (p - 1 + 1) (π'.nodeVertex m₁) (π'.nodeVertex m₂))) := by
      exact exists_not_cellWarpLE_pair π' c hnot_le
    obtain ⟨m₁ : π.S, hm₁_t, m₂ : π.S, hm₂_t, hm_ne, hm_cond⟩ := hm_exists
    have hsub_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
    rw [hsub_eq] at hm_cond
    have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₁_t
    have hm₂_Θ : m₂ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₂_t
    have hm₁_bd : m₁ ∈ π.Γ.N ∩ bd π.S := ⟨hm₁_Θ.1, hΘ_bd hm₁_Θ.2⟩
    have hm₂_bd : m₂ ∈ π.Γ.N ∩ bd π.S := ⟨hm₂_Θ.1, hΘ_bd hm₂_Θ.2⟩
    have hm₁_lt : (π'.borderSet m₁).ncard ≤ p - 1 := by
      have := hcase1' m₁ hm₁_Θ
      change (π.borderSet m₁ \ A.vertexSet).ncard ≤ p - 1
      omega
    have hm₂_lt : (π'.borderSet m₂).ncard ≤ p - 1 := by
      have := hcase1' m₂ hm₂_Θ
      change (π.borderSet m₂ \ A.vertexSet).ncard ≤ p - 1
      omega
    have hm_not_link : ¬ ((π'.borderPlus m₁).ncard = p →
        (π'.borderPlus m₂).ncard = p →
        Portrayal.LinkagePairs (π'.cellGraph c).skeleton (π'.borderPlus m₁) (π'.borderPlus m₂)
          p (π'.nodeVertex m₁) (π'.nodeVertex m₂)) :=
      fun h => hm_cond ⟨hm₁_lt, hm₂_lt, h⟩
    have hm_link_ex : (π'.borderPlus m₁).ncard = p ∧
        (π'.borderPlus m₂).ncard = p ∧
        ∃ (P : Fin p → PathFromTo (π'.cellGraph c).skeleton
            (π'.borderPlus m₁) (π'.borderPlus m₂)),
          (Pairwise fun i j =>
            Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P j).walk.support}) ∧
          ∀ i : Fin p,
            (P i).first = π'.nodeVertex m₁ → (P i).last ≠ π'.nodeVertex m₂ := by
      by_contra h_neg
      apply hm_not_link
      intro h1 h2 P hP_disj
      by_contra h_no_i
      apply h_neg
      refine ⟨h1, h2, P, hP_disj, fun i hfirst hlast => h_no_i ⟨i, hfirst, hlast⟩⟩
    obtain ⟨hbp₁_eq, hbp₂_eq, P, hP_disj, hP_not_pair⟩ := hm_link_ex
    have hm₁_dom' : m₁ ∈ π'.domγ := by
      by_contra hnot
      rw [π'.ncard_borderPlus_of_notMem_domγ hnot] at hbp₁_eq
      omega
    have hm₂_dom' : m₂ ∈ π'.domγ := by
      by_contra hnot
      rw [π'.ncard_borderPlus_of_notMem_domγ hnot] at hbp₂_eq
      omega
    have hm₁_card : (π.borderSet m₁ \ A.vertexSet).ncard = p - 1 := by
      have := π'.ncard_borderPlus_of_mem_domγ hm₁_dom' hm₁_bd.2
      change (π'.borderPlus m₁).ncard = (π.borderSet m₁ \ A.vertexSet).ncard + 1 at this
      omega
    have hm₂_card : (π.borderSet m₂ \ A.vertexSet).ncard = p - 1 := by
      have := π'.ncard_borderPlus_of_mem_domγ hm₂_dom' hm₂_bd.2
      change (π'.borderPlus m₂).ncard = (π.borderSet m₂ \ A.vertexSet).ncard + 1 at this
      omega
    have hp_ge2 : 2 ≤ p := by
      by_contra hlt
      have hp1 : p = 1 := by omega
      subst hp1
      have hbp₁_sing : π'.borderPlus m₁ = {π'.nodeVertex m₁} := by
        have hempty : π'.borderSet m₁ = ∅ :=
          (ncard_eq_zero ((π.borderSet_finite hm₁_bd).subset sdiff_subset)).mp hm₁_card
        rw [π'.borderPlus_eq_insert hm₁_dom', hempty, insert_empty_eq]
      have hbp₂_sing : π'.borderPlus m₂ = {π'.nodeVertex m₂} := by
        have hempty : π'.borderSet m₂ = ∅ :=
          (ncard_eq_zero ((π.borderSet_finite hm₂_bd).subset sdiff_subset)).mp hm₂_card
        rw [π'.borderPlus_eq_insert hm₂_dom', hempty, insert_empty_eq]
      have hfirst0 : (P ⟨0, Nat.zero_lt_one⟩).first = π'.nodeVertex m₁ :=
        mem_singleton_iff.mp (hbp₁_sing ▸ (P ⟨0, Nat.zero_lt_one⟩).first_mem)
      have hlast0 : (P ⟨0, Nat.zero_lt_one⟩).last = π'.nodeVertex m₂ :=
        mem_singleton_iff.mp (hbp₂_sing ▸ (P ⟨0, Nat.zero_lt_one⟩).last_mem)
      exact hP_not_pair ⟨0, Nat.zero_lt_one⟩ hfirst0 hlast0
    have htilde_m : tilde c = {m₁, m₂} := by
      have h1 : m₁ ∈ ({n₁, n₂} : Set π.S) := htilde ▸ hm₁_t
      have h2 : m₂ ∈ ({n₁, n₂} : Set π.S) := htilde ▸ hm₂_t
      refine htilde.trans ?_
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact (hm_ne rfl).elim
      · rfl
      · exact Set.pair_comm _ _
      · exact (hm_ne rfl).elim
    refine ⟨c, hc, hcΘ, m₁, m₂, hm_ne, htilde_m, hm₁_dom'.1, hm₂_dom'.1, hm₁_dom'.2, hm₂_dom'.2,
      ?_, hm₁_card, hm₂_card, hp_ge2⟩
    intro u₀ hu₀ v₀ hv₀
    refine ⟨fun W_A => ?_⟩
    let W_Ap := W_A.toPath.1
    have hW_Ap_path : W_Ap.IsPath := W_A.toPath.2
    have hle_Ac : A ∩ π.cellGraph c ≤ π.cellGraph c :=
      inter_le_right hsep.left_le (π.cellGraph_le c hc)
    obtain ⟨W_c, hsupp_c⟩ := walk_skeleton_mono hle_Ac W_Ap
    have hW_c_path : W_c.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hsupp_c]
      exact SimpleGraph.Walk.IsPath.support_nodup hW_Ap_path
    have hW_c_supp_A : {z | z ∈ W_c.support} ⊆ A.vertexSet := by
      intro z hz
      rw [hsupp_c] at hz
      exact (walk_support_subset_vertexSet hu₀.1 W_Ap hz).1
    let Q_extra : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
      ⟨u₀, v₀, W_c, hW_c_path, Or.inl hu₀.2, Or.inl hv₀.2⟩
    have hbp₁ := π.restrictQuotient_borderPlus A B hsep c' hc' m₁
    have hbp₂ := π.restrictQuotient_borderPlus A B hsep c' hc' m₂
    have hlift_linkage : ∀ i : Fin p,
        ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
          Q.first = (P i).first ∧ Q.last = (P i).last ∧
          Q.walk.support = (P i).walk.support ∧
          {z | z ∈ Q.walk.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
      exact lift_restricted_linkage_paths (α := α) (β := β) (G := G) (p := p) π (A := A) (B := B)
        c' hc' hsep c hc hbd m₁ hm₁_t m₂ P hbp₁ hbp₂
    choose Q hQ_first hQ_last hQ_supp hQ_sub using hlift_linkage
    let Q_all : Fin (p + 1) →
        PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
      fun i => if h : i.1 < p then Q ⟨i.1, h⟩ else Q_extra
    have hQ_all_disj : Pairwise fun i j =>
        Disjoint {z | z ∈ (Q_all i).walk.support} {z | z ∈ (Q_all j).walk.support} := by
      apply disjoint_paths_with_one_extra Q Q_extra _ _ hW_c_supp_A
      · intro i j hij
        simpa only [hQ_supp] using hP_disj hij
      · exact fun i _ hz => (hQ_sub i hz).2
    obtain ⟨hbp₁_ge, hbp₂_ge⟩ :=
      ncard_endsets_ge_of_disjoint_paths Q_all hQ_all_disj
        (π.borderPlus_finite hm₁_bd) (π.borderPlus_finite hm₂_bd)
    have hcw_le_p : π.cellWarp c ≤ p := hp ▸ π.cellWarp_le_warpAt hc hcΘ
    have hspec_c := (π.cellWarp_le_iff hc hbd).mp hcw_le_p m₁ hm₁_t m₂ hm₂_t hm_ne
    have hbp₁_le : (π.borderPlus m₁).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hm₁_bd).trans (Nat.add_le_add_right hspec_c.1 1)
    have hbp₂_le : (π.borderPlus m₂).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hm₂_bd).trans (Nat.add_le_add_right hspec_c.2.1 1)
    obtain ⟨i, hfirst_i, hlast_i⟩ :=
      hspec_c.2.2 (by omega) (by omega) Q_all hQ_all_disj
    dsimp only [Q_all] at hfirst_i hlast_i
    split_ifs at hfirst_i hlast_i with hi
    · exact hP_not_pair ⟨i.1, hi⟩
        ((hQ_first ⟨i.1, hi⟩).symm.trans hfirst_i)
        ((hQ_last ⟨i.1, hi⟩).symm.trans hlast_i)
    · exact hm₁_dom'.2 (hfirst_i ▸ hu₀.1.1)

/-! ## 4. Hitting All Border-Plus Sets on a Cuff: (6.6) (Pages 176–177) -/

/-- **Graph Minors XVII, (6.6)** (page 176):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$ with $warp \le p$ and $ord(\mathscr{T}) > z + 2p + 2$, and let $\Theta$ be
a cuff. There is no $X \subseteq V(G)$ with $|X| \le z/3$ such that $X \cap \beta(n+) \ne
\emptyset$ for every node $n$ bordering $\Theta$." -/
theorem theorem_6_6_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    {X : Set α} (hX_sub : X ⊆ G.vertexSet) (hX_card : 3 * X.ncard ≤ z) :
    ¬ (∀ n ∈ π.Γ.N ∩ Θ, (X ∩ π.borderPlus n).Nonempty) := by
  classical
  intro hX
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  set k := (π.Γ.N ∩ Θ).ncard
  set q := π.warpAt Θ with hq_def
  have hq_pos : 1 ≤ q :=
    theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) hΘ
  let y_fn : α → α := fun x =>
    if h : ∃ i : Fin k,
        x ∈ π.borderPlus (E.node i) ∧
        x ∉ π.borderPlus (E.node (nextIdx E.two_le i)) ∧
        E.node i ∈ π.domγ then
      π.nodeVertex (E.node (Classical.choose h))
    else x
  have hy_spec : ∀ x ∈ X, ∀ i : Fin k,
      x ∈ π.borderPlus (E.node i) → x ∉ π.borderPlus (E.node (nextIdx E.two_le i)) →
      E.node i ∈ π.domγ → y_fn x = π.nodeVertex (E.node i) := by
    intro x _ i hx₁ hx₂ hdom
    have hex : ∃ j : Fin k,
        x ∈ π.borderPlus (E.node j) ∧
        x ∉ π.borderPlus (E.node (nextIdx E.two_le j)) ∧
        E.node j ∈ π.domγ := ⟨i, hx₁, hx₂, hdom⟩
    dsimp only [y_fn]
    rw [dite_eq_left hex]
    have hspec := Classical.choose_spec hex
    have hij := lemma_6_6_claim_1 π E ⟨hspec.1, hspec.2.1⟩ ⟨hx₁, hx₂⟩
    rw [hij]
  let z_fn : α → α := fun x =>
    if h : ∃ n ∈ π.domγ ∩ bd π.S, x = π.nodeVertex n ∧ (π.borderSet n).ncard = q then
      have hne : (π.borderSet (Classical.choose h)).Nonempty := by
        have hspec := Classical.choose_spec h
        have hfin : (π.borderSet (Classical.choose h)).Finite :=
          π.borderSet_finite ⟨π.domγ_subset hspec.1.1, hspec.1.2⟩
        exact (ncard_pos hfin).mp (by omega)
      Classical.choose hne
    else x
  have hz_spec : ∀ x ∈ X, ∀ n ∈ π.domγ ∩ bd π.S, x = π.nodeVertex n →
      (π.borderSet n).ncard = q → z_fn x ∈ π.borderSet n := by
    intro x _ n hdom hEq hcard
    have hex : ∃ m ∈ π.domγ ∩ bd π.S, x = π.nodeVertex m ∧ (π.borderSet m).ncard = q :=
      ⟨n, hdom, hEq, hcard⟩
    dsimp only [z_fn]
    rw [dite_eq_left hex]
    have hspec := Classical.choose_spec hex
    have hmn : Classical.choose hex = n :=
      π.nodeVertex_injOn hspec.1.1 hdom.1 (hspec.2.1.symm.trans hEq)
    have hfin : (π.borderSet (Classical.choose hex)).Finite :=
      π.borderSet_finite ⟨π.domγ_subset hspec.1.1, hspec.1.2⟩
    have hne : (π.borderSet (Classical.choose hex)).Nonempty :=
      (ncard_pos hfin).mp (by omega)
    exact hmn ▸ Classical.choose_spec hne
  let W : Set α := X ∪ y_fn '' X ∪ z_fn '' X
  have hXW : X ⊆ W := subset_union_left.trans subset_union_left
  have hyW : y_fn '' X ⊆ W := subset_union_right.trans subset_union_left
  have hzW : z_fn '' X ⊆ W := subset_union_right
  have hW_sub : W ⊆ G.vertexSet := by
    refine union_subset (union_subset hX_sub ?_) ?_
    · rintro _ ⟨x, hxX, rfl⟩
      dsimp only [y_fn]
      split_ifs with h
      · exact π.nodeVertex_mem _ (Classical.choose_spec h).2.2
      · exact hX_sub hxX
    · rintro _ ⟨x, hxX, rfl⟩
      dsimp only [z_fn]
      split_ifs with h
      · have hspec := Classical.choose_spec h
        have hfin : (π.borderSet (Classical.choose h)).Finite :=
          π.borderSet_finite ⟨π.domγ_subset hspec.1.1, hspec.1.2⟩
        have hne : (π.borderSet (Classical.choose h)).Nonempty :=
          (ncard_pos hfin).mp (by omega)
        exact π.borderSet_subset _ ⟨π.domγ_subset hspec.1.1, hspec.1.2⟩
          (Classical.choose_spec hne)
      · exact hX_sub hxX
  have hX_fin : X.Finite := G.vertexSet_finite.subset hX_sub
  have hW_card : W.ncard ≤ z := by
    have h1 : W.ncard ≤ (X ∪ y_fn '' X).ncard + (z_fn '' X).ncard := ncard_union_le _ _
    have h2 : (X ∪ y_fn '' X).ncard ≤ X.ncard + (y_fn '' X).ncard := ncard_union_le _ _
    have h3 : (y_fn '' X).ncard ≤ X.ncard := ncard_image_le hX_fin
    have h4 : (z_fn '' X).ncard ≤ X.ncard := ncard_image_le hX_fin
    omega
  let A := discreteSubhypergraph G W hW_sub
  have hAG_mem : (A, G) ∈ 𝒯 := IsTangle.discrete_mem h𝒯 hW_sub (by omega)
  have hord_AG : separationOrder A G ≤ z := by
    unfold separationOrder
    have hEq : (A ∩ G).vertexSet = W := inter_eq_self_of_subset_left hW_sub
    rw [hEq]
    exact hW_card
  rcases theorem_6_5_proof h𝒯 π hT hwarp hred hθ hAG_mem hord_AG hΘ rfl with
    ⟨n, hn, hcard, hdisj⟩ |
    ⟨c, hc, hcΘ, n₁, n₂, _, htilde, hn₁_dom, hn₂_dom, hn₁_notW, hn₂_notW, hno_walk, _, _, _⟩
  · obtain ⟨w, hwW, hwn⟩ := lemma_6_6_claim_2 π hΘ_bd hX hz_spec hXW hzW hn hcard
    exact Set.disjoint_left.mp hdisj hwn hwW
  · obtain ⟨x, ⟨hxW, hxn₁⟩, hxn₂⟩ :=
      lemma_6_6_claim_3 π E hX hy_spec hXW hyW hc hcΘ htilde hn₁_dom hn₂_dom hn₁_notW hn₂_notW
    have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
    have hn₁_t : n₁ ∈ tilde c := htilde ▸ mem_insert _ _
    have hxc : x ∈ (π.cellGraph c).vertexSet := π.p3_subset c hc hbd n₁ hn₁_t hxn₁
    have hxAc : x ∈ (A ∩ π.cellGraph c).vertexSet := ⟨hxW, hxc⟩
    exact (hno_walk x ⟨hxAc, hxn₁⟩ x ⟨hxAc, hxn₂⟩).false .nil

/-! ## 5. Disc Cut by a Normal $I$-Arc and (6.7) (Pages 177–178) -/

/-- **Graph Minors XVII, (6.7)** (page 177):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$ with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F$ be a
$\Sigma$-normal $I$-arc with ends $n_1, n_2$ and with $|F \cap dom(\gamma)| \le z - 2p - 1$. Let
$\Delta$ be as in (6.3). Then $\beta(n_1 +) \cap \beta(n_2 +) \subseteq \beta(n+)$ for all $n \in
N(\Gamma) \cap \Delta \cap bd(\Sigma)$." (The paper writes "$\Sigma$-normal" for
"$\Gamma$-normal".) -/
theorem theorem_6_7_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ)
    {F Δ : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFγ_le : 2 * p + 1 ≤ z ∧ (F ∩ π.domγ).ncard ≤ z - 2 * p - 1)
    (hΔ : IsClosedDisc Δ) (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    {n' : π.S} (hn' : n' ∈ π.Γ.N ∩ Δ ∩ bd π.S) :
    π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n' := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  rintro v ⟨hv₁, hv₂⟩
  by_contra hvn'
  have hn₁_mem : n₁ ∈ F ∩ bd π.S := hFbd ▸ mem_insert _ _
  have hn₂_mem : n₂ ∈ F ∩ bd π.S := hFbd ▸ mem_insert_of_mem _ (mem_singleton _)
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S :=
    ⟨hnorm (show n₁ ∈ F ∩ π.Γ.U from ⟨hn₁_mem.1, π.Γ.bd_subset hn₁_mem.2⟩), hn₁_mem.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S :=
    ⟨hnorm (show n₂ ∈ F ∩ π.Γ.U from ⟨hn₂_mem.1, π.Γ.bd_subset hn₂_mem.2⟩), hn₂_mem.2⟩
  obtain ⟨Θ, hΘ, hn₁Θ, hn₂Θ⟩ := π.cuff_eq_of_borderPlus_inter_nonempty hn₁_bd hn₂_bd hv₁ hv₂
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  obtain ⟨hsep_F, ⟨c₁, hc₁, hc₁Δ, hc₁bd, hn₁_c₁⟩, hord_Θ⟩ :=
    GraphMinor.GM17.normalIArcDiscPainting π.S π.isSurface π.Γ F Δ Θ n₁ n₂ hnorm hF hFbd hΘ hn₁Θ
      hn₂Θ hΔ hF_bd hbd_sub
  set q := π.warpAt Θ
  have hq_pos : 1 ≤ q :=
    theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) hΘ
  let I₁ := {c ∈ π.Γ.C | c ⊆ Δ}
  let I₂ := π.Γ.C \ I₁
  have hI₁_sub : I₁ ⊆ π.Γ.C := fun _ hc => hc.1
  have hsep_I : ∀ d₁ ∈ I₁, ∀ d₂ ∈ I₂, tilde d₁ ∩ tilde d₂ ⊆ F :=
    fun d₁ hd₁ d₂ hd₂ => hsep_F d₁ hd₁.1 hd₁.2 d₂ hd₂.1 (fun h => hd₂.2 ⟨hd₂.1, h⟩)
  have hatt_sub : attachments G (π.areaGraph Δ) ⊆
      π.borderSet n₁ ∪ π.borderSet n₂ ∪ π.nodeVertex '' (F ∩ π.domγ) := by
    intro w hw
    have hw_inter : w ∈ (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet := by
      rcases hw with ⟨hw₁, e, ⟨heG, he_not₁⟩, hew⟩
      obtain ⟨c₂, hc₂, hec₂⟩ := π.p1_edge e heG
      have hc₂_I₂ : c₂ ∈ I₂ :=
        ⟨hc₂, fun hc₂_I₁ => he_not₁ (mem_biUnion ⟨hc₂_I₁, hc₂⟩ hec₂)⟩
      have hwc₂ : w ∈ (π.cellGraph c₂).vertexSet := by
        have hends := (π.cellGraph_le c₂ hc₂).3 e hec₂
        exact (π.cellGraph c₂).vertex_mem_of_inc
          (by change w ∈ (π.cellGraph c₂).ends e; rw [← hends]; exact hew)
      exact ⟨hw₁, mem_biUnion ⟨hc₂_I₂, hc₂⟩ hwc₂⟩
    have hcov : I₁ ∪ I₂ = π.Γ.C := union_sdiff_cancel hI₁_sub
    have hdisj_I : Disjoint I₁ I₂ := disjoint_sdiff_self_right
    have h21_eq := (theorem_2_1_proof π hcov hdisj_I).2
    rw [h21_eq] at hw_inter
    rcases hw_inter with hw_γ | hw_β
    · rw [mem_iUnion₂] at hw_γ
      rcases hw_γ with ⟨d₁, hd₁, hw_γ⟩
      rw [mem_iUnion₂] at hw_γ
      rcases hw_γ with ⟨d₂, hd₂, hw_γ⟩
      rw [← π.gammaImage_inter, Portrayal.mem_gammaImage_iff] at hw_γ
      rcases hw_γ with ⟨n, ⟨hnd, hnγ⟩, rfl⟩
      have hnF : n ∈ F := hsep_I d₁ hd₁ d₂ hd₂ hnd
      exact Or.inr ⟨n, ⟨hnF, hnγ⟩, rfl⟩
    · rw [mem_iUnion₂] at hw_β
      rcases hw_β with ⟨n, ⟨d₁, hd₁, _, d₂, hd₂, hbd₂, hnd⟩, hwn⟩
      have hnF : n ∈ F := hsep_I d₁ hd₁ d₂ hd₂ hnd
      obtain ⟨u₂, v₂, _, htilde₂, _, _, hu₂, hv₂⟩ := π.Γ.border_cell_exists_ends hd₂.1 hbd₂
      have hn_uv : n ∈ ({u₂, v₂} : Set π.S) := htilde₂ ▸ hnd.2
      have hnbd : n ∈ bd π.S := by rcases hn_uv with rfl | rfl <;> exact ‹n ∈ π.Γ.N ∩ bd π.S›.2
      have hn_pair : n ∈ ({n₁, n₂} : Set π.S) := hFbd ▸ ⟨hnF, hnbd⟩
      rcases hn_pair with rfl | rfl
      · exact Or.inl (Or.inl hwn)
      · exact Or.inl (Or.inr hwn)
  have hn₁_card : (π.borderSet n₁).ncard ≤ p :=
    (π.ncard_borderSet_le_warp hn₁_bd).trans hwarp
  have hn₂_card : (π.borderSet n₂).ncard ≤ p :=
    (π.ncard_borderSet_le_warp hn₂_bd).trans hwarp
  have hFγ_fin : (F ∩ π.domγ).Finite :=
    (π.Γ.finite_N.subset π.domγ_subset).inter_of_right F
  have hatt_le : (attachments G (π.areaGraph Δ)).ncard ≤ z - 1 := by
    have hfin_u : (π.borderSet n₁ ∪ π.borderSet n₂ ∪ π.nodeVertex '' (F ∩ π.domγ)).Finite :=
      ((π.borderSet_finite hn₁_bd).union (π.borderSet_finite hn₂_bd)).union (hFγ_fin.image _)
    have h0 := ncard_le_ncard hatt_sub hfin_u
    have h1 := ncard_union_le (π.borderSet n₁ ∪ π.borderSet n₂) (π.nodeVertex '' (F ∩ π.domγ))
    have h2 := ncard_union_le (π.borderSet n₁) (π.borderSet n₂)
    have h3 := ncard_image_le (f := π.nodeVertex) hFγ_fin
    omega
  have hv_in_Δ : v ∈ (π.areaGraph Δ).vertexSet := by
    have hvc₁ : v ∈ (π.cellGraph c₁).vertexSet :=
      π.borderPlus_subset_cellGraph hc₁ hc₁bd hn₁_c₁ hv₁
    exact mem_biUnion ⟨⟨hc₁, hc₁Δ⟩, hc₁⟩ hvc₁
  have hvG : v ∈ G.vertexSet := (π.cellsUnion_le I₁).1 hv_in_Δ
  let u : α :=
    if h : ∃ n ∈ π.Γ.N ∩ Θ ∩ π.domγ, π.nodeVertex n = v ∧ (π.borderSet n).Nonempty then
      Classical.choose (Classical.choose_spec h).2.2
    else v
  have huG : u ∈ G.vertexSet := by
    dsimp only [u]
    split_ifs with h
    · have hspec := Classical.choose_spec h
      exact π.borderSet_subset _ ⟨hspec.1.1.1, hΘ_bd hspec.1.1.2⟩
        (Classical.choose_spec hspec.2.2)
    · exact hvG
  let Hu := discreteSubhypergraph G {u} (singleton_subset_iff.mpr huG)
  have hHu_small : IsSmallWrt 𝒯 Hu :=
    ⟨G, IsTangle.discrete_mem h𝒯 (singleton_subset_iff.mpr huG) (by simp; omega)⟩
  let A := π.areaGraph Δ ∪ Hu
  have hvA : v ∈ A.vertexSet := Or.inl hv_in_Δ
  have huA : u ∈ A.vertexSet := Or.inr (mem_singleton u)
  have hA_le_G : A ≤ G := by
    have h1 := π.cellsUnion_le I₁
    have h2 : Hu ≤ G := ⟨singleton_subset_iff.mpr huG, empty_subset _, fun _ h => h.elim⟩
    exact union_le h1 h2
  have hatt_A_le : (attachments G A).ncard ≤ z := by
    have hsub : attachments G A ⊆ attachments G (π.areaGraph Δ) ∪ {u} := by
      rintro w ⟨hwΔ | rfl, e, ⟨heG, he_not⟩, hinc⟩
      · exact Or.inl ⟨hwΔ, e, ⟨heG, fun heΔ => he_not (Or.inl heΔ)⟩, hinc⟩
      · exact Or.inr (mem_singleton u)
    have h0 := ncard_le_ncard hsub (attachments_finite.union (finite_singleton u))
    have h1 := ncard_union_le (attachments G (π.areaGraph Δ)) {u}
    have h2 : ({u} : Set α).ncard = 1 := ncard_singleton u
    omega
  have hsmall_A : IsSmallWrt 𝒯 A := by
    refine hsmall.union h𝒯 hHu_small ?_
    change (attachments G A).ncard < θ
    omega
  let B := complSubhypergraph G A
  have hsep_AB : G.IsSeparation A B := isSeparation_complSubhypergraph hA_le_G
  have hord_AB : separationOrder A B ≤ z := by
    rw [separationOrder_complSubhypergraph]
    exact hatt_A_le
  have hAB : (A, B) ∈ 𝒯 := theorem_4_1_i h𝒯 hsmall_A hsep_AB (by omega)
  rcases theorem_6_5_proof h𝒯 π hT hwarp hred hθ hAB hord_AB hΘ rfl with
    ⟨n, hn, hcard, hdisj⟩ |
    ⟨c, hc, hcΘ, m₁, m₂, _, htilde, hm₁_dom, hm₂_dom, hm₁_notA, hm₂_notA, hno_walk, _, _, _⟩
  · have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
    obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
    rcases hn_range with ⟨i, rfl⟩
    let c := E.cell i
    have hc_range : c ∈ {d ∈ π.Γ.C | (d ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have hbd_c : (c ∩ bd π.S).Nonempty := hc_range.2.mono (inter_subset_inter_right _ hΘ_bd)
    have hn_t : E.node i ∈ tilde c := by
      rw [E.cell_tilde i]; exact mem_insert _ _
    have hn_bd : E.node i ∈ π.Γ.N ∩ bd π.S := ⟨hn.1, hΘ_bd hn.2⟩
    have hbs_ne : (π.borderSet (E.node i)).Nonempty :=
      (ncard_pos (π.borderSet_finite hn_bd)).mp (by omega)
    have hc_not_Δ : ¬ c ⊆ Δ := by
      intro hcΔ
      obtain ⟨w, hwn⟩ := hbs_ne
      have hwc : w ∈ (π.cellGraph c).vertexSet :=
        π.p3_subset c hc_range.1 hbd_c (E.node i) hn_t hwn
      have hwA : w ∈ A.vertexSet := Or.inl (mem_biUnion ⟨⟨hc_range.1, hcΔ⟩, hc_range.1⟩ hwc)
      exact Set.disjoint_left.mp hdisj hwn hwA
    obtain ⟨hn'Θ, hord⟩ := hord_Θ n' hn' c hc_range.1 hc_range.2 hc_not_Δ (E.node i) hn_t
    have hvn : v ∈ π.borderPlus (E.node i) := by
      have hp7 := π.p7 Θ hΘ n₁ ⟨hn₁_bd.1, hn₁Θ⟩ n' ⟨hn'.1.1, hn'Θ⟩
        n₂ ⟨hn₂_bd.1, hn₂Θ⟩ (E.node i) hn hord v hv₁ hv₂
      exact hp7.resolve_left hvn'
    rcases hvn with hvn_bs | ⟨hn_dom, hEq_v⟩
    · exact Set.disjoint_left.mp hdisj hvn_bs hvA
    · have hex : ∃ m ∈ π.Γ.N ∩ Θ ∩ π.domγ,
          π.nodeVertex m = v ∧ (π.borderSet m).Nonempty :=
        ⟨E.node i, ⟨hn, hn_dom⟩, hEq_v.symm, hbs_ne⟩
      have hu_mem : u ∈ π.borderSet (E.node i) := by
        dsimp only [u]
        rw [dite_eq_left hex]
        have hspec := Classical.choose_spec hex
        have hmi : Classical.choose hex = E.node i :=
          π.nodeVertex_injOn hspec.1.2 hn_dom (hspec.2.1.trans hEq_v)
        exact hmi ▸ Classical.choose_spec hspec.2.2
      exact Set.disjoint_left.mp hdisj hu_mem huA
  · have hm₁_t : m₁ ∈ tilde c := htilde ▸ mem_insert _ _
    have hm₂_t : m₂ ∈ tilde c := htilde ▸ mem_insert_of_mem _ (mem_singleton _)
    have htilde_Θ : tilde c ⊆ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc hΘ hcΘ).2.2.2.1
    have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₁_t
    have hm₂_Θ : m₂ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₂_t
    have hc_not_Δ : ¬ c ⊆ Δ := by
      intro hcΔ
      have hvc : π.nodeVertex m₁ ∈ (π.cellGraph c).vertexSet := π.p2 c hc m₁ ⟨hm₁_t, hm₁_dom⟩
      exact hm₁_notA (Or.inl (mem_biUnion ⟨⟨hc, hcΔ⟩, hc⟩ hvc))
    obtain ⟨hn'Θ, hord₁⟩ := hord_Θ n' hn' c hc hcΘ hc_not_Δ m₁ hm₁_t
    obtain ⟨_, hord₂⟩ := hord_Θ n' hn' c hc hcΘ hc_not_Δ m₂ hm₂_t
    have hvm₁ : v ∈ π.borderPlus m₁ :=
      (π.p7 Θ hΘ n₁ ⟨hn₁_bd.1, hn₁Θ⟩ n' ⟨hn'.1.1, hn'Θ⟩
        n₂ ⟨hn₂_bd.1, hn₂Θ⟩ m₁ hm₁_Θ hord₁ v hv₁ hv₂).resolve_left hvn'
    have hvm₂ : v ∈ π.borderPlus m₂ :=
      (π.p7 Θ hΘ n₁ ⟨hn₁_bd.1, hn₁Θ⟩ n' ⟨hn'.1.1, hn'Θ⟩
        n₂ ⟨hn₂_bd.1, hn₂Θ⟩ m₂ hm₂_Θ hord₂ v hv₁ hv₂).resolve_left hvn'
    have hvm₁_bs : v ∈ π.borderSet m₁ := by
      rcases hvm₁ with h | ⟨_, rfl⟩
      · exact h
      · exact (hm₁_notA hvA).elim
    have hvm₂_bs : v ∈ π.borderSet m₂ := by
      rcases hvm₂ with h | ⟨_, rfl⟩
      · exact h
      · exact (hm₂_notA hvA).elim
    have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
    have hvc : v ∈ (π.cellGraph c).vertexSet := π.p3_subset c hc hbd_c m₁ hm₁_t hvm₁_bs
    have hvAc : v ∈ (A ∩ π.cellGraph c).vertexSet := ⟨hvA, hvc⟩
    exact (hno_walk v ⟨hvAc, hvm₁_bs⟩ v ⟨hvAc, hvm₂_bs⟩).false .nil

end GraphMinor.GM17
