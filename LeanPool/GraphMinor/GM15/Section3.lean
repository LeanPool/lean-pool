/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.RadialAccess
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section6c
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# Graph Minors XV, Section 3: Rigidity

This file formalizes Section 3 ("Rigidity", pages 119–124) of N. Robertson and P. D. Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148:
- **Graph Minors XV, (3.1)** (`GM15Theorem31Statement`, page 119): characterization of dials in a
  rigid drawing with a tangle of order `≥ 3`.
- **Graph Minors XV, (3.2)** (`GM15Theorem32Statement`, page 119): gluing lemma for rigidity of a
  drawing in `Σ = Σ₁ ∪ Σ₂`.
- **Graph Minors XV, (3.3)** (`GM15Theorem33Statement`, page 120) and Claim (2) of its proof
  (`theorem_3_3_claim_2`, page 121): adding a crosscap in a region `Λ` of `H` using `φ` disjoint
  `η(H)`-paths whose ends are in order on `H ∩ bd(Λ)` and free with respect to `T`.
- **Graph Minors XV, (3.4)** (`GM15Theorem34Statement`, page 122): a drawing $H'$ that adds
  `k - 1` parallel paths across a region `Λ` of `H` has regions `r₁, r₂` with
  `d'(r₁, r₂) ≥ 2k - 6` and `d'({v_k}, {v_{2k}}) ≥ 2k - 8`. The formal statement also records
  distance monotonicity and boundary order. `GM15Theorem34DrawnStatement` first draws paths of `G`.
- **Graph Minors XV, (3.5)** (`GM15Theorem35Statement`, page 123): adding a handle between two
  distinct regions `Λ₁, Λ₂` of `H` using `φ` disjoint `η(H)`-paths.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

/-- Statement of Graph Minors XV, (3.1) (page 119):
"Let $H$ be a rigid drawing in a surface $\Sigma$, and let $\mathscr{T}$ be a tangle in $H$ of
order $\ge 3$. Let $\Delta \subseteq \Sigma$ be a closed disc with $bd(\Delta) \cap U(H) \subseteq
V(H)$ and $|bd(\Delta) \cap V(H)| \le 2$. Then $(H \cap \Delta, H \cap \overline{\Sigma - \Delta})
\in \mathscr{T}$ if and only if $\Delta$ is a dial for $bd(\Delta)$." -/
def GM15Theorem31Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Δ : Set S),
    IsClosedSurface S → ConnectedSpace S → IsRigid H → IsTangle H.toHypergraph θ T → 3 ≤ θ →
    IsClosedDisc Δ → subBd Δ ∩ H.U ⊆ H.V → (subBd Δ ∩ H.V).ncard ≤ 2 →
    (((H.interSet Δ).toHypergraph, (H.interSet (closure (univ \ Δ))).toHypergraph) ∈ T ↔
      IsDial H (subBd Δ) Δ)

/-- For a closed subset `K`, the vertex set of `H.interSet K` is `H.V ∩ K`. -/
theorem interSet_V_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {K : Set S} (hK : IsClosed K) :
    (H.interSet K).V = H.V ∩ K := by
  rw [Drawing.interSet, Drawing.span_V, Drawing.spanV]
  refine Subset.antisymm (union_subset inter_subset_left ?_)
    (fun x hx => Or.inl ⟨hx, hx.1⟩)
  refine iUnion₂_subset fun e he x hx => ⟨hx.2, ?_⟩
  exact hK.closure_subset_iff.mpr he.1.2 hx.1

/-- The edge set of `H.interSet K` is `{e ∈ H.E | e ⊆ K}`. -/
theorem interSet_E {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) (K : Set S) :
    (H.interSet K).E = {e ∈ H.E | e ⊆ K} := by
  rw [Drawing.interSet, Drawing.span_E]
  ext e
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

/-- In any drawing `Γ`, the ends of an edge `e ∈ Γ.E` in `Γ.toHypergraph` are `closure e ∩ Γ.V`. -/
theorem toHypergraph_ends_eq {S : Type w} [TopologicalSpace S] (Γ : Drawing S)
    {e : Set S} (he : e ∈ Γ.E) :
    Γ.toHypergraph.ends e = closure e ∩ Γ.V := by
  ext v
  simp only [Hypergraph.ends, mem_ofPred_eq, Drawing.toHypergraph, mem_inter_iff]
  exact ⟨fun ⟨_, hv, hve⟩ => ⟨hve, hv⟩, fun ⟨hve, hv⟩ => ⟨he, hv, hve⟩⟩

/-- Any subdrawing `Γ₁` of `Γ₂` induces a subhypergraph `Γ₁.toHypergraph ≤ Γ₂.toHypergraph`. -/
theorem toHypergraph_le_of_isSubdrawing {S : Type w} [TopologicalSpace S]
    {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) :
    Γ₁.toHypergraph ≤ Γ₂.toHypergraph := by
  refine ⟨h.1, h.2, fun e he => ?_⟩
  have he₁ : e ∈ Γ₁.E := he
  rw [toHypergraph_ends_eq Γ₂ (h.2 he₁), toHypergraph_ends_eq Γ₁ he₁, h.closure_inter_V he₁]

/-- For a closed subset `K`, `(H.interSet K).toHypergraph` is a subhypergraph of
`H.toHypergraph`. -/
theorem interSet_toHypergraph_le_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {K : Set S} (_hK : IsClosed K) :
    (H.interSet K).toHypergraph ≤ H.toHypergraph :=
  toHypergraph_le_of_isSubdrawing (Drawing.span_isSubdrawing H _ _)

/-- Monotonicity of `(H.interSet K).toHypergraph` with respect to closed sets `K₁ ⊆ K₂`. -/
theorem interSet_toHypergraph_mono_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {K₁ K₂ : Set S} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) (hsub : K₁ ⊆ K₂) :
    (H.interSet K₁).toHypergraph ≤ (H.interSet K₂).toHypergraph := by
  have hsubD : (H.interSet K₁).IsSubdrawing (H.interSet K₂) := by
    refine ⟨?_, ?_⟩
    · rw [interSet_V_of_isClosed H hK₁, interSet_V_of_isClosed H hK₂]
      exact inter_subset_inter_right _ hsub
    · rw [interSet_E, interSet_E]
      exact fun _ h => ⟨h.1, h.2.trans hsub⟩
  exact toHypergraph_le_of_isSubdrawing hsubD

private lemma isAcyclic_of_leaf {α : Type*} {K₁ K₂ : SimpleGraph α} {a w : α}
    (hleaf : ∀ x, K₂.Adj a x → x = w)
    (hsub : ∀ x y, x ≠ a → y ≠ a → K₂.Adj x y → K₁.Adj x y)
    (hAcyc : K₁.IsAcyclic) :
    K₂.IsAcyclic := by
  classical
  intro u c hc
  have ha_not : a ∉ c.support := by
    intro ha
    let p := c.rotate a ha
    have hp : p.IsCycle := hc.rotate ha
    have h1 : p.snd = w := hleaf _ (p.adj_snd hp.not_nil)
    have h2 : p.penultimate = w := hleaf _ (p.adj_penultimate hp.not_nil).symm
    exact hp.snd_ne_penultimate (h1.trans h2.symm)
  have hed : ∀ e ∈ c.edges, e ∈ K₁.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ≠ a := fun h => ha_not (h ▸ c.fst_mem_support_of_mem_edges he)
      have hy : y ≠ a := fun h => ha_not (h ▸ c.snd_mem_support_of_mem_edges he)
      exact hsub x y hx hy (c.adj_of_mem_edges he)
  exact hAcyc (c.transfer K₁ hed) (hc.transfer hed)

private lemma not_hasCircuit_of_edgeSet_empty {α β : Type*} {G : Hypergraph α β}
    (hE : G.edgeSet = ∅) :
    ¬ GM10.HasCircuit G := by
  rintro (⟨e, he, _⟩ | ⟨e₁, he₁, _⟩ | hacyc)
  · exact absurd he (hE ▸ notMem_empty e)
  · exact absurd he₁ (hE ▸ notMem_empty e₁)
  · apply hacyc
    have hbot : G.skeleton = ⊥ := by
      ext x y
      simp only [SimpleGraph.bot_adj, iff_false]
      rintro ⟨_, e, hx, _⟩
      exact notMem_empty e (hE ▸ G.edge_mem_of_inc hx)
    rw [hbot]
    exact SimpleGraph.isAcyclic_bot

private lemma not_hasCircuit_walkDrawing {S : Type w} [TopologicalSpace S] [T1Space S]
    (P : Drawing S) {u v : S} {W : GraphWalk P.toGraph u v} (hW : W.IsSimple) :
    ¬ GM10.HasCircuit (walkDrawing P W).toHypergraph := by
  induction W with
  | nil hu =>
    apply not_hasCircuit_of_edgeSet_empty
    change (walkDrawing P (GraphWalk.nil hu)).E = ∅
    rw [walkDrawing_E]
    simp
  | @cons a w _ e h r ih =>
    have hnd := List.nodup_cons.mp hW
    have ha_not : a ∉ r.support := hnd.1
    have ih' : ¬ GM10.HasCircuit (walkDrawing P r).toHypergraph := ih hnd.2
    have haw : a ≠ w := fun heq => ha_not (heq ▸ r.start_mem_support)
    set H₁ := (walkDrawing P r).toHypergraph
    set H₂ := (walkDrawing P (GraphWalk.cons h r)).toHypergraph
    have hle₁ : H₁ ≤ P.toHypergraph := toHypergraph_le_of_isSubdrawing
      (walkDrawing_isSubdrawing P r)
    have hle₂ : H₂ ≤ P.toHypergraph :=
      toHypergraph_le_of_isSubdrawing (walkDrawing_isSubdrawing P (GraphWalk.cons h r))
    have hE₁ : H₁.edgeSet = {f | f ∈ r.edges} := walkDrawing_E P r
    have hE₂ : H₂.edgeSet = {f | f ∈ e :: r.edges} := walkDrawing_E P (GraphWalk.cons h r)
    have hends_r : ∀ f ∈ r.edges, H₁.ends f = closure f ∩ P.V ∧ H₂.ends f = closure f ∩ P.V ∧
        closure f ∩ P.V ⊆ {x | x ∈ r.support} ∧ a ∉ closure f ∩ P.V := by
      intro f hf
      have hf₁ : f ∈ H₁.edgeSet := by rw [hE₁]; exact hf
      have hf₂ : f ∈ H₂.edgeSet := by rw [hE₂]; exact List.mem_cons_of_mem e hf
      have hfP : f ∈ P.E := hle₁.edgeSet_subset hf₁
      obtain ⟨x, y, hxy⟩ := (P.toGraph.edge_mem_iff_exists_isLink f).mp hfP
      have hsub : closure f ∩ P.V ⊆ {z | z ∈ r.support} := by
        rw [hxy.2.2.2]
        rintro z (rfl | hz)
        · exact r.left_mem_support_of_mem_edges hf hxy
        · rw [mem_singleton_iff.mp hz]
          exact r.left_mem_support_of_mem_edges hf hxy.symm
      refine ⟨(hle₁.ends_eq f hf₁).symm.trans (toHypergraph_ends_eq P hfP),
        (hle₂.ends_eq f hf₂).symm.trans (toHypergraph_ends_eq P hfP),
        hsub, fun ha => ha_not (hsub ha)⟩
    have he₂ : e ∈ H₂.edgeSet := by rw [hE₂]; exact List.mem_cons_self
    have hends_e : H₂.ends e = {a, w} := by
      rw [← hle₂.ends_eq e he₂, toHypergraph_ends_eq P h.1, h.2.2.2]
    rintro (⟨f, hf, hcard⟩ | ⟨f₁, hf₁, f₂, hf₂, hne, hcard⟩ | hacyc)
    · rw [hE₂, mem_ofPred_eq, List.mem_cons] at hf
      rcases hf with rfl | hf
      · rw [hends_e, Set.ncard_pair haw] at hcard
        omega
      · obtain ⟨he₁, he₂', _, _⟩ := hends_r f hf
        exact ih' (Or.inl ⟨f, by rw [hE₁]; exact hf, by rwa [he₁, ← he₂']⟩)
    · have hf₁' : f₁ = e ∨ f₁ ∈ r.edges := by rwa [hE₂, mem_ofPred_eq, List.mem_cons] at hf₁
      have hf₂' : f₂ = e ∨ f₂ ∈ r.edges := by rwa [hE₂, mem_ofPred_eq, List.mem_cons] at hf₂
      rcases hf₁' with rfl | hf₁' <;> rcases hf₂' with rfl | hf₂'
      · exact hne rfl
      · obtain ⟨_, he₂', _, ha_not_f⟩ := hends_r f₂ hf₂'
        have hsub : H₂.ends f₁ ∩ H₂.ends f₂ ⊆ {w} := by
          rw [hends_e, he₂']
          rintro z ⟨rfl | hzw, hzf⟩
          · exact (ha_not_f hzf).elim
          · exact hzw
        have hle := Set.ncard_le_ncard hsub (Set.finite_singleton w)
        rw [Set.ncard_singleton] at hle
        omega
      · obtain ⟨_, he₁', _, ha_not_f⟩ := hends_r f₁ hf₁'
        have hsub : H₂.ends f₁ ∩ H₂.ends f₂ ⊆ {w} := by
          rw [hends_e, he₁']
          rintro z ⟨hzf, rfl | hzw⟩
          · exact (ha_not_f hzf).elim
          · exact hzw
        have hle := Set.ncard_le_ncard hsub (Set.finite_singleton w)
        rw [Set.ncard_singleton] at hle
        omega
      · obtain ⟨he₁₁, he₁₂, _, _⟩ := hends_r f₁ hf₁'
        obtain ⟨he₂₁, he₂₂, _, _⟩ := hends_r f₂ hf₂'
        refine ih' (Or.inr (Or.inl ⟨f₁, by rw [hE₁]; exact hf₁', f₂, by rw [hE₁]; exact hf₂',
          hne, ?_⟩))
        rwa [he₁₁, he₂₁, ← he₁₂, ← he₂₂]
    · apply hacyc
      have hAcyc₁ : H₁.skeleton.IsAcyclic := by
        by_contra hnot
        exact ih' (Or.inr (Or.inr hnot))
      refine isAcyclic_of_leaf (K₁ := H₁.skeleton) (a := a) (w := w) ?_ ?_ hAcyc₁
      · intro x ⟨hax, f, hfa, hfx⟩
        have hf : f ∈ H₂.edgeSet := H₂.edge_mem_of_inc hfa
        rw [hE₂, mem_ofPred_eq, List.mem_cons] at hf
        rcases hf with rfl | hf
        · have hx : x ∈ H₂.ends f := hfx
          rw [hends_e] at hx
          rcases hx with rfl | hxw
          · exact (hax rfl).elim
          · exact mem_singleton_iff.mp hxw
        · obtain ⟨_, he₂', _, ha_not_f⟩ := hends_r f hf
          have ha' : a ∈ H₂.ends f := hfa
          rw [he₂'] at ha'
          exact (ha_not_f ha').elim
      · intro x y hx hy ⟨hxy, f, hfx, hfy⟩
        have hf : f ∈ H₂.edgeSet := H₂.edge_mem_of_inc hfx
        rw [hE₂, mem_ofPred_eq, List.mem_cons] at hf
        rcases hf with rfl | hf
        · have hx' : x ∈ H₂.ends f := hfx
          have hy' : y ∈ H₂.ends f := hfy
          rw [hends_e] at hx' hy'
          have hxw : x = w := mem_singleton_iff.mp (hx'.resolve_left hx)
          have hyw : y = w := mem_singleton_iff.mp (hy'.resolve_left hy)
          exact (hxy (hxw.trans hyw.symm)).elim
        · obtain ⟨he₁', he₂', _, _⟩ := hends_r f hf
          have hx' : x ∈ H₁.ends f := by
            have : x ∈ H₂.ends f := hfx
            rwa [he₁', ← he₂']
          have hy' : y ∈ H₁.ends f := by
            have : y ∈ H₂.ends f := hfy
            rwa [he₁', ← he₂']
          exact ⟨hxy, f, hx', hy'⟩

/-- A path drawing `P` (`P.IsPathBetween u v`) has no circuit in `P.toHypergraph`. -/
theorem not_hasCircuit_of_isPathBetween {S : Type w} [TopologicalSpace S] [T1Space S]
    {P : Drawing S} {u v : S} (hP : P.IsPathBetween u v) :
    ¬ GM10.HasCircuit P.toHypergraph := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  have hEq : P = walkDrawing P W :=
    Drawing.ext_of_V_E (hV.trans (walkDrawing_V P W).symm) (hE.trans (walkDrawing_E P W).symm)
  rw [hEq]
  exact not_hasCircuit_walkDrawing P hW

/-- For any dial `Δ` for `F, H` with `F ∩ H.U ⊆ H.V`, `H ∩ Δ` has no circuit. -/
theorem not_hasCircuit_of_isDial {S : Type w} [TopologicalSpace S] [T1Space S]
    {H : Drawing S} {F Δ : Set S} (hU : F ∩ H.U ⊆ H.V) (hDial : IsDial H F Δ) :
    ¬ GM10.HasCircuit (H.interSet Δ).toHypergraph := by
  rcases hDial.2.2 with hsub | ⟨u, v, _, _, hPath⟩
  · apply not_hasCircuit_of_edgeSet_empty
    change (H.interSet Δ).E = ∅
    rw [interSet_E]
    ext e
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro he heΔ
    obtain ⟨_, hdV, heU, ⟨x, hxe⟩⟩ := GM14.PaintingOrDrawing.edge_props (Γ := .drawing H) he
    exact Set.disjoint_left.mp hdV hxe (hU ⟨hsub ⟨heΔ hxe, heU hxe⟩, heU hxe⟩)
  · exact not_hasCircuit_of_isPathBetween hPath

/-- For a closed subset `K` with `subBd K ∩ H.U ⊆ H.V`, `H ∩ K` and `H ∩ closure(Σ - K)` form a
separation of `H` of order `|subBd K ∩ H.V|`. -/
theorem isSeparation_interSet_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {K : Set S} (hK : IsClosed K) (hU : subBd K ∩ H.U ⊆ H.V) :
    H.toHypergraph.IsSeparation (H.interSet K).toHypergraph
      (H.interSet (closure (univ \ K))).toHypergraph ∧
    separationOrder (H.interSet K).toHypergraph
      (H.interSet (closure (univ \ K))).toHypergraph = (subBd K ∩ H.V).ncard := by
  have hK' : IsClosed (closure (univ \ K)) := isClosed_closure
  have hle₁ := interSet_toHypergraph_le_of_isClosed H hK
  have hle₂ := interSet_toHypergraph_le_of_isClosed H hK'
  have hedge : ∀ e ∈ H.E, (e ⊆ K ∨ e ⊆ closure (univ \ K)) ∧ ¬ (e ⊆ K ∧ e ⊆ closure (univ \ K))
    := by
    intro e he
    obtain ⟨hp, hdV, heU, hne⟩ := GM14.PaintingOrDrawing.edge_props (Γ := .drawing H) he
    have hdfr : Disjoint e (frontier K) := by
      rw [← subBd_eq_frontier, Set.disjoint_left]
      intro x hxe hxbd
      exact Set.disjoint_left.mp hdV hxe (hU ⟨hxbd, heU hxe⟩)
    constructor
    · rcases GM14.subset_or_disjoint_of_frontier hK hp hdfr with hsub | hdisj
      · exact Or.inl hsub
      · refine Or.inr (Subset.trans ?_ subset_closure)
        intro x hxe
        exact ⟨mem_univ x, Set.disjoint_left.mp hdisj hxe⟩
    · rintro ⟨hsub₁, hsub₂⟩
      obtain ⟨x, hxe⟩ := hne
      have hxbd : x ∈ subBd K := ⟨subset_closure (hsub₁ hxe), hsub₂ hxe⟩
      exact Set.disjoint_left.mp hdV hxe (hU ⟨hxbd, heU hxe⟩)
  refine ⟨?_, ?_⟩
  · rw [isSeparation_iff_of_le hle₁ hle₂]
    refine ⟨?_, ?_, ?_⟩
    · ext v
      simp only [mem_union, Drawing.toHypergraph, interSet_V_of_isClosed H hK,
        interSet_V_of_isClosed H hK', mem_inter_iff]
      refine ⟨fun h => h.elim And.left And.left, fun hv => ?_⟩
      by_cases hvK : v ∈ K
      · exact Or.inl ⟨hv, hvK⟩
      · exact Or.inr ⟨hv, subset_closure ⟨mem_univ v, hvK⟩⟩
    · ext e
      simp only [mem_union, Drawing.toHypergraph, interSet_E, mem_ofPred_eq]
      exact ⟨fun h => h.elim And.left And.left,
        fun he => (hedge e he).1.elim (fun h => Or.inl ⟨he, h⟩) (fun h => Or.inr ⟨he, h⟩)⟩
    · ext e
      simp only [mem_inter_iff, Drawing.toHypergraph, interSet_E, mem_ofPred_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro h₁ _ h₂
      exact (hedge e h₁.1).2 ⟨h₁.2, h₂⟩
  · have hinter : ((H.interSet K).toHypergraph ∩
        (H.interSet (closure (univ \ K))).toHypergraph).vertexSet = subBd K ∩ H.V := by
      ext v
      simp only [inter_vertexSet, mem_inter_iff, Drawing.toHypergraph,
        interSet_V_of_isClosed H hK, interSet_V_of_isClosed H hK', subBd, hK.closure_eq]
      tauto
    rw [separationOrder, hinter]

/-- **Graph Minors XV, (3.1)** (page 119):
In a rigid drawing `H` in a connected closed surface `Σ` with a tangle `T` of order `≥ 3`, for any
closed disc `Δ ⊆ Σ` with `bd(Δ) ∩ U(H) ⊆ V(H)` and `|bd(Δ) ∩ V(H)| ≤ 2`,
`(H ∩ Δ, H ∩ closure(Σ - Δ)) ∈ T` if and only if `Δ` is a dial for `bd(Δ)`. -/
theorem theorem_3_1_proof : GM15Theorem31Statement.{w} := by
  intro S _ _ H θ T Δ hS hConn hRigid hT hθ hΔ hU hV
  obtain ⟨hsep, hord⟩ := isSeparation_interSet_of_isClosed H hΔ.isClosed hU
  constructor
  · intro hAB
    have hbd_eq : subBd Δ = discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ
    have hOArc : IsOArc (subBd Δ) := hbd_eq ▸ hΔ.isOArc_discBd
    obtain ⟨Δ', hDial'⟩ := hRigid (subBd Δ) hOArc hU hV
    by_cases hEq : Δ = Δ'
    · subst hEq
      exact hDial'
    · exfalso
      have hΔ' : IsClosedDisc Δ' := hDial'.1
      have hbd' : subBd Δ' = subBd Δ := hDial'.2.1
      have hdiscBd_eq : discBd Δ = discBd Δ' := by
        rw [← hbd_eq, ← hbd', IsClosedDisc.subBd_eq_discBd hS hΔ']
      have hcov : Δ ∪ Δ' = univ := GM14.cover_of_discBd_eq hS hΔ hΔ' hdiscBd_eq hEq
      have hsub : closure (univ \ Δ) ⊆ Δ' := by
        refine hΔ'.isClosed.closure_subset_iff.mpr (fun x hx => ?_)
        have hx' : x ∈ Δ ∪ Δ' := hcov ▸ mem_univ x
        exact hx'.resolve_left hx.2
      have hle : (H.interSet (closure (univ \ Δ))).toHypergraph ≤ (H.interSet Δ').toHypergraph :=
        interSet_toHypergraph_mono_of_isClosed H isClosed_closure hΔ'.isClosed hsub
      have hcircB : GM10.HasCircuit (H.interSet (closure (univ \ Δ))).toHypergraph :=
        GM10.theorem_2_10_proof hT hθ hAB
      exact not_hasCircuit_of_isDial hU hDial' (hcircB.mono hle)
  · intro hDial
    have hord' : separationOrder (H.interSet (closure (univ \ Δ))).toHypergraph
        (H.interSet Δ).toHypergraph < θ := by
      rw [separationOrder_comm, hord]
      omega
    rcases hT.axiom1 hsep.symm hord' with hBA | hAB
    · exfalso
      exact not_hasCircuit_of_isDial hU hDial (GM10.theorem_2_10_proof hT hθ hBA)
    · exact hAB

/-- Statement of Graph Minors XV, (3.2) (pages 119–120):
"Let $\Sigma$ be a surface with $bd(\Sigma) = \emptyset$, and let $\Sigma_1, \Sigma_2 \subseteq
\Sigma$ be surfaces with $\Sigma_1 \cup \Sigma_2 = \Sigma$ and $\Sigma_1 \cap \Sigma_2 =
bd(\Sigma_1) = bd(\Sigma_2)$. Let $H$ be a drawing in $\Sigma$ with $\Sigma_1 \cap \Sigma_2
\subseteq U(H)$, and let $X \subseteq V(H) \cap \Sigma_1 \cap \Sigma_2$. Let $\hat{\Sigma}_1$ be a
surface with $\Sigma_1 \subseteq \hat{\Sigma}_1$ and $bd(\hat{\Sigma}_1) = \emptyset$, such that
each O-arc in $bd(\Sigma_1)$ bounds an open disc in $\hat{\Sigma}_1$ disjoint from $\Sigma_1$
(thus, $\hat{\Sigma}_1$ is obtained from $\Sigma_1$ by “pasting” a disc onto each O-arc in
$bd(\Sigma_1)$). Suppose that ...
(i) if $r$ is a region of $H$ in $\Sigma$ and $r \subseteq \Sigma_1$, there is at most one
component $F$ of $\Sigma_1 \cap \Sigma_2$ with $\bar{r} \cap F \ne \emptyset$
(ii) for every $O$-arc $F \subseteq \hat{\Sigma}_1$, with $F \cap U(H) \subseteq V(H)$ and $|F
\cap V(H)| \le 2$, there is a dial $\Delta \subseteq \hat{\Sigma}_1$ for $F, H \cap \Sigma_1$ with
$|X \cap \Delta| \le |F \cap V(H)|$
(iii) for every $O$-arc $F \subseteq \Sigma_2$ with $F \cap U(H) \subseteq V(H)$ and $|F \cap
V(H)| \le 2$, there is a dial $\Delta \subseteq \Sigma_2$ for $F, H$
(iv) if $F \subseteq \Sigma_2$ is a line with ends $u, v \in \Sigma_1 \cap \Sigma_2 \cap V(H)$ and
is otherwise disjoint from $U(H)$, and $P$ is a path of $H \cap \Sigma_1 \cap \Sigma_2$ with ends
$u, v$ and with $|V(P) \cap X| \le 2$, then the $O$-arc $U(P) \cup F$ bounds an open disc in
$\Sigma_2$ disjoint from $U(H)$.
Then $H$ is rigid in $\Sigma$." -/
def GM15Theorem32Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {S_hat : Type w} [TopologicalSpace S_hat] [T2Space S_hat]
    {t : ℕ} (C : Fin t → Set S) (P₁ P₂ : Set S) (ι : P₁ → S_hat) (D : Fin t → Set S_hat)
    (H : Drawing S) (H₁ : Drawing S_hat) (X : Set S),
    GM12.IsCappedSplit C P₁ P₂ ι D →
    GM12.IsCappedDrawing ι H H₁ →
    P₁ ∩ P₂ ⊆ H.U →
    X ⊆ H.V ∩ (P₁ ∩ P₂) →
    (∀ r ∈ H.R, r ⊆ P₁ → ∀ i j : Fin t,
      (closure r ∩ C i).Nonempty → (closure r ∩ C j).Nonempty → i = j) →
    (∀ F : Set S_hat, IsOArc F → F ∩ H₁.U ⊆ H₁.V → (F ∩ H₁.V).ncard ≤ 2 →
      ∃ Δ : Set S_hat, IsDial H₁ F Δ ∧ ((ι '' ((↑) ⁻¹' X)) ∩ Δ).ncard ≤ (F ∩ H₁.V).ncard) →
    (∀ F : Set S, F ⊆ P₂ → IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 →
      ∃ Δ : Set S, Δ ⊆ P₂ ∧ IsDial H F Δ) →
    (∀ (F : Set S) (u v : S) (P : Drawing S),
      F ⊆ P₂ → u ∈ (P₁ ∩ P₂) ∩ H.V → v ∈ (P₁ ∩ P₂) ∩ H.V →
      IsLineWithEnds F u v → F ∩ H.U ⊆ {u, v} →
      P.IsSubdrawing (H.interSet (P₁ ∩ P₂)) → P.IsPathBetween u v →
      (P.V ∩ X).ncard ≤ 2 →
      ∃ U₀ : Set S, IsOpenDisc U₀ ∧ IsClosedDisc (closure U₀) ∧ U₀ ⊆ P₂ ∧
        subBd U₀ = P.U ∪ F ∧ Disjoint U₀ H.U) →
    IsRigid H

/-- Monotonicity of `H.interSet K` as a subdrawing with respect to closed sets `K₁ ⊆ K₂`. -/
theorem interSet_isSubdrawing_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {K₁ K₂ : Set S} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) (hsub : K₁ ⊆ K₂) :
    (H.interSet K₁).IsSubdrawing (H.interSet K₂) := by
  refine ⟨?_, ?_⟩
  · rw [interSet_V_of_isClosed H hK₁, interSet_V_of_isClosed H hK₂]
    exact inter_subset_inter_right _ hsub
  · rw [interSet_E, interSet_E]
    exact fun _ h => ⟨h.1, h.2.trans hsub⟩

private lemma isPathBetween_symm {S : Type*} [TopologicalSpace S] {P : Drawing S} {a b : S}
    (hP : P.IsPathBetween a b) : P.IsPathBetween b a := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  refine ⟨W.reverse, hW.reverse, ?_, ?_⟩
  · rw [hV]; ext x; simp [GraphWalk.support_reverse]
  · rw [hE]; ext e; simp [GraphWalk.edges_reverse]

private lemma ends_mem_of_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {B : Set S} {u v : S} (hB : IsLineWithEnds B u v) : u ∈ B ∧ v ∈ B := by
  obtain ⟨ψ, hψ0, hψ1⟩ := hB
  exact ⟨hψ0 ▸ (ψ 0).2, hψ1 ▸ (ψ 1).2⟩

private lemma isPreconnected_of_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {B : Set S} {u v : S} (hB : IsLineWithEnds B u v) : IsPreconnected B := by
  obtain ⟨ψ, _, _⟩ := hB
  have hEq : B = range (fun s : unitInterval => (ψ s).1) := by
    ext x
    exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ s).2⟩
  rw [hEq]
  exact isPreconnected_range (continuous_subtype_val.comp ψ.continuous)

private lemma isCompact_of_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {B : Set S} {u v : S} (hB : IsLineWithEnds B u v) : IsCompact B := by
  obtain ⟨ψ, _, _⟩ := hB
  have hEq : B = range (fun s : unitInterval => (ψ s).1) := by
    ext x
    exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ s).2⟩
  rw [hEq]
  exact isCompact_range (continuous_subtype_val.comp ψ.continuous)

private lemma isLineWithEnds_image {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {B : Set S} {u v : S} (hB : IsLineWithEnds B u v) {f : S → T} {f' : T → S}
    (hf : ContinuousOn f B) (hf' : ContinuousOn f' (f '' B)) (hl : LeftInvOn f' f B) :
    IsLineWithEnds (f '' B) (f u) (f v) := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hf hf' hl
  obtain ⟨ψ, hψ0, hψ1⟩ := hB
  exact ⟨ψ.trans e, (he (ψ 0)).trans (congr_arg f hψ0), (he (ψ 1)).trans (congr_arg f hψ1)⟩

private lemma eq_of_isLineWithEnds_subset {S : Type*} [TopologicalSpace S] {B L : Set S} {u v : S}
    (hB : IsLineWithEnds B u v) (hL : IsLineWithEnds L u v) (hsub : B ⊆ L) :
    B = L := by
  refine Subset.antisymm hsub (fun x hx => ?_)
  obtain ⟨ψ, hψ0, hψ1⟩ := hB
  obtain ⟨φ, hφ0, hφ1⟩ := hL
  let α : unitInterval → unitInterval := fun s => φ.symm ⟨(ψ s).1, hsub (ψ s).2⟩
  have hα : Continuous α :=
    φ.symm.continuous.comp ((continuous_subtype_val.comp ψ.continuous).subtype_mk _)
  have hα0 : α 0 = 0 := by
    apply φ.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (hψ0.trans hφ0.symm)
  have hα1 : α 1 = 1 := by
    apply φ.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (hψ1.trans hφ1.symm)
  have hmem0 : (0 : unitInterval) ∈ range α := ⟨0, hα0⟩
  have hmem1 : (1 : unitInterval) ∈ range α := ⟨1, hα1⟩
  have ht : φ.symm ⟨x, hx⟩ ∈ Icc (0 : unitInterval) 1 :=
    ⟨(φ.symm ⟨x, hx⟩).2.1, (φ.symm ⟨x, hx⟩).2.2⟩
  obtain ⟨s, hs⟩ := (isPreconnected_range hα).ordConnected.out hmem0 hmem1 ht
  have hφs : φ (α s) = ⟨x, hx⟩ := by rw [hs, Homeomorph.apply_symm_apply]
  have hψs : (ψ s).1 = x := by
    have h1 : (φ (α s)).1 = (ψ s).1 := by
      simp only [α, Homeomorph.apply_symm_apply]
    exact h1.symm.trans (congr_arg Subtype.val hφs)
  exact hψs ▸ (ψ s).2

private lemma not_isOArc_subset_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {J L : Set S} {u v : S} (hJ : IsOArc J) (hL : IsLineWithEnds L u v) (hsub : J ⊆ L) :
    False := by
  obtain ⟨φ, _, _⟩ := hL
  obtain ⟨γ⟩ := hJ
  let g : Circle → ℝ := fun z => (φ.symm ⟨(γ z).1, hsub (γ z).2⟩).1
  have hg : Continuous g :=
    continuous_subtype_val.comp (φ.symm.continuous.comp
      ((continuous_subtype_val.comp γ.continuous).subtype_mk _))
  refine GM11.not_injective_circle_real hg fun z₁ z₂ h => ?_
  have h1 := congr_arg Subtype.val (congr_arg φ (Subtype.ext h))
  simp only [Homeomorph.apply_symm_apply] at h1
  exact γ.injective (Subtype.ext h1)

open Classical in
private noncomputable def cappedFwd {S S_hat : Type*} (P₁ : Set S) (ι : P₁ → S_hat) (p₀ : P₁)
    (x : S) : S_hat :=
  if hx : x ∈ P₁ then ι ⟨x, hx⟩ else ι p₀

open Classical in
private noncomputable def cappedInv {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    (P₁ : Set S) (ι : P₁ → S_hat) (hEmb : IsEmbedding ι) (p₀ : P₁) (y : S_hat) : S :=
  if hy : y ∈ range ι then (hEmb.toHomeomorph.symm ⟨y, hy⟩).1 else p₀.1

private lemma cappedFwd_apply_of_mem {S S_hat : Type*} {P₁ : Set S} {ι : P₁ → S_hat} {p₀ : P₁}
    {x : S} (hx : x ∈ P₁) : cappedFwd P₁ ι p₀ x = ι ⟨x, hx⟩ := by
  unfold cappedFwd
  split_ifs
  rfl

private lemma cappedInv_apply_of_mem {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} {hEmb : IsEmbedding ι} {p₀ : P₁}
    {y : S_hat} (hy : y ∈ range ι) :
    cappedInv P₁ ι hEmb p₀ y = (hEmb.toHomeomorph.symm ⟨y, hy⟩).1 := by
  unfold cappedInv
  split_ifs
  rfl

private lemma mapsTo_cappedFwd {S S_hat : Type*} {P₁ : Set S} {ι : P₁ → S_hat} {p₀ : P₁} :
    MapsTo (cappedFwd P₁ ι p₀) P₁ (range ι) :=
  fun x hx => by rw [cappedFwd_apply_of_mem hx]; exact mem_range_self (⟨x, hx⟩ : P₁)

private lemma mapsTo_cappedInv {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} {hEmb : IsEmbedding ι} {p₀ : P₁} :
    MapsTo (cappedInv P₁ ι hEmb p₀) (range ι) P₁ :=
  fun y hy => by rw [cappedInv_apply_of_mem hy]; exact (hEmb.toHomeomorph.symm ⟨y, hy⟩).2

private lemma leftInvOn_cappedInv {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} {hEmb : IsEmbedding ι} {p₀ : P₁} :
    LeftInvOn (cappedInv P₁ ι hEmb p₀) (cappedFwd P₁ ι p₀) P₁ := by
  intro x hx
  have hfx : cappedFwd P₁ ι p₀ x ∈ range ι := mapsTo_cappedFwd hx
  rw [cappedInv_apply_of_mem hfx]
  have hsub : (⟨cappedFwd P₁ ι p₀ x, hfx⟩ : range ι) = hEmb.toHomeomorph ⟨x, hx⟩ := by
    ext; exact cappedFwd_apply_of_mem hx
  rw [hsub, Homeomorph.symm_apply_apply]

private lemma leftInvOn_cappedFwd {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} {hEmb : IsEmbedding ι} {p₀ : P₁} :
    LeftInvOn (cappedFwd P₁ ι p₀) (cappedInv P₁ ι hEmb p₀) (range ι) := by
  intro y hy
  have hgy : cappedInv P₁ ι hEmb p₀ y ∈ P₁ := mapsTo_cappedInv hy
  rw [cappedFwd_apply_of_mem hgy]
  have hsub : (⟨cappedInv P₁ ι hEmb p₀ y, hgy⟩ : P₁) = hEmb.toHomeomorph.symm ⟨y, hy⟩ := by
    ext; exact cappedInv_apply_of_mem hy
  exact congr_arg Subtype.val
    ((congr_arg hEmb.toHomeomorph hsub).trans (Homeomorph.apply_symm_apply _ _))

private lemma continuousOn_cappedFwd {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} (hEmb : IsEmbedding ι) (p₀ : P₁) :
    ContinuousOn (cappedFwd P₁ ι p₀) P₁ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : P₁.domRestrict (cappedFwd P₁ ι p₀) = ι := by
    ext x; exact cappedFwd_apply_of_mem x.2
  rw [hEq]
  exact hEmb.continuous

private lemma continuousOn_cappedInv {S S_hat : Type*} [TopologicalSpace S] [TopologicalSpace S_hat]
    {P₁ : Set S} {ι : P₁ → S_hat} (hEmb : IsEmbedding ι) (p₀ : P₁) :
    ContinuousOn (cappedInv P₁ ι hEmb p₀) (range ι) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (range ι).domRestrict (cappedInv P₁ ι hEmb p₀) =
      Subtype.val ∘ hEmb.toHomeomorph.symm := by
    ext y; exact cappedInv_apply_of_mem y.2
  rw [hEq]
  exact continuous_subtype_val.comp hEmb.toHomeomorph.symm.continuous

private lemma cappedFwd_image_eq_of_subset {S S_hat : Type*} {P₁ : Set S} {ι : P₁ → S_hat}
    {p₀ : P₁} {A : Set S} (hA : A ⊆ P₁) :
    cappedFwd P₁ ι p₀ '' A = ι '' ((↑) ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨x, hxA, rfl⟩
    exact ⟨⟨x, hA hxA⟩, hxA, (cappedFwd_apply_of_mem (hA hxA)).symm⟩
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    exact ⟨x, hxA, cappedFwd_apply_of_mem hxP⟩

private lemma cappedFwd_image_inter_P₁ {S S_hat : Type*} {P₁ : Set S} {ι : P₁ → S_hat}
    {p₀ : P₁} (A : Set S) :
    cappedFwd P₁ ι p₀ '' (A ∩ P₁) = ι '' ((↑) ⁻¹' A) := by
  rw [cappedFwd_image_eq_of_subset inter_subset_right]
  ext y
  simp only [mem_image, mem_preimage, mem_inter_iff, Subtype.exists]
  exact ⟨fun ⟨x, hxP, ⟨hxA, _⟩, hy⟩ => ⟨x, hxP, hxA, hy⟩,
    fun ⟨x, hxP, hxA, hy⟩ => ⟨x, hxP, ⟨hxA, hxP⟩, hy⟩⟩

private lemma walk_transfer_of_image {S S_hat : Type*} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace S_hat] [T2Space S_hat]
    {K : Set S_hat} (hK : IsCompact K)
    {f : S → S_hat} {g : S_hat → S}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K))
    (hl : LeftInvOn f g K)
    {Q_hat : Drawing S_hat} {Q : Drawing S}
    (hU_sub : Q_hat.U ⊆ K) (hU : Q.U = g '' Q_hat.U) (hV : Q.V = g '' Q_hat.V) :
    Q.E = image g '' Q_hat.E ∧
    ∀ {u_hat v_hat : S_hat} (W_hat : GraphWalk Q_hat.toGraph u_hat v_hat),
      ∃ W : GraphWalk Q.toGraph (g u_hat) (g v_hat),
        W.support = W_hat.support.map g ∧
        W.edges = W_hat.edges.map (image g) := by
  have hinj : InjOn g K := hl.injOn
  have hUV : Q.U \ Q.V = g '' (Q_hat.U \ Q_hat.V) := by
    rw [hU, hV]
    ext x
    constructor
    · rintro ⟨⟨y, hyU, rfl⟩, hyV⟩
      exact ⟨y, ⟨hyU, fun h => hyV ⟨y, h, rfl⟩⟩, rfl⟩
    · rintro ⟨y, ⟨hyU, hyV⟩, rfl⟩
      refine ⟨⟨y, hyU, rfl⟩, ?_⟩
      rintro ⟨z, hzV, hzy⟩
      exact hyV (hinj (Q_hat.V_subset_U.trans hU_sub hzV) (hU_sub hyU) hzy ▸ hzV)
  have hUV_sub : Q_hat.U \ Q_hat.V ⊆ K := sdiff_subset.trans hU_sub
  have hE : Q.E = image g '' Q_hat.E := by
    change arcComponentsIn (Q.U \ Q.V) = image g '' arcComponentsIn (Q_hat.U \ Q_hat.V)
    rw [hUV]
    exact GM11.arcComponentsIn_image (hg.mono hUV_sub)
      (hf.mono (image_mono hUV_sub)) (hl.mono hUV_sub)
  refine ⟨hE, ?_⟩
  have hLink : ∀ {e_hat : Set S_hat} {x_hat y_hat : S_hat},
      Q_hat.toGraph.IsLink e_hat x_hat y_hat →
      Q.toGraph.IsLink (g '' e_hat) (g x_hat) (g y_hat) := by
    rintro e_hat x_hat y_hat ⟨he_hat, hx_hat, hy_hat, hcl_hat⟩
    have he_sub : e_hat ⊆ K :=
      (GM14.PaintingOrDrawing.edge_props (Γ := .drawing Q_hat) he_hat).2.2.1.trans hU_sub
    have hcl_sub : closure e_hat ⊆ K := hK.isClosed.closure_subset_iff.mpr he_sub
    have hcl_comp : IsCompact (closure e_hat) := hK.of_isClosed_subset isClosed_closure hcl_sub
    have hcl_img : g '' closure e_hat = closure (g '' e_hat) :=
      image_closure_of_isCompact hcl_comp (hg.mono hcl_sub)
    refine ⟨hE ▸ mem_image_of_mem (image g) he_hat,
      hV ▸ mem_image_of_mem g hx_hat, hV ▸ mem_image_of_mem g hy_hat, ?_⟩
    rw [← hcl_img, hV, ← hinj.image_inter hcl_sub (Q_hat.V_subset_U.trans hU_sub), hcl_hat]
    simp [image_insert_eq]
  intro u_hat v_hat W_hat
  induction W_hat with
  | @nil v₀ hu =>
    have hgu : g v₀ ∈ V(Q.toGraph) := by
      change g v₀ ∈ Q.V
      rw [hV]
      exact mem_image_of_mem g hu
    exact ⟨GraphWalk.nil hgu, rfl, rfl⟩
  | @cons a w _ e h r ih =>
    obtain ⟨W', hs', he'⟩ := ih
    refine ⟨GraphWalk.cons (hLink h) W', ?_, ?_⟩
    · simp [GraphWalk.support_cons, hs']
    · simp [GraphWalk.edges, he']

private lemma isPathBetween_of_image {S S_hat : Type*} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace S_hat] [T2Space S_hat]
    {K : Set S_hat} (hK : IsCompact K)
    {f : S → S_hat} {g : S_hat → S}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K))
    (hl : LeftInvOn f g K)
    {Q_hat : Drawing S_hat} {Q : Drawing S} {u_hat v_hat : S_hat}
    (hU_sub : Q_hat.U ⊆ K) (hU : Q.U = g '' Q_hat.U) (hV : Q.V = g '' Q_hat.V)
    (hPath : Q_hat.IsPathBetween u_hat v_hat) :
    Q.IsPathBetween (g u_hat) (g v_hat) := by
  obtain ⟨hE, hWalk⟩ := walk_transfer_of_image hK hg hf hl hU_sub hU hV
  obtain ⟨W_hat, hW_hat, hV_hat, hE_hat⟩ := hPath
  obtain ⟨W, hs, he⟩ := hWalk W_hat
  have hinj : InjOn g K := hl.injOn
  have hsupp_sub : ∀ x ∈ W_hat.support, x ∈ K := by
    intro x hx
    have hxV : x ∈ Q_hat.V := by rw [hV_hat]; exact hx
    exact hU_sub (Q_hat.V_subset_U hxV)
  refine ⟨W, ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [hs]
    exact hW_hat.map_on fun x hx y hy hxy => hinj (hsupp_sub x hx) (hsupp_sub y hy) hxy
  · rw [hV, hV_hat, hs]
    ext x
    simp [List.mem_map]
  · rw [hE, hE_hat, he]
    ext e
    simp [List.mem_map]

private lemma halfEdges_nonempty_of_isOArc {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → unitInterval → S} (hγ : GM11.EdgePar Γ γ)
    {J : Set S} (hJ : IsOArc J) (hJU : J ⊆ Γ.U) {x : S} (hxJ : x ∈ J) (hxV : x ∈ Γ.V) :
    (GM11.halfEdges Γ γ x).Nonempty := by
  by_contra hne
  have hno : ∀ g ∈ Γ.E, x ∉ closure g := by
    intro g hg hxg
    obtain ⟨b, hb⟩ := GM11.exists_end_eq hγ hg hxV hxg
    exact hne ⟨(g, b), hg, hb⟩
  have hcl : IsClosed (Γ.U \ {x}) := by
    have heq : Γ.U \ {x} = (Γ.V \ {x}) ∪ ⋃ g ∈ Γ.E, closure g := by
      ext y
      rw [Γ.U_eq]
      constructor
      · rintro ⟨hy | hy, hyx⟩
        · exact Or.inl ⟨hy, hyx⟩
        · exact Or.inr hy
      · rintro (⟨hy, hyx⟩ | hy)
        · exact ⟨Or.inl hy, hyx⟩
        · refine ⟨Or.inr hy, fun h => ?_⟩
          obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp hy
          exact hno g hg (mem_singleton_iff.mp h ▸ hyg)
    rw [heq]
    exact (Γ.finite_V.subset sdiff_subset).isClosed.union
      (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
  have hJx_sub : J \ {x} ⊆ Γ.U \ {x} := sdiff_subset_sdiff hJU Subset.rfl
  have hcl_sub : closure (J \ {x}) ⊆ Γ.U \ {x} := hcl.closure_subset_iff.mpr hJx_sub
  have hx_not_cl : x ∉ closure (J \ {x}) := fun hxcl => (hcl_sub hxcl).2 rfl
  have hJ_conn : IsPreconnected J := by
    obtain ⟨φ⟩ := hJ
    have hEq : J = range (fun z : Circle => (φ z).1) := by
      ext y
      exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
    rw [hEq]
    exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
  have hJ_cov : J ⊆ (closure (J \ {x}))ᶜ ∪ ({x} : Set S)ᶜ := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact Or.inl hx_not_cl
    · exact Or.inr hyx
  obtain ⟨w, hwJ, hw_not⟩ :=
    ((GM11.infinite_of_isOArc hJ).sdiff (finite_singleton x)).nonempty
  obtain ⟨y, hyJ, hy_not_cl, hy_ne⟩ :=
    hJ_conn (closure (J \ {x}))ᶜ ({x} : Set S)ᶜ
      isClosed_closure.isOpen_compl isClosed_singleton.isOpen_compl hJ_cov
      ⟨x, hxJ, hx_not_cl⟩ ⟨w, hwJ, hw_not⟩
  exact hy_not_cl (subset_closure ⟨hyJ, hy_ne⟩)

private lemma exists_chord_in_cappingDisc {S_hat : Type*} [TopologicalSpace S_hat] [T2Space S_hat]
    (hS_hat : IsClosedSurface S_hat) {H₁ : Drawing S_hat} {D_i : Set S_hat}
    (hOpen : IsOpenDisc D_i) (hDisj : Disjoint D_i H₁.U)
    (hOArc : IsOArc (subBd D_i)) (hBdU : subBd D_i ⊆ H₁.U)
    {u' v' : S_hat} (hu' : u' ∈ subBd D_i ∩ H₁.V) (hv' : v' ∈ subBd D_i ∩ H₁.V)
    (huv' : u' ≠ v') :
    ∃ L_D : Set S_hat, IsLineWithEnds L_D u' v' ∧ L_D \ {u', v'} ⊆ D_i := by
  have : LocallyConnectedSpace S_hat := IsClosedSurface.locallyConnectedSpace hS_hat
  have hConn : IsPreconnected D_i := hOpen.isPathConnected.isConnected.isPreconnected
  obtain ⟨x₀, hx₀⟩ : D_i.Nonempty := by
    obtain ⟨φ⟩ := hOpen.2
    exact ⟨(φ ⟨0, by simp [OpenUnitDisc]⟩).1, (φ _).2⟩
  have : Nonempty S_hat := ⟨x₀⟩
  obtain ⟨r, hr, hx₀r⟩ := GM11.exists_region_of_notMem (Γ := H₁) (disjoint_left.mp hDisj hx₀)
  have hDr : D_i ⊆ r := GM11.subset_region hr hConn hDisj hx₀ hx₀r
  obtain ⟨_, hclD⟩ := isOpen_disjoint_subBd_and_closure_eq hOpen.1
  have hrD : r ⊆ D_i := by
    have hdis_fr : Disjoint r (frontier (closure D_i)) := by
      refine disjoint_left.mpr fun y hyr hyfr => ?_
      exact GM11.region_subset hr hyr (hBdU (subBd_eq_frontier D_i ▸ frontier_closure_subset hyfr))
    have hr_cl : r ⊆ closure D_i :=
      GM14.subset_of_disjoint_frontier (GM11.region_isPreconnected hr) isClosed_closure
        hdis_fr hx₀r (subset_closure hx₀)
    intro y hyr
    rcases hclD ▸ hr_cl hyr with hyD | hyBd
    · exact hyD
    · exact (GM11.region_subset hr hyr (hBdU hyBd)).elim
  have hR : D_i ∈ H₁.R := Subset.antisymm hDr hrD ▸ hr
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar H₁
  have hne_u : (GM11.halfEdges H₁ γ u').Nonempty :=
    halfEdges_nonempty_of_isOArc hγ hOArc hBdU hu'.1 hu'.2
  have hne_v : (GM11.halfEdges H₁ γ v').Nonempty :=
    halfEdges_nonempty_of_isOArc hγ hOArc hBdU hv'.1 hv'.2
  obtain ⟨g₁, hg₁, hg₁0, hg₁p⟩ :=
    GM11.exists_access hS_hat H₁ hγ hu'.2 hne_u hR hu'.1.1
  obtain ⟨g₂, hg₂, hg₂0, hg₂p⟩ :=
    GM11.exists_access hS_hat H₁ hγ hv'.2 hne_v hR hv'.1.1
  have hu'_not_D : u' ∉ D_i := fun h => disjoint_left.mp hDisj h (H₁.V_subset_U hu'.2)
  obtain ⟨a, ha_cont, ha_inj, ha0, ha1, hap, -⟩ :=
    GM11.exists_chord hOpen.isPathConnected huv' hu'_not_D hg₁ hg₂ hg₁0 hg₂0 hg₁p hg₂p
  refine ⟨range a, ha0 ▸ ha1 ▸ GM11.isLine_range ha_cont ha_inj, ?_⟩
  rintro z ⟨⟨t, rfl⟩, hzt⟩
  have ht0 : t ≠ 0 := fun h => hzt (Or.inl (by rw [← ha0, h]))
  have ht1 : t ≠ 1 := fun h => hzt (Or.inr (by rw [mem_singleton_iff, ← ha1, h]))
  exact hap t ht0 ht1

private theorem capped_disc_without_cap_lies_in_range
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H₁ : Drawing S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hDi_bd_U : ∀ (i : Fin t), subBd (D i) ⊆ H₁.U)
    (hDi_disj_range : ∀ (i : Fin t), Disjoint (D i) (range ι)) :
    ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → subBd Δ_hat ⊆ range ι → (∀ (i : Fin t), ¬subBd (D
      i) ⊆ Δ_hat ∩ H₁.U) → Δ_hat ⊆ range ι := by
  intro Δ_hat hΔ_hat hbd_range hno y hy
  by_contra hy_not
  have hy_iUnion : y ∈ ⋃ i, D i := hSplit.compl ▸ hy_not
  obtain ⟨i, hyDi⟩ := mem_iUnion.mp hy_iUnion
  have hdis_fr : Disjoint (D i) (frontier Δ_hat) := by
    rw [← subBd_eq_frontier]
    exact (hDi_disj_range i).mono_right hbd_range
  have hDi_sub : D i ⊆ Δ_hat :=
    GM14.subset_of_disjoint_frontier
      (hSplit.isOpenDisc i).isPathConnected.isConnected.isPreconnected
      hΔ_hat.isClosed hdis_fr hyDi hy
  have hbdDi_sub : subBd (D i) ⊆ Δ_hat :=
    Subset.trans (fun _ hz => hz.1) (hΔ_hat.isClosed.closure_subset_iff.mpr hDi_sub)
  exact hno i (subset_inter hbdDi_sub (hDi_bd_U i))

private theorem pullback_of_capped_disc
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (hS : IsClosedSurface S)
    (hS_hat : IsClosedSurface S_hat)
    (f : S → S_hat)
    (g : S_hat → S)
    (hf_cont : ContinuousOn f P₁)
    (hg_cont : ContinuousOn g (range ι))
    (hgf_inv : LeftInvOn f g (range ι))
    (hg_maps : MapsTo g (range ι) P₁) :
    ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → Δ_hat ⊆ range ι → IsClosedDisc (g '' Δ_hat) ∧
      subBd (g '' Δ_hat) = g '' subBd Δ_hat ∧ g '' Δ_hat ⊆ P₁ := by
  intro Δ_hat hΔ_hat hΔ_range
  have hsub_P₁ : g '' Δ_hat ⊆ P₁ := (hg_maps.mono hΔ_range Subset.rfl).image_subset
  obtain ⟨hDisc, hdiscBd⟩ :=
    hΔ_hat.image (hg_cont.mono hΔ_range) (hf_cont.mono hsub_P₁) (hgf_inv.mono hΔ_range)
  refine ⟨hDisc, ?_, hsub_P₁⟩
  rw [IsClosedDisc.subBd_eq_discBd hS hDisc, hdiscBd,
    ← IsClosedDisc.subBd_eq_discBd hS_hat hΔ_hat]

private theorem boundary_arcs_meet_first_disc {S : Type*} [TopologicalSpace S]
    {P₁ P₂ : Set S} {x₁ x₂ : S} (hP₁ : IsClosed P₁)
    (hx₁P₁ : x₁ ∈ P₁) (hx₂_not_P₁ : x₂ ∉ P₁) (hx₁_not_P₂ : x₁ ∉ P₂)
    (hfrP₁ : frontier P₁ ⊆ P₁ ∩ P₂) :
    ∀ {A : Set S}, IsLineWithEnds A x₁ x₂ →
      ∃ w ∈ A ∩ (P₁ ∩ P₂), w ∉ ({x₁, x₂} : Set S) := by
  intro A hA
  obtain ⟨hx₁A, hx₂A⟩ := ends_mem_of_isLineWithEnds hA
  have hne : (A ∩ frontier P₁).Nonempty := by
    by_contra h
    have hdis : Disjoint A (frontier P₁) := disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp h)
    exact hx₂_not_P₁ (GM14.subset_of_disjoint_frontier (isPreconnected_of_isLineWithEnds hA)
      hP₁ hdis hx₁A hx₁P₁ hx₂A)
  obtain ⟨w, hwA, hwfr⟩ := hne
  have hw12 : w ∈ P₁ ∩ P₂ := hfrP₁ hwfr
  refine ⟨w, ⟨hwA, hw12⟩, ?_⟩
  rintro (rfl | rfl)
  · exact hx₁_not_P₂ hw12.2
  · exact hx₂_not_P₁ hw12.1

private theorem boundary_arc_lies_on_one_side
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (F : Set S)
    (hP₁_cl : IsClosed P₁)
    (hP₂_cl : IsClosed P₂)
    (hfrP₁ : frontier P₁ ⊆ P₁ ∩ P₂)
    (hfrP₂ : frontier P₂ ⊆ P₁ ∩ P₂)
    (u : S)
    (v : S)
    (hF12_eq : F ∩ (P₁ ∩ P₂) = {u, v}) :
    ∀ {L : Set S}, IsLineWithEnds L u v → L ⊆ F → L ⊆ P₁ ∨ L ⊆ P₂ := by
  intro L hL hLF
  have hconn : IsPreconnected (L \ {u, v}) :=
    (GM11.isPathConnected_sdiff_pair hL).isConnected.isPreconnected
  obtain ⟨w, hw⟩ := (GM11.isPathConnected_sdiff_pair hL).nonempty
  have hdis₁ : Disjoint (L \ {u, v}) (frontier P₁) := by
    refine disjoint_left.mpr fun z hz hzfr => hz.2 ?_
    exact hF12_eq ▸ ⟨hLF hz.1, hfrP₁ hzfr⟩
  have hdis₂ : Disjoint (L \ {u, v}) (frontier P₂) := by
    refine disjoint_left.mpr fun z hz hzfr => hz.2 ?_
    exact hF12_eq ▸ ⟨hLF hz.1, hfrP₂ hzfr⟩
  have hsub_cl : L ⊆ closure (L \ {u, v}) :=
    (GM11.closure_sdiff_pair hL).symm.subset
  rcases eq_univ_iff_forall.mp hSplit.union w with hwP₁ | hwP₂
  · left
    have h1 : L \ {u, v} ⊆ P₁ :=
      GM14.subset_of_disjoint_frontier hconn hP₁_cl hdis₁ hw hwP₁
    exact hsub_cl.trans (hP₁_cl.closure_subset_iff.mpr h1)
  · right
    have h2 : L \ {u, v} ⊆ P₂ :=
      GM14.subset_of_disjoint_frontier hconn hP₂_cl hdis₂ hw hwP₂
    exact hsub_cl.trans (hP₂_cl.closure_subset_iff.mpr h2)

private theorem split_circle_at_two_boundary_points
    {S : Type w}
    [TopologicalSpace S]
    (P₁ : Set S)
    (P₂ : Set S)
    (F : Set S)
    (hF₂ : ¬F ⊆ P₂)
    (hF₁ : ¬F ⊆ P₁)
    (u : S)
    (v : S)
    (F₁_0 : Set S)
    (F₂_0 : Set S)
    (hF₁_0 : IsLineWithEnds F₁_0 u v)
    (hF₂_0 : IsLineWithEnds F₂_0 u v)
    (hF_0_union : F₁_0 ∪ F₂_0 = F)
    (hF_0_inter : F₁_0 ∩ F₂_0 = {u, v})
    (hArc_side : ∀ {L : Set S}, IsLineWithEnds L u v → L ⊆ F → L ⊆ P₁ ∨ L ⊆ P₂) :
    ∃ F₁ F₂, IsLineWithEnds F₁ u v ∧ IsLineWithEnds F₂ u v ∧ F₁ ∪ F₂ = F ∧ F₁ ∩ F₂ = {u, v} ∧ F₁ ⊆
      P₁ ∧ F₂ ⊆ P₂ := by
  have hsub₁ : F₁_0 ⊆ F := hF_0_union ▸ subset_union_left
  have hsub₂ : F₂_0 ⊆ F := hF_0_union ▸ subset_union_right
  rcases hArc_side hF₁_0 hsub₁ with h1P₁ | h1P₂ <;>
    rcases hArc_side hF₂_0 hsub₂ with h2P₁ | h2P₂
  · exact (hF₁ (hF_0_union ▸ union_subset h1P₁ h2P₁)).elim
  · exact ⟨F₁_0, F₂_0, hF₁_0, hF₂_0, hF_0_union, hF_0_inter, h1P₁, h2P₂⟩
  · exact ⟨F₂_0, F₁_0, hF₂_0, hF₁_0, Set.union_comm F₂_0 F₁_0 ▸ hF_0_union,
      Set.inter_comm F₂_0 F₁_0 ▸ hF_0_inter, h2P₁, h1P₂⟩
  · exact (hF₂ (hF_0_union ▸ union_subset h1P₂ h2P₂)).elim

private theorem boundary_arc_mem_disc
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    (H₁ : Drawing S_hat)
    (u' : S_hat)
    (v' : S_hat)
    (F_hat : Set S_hat)
    (hF_hat_U : F_hat ∩ H₁.U = {u', v'})
    (Δ_hat : Set S_hat)
    (hΔ_hat_disc : IsClosedDisc Δ_hat)
    (hΔ_hat_bd : subBd Δ_hat = F_hat)
    (hu'Δ : u' ∈ Δ_hat) (hv'Δ : v' ∈ Δ_hat)
    (z₀ : S_hat)
    (hz₀_Δ : z₀ ∈ Δ_hat)
    (B₁ : Set S_hat)
    (hB₁_line : IsLineWithEnds B₁ u' v')
    (hz₀_B₁ : z₀ ∈ B₁)
    (hz₀_not_uv : z₀ ∉ ({u', v'} : Set S_hat))
    (hB₁_U : B₁ ⊆ H₁.U) :
    B₁ ⊆ Δ_hat := by
  have hdis_fr : Disjoint (B₁ \ {u', v'}) (frontier Δ_hat) := by
    rw [← subBd_eq_frontier, hΔ_hat_bd]
    refine disjoint_left.mpr fun z hz hzF => hz.2 ?_
    exact hF_hat_U ▸ ⟨hzF, hB₁_U hz.1⟩
  have hdiff_sub : B₁ \ {u', v'} ⊆ Δ_hat :=
    GM14.subset_of_disjoint_frontier
      (GM11.isPathConnected_sdiff_pair hB₁_line).isConnected.isPreconnected
      hΔ_hat_disc.isClosed hdis_fr ⟨hz₀_B₁, hz₀_not_uv⟩ hz₀_Δ
  intro z hz
  by_cases hzuv : z ∈ ({u', v'} : Set S_hat)
  · rcases hzuv with rfl | rfl
    · exact hu'Δ
    · exact hv'Δ
  · exact hdiff_sub ⟨hz, hzuv⟩

private theorem capped_path_avoids_cap
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    (H₁ : Drawing S_hat)
    (u' : S_hat)
    (v' : S_hat)
    (hu'v' : u' ≠ v')
    (F_hat : Set S_hat)
    (hF_hat_V : F_hat ∩ H₁.V = {u', v'})
    (Δ_hat : Set S_hat)
    (hDial_hat : IsDial H₁ F_hat Δ_hat)
    (z₀ : S_hat)
    (hz₀_Δ : z₀ ∈ Δ_hat)
    (hz₀_not_F : z₀ ∉ F_hat)
    (B₁ : Set S_hat)
    (hz₀_B₁ : z₀ ∈ B₁)
    (hB₁_U : B₁ ⊆ H₁.U) :
    (H₁.interSet Δ_hat).IsPathBetween u' v' := by
  rcases hDial_hat.2.2 with hsubF | ⟨u'', v'', _, hFV'', hPath''⟩
  · exact (hz₀_not_F (hsubF ⟨hz₀_Δ, hB₁_U hz₀_B₁⟩)).elim
  · have hpair : ({u', v'} : Set S_hat) = {u'', v''} := hF_hat_V.symm.trans hFV''
    have hu'_mem : u' ∈ ({u'', v''} : Set S_hat) := hpair ▸ Or.inl rfl
    have hv'_mem : v' ∈ ({u'', v''} : Set S_hat) := hpair ▸ Or.inr rfl
    rcases mem_insert_iff.mp hu'_mem with hu1 | hu2 <;>
      rcases mem_insert_iff.mp hv'_mem with hv1 | hv2
    · exact (hu'v' (hu1.trans hv1.symm)).elim
    · rw [hu1, mem_singleton_iff.mp hv2]
      exact hPath''
    · rw [mem_singleton_iff.mp hu2, hv1]
      exact isPathBetween_symm hPath''
    · exact (hu'v' ((mem_singleton_iff.mp hu2).trans (mem_singleton_iff.mp hv2).symm)).elim

private theorem first_capped_disc_lies_in_range
    {S : Type w}
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H₁ : Drawing S_hat)
    (hDi_bd_oArc : ∀ (i : Fin t), IsOArc (subBd (D i)))
    (hDisc_sub_range : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → subBd Δ_hat ⊆ range ι → (∀ (i :
      Fin t), ¬subBd (D i) ⊆ Δ_hat ∩ H₁.U) → Δ_hat ⊆ range ι)
    (u' : S_hat)
    (v' : S_hat)
    (F₁' : Set S_hat)
    (hF₁'_range : F₁' ⊆ range ι)
    (B₁ : Set S_hat)
    (hB₁_line : IsLineWithEnds B₁ u' v')
    (hB₁_range : B₁ ⊆ range ι)
    (Δ_hat₁ : Set S_hat)
    (hΔ_hat₁_disc : IsClosedDisc Δ_hat₁)
    (hΔ_hat₁_bd : subBd Δ_hat₁ = F₁' ∪ B₁)
    (hΔ_hat₁_U : Δ_hat₁ ∩ H₁.U = B₁) :
    Δ_hat₁ ⊆ range ι := by
  refine hDisc_sub_range hΔ_hat₁_disc (hΔ_hat₁_bd ▸ union_subset hF₁'_range hB₁_range)
    fun j hsub => ?_
  exact not_isOArc_subset_isLineWithEnds (hDi_bd_oArc j) hB₁_line (hΔ_hat₁_U ▸ hsub)

private theorem path_vertices_in_image
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (f : S → S_hat)
    (g : S_hat → S)
    (hfg_inv : LeftInvOn g f P₁)
    (hgf_inv : LeftInvOn f g (range ι))
    (hH₁_V : H₁.V = f '' (H.V ∩ P₁))
    (Δ_hat : Set S_hat)
    (B₁ : Set S_hat)
    (hB₁_range : B₁ ⊆ range ι)
    (P : Drawing S)
    (hL_P₁ : (g '' B₁) ⊆ P₁)
    (hP_V : P.V = H.V ∩ (g '' B₁))
    (hQ_hat_V : (H₁.interSet Δ_hat).V = H₁.V ∩ B₁) :
    P.V = g '' (H₁.interSet Δ_hat).V := by
  rw [hP_V, hQ_hat_V, hH₁_V]
  have h1 : f '' (H.V ∩ P₁) ∩ B₁ = f '' (H.V ∩ (g '' B₁)) := by
    ext y
    constructor
    · rintro ⟨⟨x, ⟨hxV, hxP₁⟩, rfl⟩, hyB₁⟩
      exact ⟨x, ⟨hxV, f x, hyB₁, hfg_inv hxP₁⟩, rfl⟩
    · rintro ⟨_, ⟨hxV, z, hzB₁, rfl⟩, rfl⟩
      exact ⟨⟨g z, ⟨hxV, hL_P₁ (mem_image_of_mem g hzB₁)⟩, rfl⟩,
        (hgf_inv (hB₁_range hzB₁)).symm ▸ hzB₁⟩
  rw [h1]
  exact (hfg_inv.mono (inter_subset_right.trans hL_P₁)).image_image.symm

private theorem augmented_path_avoids_drawing_except_vertices
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (f : S → S_hat)
    (g : S_hat → S)
    (hf_cont : ContinuousOn f P₁)
    (hg_cont : ContinuousOn g (range ι))
    (hgf_inv : LeftInvOn f g (range ι))
    (hg_inj : InjOn g (range ι))
    (hH₁_V : H₁.V = f '' (H.V ∩ P₁))
    (u' : S_hat)
    (v' : S_hat)
    (Δ_hat : Set S_hat)
    (hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat)
    (B₁ : Set S_hat)
    (hB₁_line : IsLineWithEnds B₁ u' v')
    (hB₁_range : B₁ ⊆ range ι)
    (hΔ_hat_U_eq : (H₁.interSet Δ_hat).U = B₁)
    (L : Set S) (hL : L = g '' B₁)
    (hL_P₁ : L ⊆ P₁)
    (hL_U : L ⊆ H.U)
    (hL_cl : IsClosed L)
    (hB₁_cl : IsClosed B₁)
    (hP_V : (H.interSet L).V = H.V ∩ L)
    (hQ_hat_V : (H₁.interSet Δ_hat).V = H₁.V ∩ B₁)
    (hP_V_img : (H.interSet L).V = g '' (H₁.interSet Δ_hat).V) :
    (H.interSet L).U = L := by
  refine Subset.antisymm ?_ ?_
  · rw [(H.interSet L).U_eq, hP_V, interSet_E]
    refine union_subset inter_subset_right (iUnion₂_subset fun e he => ?_)
    exact hL_cl.closure_subset_iff.mpr he.2
  · have hB₁_decomp : B₁ = (H₁.interSet Δ_hat).V ∪
        ⋃ e_hat ∈ (H₁.interSet Δ_hat).E, closure e_hat :=
      hΔ_hat_U_eq.symm.trans (H₁.interSet Δ_hat).U_eq
    conv_lhs => rw [hL]
    rw [hB₁_decomp, image_union, ← hP_V_img]
    refine union_subset (H.interSet L).V_subset_U ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e_hat, he_hat, hy_cl⟩ := mem_iUnion₂.mp hy
    have he_hat' : e_hat ∈ H₁.E ∧ e_hat ⊆ Δ_hat := by rwa [interSet_E] at he_hat
    have he_hat_B₁ : e_hat ⊆ B₁ := by
      rw [← hΔ_hat_U_eq, hΔ_hat_inter_U]
      exact subset_inter (he_hat'.1.2.1.trans sdiff_subset) he_hat'.2
    have hcl_B₁ : closure e_hat ⊆ B₁ := hB₁_cl.closure_subset_iff.mpr he_hat_B₁
    have hge_UV : g '' e_hat ⊆ H.U \ H.V := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨hL_U (hL.symm ▸ mem_image_of_mem g (he_hat_B₁ hz)), fun hgzV => ?_⟩
      have hzV : z ∈ H₁.V := by
        rw [← hgf_inv (hB₁_range (he_hat_B₁ hz)), hH₁_V]
        exact mem_image_of_mem f ⟨hgzV, hL_P₁ (hL.symm ▸ mem_image_of_mem g (he_hat_B₁ hz))⟩
      exact (he_hat'.1.2.1 hz).2 hzV
    obtain ⟨y₀, hy₀⟩ := he_hat'.1.1
    have hgy₀_UV : g y₀ ∈ H.U \ H.V := hge_UV (mem_image_of_mem g hy₀)
    obtain ⟨e, he, hgy₀_e⟩ := H.exists_edge_of_mem hgy₀_UV.1 hgy₀_UV.2
    have hge_pc : IsPathConnected (g '' e_hat) :=
      he_hat'.1.2.2.1.image' (hg_cont.mono (he_hat_B₁.trans hB₁_range))
    have hge_sub_e : g '' e_hat ⊆ e := by
      have hun : e ∪ g '' e_hat = e :=
        he.2.2.2 (e ∪ g '' e_hat) (union_subset he.2.1 hge_UV)
          (he.2.2.1.union hge_pc ⟨g y₀, hgy₀_e, mem_image_of_mem g hy₀⟩) subset_union_left
      exact subset_union_right.trans hun.subset
    have hcl_sub_e : g '' closure e_hat ⊆ closure e :=
      ((hg_cont.mono (hcl_B₁.trans hB₁_range)).image_closure).trans (closure_mono hge_sub_e)
    rcases H₁.edge_cond e_hat he_hat'.1 with
      ⟨a', b', ha'b', hcap_hat, hLine_hat⟩ | ⟨a', _, hOArc⟩
    · have ha' : a' ∈ closure e_hat ∩ H₁.V := hcap_hat ▸ Or.inl rfl
      have hb' : b' ∈ closure e_hat ∩ H₁.V := hcap_hat ▸ Or.inr rfl
      have ha'B₁ : a' ∈ B₁ := hcl_B₁ ha'.1
      have hb'B₁ : b' ∈ B₁ := hcl_B₁ hb'.1
      have ha'Q : a' ∈ (H₁.interSet Δ_hat).V := hQ_hat_V.symm ▸ ⟨ha'.2, ha'B₁⟩
      have hb'Q : b' ∈ (H₁.interSet Δ_hat).V := hQ_hat_V.symm ▸ ⟨hb'.2, hb'B₁⟩
      have hga'b' : g a' ≠ g b' :=
        fun h => ha'b' (hg_inj (hB₁_range ha'B₁) (hB₁_range hb'B₁) h)
      have hga'_eV : g a' ∈ closure e ∩ H.V :=
        ⟨hcl_sub_e (mem_image_of_mem g ha'.1), (hP_V ▸ hP_V_img ▸ mem_image_of_mem g ha'Q).1⟩
      have hgb'_eV : g b' ∈ closure e ∩ H.V :=
        ⟨hcl_sub_e (mem_image_of_mem g hb'.1), (hP_V ▸ hP_V_img ▸ mem_image_of_mem g hb'Q).1⟩
      have hLine_img : IsLineWithEnds (g '' closure e_hat) (g a') (g b') :=
        isLineWithEnds_image hLine_hat (hg_cont.mono (hcl_B₁.trans hB₁_range))
          (hf_cont.mono ((image_mono hcl_B₁).trans (hL ▸ hL_P₁)))
          (hgf_inv.mono (hcl_B₁.trans hB₁_range))
      have hcl_eq : g '' closure e_hat = closure e := by
        rcases H.edge_cond e he with ⟨a, b, _, hcap, hLine⟩ | ⟨a, hcap, _⟩
        · have ha'ab : g a' ∈ ({a, b} : Set S) := hcap ▸ hga'_eV
          have hb'ab : g b' ∈ ({a, b} : Set S) := hcap ▸ hgb'_eV
          have hLine' : IsLineWithEnds (closure e) (g a') (g b') := by
            rcases mem_insert_iff.mp ha'ab with ha1 | ha2 <;>
              rcases mem_insert_iff.mp hb'ab with hb1 | hb2
            · exact (hga'b' (ha1.trans hb1.symm)).elim
            · rw [ha1, mem_singleton_iff.mp hb2]
              exact hLine
            · rw [mem_singleton_iff.mp ha2, hb1]
              exact hLine.symm
            · exact (hga'b' ((mem_singleton_iff.mp ha2).trans
                (mem_singleton_iff.mp hb2).symm)).elim
          exact eq_of_isLineWithEnds_subset hLine_img hLine' hcl_sub_e
        · have ha1 : g a' = a := mem_singleton_iff.mp (hcap ▸ hga'_eV)
          have ha2 : g b' = a := mem_singleton_iff.mp (hcap ▸ hgb'_eV)
          exact (hga'b' (ha1.trans ha2.symm)).elim
      have he_P : e ∈ (H.interSet L).E := by
        rw [interSet_E]
        exact ⟨he, subset_closure.trans (hL.symm ▸ hcl_eq.symm ▸ image_mono hcl_B₁)⟩
      exact (H.interSet L).closure_subset_U he_P (hcl_sub_e (mem_image_of_mem g hy_cl))
    · exact (not_isOArc_subset_isLineWithEnds hOArc hB₁_line hcl_B₁).elim

private theorem path_cut_size_le
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (X : Set S)
    (hCap : GM12.IsCappedDrawing ι H H₁)
    (hX : X ⊆ H.V ∩ (P₁ ∩ P₂))
    (p₀ : ↑P₁)
    (g : S_hat → S)
    (hgf_inv : LeftInvOn (cappedFwd P₁ ι p₀) g (range ι))
    (hf_inj : InjOn (cappedFwd P₁ ι p₀) P₁)
    (F_hat : Set S_hat)
    (hF_hat_card : (F_hat ∩ H₁.V).ncard ≤ 2)
    (Δ_hat : Set S_hat)
    (hX_hat : (ι '' Subtype.val ⁻¹' X ∩ Δ_hat).ncard ≤ (F_hat ∩ H₁.V).ncard)
    (B₁ : Set S_hat)
    (hB₁_range : B₁ ⊆ range ι)
    (hB₁_sub_Δ : B₁ ⊆ Δ_hat)
    (P : Drawing S)
    (hP_V : P.V = H.V ∩ (g '' B₁)) :
    (P.V ∩ X).ncard ≤ 2 := by
  let f := cappedFwd P₁ ι p₀
  have hsub : f '' (P.V ∩ X) ⊆ (ι '' ((↑) ⁻¹' X)) ∩ Δ_hat := by
    rintro _ ⟨x, ⟨hxPV, hxX⟩, rfl⟩
    have hxP₁ : x ∈ P₁ := (hX hxX).2.1
    have hfx_X : f x ∈ ι '' ((↑) ⁻¹' X) := by
      rw [← cappedFwd_image_eq_of_subset (hX.trans (inter_subset_right.trans inter_subset_left))]
      exact mem_image_of_mem f hxX
    have hfx_Δ : f x ∈ Δ_hat := by
      have hxL : x ∈ g '' B₁ := (hP_V ▸ hxPV).2
      obtain ⟨y, hyB₁, rfl⟩ := hxL
      change cappedFwd P₁ ι p₀ (g y) ∈ Δ_hat
      rw [hgf_inv (hB₁_range hyB₁)]
      exact hB₁_sub_Δ hyB₁
    exact ⟨hfx_X, hfx_Δ⟩
  have hfin_rhs : ((ι '' ((↑) ⁻¹' X)) ∩ Δ_hat).Finite := by
    refine (H₁.finite_V.subset ?_)
    rintro y ⟨hyX, _⟩
    rw [hCap.2]
    exact image_mono (preimage_mono (hX.trans inter_subset_left)) hyX
  have heq_card : (f '' (P.V ∩ X)).ncard = (P.V ∩ X).ncard :=
    (hf_inj.mono (inter_subset_right.trans
      (hX.trans (inter_subset_right.trans inter_subset_left)))).ncard_image
  calc (P.V ∩ X).ncard = (f '' (P.V ∩ X)).ncard := heq_card.symm
    _ ≤ ((ι '' ((↑) ⁻¹' X)) ∩ Δ_hat).ncard := Set.ncard_le_ncard hsub hfin_rhs
    _ ≤ (F_hat ∩ H₁.V).ncard := hX_hat
    _ ≤ 2 := hF_hat_card

private theorem first_disc_contains_drawing_boundary
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (f : S → S_hat)
    (g : S_hat → S)
    (hfg_inv : LeftInvOn g f P₁)
    (hgf_inv : LeftInvOn f g (range ι))
    (hH₁_U : H₁.U = f '' (H.U ∩ P₁))
    (B₁ : Set S_hat)
    (Δ_hat₁ : Set S_hat)
    (hΔ_hat₁_U : Δ_hat₁ ∩ H₁.U = B₁)
    (hΔ_hat₁_range : Δ_hat₁ ⊆ range ι)
    (hΔ₁_P₁ : g '' Δ_hat₁ ⊆ P₁)
    (P : Drawing S)
    (hP_U : P.U = g '' B₁) :
    (g '' Δ_hat₁) ∩ H.U = P.U := by
  rw [hP_U]
  have h1 : (g '' Δ_hat₁) ∩ H.U = g '' (Δ_hat₁ ∩ H₁.U) := by
    rw [hH₁_U]
    ext x
    constructor
    · rintro ⟨⟨y, hyΔ, rfl⟩, hxU⟩
      exact ⟨y, ⟨hyΔ, g y, ⟨hxU, hΔ₁_P₁ (mem_image_of_mem g hyΔ)⟩,
        hgf_inv (hΔ_hat₁_range hyΔ)⟩, rfl⟩
    · rintro ⟨y, ⟨hyΔ, x, ⟨hxU, hxP₁⟩, rfl⟩, rfl⟩
      rw [hfg_inv hxP₁]
      exact ⟨⟨f x, hyΔ, hfg_inv hxP₁⟩, hxU⟩
  rw [h1, hΔ_hat₁_U]

private theorem final_disc_intersection
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (F : Set S)
    (hFU : F ∩ H.U ⊆ H.V)
    (Δ₁ : Set S)
    (L : Set S)
    (P : Drawing S)
    (hP_V : P.V = H.V ∩ L)
    (hP_U : P.U = L)
    (Δ₂ : Set S)
    (hΔ_disc : IsClosedDisc (Δ₁ ∪ Δ₂))
    (hΔ_bd : subBd (Δ₁ ∪ Δ₂) = F)
    (hΔ_U : (Δ₁ ∪ Δ₂) ∩ H.U = P.U) :
    H.interSet (Δ₁ ∪ Δ₂) = P := by
  apply GM14.Drawing.ext_UV
  · rw [(GM14.interSet_V_and_U hΔ_disc.isClosed (hΔ_bd ▸ hFU)).2, Set.inter_comm, hΔ_U]
  · rw [interSet_V_of_isClosed H hΔ_disc.isClosed, hP_V]
    ext x
    constructor
    · rintro ⟨hxV, hxΔ⟩
      exact ⟨hxV, hP_U ▸ hΔ_U ▸ ⟨hxΔ, H.V_subset_U hxV⟩⟩
    · rintro ⟨hxV, hxL⟩
      exact ⟨hxV, (hΔ_U ▸ hP_U.symm ▸ hxL).1⟩

private theorem second_disc_contains_drawing_boundary
    {S : Type*} {U P F R : Set S} {u v : S}
    (hRU : Disjoint R U) (hPU : P ⊆ U) (hFU : F ∩ U = {u, v})
    (hPF : P ∩ F = {u, v}) :
    (R ∪ (P ∪ F)) ∩ U = P := by
  refine Subset.antisymm ?_ (fun x hx => ⟨Or.inr (Or.inl hx), hPU hx⟩)
  rintro x ⟨hxR | hxP | hxF, hxU⟩
  · exact (disjoint_left.mp hRU hxR hxU).elim
  · exact hxP
  · have hx : x ∈ P ∩ F := (hFU.trans hPF.symm) ▸ (show x ∈ F ∩ U from ⟨hxF, hxU⟩)
    exact hx.1

private theorem joined_discs_have_original_boundary
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Δ₁ Δ₂ F₁ F₂ P : Set S} {u v : S}
    (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂) (hΔ : IsClosedDisc (Δ₁ ∪ Δ₂))
    (hΔ_bd : discBd (Δ₁ ∪ Δ₂) = (discBd Δ₁ ∪ discBd Δ₂) \ (P \ {u, v}))
    (hΔ₁_bd : subBd Δ₁ = F₁ ∪ P) (hΔ₂_bd : subBd Δ₂ = P ∪ F₂)
    (hF₁P : F₁ ∩ P = {u, v}) (hPF₂ : P ∩ F₂ = {u, v}) :
    subBd (Δ₁ ∪ Δ₂) = F₁ ∪ F₂ := by
  rw [IsClosedDisc.subBd_eq_discBd hS hΔ, hΔ_bd,
    ← IsClosedDisc.subBd_eq_discBd hS hΔ₁, ← IsClosedDisc.subBd_eq_discBd hS hΔ₂,
    hΔ₁_bd, hΔ₂_bd]
  have hlo : ({u, v} : Set S) ⊆ F₁ := hF₁P ▸ inter_subset_left
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨(hxF₁ | hxP) | (hxP | hxF₂), hx_not⟩
    · exact Or.inl hxF₁
    · exact Or.inl (hlo (by_contra fun hx => hx_not ⟨hxP, hx⟩))
    · exact Or.inl (hlo (by_contra fun hx => hx_not ⟨hxP, hx⟩))
    · exact Or.inr hxF₂
  · rintro x (hxF₁ | hxF₂)
    · exact ⟨Or.inl (Or.inl hxF₁), fun ⟨hxP, hxuv⟩ => hxuv (hF₁P ▸ ⟨hxF₁, hxP⟩)⟩
    · exact ⟨Or.inr (Or.inr hxF₂), fun ⟨hxP, hxuv⟩ => hxuv (hPF₂ ▸ ⟨hxP, hxF₂⟩)⟩

private theorem fitting_first_side_disc
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    {t : ℕ}
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (X : Set S)
    (hCond2 : ∀ (F : Set S_hat), IsOArc F → F ∩ H₁.U ⊆ H₁.V → (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ, IsDial
      H₁ F Δ ∧ (ι '' Subtype.val ⁻¹' X ∩ Δ).ncard ≤ (F ∩ H₁.V).ncard)
    (F : Set S)
    (hF : IsOArc F)
    (hFU : F ∩ H.U ⊆ H.V)
    (hFV : (F ∩ H.V).ncard ≤ 2)
    (hRange_comp : IsCompact (range ι))
    (f : S → S_hat)
    (g : S_hat → S)
    (hf_cont : ContinuousOn f P₁)
    (hg_cont : ContinuousOn g (range ι))
    (hfg_inv : LeftInvOn g f P₁)
    (hgf_inv : LeftInvOn f g (range ι))
    (hf_maps : MapsTo f P₁ (range ι))
    (hg_maps : MapsTo g (range ι) P₁)
    (hf_inj : InjOn f P₁)
    (hg_inj : InjOn g (range ι))
    (hH₁_U : H₁.U = f '' (H.U ∩ P₁))
    (hH₁_V : H₁.V = f '' (H.V ∩ P₁))
    (hH₁_U_sub : H₁.U ⊆ range ι)
    (hH₁_V_sub : H₁.V ⊆ range ι)
    (hDi_bd_oArc : ∀ (i : Fin t), IsOArc (subBd (D i)))
    (hDisc_sub_range : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → subBd Δ_hat ⊆ range ι → (∀ (i :
      Fin t), ¬subBd (D i) ⊆ Δ_hat ∩ H₁.U) → Δ_hat ⊆ range ι)
    (hPullback_disc : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → Δ_hat ⊆ range ι → IsClosedDisc
      (g '' Δ_hat) ∧ subBd (g '' Δ_hat) = g '' subBd Δ_hat ∧ g '' Δ_hat ⊆ P₁)
    (hF₁ : F ⊆ P₁) :
    ∃ Δ, IsDial H F Δ := by
  let F_hat : Set S_hat := f '' F
  have hF_hat_range : F_hat ⊆ range ι := (hf_maps.mono hF₁ Subset.rfl).image_subset
  have hF_hat_oArc : IsOArc F_hat :=
    hF.image (hf_cont.mono hF₁) (hg_cont.mono hF_hat_range) (hfg_inv.mono hF₁)
  have hF_hat_U : F_hat ∩ H₁.U = f '' (F ∩ H.U) := by
    rw [hH₁_U, ← hf_inj.image_inter hF₁ inter_subset_right]
    congr 1; ext x; exact ⟨fun ⟨hxF, hxU, _⟩ => ⟨hxF, hxU⟩, fun ⟨hxF, hxU⟩ => ⟨hxF, hxU, hF₁ hxF⟩⟩
  have hF_hat_V : F_hat ∩ H₁.V = f '' (F ∩ H.V) := by
    rw [hH₁_V, ← hf_inj.image_inter hF₁ inter_subset_right]
    congr 1; ext x; exact ⟨fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩, fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, hF₁ hxF⟩⟩
  have hF_hat_UV : F_hat ∩ H₁.U ⊆ H₁.V := by
    rw [hF_hat_U, hH₁_V]
    exact image_mono fun x hx => ⟨hFU hx, hF₁ hx.1⟩
  have hF_hat_card : (F_hat ∩ H₁.V).ncard ≤ 2 := by
    rw [hF_hat_V]
    exact (Set.ncard_image_le (H.finite_V.subset inter_subset_right)).trans hFV
  obtain ⟨Δ_hat, hDial_hat, _⟩ := hCond2 F_hat hF_hat_oArc hF_hat_UV hF_hat_card
  have hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat :=
    (GM14.interSet_V_and_U hDial_hat.1.isClosed (hDial_hat.2.1 ▸ hF_hat_UV)).2
  have hΔ_hat_range : Δ_hat ⊆ range ι := by
    refine hDisc_sub_range hDial_hat.1 (hDial_hat.2.1.symm ▸ hF_hat_range) fun i hsub => ?_
    rcases hDial_hat.2.2 with hsubF | ⟨u', v', hu'v', _, hPath⟩
    · have hfin : (subBd (D i)).Finite :=
        H₁.finite_V.subset (hsub.trans (fun z hz => hF_hat_UV ⟨hsubF hz, hz.2⟩))
      exact GM11.infinite_of_isOArc (hDi_bd_oArc i) hfin
    · have hLine : IsLineWithEnds (H₁.interSet Δ_hat).U u' v' :=
        GM14.isLine_of_isPathBetween hPath hu'v'
      have hsub' : subBd (D i) ⊆ (H₁.interSet Δ_hat).U := by
        rw [hΔ_hat_inter_U, Set.inter_comm]
        exact hsub
      exact not_isOArc_subset_isLineWithEnds (hDi_bd_oArc i) hLine hsub'
  obtain ⟨hΔ_disc, hΔ_bd, hΔ_P₁⟩ := hPullback_disc hDial_hat.1 hΔ_hat_range
  let Δ : Set S := g '' Δ_hat
  have hΔ_bd_eq : subBd Δ = F := by
    rw [hΔ_bd, hDial_hat.2.1]
    exact (hfg_inv.mono hF₁).image_image
  have hΔ_inter_U : (H.interSet Δ).U = H.U ∩ Δ :=
    (GM14.interSet_V_and_U hΔ_disc.isClosed (hΔ_bd_eq ▸ hFU)).2
  have hΔ_U : (H.interSet Δ).U = g '' (H₁.interSet Δ_hat).U := by
    rw [hΔ_inter_U, hΔ_hat_inter_U, hH₁_U]
    have h1 : f '' (H.U ∩ P₁) ∩ Δ_hat = f '' (H.U ∩ Δ) := by
      ext y
      constructor
      · rintro ⟨⟨x, ⟨hxU, hxP₁⟩, rfl⟩, hyΔ⟩
        exact ⟨x, ⟨hxU, f x, hyΔ, hfg_inv hxP₁⟩, rfl⟩
      · rintro ⟨_, ⟨hxU, z, hzΔ, rfl⟩, rfl⟩
        exact ⟨⟨g z, ⟨hxU, hΔ_P₁ (mem_image_of_mem g hzΔ)⟩, rfl⟩,
          (hgf_inv (hΔ_hat_range hzΔ)).symm ▸ hzΔ⟩
    rw [h1]
    exact (hfg_inv.mono (inter_subset_right.trans hΔ_P₁)).image_image.symm
  have hΔ_V : (H.interSet Δ).V = g '' (H₁.interSet Δ_hat).V := by
    rw [interSet_V_of_isClosed H hΔ_disc.isClosed,
      interSet_V_of_isClosed H₁ hDial_hat.1.isClosed, hH₁_V]
    have h1 : f '' (H.V ∩ P₁) ∩ Δ_hat = f '' (H.V ∩ Δ) := by
      ext y
      constructor
      · rintro ⟨⟨x, ⟨hxV, hxP₁⟩, rfl⟩, hyΔ⟩
        exact ⟨x, ⟨hxV, f x, hyΔ, hfg_inv hxP₁⟩, rfl⟩
      · rintro ⟨_, ⟨hxV, z, hzΔ, rfl⟩, rfl⟩
        exact ⟨⟨g z, ⟨hxV, hΔ_P₁ (mem_image_of_mem g hzΔ)⟩, rfl⟩,
          (hgf_inv (hΔ_hat_range hzΔ)).symm ▸ hzΔ⟩
    rw [h1]
    exact (hfg_inv.mono (inter_subset_right.trans hΔ_P₁)).image_image.symm
  refine ⟨Δ, hΔ_disc, hΔ_bd_eq, ?_⟩
  rcases hDial_hat.2.2 with hsubF | ⟨u', v', hu'v', hFV_hat, hPath⟩
  · left
    have h1 : (H.interSet Δ).U ⊆ g '' F_hat := by
      rw [hΔ_U, hΔ_hat_inter_U, Set.inter_comm]
      exact image_mono hsubF
    rw [hΔ_inter_U, Set.inter_comm, (hfg_inv.mono hF₁).image_image] at h1
    exact h1
  · right
    have hu'_range : u' ∈ range ι := by
      have hu'V : u' ∈ F_hat ∩ H₁.V := hFV_hat ▸ Or.inl rfl
      exact hH₁_V_sub hu'V.2
    have hv'_range : v' ∈ range ι := by
      have hv'V : v' ∈ F_hat ∩ H₁.V := hFV_hat ▸ Or.inr rfl
      exact hH₁_V_sub hv'V.2
    have hguv : g u' ≠ g v' := fun h => hu'v' (hg_inj hu'_range hv'_range h)
    have hFV_eq : F ∩ H.V = {g u', g v'} := by
      have h1 : g '' (F_hat ∩ H₁.V) = F ∩ H.V := by
        rw [hF_hat_V]
        exact (hfg_inv.mono (inter_subset_left.trans hF₁)).image_image
      rw [← h1, hFV_hat]
      simp [image_insert_eq]
    have hQ_sub : (H₁.interSet Δ_hat).U ⊆ range ι := by
      rw [hΔ_hat_inter_U]
      exact inter_subset_left.trans hH₁_U_sub
    have hPath_S : (H.interSet Δ).IsPathBetween (g u') (g v') :=
      isPathBetween_of_image hRange_comp hg_cont
        (hf_cont.mono (hg_maps.image_subset))
        hgf_inv hQ_sub hΔ_U hΔ_V hPath
    exact ⟨g u', g v', hguv, hFV_eq, hPath_S⟩

private theorem crossing_boundary_has_two_interface_points
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H : Drawing S)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hInterU : P₁ ∩ P₂ ⊆ H.U)
    (F : Set S)
    (hF : IsOArc F)
    (hFU : F ∩ H.U ⊆ H.V)
    (hFV : (F ∩ H.V).ncard ≤ 2)
    (hP₁_cl : IsClosed P₁)
    (x₁ : S)
    (hx₁F : x₁ ∈ F)
    (hx₁_not_P₂ : x₁ ∉ P₂)
    (hx₁P₁ : x₁ ∈ P₁)
    (hF₁ : ¬F ⊆ P₁)
    (hfrP₁ : frontier P₁ ⊆ P₁ ∩ P₂) :
    ∃ u v, u ≠ v ∧ u ∈ F ∧ v ∈ F ∧ u ∈ H.V ∧ v ∈ H.V ∧ u ∈ P₁ ∩ P₂ ∧ v ∈ P₁ ∩ P₂ ∧ F ∩ H.V = {u,
      v} ∧ F ∩ H.U = {u, v} ∧ F ∩ (P₁ ∩ P₂) = {u, v} := by
  obtain ⟨x₂, hx₂F, hx₂_not_P₁⟩ := not_subset.mp hF₁
  have hx₂P₂ : x₂ ∈ P₂ := (eq_univ_iff_forall.mp hSplit.union x₂).resolve_left hx₂_not_P₁
  have hx₁₂ : x₁ ≠ x₂ := fun h => hx₂_not_P₁ (h ▸ hx₁P₁)
  obtain ⟨A₁, A₂, hA₁, hA₂, hA_union, hA_inter⟩ := hF.lines hx₁F hx₂F hx₁₂
  have hA_meets : ∀ {A : Set S}, IsLineWithEnds A x₁ x₂ →
      ∃ w ∈ A ∩ (P₁ ∩ P₂), w ∉ ({x₁, x₂} : Set S) := by
    exact boundary_arcs_meet_first_disc hP₁_cl hx₁P₁ hx₂_not_P₁ hx₁_not_P₂ hfrP₁
  obtain ⟨u, ⟨huA₁, hu12⟩, hu_not_x⟩ := hA_meets hA₁
  obtain ⟨v, ⟨hvA₂, hv12⟩, hv_not_x⟩ := hA_meets hA₂
  have huv : u ≠ v := fun h => hu_not_x (hA_inter ▸ ⟨huA₁, h ▸ hvA₂⟩)
  have huF : u ∈ F := hA_union ▸ Or.inl huA₁
  have hvF : v ∈ F := hA_union ▸ Or.inr hvA₂
  have huV : u ∈ H.V := hFU ⟨huF, hInterU hu12⟩
  have hvV : v ∈ H.V := hFU ⟨hvF, hInterU hv12⟩
  have huv_sub_F12 : ({u, v} : Set S) ⊆ F ∩ (P₁ ∩ P₂) := by
    rintro z (rfl | rfl)
    · exact ⟨huF, hu12⟩
    · exact ⟨hvF, hv12⟩
  have hF12_sub_FV : F ∩ (P₁ ∩ P₂) ⊆ F ∩ H.V :=
    fun z hz => ⟨hz.1, hFU ⟨hz.1, hInterU hz.2⟩⟩
  have hFV_sub_FU : F ∩ H.V ⊆ F ∩ H.U :=
    inter_subset_inter_right _ H.V_subset_U
  have hFU_sub_FV : F ∩ H.U ⊆ F ∩ H.V :=
    fun z hz => ⟨hz.1, hFU hz⟩
  have hFV_eq : F ∩ H.V = {u, v} := by
    refine (Set.eq_of_subset_of_ncard_le (huv_sub_F12.trans hF12_sub_FV) ?_
      (H.finite_V.subset inter_subset_right)).symm
    rw [Set.ncard_pair huv]
    exact hFV
  have hFU_eq : F ∩ H.U = {u, v} :=
    Subset.antisymm (hFU_sub_FV.trans hFV_eq.subset) (hFV_eq ▸ hFV_sub_FU)
  have hF12_eq : F ∩ (P₁ ∩ P₂) = {u, v} :=
    Subset.antisymm (hF12_sub_FV.trans hFV_eq.subset) huv_sub_F12
  exact ⟨u, v, huv, huF, hvF, huV, hvV, hu12, hv12, hFV_eq, hFU_eq, hF12_eq⟩

private theorem capped_disc_contains_spanning_boundary_path
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H₁ : Drawing S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hS_hat : IsClosedSurface S_hat)
    (hDi_bd_U : ∀ (i : Fin t), subBd (D i) ⊆ H₁.U)
    (hDi_bd_oArc : ∀ (i : Fin t), IsOArc (subBd (D i)))
    (hDi_disj_range : ∀ (i : Fin t), Disjoint (D i) (range ι))
    (i : Fin t)
    (u' : S_hat)
    (v' : S_hat)
    (F₁' : Set S_hat)
    (hu'_bd : u' ∈ subBd (D i))
    (hv'_bd : v' ∈ subBd (D i))
    (hu'v' : u' ≠ v')
    (hF₁'_range : F₁' ⊆ range ι)
    (hF₁'_line : IsLineWithEnds F₁' u' v')
    (hF₁'_U : F₁' ∩ H₁.U = {u', v'})
    (L_D : Set S_hat)
    (hL_D_line : IsLineWithEnds L_D u' v')
    (hL_D_sub : L_D \ {u', v'} ⊆ D i)
    (hu'F₁' : u' ∈ F₁')
    (hv'F₁' : v' ∈ F₁')
    (hF_hat_U : (F₁' ∪ L_D) ∩ H₁.U = {u', v'})
    (hF_hat_V : (F₁' ∪ L_D) ∩ H₁.V = {u', v'})
    (Δ_hat : Set S_hat)
    (hDial_hat : IsDial H₁ (F₁' ∪ L_D) Δ_hat)
    (hΔ_hat_disc : IsClosedDisc Δ_hat)
    (hΔ_hat_bd : subBd Δ_hat = F₁' ∪ L_D)
    (hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat)
    (hF_hat_sub_Δ : (F₁' ∪ L_D) ⊆ Δ_hat) :
    ∃ B₁, IsLineWithEnds B₁ u' v' ∧ B₁ ⊆ subBd (D i) ∧ B₁ ⊆ Δ_hat ∧ (H₁.interSet
      Δ_hat).IsPathBetween u' v' ∧ (H₁.interSet Δ_hat).U = B₁ := by
  let F_hat := F₁' ∪ L_D
  let U_hat : Set S_hat := Δ_hat \ frontier Δ_hat
  have hU_hat_eq : U_hat = Δ_hat \ F_hat := by
    change Δ_hat \ frontier Δ_hat = Δ_hat \ F_hat
    rw [← subBd_eq_frontier, hΔ_hat_bd]
  have hU_hat_conn : IsPreconnected U_hat :=
    GM11.IsClosedDisc.isPreconnected_diff_frontier hS_hat hΔ_hat_disc
  have hΔ_hat_sub_cl : Δ_hat ⊆ closure U_hat :=
    GM11.IsClosedDisc.subset_closure_diff_frontier hS_hat hΔ_hat_disc
  obtain ⟨y₁, hy₁⟩ := (GM11.isPathConnected_sdiff_pair hL_D_line).nonempty
  have hy₁_Di : y₁ ∈ D i := hL_D_sub hy₁
  have hy₁_cl : y₁ ∈ closure U_hat :=
    hΔ_hat_sub_cl (hF_hat_sub_Δ (Or.inr hy₁.1))
  obtain ⟨z₁, hz₁_Di, hz₁_U⟩ := mem_closure_iff.mp hy₁_cl (D i) (hSplit.isOpenDisc i).1 hy₁_Di
  obtain ⟨y₂, hy₂⟩ := (GM11.isPathConnected_sdiff_pair hF₁'_line).nonempty
  obtain ⟨_, hcl_Di⟩ := isOpen_disjoint_subBd_and_closure_eq (hSplit.isOpenDisc i).1
  have hy₂_not_cl : y₂ ∈ (closure (D i))ᶜ := by
    rw [hcl_Di]
    rintro (hy₂_Di | hy₂_bd)
    · exact disjoint_left.mp (hDi_disj_range i) hy₂_Di (hF₁'_range hy₂.1)
    · exact hy₂.2 (hF₁'_U ▸ ⟨hy₂.1, hDi_bd_U i hy₂_bd⟩)
  have hy₂_cl : y₂ ∈ closure U_hat :=
    hΔ_hat_sub_cl (hF_hat_sub_Δ (Or.inl hy₂.1))
  obtain ⟨z₂, hz₂_not_cl, hz₂_U⟩ :=
    mem_closure_iff.mp hy₂_cl (closure (D i))ᶜ isClosed_closure.isOpen_compl hy₂_not_cl
  have hU_hat_meets_bd : (U_hat ∩ subBd (D i)).Nonempty := by
    by_contra h
    have hdis_bd : Disjoint U_hat (subBd (D i)) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
    have hdis_fr : Disjoint U_hat (frontier (closure (D i))) :=
      hdis_bd.mono_right (subBd_eq_frontier (D i) ▸ frontier_closure_subset)
    exact hz₂_not_cl (GM14.subset_of_disjoint_frontier hU_hat_conn isClosed_closure
      hdis_fr hz₁_U (subset_closure hz₁_Di) hz₂_U)
  obtain ⟨z₀, hz₀_U, hz₀_bd⟩ := hU_hat_meets_bd
  have hz₀_Δ : z₀ ∈ Δ_hat := (hU_hat_eq ▸ hz₀_U).1
  have hz₀_not_F : z₀ ∉ F_hat := (hU_hat_eq ▸ hz₀_U).2
  obtain ⟨B₁_0, B₂_0, hB₁_0, hB₂_0, hB_union, hB_inter⟩ :=
    (hDi_bd_oArc i).lines hu'_bd hv'_bd hu'v'
  have hB₁_exists : ∃ B₁ : Set S_hat,
      IsLineWithEnds B₁ u' v' ∧ B₁ ⊆ subBd (D i) ∧ z₀ ∈ B₁ := by
    rcases hB_union ▸ hz₀_bd with hz₀1 | hz₀2
    · exact ⟨B₁_0, hB₁_0, hB_union ▸ subset_union_left, hz₀1⟩
    · exact ⟨B₂_0, hB₂_0, hB_union ▸ subset_union_right, hz₀2⟩
  obtain ⟨B₁, hB₁_line, hB₁_bd, hz₀_B₁⟩ := hB₁_exists
  obtain ⟨hu'B₁, hv'B₁⟩ := ends_mem_of_isLineWithEnds hB₁_line
  have hz₀_not_uv : z₀ ∉ ({u', v'} : Set S_hat) := by
    rintro (rfl | rfl)
    · exact hz₀_not_F (Or.inl hu'F₁')
    · exact hz₀_not_F (Or.inl hv'F₁')
  have hB₁_U : B₁ ⊆ H₁.U := hB₁_bd.trans (hDi_bd_U i)
  have hB₁_sub_Δ : B₁ ⊆ Δ_hat := by
    exact boundary_arc_mem_disc (S_hat := S_hat) H₁ u' v' F_hat hF_hat_U
      Δ_hat hΔ_hat_disc hΔ_hat_bd (hF_hat_sub_Δ (Or.inl hu'F₁'))
      (hF_hat_sub_Δ (Or.inl hv'F₁')) z₀ hz₀_Δ B₁ hB₁_line hz₀_B₁ hz₀_not_uv hB₁_U
  have hPath_hat : (H₁.interSet Δ_hat).IsPathBetween u' v' := by
    exact capped_path_avoids_cap (S_hat := S_hat) H₁ u' v' hu'v' F_hat hF_hat_V Δ_hat hDial_hat z₀
      hz₀_Δ hz₀_not_F B₁ hz₀_B₁ hB₁_U
  have hΔ_hat_U_eq : (H₁.interSet Δ_hat).U = B₁ := by
    have hLine : IsLineWithEnds (H₁.interSet Δ_hat).U u' v' :=
      GM14.isLine_of_isPathBetween hPath_hat hu'v'
    have hsub : B₁ ⊆ (H₁.interSet Δ_hat).U := by
      rw [hΔ_hat_inter_U]
      exact subset_inter hB₁_U hB₁_sub_Δ
    exact (eq_of_isLineWithEnds_subset hB₁_line hLine hsub).symm
  -- Cut out `Δ_hat₁ ⊆ Δ_hat` bounded by `F₁' ∪ B₁`.
  exact ⟨B₁, hB₁_line, hB₁_bd, hB₁_sub_Δ, hPath_hat, hΔ_hat_U_eq⟩

private theorem glue_discs_across_boundary_path
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (X : Set S)
    (hInterU : P₁ ∩ P₂ ⊆ H.U)
    (hCond4 : ∀ (F : Set S) (u v : S) (P : Drawing S), F ⊆ P₂ → u ∈ P₁ ∩ P₂ ∩ H.V → v ∈ P₁ ∩ P₂ ∩
      H.V → IsLineWithEnds F u v → F ∩ H.U ⊆ {u, v} → P.IsSubdrawing (H.interSet (P₁ ∩ P₂)) →
      P.IsPathBetween u v → (P.V ∩ X).ncard ≤ 2 → ∃ U₀, IsOpenDisc U₀ ∧ IsClosedDisc (closure U₀)
      ∧ U₀ ⊆ P₂ ∧ subBd U₀ = P.U ∪ F ∧ Disjoint U₀ H.U)
    (F : Set S)
    (hFU : F ∩ H.U ⊆ H.V)
    (hS : IsClosedSurface S)
    (hP₂_cl : IsClosed P₂)
    (f : S → S_hat)
    (g : S_hat → S)
    (hfg_inv : LeftInvOn g f P₁)
    (hgf_inv : LeftInvOn f g (range ι))
    (hH₁_U : H₁.U = f '' (H.U ∩ P₁))
    (u : S)
    (v : S)
    (huv : u ≠ v)
    (huV : u ∈ H.V)
    (hvV : v ∈ H.V)
    (hu12 : u ∈ P₁ ∩ P₂)
    (hv12 : v ∈ P₁ ∩ P₂)
    (hFV_eq : F ∩ H.V = {u, v})
    (F₁ : Set S)
    (F₂ : Set S)
    (hF₂_line : IsLineWithEnds F₂ u v)
    (hF_union : F₁ ∪ F₂ = F)
    (hF₁_P₁ : F₁ ⊆ P₁)
    (hF₂_P₂ : F₂ ⊆ P₂)
    (huF₁ : u ∈ F₁)
    (hvF₁ : v ∈ F₁)
    (huF₂ : u ∈ F₂)
    (hvF₂ : v ∈ F₂)
    (hF₁_U : F₁ ∩ H.U = {u, v})
    (hF₂_U : F₂ ∩ H.U = {u, v})
    (u' : S_hat)
    (v' : S_hat)
    (B₁ : Set S_hat)
    (hu'B₁ : u' ∈ B₁)
    (hv'B₁ : v' ∈ B₁)
    (Δ_hat₁ : Set S_hat)
    (hΔ_hat₁_bd : subBd Δ_hat₁ = (f '' F₁) ∪ B₁)
    (hΔ_hat₁_U : Δ_hat₁ ∩ H₁.U = B₁)
    (hΔ_hat₁_range : Δ_hat₁ ⊆ range ι)
    (hΔ₁_disc : IsClosedDisc (g '' Δ_hat₁))
    (hΔ₁_bd_img : subBd (g '' Δ_hat₁) = g '' subBd Δ_hat₁)
    (hΔ₁_P₁ : g '' Δ_hat₁ ⊆ P₁)
    (P : Drawing S)
    (hL_U : (g '' B₁) ⊆ H.U)
    (hgu' : g u' = u)
    (hgv' : g v' = v)
    (hL_line : IsLineWithEnds (g '' B₁) u v)
    (hP_V : P.V = H.V ∩ (g '' B₁))
    (hP_sub : P.IsSubdrawing (H.interSet (P₁ ∩ P₂)))
    (hP_U : P.U = (g '' B₁))
    (hP_path : P.IsPathBetween u v)
    (hPX_card : (P.V ∩ X).ncard ≤ 2) :
    ∃ Δ, IsDial H F Δ := by
  let Δ₁ := g '' Δ_hat₁
  let L := g '' B₁
  obtain ⟨U₀, hU₀_open, hU₀_cl_disc, hU₀_P₂, hU₀_bd, hU₀_disj⟩ :=
    hCond4 F₂ u v P hF₂_P₂ ⟨hu12, huV⟩ ⟨hv12, hvV⟩ hF₂_line hF₂_U.subset hP_sub hP_path hPX_card
  let Δ₂ : Set S := closure U₀
  have hΔ₂_P₂ : Δ₂ ⊆ P₂ := hP₂_cl.closure_subset_iff.mpr hU₀_P₂
  have hP_F₂_inter : P.U ∩ F₂ = {u, v} := by
    rw [hP_U]
    refine Subset.antisymm ?_ ?_
    · intro z ⟨hzL, hzF₂⟩
      exact hF₂_U ▸ ⟨hzF₂, hL_U hzL⟩
    · rintro z (rfl | rfl)
      · exact ⟨hgu' ▸ mem_image_of_mem g hu'B₁, huF₂⟩
      · exact ⟨hgv' ▸ mem_image_of_mem g hv'B₁, hvF₂⟩
  have hP_F₂_oArc : IsOArc (P.U ∪ F₂) :=
    Surface.oArc_of_lines (hP_U ▸ hL_line) hF₂_line hP_F₂_inter
  have hΔ₂_bd : subBd Δ₂ = P.U ∪ F₂ := by
    rw [GM14.subBd_closure_eq_subBd_of_isOpenDisc hS hU₀_open (hU₀_bd ▸ hP_F₂_oArc) hU₀_cl_disc,
      hU₀_bd]
  obtain ⟨_, hcl_U₀⟩ := isOpen_disjoint_subBd_and_closure_eq hU₀_open.1
  have hΔ₂_eq : Δ₂ = U₀ ∪ (P.U ∪ F₂) := hcl_U₀.trans (by rw [hU₀_bd])
  have hΔ₁_bd : subBd Δ₁ = F₁ ∪ P.U := by
    rw [hΔ₁_bd_img, hΔ_hat₁_bd, image_union, (hfg_inv.mono hF₁_P₁).image_image, hP_U]
  have hΔ₁_U : Δ₁ ∩ H.U = P.U := by
    exact first_disc_contains_drawing_boundary (S := S) (S_hat := S_hat) P₁ ι H H₁ f g hfg_inv
      hgf_inv hH₁_U B₁ Δ_hat₁ hΔ_hat₁_U hΔ_hat₁_range hΔ₁_P₁ P hP_U
  have hΔ₂_U : Δ₂ ∩ H.U = P.U := by
    rw [hΔ₂_eq]
    exact second_disc_contains_drawing_boundary hU₀_disj (hP_U.symm ▸ hL_U)
      hF₂_U hP_F₂_inter
  have hΔ12_inter : Δ₁ ∩ Δ₂ = P.U := by
    refine Subset.antisymm ?_ ?_
    · intro x ⟨hxΔ₁, hxΔ₂⟩
      have hxU : x ∈ H.U := hInterU ⟨hΔ₁_P₁ hxΔ₁, hΔ₂_P₂ hxΔ₂⟩
      exact hΔ₁_U ▸ ⟨hxΔ₁, hxU⟩
    · intro x hxPU
      exact ⟨(hΔ₁_U ▸ hxPU).1, (hΔ₂_U ▸ hxPU).1⟩
  have hL_bd₁ : P.U ⊆ discBd Δ₁ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hΔ₁_disc, hΔ₁_bd]
    exact subset_union_right
  have hL_bd₂ : P.U ⊆ discBd Δ₂ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hU₀_cl_disc, hΔ₂_bd]
    exact subset_union_left
  obtain ⟨hΔ_disc, hΔ_discBd⟩ :=
    disc_union Δ₁ Δ₂ P.U u v hΔ₁_disc hU₀_cl_disc (hP_U ▸ hL_line) hΔ12_inter hL_bd₁ hL_bd₂
  have hF₁_P_inter : F₁ ∩ P.U = {u, v} := by
    rw [hP_U]
    refine Subset.antisymm ?_ ?_
    · intro z ⟨hzF₁, hzL⟩
      exact hF₁_U ▸ ⟨hzF₁, hL_U hzL⟩
    · rintro z (rfl | rfl)
      · exact ⟨huF₁, hgu' ▸ mem_image_of_mem g hu'B₁⟩
      · exact ⟨hvF₁, hgv' ▸ mem_image_of_mem g hv'B₁⟩
  have hΔ_bd : subBd (Δ₁ ∪ Δ₂) = F := by
    rw [← hF_union]
    exact joined_discs_have_original_boundary hS hΔ₁_disc hU₀_cl_disc hΔ_disc hΔ_discBd hΔ₁_bd
      hΔ₂_bd hF₁_P_inter hP_F₂_inter
  have hΔ_U : (Δ₁ ∪ Δ₂) ∩ H.U = P.U := by
    rw [union_inter_distrib_right, hΔ₁_U, hΔ₂_U, Set.union_self]
  have hΔ_interSet : H.interSet (Δ₁ ∪ Δ₂) = P := by
    exact final_disc_intersection (S := S) H F hFU Δ₁ L P hP_V hP_U Δ₂ hΔ_disc hΔ_bd hΔ_U
  refine ⟨Δ₁ ∪ Δ₂, hΔ_disc, hΔ_bd, Or.inr ⟨u, v, huv, hFV_eq, ?_⟩⟩
  rwa [hΔ_interSet]

private theorem cap_boundary_arc_closes_curve
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H₁ : Drawing S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hS_hat : IsClosedSurface S_hat)
    (hDi_bd_U : ∀ (i : Fin t), subBd (D i) ⊆ H₁.U)
    (hDi_bd_oArc : ∀ (i : Fin t), IsOArc (subBd (D i)))
    (hDi_disj_range : ∀ (i : Fin t), Disjoint (D i) (range ι))
    (hDi_disj_U : ∀ (i : Fin t), Disjoint (D i) H₁.U)
    (i : Fin t)
    (u' : S_hat)
    (v' : S_hat)
    (F₁' : Set S_hat)
    (hu'_bd : u' ∈ subBd (D i))
    (hv'_bd : v' ∈ subBd (D i))
    (hu'_V : u' ∈ H₁.V)
    (hv'_V : v' ∈ H₁.V)
    (hu'v' : u' ≠ v')
    (hF₁'_range : F₁' ⊆ range ι)
    (hF₁'_line : IsLineWithEnds F₁' u' v')
    (hF₁'_U : F₁' ∩ H₁.U = {u', v'}) :
    ∃ L_D, IsLineWithEnds L_D u' v' ∧ L_D \ {u', v'} ⊆ D i ∧ F₁' ∩ L_D = {u', v'} ∧ IsOArc (F₁' ∪
      L_D) ∧ L_D ∩ H₁.U = {u', v'} ∧
      (F₁' ∪ L_D) ∩ H₁.U = {u', v'} ∧ (F₁' ∪ L_D) ∩ H₁.V = {u', v'} := by
  obtain ⟨L_D, hL_D_line, hL_D_sub⟩ :=
    exists_chord_in_cappingDisc hS_hat (hSplit.isOpenDisc i) (hDi_disj_U i)
      (hDi_bd_oArc i) (hDi_bd_U i) ⟨hu'_bd, hu'_V⟩ ⟨hv'_bd, hv'_V⟩ hu'v'
  obtain ⟨hu'F₁', hv'F₁'⟩ := ends_mem_of_isLineWithEnds hF₁'_line
  obtain ⟨hu'L_D, hv'L_D⟩ := ends_mem_of_isLineWithEnds hL_D_line
  have hF₁'_L_D_inter : F₁' ∩ L_D = {u', v'} := by
    refine Subset.antisymm ?_ ?_
    · rintro y ⟨hyF₁', hyL_D⟩
      by_contra hy_not
      exact disjoint_left.mp (hDi_disj_range i) (hL_D_sub ⟨hyL_D, hy_not⟩) (hF₁'_range hyF₁')
    · rintro y (rfl | rfl)
      · exact ⟨hu'F₁', hu'L_D⟩
      · exact ⟨hv'F₁', hv'L_D⟩
  let F_hat : Set S_hat := F₁' ∪ L_D
  have hF_hat_oArc : IsOArc F_hat := Surface.oArc_of_lines hF₁'_line hL_D_line hF₁'_L_D_inter
  have hL_D_U : L_D ∩ H₁.U = {u', v'} := by
    refine Subset.antisymm ?_ ?_
    · rintro y ⟨hyL_D, hyU⟩
      by_contra hy_not
      exact disjoint_left.mp (hDi_disj_U i) (hL_D_sub ⟨hyL_D, hy_not⟩) hyU
    · rintro y (rfl | rfl)
      · exact ⟨hu'L_D, H₁.V_subset_U hu'_V⟩
      · exact ⟨hv'L_D, H₁.V_subset_U hv'_V⟩
  have hF_hat_U : F_hat ∩ H₁.U = {u', v'} := by
    rw [union_inter_distrib_right, hF₁'_U, hL_D_U, Set.union_self]
  have hF_hat_V : F_hat ∩ H₁.V = {u', v'} := by
    refine Subset.antisymm ?_ ?_
    · exact (inter_subset_inter_right _ H₁.V_subset_U).trans hF_hat_U.subset
    · rintro y (rfl | rfl)
      · exact ⟨Or.inl hu'F₁', hu'_V⟩
      · exact ⟨Or.inl hv'F₁', hv'_V⟩
  exact ⟨L_D, hL_D_line, hL_D_sub, hF₁'_L_D_inter, hF_hat_oArc, hL_D_U, hF_hat_U, hF_hat_V⟩

private theorem capped_boundary_path_spans_subdisc
    {S : Type w}
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    {t : ℕ}
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H₁ : Drawing S_hat)
    (hS_hat : IsClosedSurface S_hat)
    (hDi_bd_oArc : ∀ (i : Fin t), IsOArc (subBd (D i)))
    (hDisc_sub_range : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → subBd Δ_hat ⊆ range ι → (∀ (i :
      Fin t), ¬subBd (D i) ⊆ Δ_hat ∩ H₁.U) → Δ_hat ⊆ range ι)
    (u' : S_hat)
    (v' : S_hat)
    (F₁' : Set S_hat)
    (hF₁'_range : F₁' ⊆ range ι)
    (hF₁'_line : IsLineWithEnds F₁' u' v')
    (hF₁'_U : F₁' ∩ H₁.U = {u', v'})
    (hu'F₁' : u' ∈ F₁')
    (hv'F₁' : v' ∈ F₁')
    (Δ_hat : Set S_hat)
    (hΔ_hat_disc : IsClosedDisc Δ_hat)
    (hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat)
    (hF₁'_sub_Δ : F₁' ⊆ Δ_hat)
    (B₁ : Set S_hat)
    (hB₁_line : IsLineWithEnds B₁ u' v')
    (hB₁_sub_Δ : B₁ ⊆ Δ_hat)
    (hΔ_hat_U_eq : (H₁.interSet Δ_hat).U = B₁)
    (hu'B₁ : u' ∈ B₁)
    (hv'B₁ : v' ∈ B₁)
    (hB₁_U : B₁ ⊆ H₁.U)
    (hB₁_range : B₁ ⊆ range ι) :
    ∃ Δ_hat₁, F₁' ∩ B₁ = {u', v'} ∧ IsClosedDisc Δ_hat₁ ∧ subBd Δ_hat₁ = F₁' ∪ B₁ ∧ Δ_hat₁ ∩ H₁.U
      = B₁ ∧ Δ_hat₁ ⊆ range ι := by
  have hF₁'_B₁_inter : F₁' ∩ B₁ = {u', v'} := by
    refine Subset.antisymm ?_ ?_
    · intro z ⟨hzF₁', hzB₁⟩
      exact hF₁'_U ▸ ⟨hzF₁', hB₁_U hzB₁⟩
    · rintro z (rfl | rfl)
      · exact ⟨hu'F₁', hu'B₁⟩
      · exact ⟨hv'F₁', hv'B₁⟩
  have hF₁'_B₁_oArc : IsOArc (F₁' ∪ B₁) :=
    Surface.oArc_of_lines hF₁'_line hB₁_line hF₁'_B₁_inter
  have hF₁'_B₁_sub_Δ : F₁' ∪ B₁ ⊆ Δ_hat :=
    union_subset hF₁'_sub_Δ hB₁_sub_Δ
  obtain ⟨Δ_hat₁, ⟨hΔ_hat₁_sub, hΔ_hat₁_disc, hΔ_hat₁_discBd, -⟩, -⟩ :=
    disc_oArc Δ_hat (F₁' ∪ B₁) hΔ_hat_disc hF₁'_B₁_sub_Δ hF₁'_B₁_oArc
  have hΔ_hat₁_bd : subBd Δ_hat₁ = F₁' ∪ B₁ :=
    (IsClosedDisc.subBd_eq_discBd hS_hat hΔ_hat₁_disc).trans hΔ_hat₁_discBd
  have hΔ_hat₁_U : Δ_hat₁ ∩ H₁.U = B₁ := by
    refine Subset.antisymm ?_ ?_
    · calc Δ_hat₁ ∩ H₁.U ⊆ Δ_hat ∩ H₁.U := inter_subset_inter_left _ hΔ_hat₁_sub
        _ = (H₁.interSet Δ_hat).U := by rw [hΔ_hat_inter_U, Set.inter_comm]
        _ = B₁ := hΔ_hat_U_eq
    · refine subset_inter ?_ hB₁_U
      intro z hz
      have hbd_z : z ∈ subBd Δ_hat₁ := hΔ_hat₁_bd.symm ▸ Or.inr hz
      exact hΔ_hat₁_disc.isClosed.closure_eq ▸ hbd_z.1
  have hΔ_hat₁_range : Δ_hat₁ ⊆ range ι := by
    exact first_capped_disc_lies_in_range (S := S) (S_hat := S_hat) (t := t) P₁ ι D H₁ hDi_bd_oArc
      hDisc_sub_range u' v' F₁' hF₁'_range B₁ hB₁_line hB₁_range Δ_hat₁ hΔ_hat₁_disc hΔ_hat₁_bd
      hΔ_hat₁_U
  -- Pull back `Δ₁ := g '' Δ_hat₁` and `P := H.interSet (g '' B₁)`.
  exact ⟨Δ_hat₁, hF₁'_B₁_inter, hΔ_hat₁_disc, hΔ_hat₁_bd, hΔ_hat₁_U, hΔ_hat₁_range⟩

private theorem disc_in_capped_drawing_pulls_back
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    (P₁ : Set S)
    (ι : ↑P₁ → S_hat)
    (hS : IsClosedSurface S)
    (hS_hat : IsClosedSurface S_hat)
    (f : S → S_hat)
    (g : S_hat → S)
    (hf_cont : ContinuousOn f P₁)
    (hg_cont : ContinuousOn g (range ι))
    (hgf_inv : LeftInvOn f g (range ι))
    (hg_maps : MapsTo g (range ι) P₁) :
    ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → Δ_hat ⊆ range ι → IsClosedDisc (g '' Δ_hat) ∧
      subBd (g '' Δ_hat) = g '' subBd Δ_hat ∧ g '' Δ_hat ⊆ P₁ := by
  exact pullback_of_capped_disc (S := S) (S_hat := S_hat) P₁ ι hS hS_hat f g hf_cont hg_cont
    hgf_inv hg_maps

private theorem boundary_path_pulls_back_with_bounded_cut
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    [T2Space S_hat]
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (H : Drawing S)
    (H₁ : Drawing S_hat)
    (X : Set S)
    (hCap : GM12.IsCappedDrawing ι H H₁)
    (hX : X ⊆ H.V ∩ (P₁ ∩ P₂))
    (hRange_comp : IsCompact (range ι))
    (p₀ : ↑P₁)
    (g : S_hat → S)
    (hf_cont : ContinuousOn (cappedFwd P₁ ι p₀) P₁)
    (hg_cont : ContinuousOn g (range ι))
    (hfg_inv : LeftInvOn g (cappedFwd P₁ ι p₀) P₁)
    (hgf_inv : LeftInvOn (cappedFwd P₁ ι p₀) g (range ι))
    (hg_maps : MapsTo g (range ι) P₁)
    (hf_inj : InjOn (cappedFwd P₁ ι p₀) P₁)
    (hg_inj : InjOn g (range ι))
    (hH₁_V : H₁.V = cappedFwd P₁ ι p₀ '' (H.V ∩ P₁))
    (u : S)
    (v : S)
    (u' : S_hat)
    (v' : S_hat)
    (F_hat : Set S_hat)
    (hF_hat_card : (F_hat ∩ H₁.V).ncard ≤ 2)
    (Δ_hat : Set S_hat)
    (hX_hat : (ι '' Subtype.val ⁻¹' X ∩ Δ_hat).ncard ≤ (F_hat ∩ H₁.V).ncard)
    (hΔ_hat_disc : IsClosedDisc Δ_hat)
    (hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat)
    (B₁ : Set S_hat)
    (hB₁_line : IsLineWithEnds B₁ u' v')
    (hB₁_sub_Δ : B₁ ⊆ Δ_hat)
    (hPath_hat : (H₁.interSet Δ_hat).IsPathBetween u' v')
    (hΔ_hat_U_eq : (H₁.interSet Δ_hat).U = B₁)
    (hB₁_range : B₁ ⊆ range ι)
    (hL_P₁ : (g '' B₁) ⊆ P₁)
    (hL_U : (g '' B₁) ⊆ H.U)
    (hgu' : g u' = u)
    (hgv' : g v' = v)
    (hL_cl : IsClosed (g '' B₁))
    (hB₁_cl : IsClosed B₁)
    (hP_V : (H.interSet (g '' B₁)).V = H.V ∩ (g '' B₁)) :
    (H.interSet (g '' B₁)).U = (g '' B₁) ∧ (H.interSet (g '' B₁)).IsPathBetween u v ∧ ((H.interSet
      (g '' B₁)).V ∩ X).ncard ≤ 2 := by
  let f := cappedFwd P₁ ι p₀
  let L := g '' B₁
  let P := H.interSet L
  have hQ_hat_V : (H₁.interSet Δ_hat).V = H₁.V ∩ B₁ := by
    rw [interSet_V_of_isClosed H₁ hΔ_hat_disc.isClosed]
    have h1 : H₁.V ∩ Δ_hat = H₁.V ∩ (H₁.U ∩ Δ_hat) := by
      ext y
      exact ⟨fun ⟨hyV, hyΔ⟩ => ⟨hyV, H₁.V_subset_U hyV, hyΔ⟩, fun ⟨hyV, _, hyΔ⟩ => ⟨hyV, hyΔ⟩⟩
    rw [h1, ← hΔ_hat_inter_U, hΔ_hat_U_eq]
  have hP_V_img : P.V = g '' (H₁.interSet Δ_hat).V := by
    exact path_vertices_in_image (S := S) (S_hat := S_hat) P₁ ι H H₁ f g hfg_inv hgf_inv hH₁_V
      Δ_hat B₁ hB₁_range P hL_P₁ hP_V hQ_hat_V
  have hP_U : P.U = L := by
    exact augmented_path_avoids_drawing_except_vertices (S := S) (S_hat := S_hat) P₁ ι H H₁ f g
      hf_cont hg_cont hgf_inv hg_inj hH₁_V u' v' Δ_hat hΔ_hat_inter_U B₁ hB₁_line hB₁_range
      hΔ_hat_U_eq L rfl hL_P₁ hL_U hL_cl hB₁_cl hP_V hQ_hat_V hP_V_img
  have hP_path : P.IsPathBetween u v := by
    rw [← hgu', ← hgv']
    exact isPathBetween_of_image hRange_comp hg_cont
      (hf_cont.mono (hg_maps.image_subset))
      hgf_inv (hΔ_hat_U_eq ▸ hB₁_range)
      (hP_U.trans (congr_arg (image g) hΔ_hat_U_eq.symm)) hP_V_img hPath_hat
  have hPX_card : (P.V ∩ X).ncard ≤ 2 := by
    exact path_cut_size_le (S := S) (S_hat := S_hat) P₁ P₂ ι H H₁ X hCap hX p₀ g hgf_inv hf_inj
      F_hat hF_hat_card Δ_hat hX_hat B₁ hB₁_range hB₁_sub_Δ P hP_V
  exact ⟨hP_U, hP_path, hPX_card⟩

private theorem arc_ends_lie_on_same_interface
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (H : Drawing S)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hInterU : P₁ ∩ P₂ ⊆ H.U)
    (hCond1 : ∀ r ∈ H.R, r ⊆ P₁ → ∀ (i j : Fin t), (closure r ∩ C i).Nonempty → (closure r ∩ C
      j).Nonempty → i = j)
    (hP₁_cl : IsClosed P₁)
    (hfrP₁ : frontier P₁ ⊆ P₁ ∩ P₂)
    (u : S)
    (v : S)
    (hu12 : u ∈ P₁ ∩ P₂)
    (hv12 : v ∈ P₁ ∩ P₂)
    (F₁ : Set S)
    (hF₁_line : IsLineWithEnds F₁ u v)
    (hF₁_P₁ : F₁ ⊆ P₁)
    (huF₁ : u ∈ F₁)
    (hvF₁ : v ∈ F₁)
    (hF₁_U : F₁ ∩ H.U = {u, v}) :
    ∃ i, u ∈ C i ∧ v ∈ C i := by
  obtain ⟨w₁, hw₁⟩ := (GM11.isPathConnected_sdiff_pair hF₁_line).nonempty
  have hw₁_not_U : w₁ ∉ H.U := fun h => hw₁.2 (hF₁_U ▸ ⟨hw₁.1, h⟩)
  obtain ⟨r₁, hr₁, hw₁_r₁⟩ := GM11.exists_region_of_notMem hw₁_not_U
  have hF₁_diff_U : Disjoint (F₁ \ {u, v}) H.U :=
    disjoint_left.mpr fun z hz hzU => hz.2 (hF₁_U ▸ ⟨hz.1, hzU⟩)
  have hF₁_diff_r₁ : F₁ \ {u, v} ⊆ r₁ :=
    GM11.subset_region hr₁ (GM11.isPathConnected_sdiff_pair hF₁_line).isConnected.isPreconnected
      hF₁_diff_U hw₁ hw₁_r₁
  have hF₁_cl_r₁ : F₁ ⊆ closure r₁ :=
    (GM11.closure_sdiff_pair hF₁_line).symm.subset.trans (closure_mono hF₁_diff_r₁)
  have hr₁_P₁ : r₁ ⊆ P₁ := by
    have hdis_r₁ : Disjoint r₁ (frontier P₁) :=
      disjoint_left.mpr fun z hzr₁ hzfr => GM11.region_subset hr₁ hzr₁ (hInterU (hfrP₁ hzfr))
    exact GM14.subset_of_disjoint_frontier (GM11.region_isPreconnected hr₁) hP₁_cl
      hdis_r₁ hw₁_r₁ (hF₁_P₁ hw₁.1)
  obtain ⟨i, hu_Ci⟩ := mem_iUnion.mp (hSplit.inter ▸ hu12)
  obtain ⟨j, hv_Cj⟩ := mem_iUnion.mp (hSplit.inter ▸ hv12)
  have hij : i = j :=
    hCond1 r₁ hr₁ hr₁_P₁ i j ⟨u, hF₁_cl_r₁ huF₁, hu_Ci⟩ ⟨v, hF₁_cl_r₁ hvF₁, hv_Cj⟩
  have hv_Ci : v ∈ C i := hij ▸ hv_Cj
  exact ⟨i, hu_Ci, hv_Ci⟩

private theorem frontier_first_side_is_on_interface
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hP₁_cl : IsClosed P₁)
    (hP₂_cl : IsClosed P₂) :
    frontier P₁ ⊆ P₁ ∩ P₂ := by
  rintro z ⟨hz₁, hz₂⟩
  refine ⟨hP₁_cl.closure_eq ▸ hz₁, by_contra fun hzP₂ => hz₂ ?_⟩
  exact interior_maximal (fun w hw => (eq_univ_iff_forall.mp hSplit.union w).resolve_right hw)
    hP₂_cl.isOpen_compl hzP₂

private theorem frontier_second_side_is_on_interface
    {S : Type w}
    [TopologicalSpace S]
    {S_hat : Type w}
    [TopologicalSpace S_hat]
    {t : ℕ}
    (C : Fin t → Set S)
    (P₁ : Set S)
    (P₂ : Set S)
    (ι : ↑P₁ → S_hat)
    (D : Fin t → Set S_hat)
    (hSplit : GM12.IsCappedSplit C P₁ P₂ ι D)
    (hP₁_cl : IsClosed P₁)
    (hP₂_cl : IsClosed P₂) :
    frontier P₂ ⊆ P₁ ∩ P₂ := by
  rintro z ⟨hz₁, hz₂⟩
  refine ⟨by_contra fun hzP₁ => hz₂ ?_, hP₂_cl.closure_eq ▸ hz₁⟩
  exact interior_maximal (fun w hw => (eq_univ_iff_forall.mp hSplit.union w).resolve_left hw)
    hP₁_cl.isOpen_compl hzP₁

private theorem arc_inter_drawing_at_ends {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {F L : Set S} {u v : S} (hFU : F ∩ H.U = {u, v})
    (hLF : L ⊆ F) (huL : u ∈ L) (hvL : v ∈ L) (huU : u ∈ H.U) (hvU : v ∈ H.U) :
    L ∩ H.U = {u, v} := by
  refine Subset.antisymm ((inter_subset_inter_left _ hLF).trans hFU.subset) ?_
  rintro z (rfl | rfl)
  · exact ⟨huL, huU⟩
  · exact ⟨hvL, hvU⟩

/-- **Graph Minors XV, (3.2)** (pages 119–120):
Gluing lemma for rigidity of a drawing `H` across a decomposition `Σ = Σ₁ ∪ Σ₂`. -/
theorem theorem_3_2_proof : GM15Theorem32Statement.{w} := by
  intro S _ _ S_hat _ _ t C P₁ P₂ ι D H H₁ X
    hSplit hCap hInterU hX hCond1 hCond2 hCond3 hCond4 F hF hFU hFV
  have hS : IsClosedSurface S := hSplit.surface.1
  have hS_hat : IsClosedSurface S_hat := hSplit.surface_hat
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : LocallyConnectedSpace S_hat := IsClosedSurface.locallyConnectedSpace hS_hat
  have : CompactSpace P₁ := hSplit.manifold₁.1
  have : CompactSpace P₂ := hSplit.manifold₂.1
  have hP₁_comp : IsCompact P₁ := isCompact_iff_compactSpace.mpr inferInstance
  have hP₂_comp : IsCompact P₂ := isCompact_iff_compactSpace.mpr inferInstance
  have hP₁_cl : IsClosed P₁ := hP₁_comp.isClosed
  have hP₂_cl : IsClosed P₂ := hP₂_comp.isClosed
  have hRange_comp : IsCompact (range ι) := isCompact_range hSplit.isEmbedding.continuous
  have hRange_cl : IsClosed (range ι) := hRange_comp.isClosed
  by_cases hF₂ : F ⊆ P₂
  · obtain ⟨Δ, _, hDial⟩ := hCond3 F hF₂ hF hFU hFV
    exact ⟨Δ, hDial⟩
  obtain ⟨x₁, hx₁F, hx₁_not_P₂⟩ := not_subset.mp hF₂
  have hx₁P₁ : x₁ ∈ P₁ := (eq_univ_iff_forall.mp hSplit.union x₁).resolve_right hx₁_not_P₂
  let p₀ : P₁ := ⟨x₁, hx₁P₁⟩
  let f : S → S_hat := cappedFwd P₁ ι p₀
  let g : S_hat → S := cappedInv P₁ ι hSplit.isEmbedding p₀
  have hf_cont : ContinuousOn f P₁ := continuousOn_cappedFwd hSplit.isEmbedding p₀
  have hg_cont : ContinuousOn g (range ι) := continuousOn_cappedInv hSplit.isEmbedding p₀
  have hfg_inv : LeftInvOn g f P₁ := leftInvOn_cappedInv
  have hgf_inv : LeftInvOn f g (range ι) := leftInvOn_cappedFwd
  have hf_maps : MapsTo f P₁ (range ι) := mapsTo_cappedFwd
  have hg_maps : MapsTo g (range ι) P₁ := mapsTo_cappedInv
  have hf_inj : InjOn f P₁ := hfg_inv.injOn
  have hg_inj : InjOn g (range ι) := hgf_inv.injOn
  have hH₁_U : H₁.U = f '' (H.U ∩ P₁) :=
    hCap.1.trans (cappedFwd_image_inter_P₁ H.U).symm
  have hH₁_V : H₁.V = f '' (H.V ∩ P₁) :=
    hCap.2.trans (cappedFwd_image_inter_P₁ H.V).symm
  have hH₁_U_sub : H₁.U ⊆ range ι :=
    hH₁_U ▸ (hf_maps.mono inter_subset_right Subset.rfl).image_subset
  have hH₁_V_sub : H₁.V ⊆ range ι := H₁.V_subset_U.trans hH₁_U_sub
  have hCi_sub : ∀ i, C i ⊆ P₁ ∩ P₂ := fun i => hSplit.inter.symm ▸ subset_iUnion C i
  have hCi_P₁ : ∀ i, C i ⊆ P₁ := fun i => (hCi_sub i).trans inter_subset_left
  have hCi_U : ∀ i, C i ⊆ H.U := fun i => (hCi_sub i).trans hInterU
  have hDi_bd : ∀ i, subBd (D i) = f '' C i := fun i =>
    (hSplit.bounds i).trans (cappedFwd_image_eq_of_subset (hCi_P₁ i)).symm
  have hDi_bd_range : ∀ i, subBd (D i) ⊆ range ι := fun i =>
    hDi_bd i ▸ (hf_maps.mono (hCi_P₁ i) Subset.rfl).image_subset
  have hDi_bd_U : ∀ i, subBd (D i) ⊆ H₁.U := fun i => by
    rw [hDi_bd i, hH₁_U]
    exact image_mono (subset_inter (hCi_U i) (hCi_P₁ i))
  have hDi_bd_oArc : ∀ i, IsOArc (subBd (D i)) := fun i => by
    rw [hDi_bd i]
    exact (hSplit.isOArc i).image (hf_cont.mono (hCi_P₁ i))
      (hg_cont.mono (hDi_bd i ▸ hDi_bd_range i)) (hfg_inv.mono (hCi_P₁ i))
  have hDi_disj_range : ∀ i, Disjoint (D i) (range ι) := fun i =>
    disjoint_compl_left.mono_left (hSplit.compl ▸ subset_iUnion D i)
  have hDi_disj_U : ∀ i, Disjoint (D i) H₁.U := fun i =>
    (hDi_disj_range i).mono_right hH₁_U_sub
  have hDisc_sub_range : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → subBd Δ_hat ⊆ range ι →
      (∀ i : Fin t, ¬ (subBd (D i) ⊆ Δ_hat ∩ H₁.U)) → Δ_hat ⊆ range ι := by
    exact capped_disc_without_cap_lies_in_range (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D H₁
      hSplit hDi_bd_U hDi_disj_range
  have hPullback_disc : ∀ {Δ_hat : Set S_hat}, IsClosedDisc Δ_hat → Δ_hat ⊆ range ι →
      IsClosedDisc (g '' Δ_hat) ∧ subBd (g '' Δ_hat) = g '' subBd Δ_hat ∧ g '' Δ_hat ⊆ P₁ := by
    exact disc_in_capped_drawing_pulls_back (S := S) (S_hat := S_hat) P₁ ι hS hS_hat f g hf_cont
      hg_cont hgf_inv hg_maps
  by_cases hF₁ : F ⊆ P₁
  · exact fitting_first_side_disc (S := S) (S_hat := S_hat) (t := t) P₁ ι D H H₁ X hCond2 F hF hFU
      hFV hRange_comp f g hf_cont hg_cont hfg_inv hgf_inv hf_maps hg_maps hf_inj hg_inj hH₁_U
      hH₁_V hH₁_U_sub hH₁_V_sub hDi_bd_oArc hDisc_sub_range hPullback_disc hF₁
  -- Case 3: `F` meets both `P₁ \ P₂` and `P₂ \ P₁`.
  have hfrP₁ : frontier P₁ ⊆ P₁ ∩ P₂ := by
    exact frontier_first_side_is_on_interface (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D
      hSplit hP₁_cl hP₂_cl
  have hfrP₂ : frontier P₂ ⊆ P₁ ∩ P₂ := by
    exact frontier_second_side_is_on_interface (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D
      hSplit hP₁_cl hP₂_cl
  have hCut : ∃ u v : S, u ≠ v ∧ u ∈ F ∧ v ∈ F ∧ u ∈ H.V ∧ v ∈ H.V ∧
      u ∈ P₁ ∩ P₂ ∧ v ∈ P₁ ∩ P₂ ∧ F ∩ H.V = {u, v} ∧
      F ∩ H.U = {u, v} ∧ F ∩ (P₁ ∩ P₂) = {u, v} := by
    exact crossing_boundary_has_two_interface_points (S := S) (S_hat := S_hat) (t := t)
      C P₁ P₂ ι D H hSplit hInterU F hF hFU hFV hP₁_cl x₁ hx₁F hx₁_not_P₂ hx₁P₁ hF₁ hfrP₁
  obtain ⟨u, v, huv, huF, hvF, huV, hvV, hu12, hv12, hFV_eq, hFU_eq, hF12_eq⟩ := hCut
  obtain ⟨F₁_0, F₂_0, hF₁_0, hF₂_0, hF_0_union, hF_0_inter⟩ := hF.lines huF hvF huv
  have hArc_side : ∀ {L : Set S}, IsLineWithEnds L u v → L ⊆ F → L ⊆ P₁ ∨ L ⊆ P₂ := by
    exact boundary_arc_lies_on_one_side (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D hSplit F
      hP₁_cl hP₂_cl hfrP₁ hfrP₂ u v hF12_eq
  have hSplit_F : ∃ F₁ F₂ : Set S,
      IsLineWithEnds F₁ u v ∧ IsLineWithEnds F₂ u v ∧
      F₁ ∪ F₂ = F ∧ F₁ ∩ F₂ = {u, v} ∧ F₁ ⊆ P₁ ∧ F₂ ⊆ P₂ := by
    exact split_circle_at_two_boundary_points (S := S) P₁ P₂ F hF₂ hF₁ u v F₁_0 F₂_0 hF₁_0 hF₂_0
      hF_0_union hF_0_inter hArc_side
  obtain ⟨F₁, F₂, hF₁_line, hF₂_line, hF_union, hF_inter, hF₁_P₁, hF₂_P₂⟩ := hSplit_F
  obtain ⟨huF₁, hvF₁⟩ := ends_mem_of_isLineWithEnds hF₁_line
  obtain ⟨huF₂, hvF₂⟩ := ends_mem_of_isLineWithEnds hF₂_line
  have hF₁_U := arc_inter_drawing_at_ends (H := H) hFU_eq
    (hF_union ▸ subset_union_left) huF₁ hvF₁ (H.V_subset_U huV) (H.V_subset_U hvV)
  have hF₂_U := arc_inter_drawing_at_ends (H := H) hFU_eq
    (hF_union ▸ subset_union_right) huF₂ hvF₂ (H.V_subset_U huV) (H.V_subset_U hvV)
  -- Find the region `r₁ ⊆ P₁` containing `F₁ \ {u, v}`, and deduce `u, v ∈ C i` for some `i`.
  have hEndsOnSameInterface : ∃ i, u ∈ C i ∧ v ∈ C i := by
    exact arc_ends_lie_on_same_interface (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D H hSplit
      hInterU hCond1 hP₁_cl hfrP₁ u v hu12 hv12 F₁ hF₁_line hF₁_P₁ huF₁ hvF₁ hF₁_U
  obtain ⟨i, hu_Ci, hv_Ci⟩ := hEndsOnSameInterface
  -- Map `F₁, u, v` to `S_hat` and add a chord `L_D` across `D i`.
  let u' : S_hat := f u
  let v' : S_hat := f v
  let F₁' : Set S_hat := f '' F₁
  have hu'_bd : u' ∈ subBd (D i) := hDi_bd i ▸ mem_image_of_mem f hu_Ci
  have hv'_bd : v' ∈ subBd (D i) := hDi_bd i ▸ mem_image_of_mem f hv_Ci
  have hu'_V : u' ∈ H₁.V := hH₁_V ▸ mem_image_of_mem f ⟨huV, hu12.1⟩
  have hv'_V : v' ∈ H₁.V := hH₁_V ▸ mem_image_of_mem f ⟨hvV, hv12.1⟩
  have hu'v' : u' ≠ v' := fun h => huv (hf_inj hu12.1 hv12.1 h)
  have hF₁'_range : F₁' ⊆ range ι := (hf_maps.mono hF₁_P₁ Subset.rfl).image_subset
  have hF₁'_line : IsLineWithEnds F₁' u' v' :=
    isLineWithEnds_image hF₁_line (hf_cont.mono hF₁_P₁) (hg_cont.mono hF₁'_range)
      (hfg_inv.mono hF₁_P₁)
  have hF₁'_U : F₁' ∩ H₁.U = {u', v'} := by
    rw [hH₁_U, ← hf_inj.image_inter hF₁_P₁ inter_subset_right]
    have h1 : F₁ ∩ (H.U ∩ P₁) = {u, v} := by
      rw [← Set.inter_assoc, hF₁_U]
      exact inter_eq_left.mpr (by rintro z (rfl | rfl); exacts [hu12.1, hv12.1])
    rw [h1]
    simp [u', v', image_insert_eq]
  have hCapArc : ∃ L_D : Set S_hat, IsLineWithEnds L_D u' v' ∧ L_D \ {u', v'} ⊆ D i ∧
      F₁' ∩ L_D = {u', v'} ∧ IsOArc (F₁' ∪ L_D) ∧
      L_D ∩ H₁.U = {u', v'} ∧ (F₁' ∪ L_D) ∩ H₁.U = {u', v'} ∧
      (F₁' ∪ L_D) ∩ H₁.V = {u', v'} := by
    exact cap_boundary_arc_closes_curve (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι D H₁ hSplit
      hS_hat hDi_bd_U hDi_bd_oArc hDi_disj_range hDi_disj_U i u' v' F₁' hu'_bd hv'_bd hu'_V hv'_V
      hu'v' hF₁'_range hF₁'_line hF₁'_U
  obtain ⟨L_D, hL_D_line, hL_D_sub, hF₁'_L_D_inter, hF_hat_oArc, hL_D_U, hF_hat_U, hF_hat_V⟩ :=
    hCapArc
  obtain ⟨hu'F₁', hv'F₁'⟩ := ends_mem_of_isLineWithEnds hF₁'_line
  obtain ⟨hu'L_D, hv'L_D⟩ := ends_mem_of_isLineWithEnds hL_D_line
  let F_hat : Set S_hat := F₁' ∪ L_D
  have hF_hat_UV : F_hat ∩ H₁.U ⊆ H₁.V := by
    rw [hF_hat_U]
    rintro y (rfl | rfl) <;> assumption
  have hF_hat_card : (F_hat ∩ H₁.V).ncard ≤ 2 := by
    rw [hF_hat_V, Set.ncard_pair hu'v']
  obtain ⟨Δ_hat, hDial_hat, hX_hat⟩ := hCond2 F_hat hF_hat_oArc hF_hat_UV hF_hat_card
  have hΔ_hat_disc : IsClosedDisc Δ_hat := hDial_hat.1
  have hΔ_hat_bd : subBd Δ_hat = F_hat := hDial_hat.2.1
  have hΔ_hat_inter_U : (H₁.interSet Δ_hat).U = H₁.U ∩ Δ_hat :=
    (GM14.interSet_V_and_U hΔ_hat_disc.isClosed (hΔ_hat_bd ▸ hF_hat_UV)).2
  have hF_hat_sub_Δ : F_hat ⊆ Δ_hat := by
    intro y hy
    exact hΔ_hat_disc.isClosed.closure_eq ▸ (hΔ_hat_bd.symm ▸ hy).1
  -- Show that `Δ_hat \ F_hat` meets `subBd (D i)` at some point `z₀ ∉ F_hat`.
  have hCappedBoundaryPath : ∃ B₁ : Set S_hat, IsLineWithEnds B₁ u' v' ∧ B₁ ⊆ subBd (D i) ∧
      B₁ ⊆ Δ_hat ∧ (H₁.interSet Δ_hat).IsPathBetween u' v' ∧
        (H₁.interSet Δ_hat).U = B₁ := by
    exact capped_disc_contains_spanning_boundary_path (S := S) (S_hat := S_hat) (t := t) C P₁ P₂ ι
      D H₁ hSplit hS_hat hDi_bd_U hDi_bd_oArc hDi_disj_range i u' v' F₁' hu'_bd
      hv'_bd hu'v' hF₁'_range hF₁'_line hF₁'_U L_D hL_D_line hL_D_sub hu'F₁' hv'F₁' hF_hat_U
      hF_hat_V Δ_hat hDial_hat hΔ_hat_disc hΔ_hat_bd hΔ_hat_inter_U hF_hat_sub_Δ
  obtain ⟨B₁, hB₁_line, hB₁_bd, hB₁_sub_Δ, hPath_hat, hΔ_hat_U_eq⟩ := hCappedBoundaryPath
  obtain ⟨hu'B₁, hv'B₁⟩ := ends_mem_of_isLineWithEnds hB₁_line
  have hB₁_U : B₁ ⊆ H₁.U := hB₁_bd.trans (hDi_bd_U i)
  have hB₁_range : B₁ ⊆ range ι := hB₁_bd.trans (hDi_bd_range i)
  have hCapSubdisc : ∃ Δ_hat₁ : Set S_hat, F₁' ∩ B₁ = {u', v'} ∧
      IsClosedDisc Δ_hat₁ ∧ subBd Δ_hat₁ = F₁' ∪ B₁ ∧ Δ_hat₁ ∩ H₁.U = B₁ ∧ Δ_hat₁ ⊆ range ι := by
    exact capped_boundary_path_spans_subdisc (S := S) (S_hat := S_hat) (t := t) P₁ ι D H₁ hS_hat
      hDi_bd_oArc hDisc_sub_range u' v' F₁' hF₁'_range hF₁'_line hF₁'_U hu'F₁' hv'F₁'
      Δ_hat hΔ_hat_disc hΔ_hat_inter_U (subset_union_left.trans hF_hat_sub_Δ) B₁ hB₁_line hB₁_sub_Δ
      hΔ_hat_U_eq hu'B₁ hv'B₁ hB₁_U hB₁_range
  obtain ⟨Δ_hat₁, hF₁'_B₁_inter, hΔ_hat₁_disc, hΔ_hat₁_bd, hΔ_hat₁_U, hΔ_hat₁_range⟩ :=
    hCapSubdisc
  obtain ⟨hΔ₁_disc, hΔ₁_bd_img, hΔ₁_P₁⟩ := hPullback_disc hΔ_hat₁_disc hΔ_hat₁_range
  let Δ₁ : Set S := g '' Δ_hat₁
  let L : Set S := g '' B₁
  let P : Drawing S := H.interSet L
  have hL_Ci : L ⊆ C i := by
    have h1 : g '' subBd (D i) = C i := by
      rw [hDi_bd i]
      exact (hfg_inv.mono (hCi_P₁ i)).image_image
    rw [← h1]
    exact image_mono hB₁_bd
  have hL_12 : L ⊆ P₁ ∩ P₂ := hL_Ci.trans (hCi_sub i)
  have hL_P₁ : L ⊆ P₁ := hL_12.trans inter_subset_left
  have hL_U : L ⊆ H.U := hL_12.trans hInterU
  have hgu' : g u' = u := hfg_inv hu12.1
  have hgv' : g v' = v := hfg_inv hv12.1
  have hL_line : IsLineWithEnds L u v := by
    rw [← hgu', ← hgv']
    exact isLineWithEnds_image hB₁_line (hg_cont.mono hB₁_range)
      (hf_cont.mono hL_P₁) (hgf_inv.mono hB₁_range)
  have hL_cl : IsClosed L := (isCompact_of_isLineWithEnds hL_line).isClosed
  have hB₁_cl : IsClosed B₁ := (isCompact_of_isLineWithEnds hB₁_line).isClosed
  have hP_V : P.V = H.V ∩ L := interSet_V_of_isClosed H hL_cl
  have hP_sub : P.IsSubdrawing (H.interSet (P₁ ∩ P₂)) :=
    interSet_isSubdrawing_of_isClosed H hL_cl (hP₁_cl.inter hP₂_cl) hL_12
  have hLiftedPath : P.U = L ∧ P.IsPathBetween u v ∧ (P.V ∩ X).ncard ≤ 2 := by
    exact boundary_path_pulls_back_with_bounded_cut (S := S) (S_hat := S_hat) P₁ P₂ ι H H₁ X hCap
      hX hRange_comp p₀ g hf_cont hg_cont hfg_inv hgf_inv hg_maps hf_inj hg_inj hH₁_V u v u' v'
      F_hat hF_hat_card Δ_hat hX_hat hΔ_hat_disc hΔ_hat_inter_U B₁ hB₁_line hB₁_sub_Δ hPath_hat
      hΔ_hat_U_eq hB₁_range hL_P₁ hL_U hgu' hgv' hL_cl hB₁_cl hP_V
  obtain ⟨hP_U, hP_path, hPX_card⟩ := hLiftedPath
  -- Apply Condition (iv) to `F₂, u, v, P`.
  have hJoinedSides : ∃ Δ, IsDial H F Δ := by
    exact glue_discs_across_boundary_path (S := S) (S_hat := S_hat) P₁ P₂ ι H H₁ X hInterU hCond4
      F hFU hS hP₂_cl f g hfg_inv hgf_inv hH₁_U u v huv huV hvV hu12 hv12 hFV_eq F₁ F₂ hF₂_line
      hF_union hF₁_P₁ hF₂_P₂ huF₁ hvF₁ huF₂ hvF₂ hF₁_U hF₂_U u' v' B₁ hu'B₁ hv'B₁ Δ_hat₁
      hΔ_hat₁_bd hΔ_hat₁_U hΔ_hat₁_range hΔ₁_disc hΔ₁_bd_img hΔ₁_P₁ P hL_U hgu' hgv' hL_line hP_V
      hP_sub hP_U hP_path hPX_card
  exact hJoinedSides

/-- Statement of Graph Minors XV, (3.3) (pages 120–121):
"Let $\Sigma$ be a surface and let $\phi \ge 3$ be an integer. Let $\mathscr{T}^*$ be a
tangle in a graph $G$, and let $H, \eta, \mathscr{T}$ be a $\Sigma$-span. Let $\Lambda
\subseteq \Sigma$ be a region of $H$ such that $H \cap bd(\Lambda)$ is a circuit, and let
$a_1, \dots, a_\phi, b_1, \dots, b_\phi$ be distinct vertices of this circuit, in order,
such that $\{a_1, \dots, a_\phi, b_1, \dots, b_\phi\}$ is free with respect to
$\mathscr{T}$. For $1 \le i \le \phi$ let $P_i$ be an $\eta(H)$-path with ends $\eta(a_i),
\eta(b_i)$, such that* ... *$P_1, \dots, P_\phi$ are mutually disjoint. Then there is a
$\Sigma'$-span of order $\phi$, where $\Sigma'$ is the surface obtained by adding a crosscap
to $\Sigma$." -/
def GM15Theorem33Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ φ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ : Set S) (P : Fin φ → Graph α β) (a b : Fin φ → S),
    IsSigmaSpan G H η θ_star θ T_star T →
    Λ ∈ H.R → IsOArc (subBd Λ) → (H.interSet (subBd Λ)).IsCircuit →
    3 ≤ φ → φ ≤ θ →
    ((List.ofFn a ++ List.ofFn b).Nodup) →
    GM12.IsListedInOrderOn (subBd Λ) (List.ofFn a ++ List.ofFn b) →
    (∀ i : Fin φ, a i ∈ H.V ∩ subBd Λ ∧ b i ∈ H.V ∩ subBd Λ) →
    (∀ i : Fin φ, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i))) →
    Pairwise (fun i j => Disjoint V(P i) V(P j)) →
    IsFreeSet H.toHypergraph T θ (range a ∪ range b) →
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingCrosscap S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T'

/-- **Graph Minors XV, (3.3), Claim (2)** (page 121):
"Every $X \subseteq \{a_1, \dots, a_\phi, b_1, \dots, b_\phi\}$ with $|X| \le \phi$ is free
with respect to $\mathscr{T}_1$." -/
theorem theorem_3_3_claim_2 {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {θ φ : ℕ} {Y X : Set S}
    (hT : IsTangle H.toHypergraph θ T)
    (hFree : IsFreeSet H.toHypergraph T θ Y)
    (hXY : X ⊆ Y) (hX : X.ncard ≤ φ) :
    IsFreeSet H.toHypergraph (GM10.truncation T φ) φ X := by
  have hFreeX : IsFreeSet H.toHypergraph T θ X := hFree.subset hT hXY
  exact ⟨hFreeX.1, hX, fun _ _ hAB hXA => hFreeX.2.2 hAB.1 hXA⟩

/-- **Graph Minors XV, (3.3), Claim (3)** (page 121):
"For every $O$-arc $F \subseteq \Sigma$ with $F \cap U(H') \subseteq V(H')$ and $|F \cap
V(H')| \le 2$, there is a dial $\Delta \subseteq \Sigma$ for $F, H' \cap \Sigma_1$ with $|X
\cap \Delta| \le |F \cap V(H')|$." -/
theorem theorem_3_3_claim_3 {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {θ : ℕ} {X F : Set S}
    (hRigid : IsRigid H)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hFree : IsFreeSet H.toHypergraph T θ X)
    (hF : IsOArc F) (hFU : F ∩ H.U ⊆ H.V) (hFV : (F ∩ H.V).ncard ≤ 2) :
    ∃ Δ : Set S, IsDial H F Δ ∧ (X ∩ Δ).ncard ≤ (F ∩ H.V).ncard := by
  obtain ⟨Δ, hDial⟩ := hRigid F hF hFU hFV
  have hMemT :
      ((H.interSet Δ).toHypergraph, (H.interSet (closure (univ \ Δ))).toHypergraph) ∈ T :=
    (theorem_3_1_proof H θ T Δ hS inferInstance hRigid hT hθ hDial.1
      (hDial.2.1 ▸ hFU) (hDial.2.1 ▸ hFV)).mpr (hDial.2.1.symm ▸ hDial)
  obtain ⟨_, hOrd⟩ := isSeparation_interSet_of_isClosed H hDial.1.isClosed (hDial.2.1 ▸ hFU)
  have hFree_sub : IsFreeSet H.toHypergraph T θ (X ∩ Δ) :=
    hFree.subset hT inter_subset_left
  have hSubA : X ∩ Δ ⊆ (H.interSet Δ).toHypergraph.vertexSet := by
    change X ∩ Δ ⊆ (H.interSet Δ).V
    rw [interSet_V_of_isClosed H hDial.1.isClosed]
    exact inter_subset_inter_left Δ hFree.1
  have hLe : (X ∩ Δ).ncard ≤ separationOrder (H.interSet Δ).toHypergraph
      (H.interSet (closure (univ \ Δ))).toHypergraph :=
    hFree_sub.2.2 hMemT hSubA
  exact ⟨Δ, hDial, hDial.2.1 ▸ hOrd ▸ hLe⟩

/-- Graph Minors XV, (3.4) (page 122), with auxiliary conclusions.

"Let $\Sigma$ be a surface and let $k \ge 3$ be an integer. Let $\mathscr{T}^*$ be a tangle
in a graph $G$, and let $H, \mathscr{T}$ be a $\Sigma$-span of order $\theta$. Let $\Lambda
\subseteq \Sigma$ be a region of $H$ such that $H \cap bd(\Lambda)$ is a circuit, and let
$v_1, \dots, v_{2k}$ be distinct vertices of this circuit, in order, such that $\{v_1,
\dots, v_{2k}\}$ is free with respect to $\mathscr{T}$. Let $H' \subseteq G$ be a drawing in
$\Sigma$ such that $H' \cap (\Sigma - \Lambda) = H$ and $H' = H \cup P_1 \cup \dots \cup
P_{k-1}$, where $P_i$ is a path with ends $v_i, v_{2k-i}$ for $1 \le i \le k - 1$. Let
$\mathscr{T}'$ be a tangle in $H'$ induced by $\mathscr{T}$; then $H', \mathscr{T}'$ is a
$\Sigma$-span of order $\theta$. Moreover, let $r_1, r_2 \subseteq \Lambda$ be the regions
of $H'$ incident with $v_k, v_{2k}$ respectively; then $d'(r_1, r_2) \ge 2k - 6$, and
$d'(v_k, v_{2k}) \ge 2k - 8$, where $d'$ is the metric of $\mathscr{T}'."

Here "$H' \subseteq G$" means that the span embedding `η'` of $H'$ agrees with `η` on $H$. The
printed statement is false unless each $P_i$ meets $H$ only in its ends and the paths are disjoint
(see the correction to (3.4) in `corrections/GM15.md`), so we add these two hypotheses. The proof
uses both ("the disjoint paths $P_1, \dots, P_{k-1}$"), and so do the uses in Section 7.

The formal statement also identifies the old drawing outside $\Lambda$ and the induced tangle,
gives monotonicity of distance on atoms of $H$, and describes each new region boundary as a circuit
drawn on an $O$-arc. It records membership and cyclic order of specified sets of four vertices on
these boundaries. Section 7 uses the boundary conclusions. -/
def GM15Theorem34Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ k : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (Λ : Set S) (v : Fin (2 * k) → S) (H' : Drawing S) (η' : SpanEmbedding H' G)
    (P : Fin (k - 1) → Drawing S) (i_k i_last : Fin (2 * k)),
    IsSigmaSpan G H η θ_star θ T_star T →
    HasTangleMetric H θ T d →
    Λ ∈ H.R → IsOArc (subBd Λ) → (H.interSet (subBd Λ)).IsCircuit →
    3 ≤ k →
    (List.ofFn v).Nodup →
    GM12.IsListedInOrderOn (subBd Λ) (List.ofFn v) →
    (∀ i : Fin (2 * k), v i ∈ H.V ∩ subBd Λ) →
    IsFreeSet H.toHypergraph T θ (range v) →
    (∀ x ∈ H.V, η'.vMap x = η.vMap x) → (∀ e ∈ H.E, η'.eMap e = η.eMap e) →
    H'.interSet (univ \ Λ) = H →
    H'.V = H.V ∪ ⋃ j : Fin (k - 1), (P j).V →
    H'.E = H.E ∪ ⋃ j : Fin (k - 1), (P j).E →
    (∀ j : Fin (k - 1),
      (P j).IsPathBetween (v ⟨j.1, by omega⟩) (v ⟨2 * k - 2 - j.1, by omega⟩)) →
    (∀ j : Fin (k - 1), (P j).U ∩ H.U = {v ⟨j.1, by omega⟩, v ⟨2 * k - 2 - j.1, by omega⟩}) →
    Pairwise (fun j₁ j₂ => Disjoint (P j₁).U (P j₂).U) →
    i_k.1 = k - 1 → i_last.1 = 2 * k - 1 →
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r₁ r₂ : Set S),
      IsSigmaSpan G H' η' θ_star θ T_star T' ∧
      HasTangleMetric H' θ T' d' ∧
      r₁ ∈ H'.R ∧ r₂ ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧
      H'.U \ Λ = H.U ∧
      T' = GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧
      (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) ∧
      IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧
      (H'.interSet (subBd r₁)).IsCircuit ∧ (H'.interSet (subBd r₂)).IsCircuit ∧
      v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧
      (∀ w₁ w₂ w₃ w₄ : S,
        w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ →
        w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
          List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
            List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
        w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
        w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧
      (∀ u₁ u₂ u₃ u₄ : S,
        u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ →
        u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
        u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧
        u₃ ∈ (H'.interSet (subBd r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) ∧
      2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last}

/-- Graph Minors XV, (3.4) (page 122), with the auxiliary conclusions of
`GM15Theorem34Statement`, applied to a constructed drawing $H'$. Given paths
$P_1, \dots, P_{k-1}$ of $G$ that meet $\eta(H)$ only in their ends, there is a drawing
$H' = H \cup P_1 \cup \dots \cup P_{k-1}$ in $\Sigma$ with the paths drawn across $\Lambda$, and
(3.4) applies to it. This is the form used in Section 7; it is proved from
`GM15Theorem34Statement` in `GraphMinor/GM15/Section3Given.lean`. -/
def GM15Theorem34DrawnStatement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ k : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (Λ : Set S) (v : Fin (2 * k) → S) (P : Fin (k - 1) → Graph α β)
    (i_k i_last : Fin (2 * k)),
    IsSigmaSpan G H η θ_star θ T_star T →
    HasTangleMetric H θ T d →
    Λ ∈ H.R → IsOArc (subBd Λ) → (H.interSet (subBd Λ)).IsCircuit →
    3 ≤ k →
    (List.ofFn v).Nodup →
    GM12.IsListedInOrderOn (subBd Λ) (List.ofFn v) →
    (∀ i : Fin (2 * k), v i ∈ H.V ∩ subBd Λ) →
    IsFreeSet H.toHypergraph T θ (range v) →
    (∀ j : Fin (k - 1), ∃ i₁ i₂ : Fin (2 * k),
      i₁.1 = j.1 ∧ i₂.1 = 2 * k - 2 - j.1 ∧
      IsHPathWithEnds G η.imageGraph (P j) (η.vMap (v i₁)) (η.vMap (v i₂))) →
    Pairwise (fun j₁ j₂ => Disjoint V(P j₁) V(P j₂)) →
    i_k.1 = k - 1 → i_last.1 = 2 * k - 1 →
    ∃ (H' : Drawing S) (η' : SpanEmbedding H' G)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r₁ r₂ : Set S),
      IsSigmaSpan G H' η' θ_star θ T_star T' ∧
      HasTangleMetric H' θ T' d' ∧
      r₁ ∈ H'.R ∧ r₂ ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧
      H'.interSet (univ \ Λ) = H ∧
      H'.U \ Λ = H.U ∧
      H.IsSubdrawing H' ∧
      (∀ x ∈ H.V, η'.vMap x = η.vMap x) ∧
      (∀ e ∈ H.E, η'.eMap e = η.eMap e) ∧
      η'.imageGraph = subgraphUnion G η.imageGraph (subgraphSUnion G (range P)) ∧
      T' = GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧
      (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) ∧
      IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧
      (H'.interSet (subBd r₁)).IsCircuit ∧ (H'.interSet (subBd r₂)).IsCircuit ∧
      v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧
      (∀ w₁ w₂ w₃ w₄ : S,
        w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ →
        w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
          List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
            List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
        w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
        w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧
      (∀ u₁ u₂ u₃ u₄ : S,
        u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ →
        u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
        u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧
        u₃ ∈ (H'.interSet (subBd r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) ∧
      2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last}

/-- Statement of Graph Minors XV, (3.5) (page 123):
"Let $\Sigma$ be a surface and let $\phi \ge 3$ be an integer. Let $\mathscr{T}^*$ be a
tangle in a graph $G$, and let $H, \eta, \mathscr{T}$ be a $\Sigma$-span. Let $\Lambda_1,
\Lambda_2 \subseteq \Sigma$ be distinct regions of $H$ so that $H \cap bd(\Lambda_i)$ is a
circuit $C_i$ ($i = 1, 2$), and no region of $H$ is incident with a vertex in $C_1$ and with
a vertex in $C_2$. Let $a_1, \dots, a_\phi$ be distinct vertices of $C_1$ in order, and let
$b_1, \dots, b_\phi$ be distinct vertices of $C_2$ in order (under some orientations of
$C_1$ and $C_2$), such that $\{a_1, \dots, a_\phi\}$ and $\{b_1, \dots, b_\phi\}$ are free
with respect to $\mathscr{T}$. For $1 \le i \le \phi$ let $P_i$ be an $\eta(H)$-path with
ends $\eta(a_i), \eta(b_i)$, such that $P_1, \dots, P_\phi$ are mutually disjoint. Then
there is a $\Sigma'$-span of order $\phi$, where $\Sigma'$ is the surface obtained by adding
a handle to $\Sigma$."

Here we depart from the paper by also assuming the line condition required by Graph Minors XII,
(5.1): every `H`-normal line `F ⊆ Σ - (Λ₁ ∪ Λ₂)` meeting both `bd(Λ₁)` and `bd(Λ₂)` satisfies
`ϕ ≤ |F ∩ V(H)|` (at `ϕ = 3` this follows from the hypothesis that no region meets both `C₁` and
`C₂`, as proved in `line_ncard_ge_three_of_no_common_region`). -/
def GM15Theorem35Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ φ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ₁ Λ₂ : Set S) (P : Fin φ → Graph α β) (a b : Fin φ → S),
    IsSigmaSpan G H η θ_star θ T_star T →
    Λ₁ ∈ H.R → Λ₂ ∈ H.R → Λ₁ ≠ Λ₂ →
    IsOArc (subBd Λ₁) → IsOArc (subBd Λ₂) →
    (H.interSet (subBd Λ₁)).IsCircuit → (H.interSet (subBd Λ₂)).IsCircuit →
    (∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty →
      Disjoint (closure r) (H.V ∩ subBd Λ₂)) →
    (∀ F : Set S, IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) →
      (F ∩ subBd Λ₁).Nonempty → (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard) →
    3 ≤ φ → φ ≤ θ →
    (List.ofFn a).Nodup → (List.ofFn b).Nodup →
    GM12.IsListedInOrderOn (subBd Λ₁) (List.ofFn a) →
    GM12.IsListedInOrderOn (subBd Λ₂) (List.ofFn b) →
    (∀ i : Fin φ, a i ∈ H.V ∩ subBd Λ₁ ∧ b i ∈ H.V ∩ subBd Λ₂) →
    (∀ i : Fin φ, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i))) →
    Pairwise (fun i j => Disjoint V(P i) V(P j)) →
    IsFreeSet H.toHypergraph T θ (range a) →
    IsFreeSet H.toHypergraph T θ (range b) →
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingHandle S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T'

/-- At `φ = 3`, the line condition in `GM15Theorem35Statement` follows from the paper's hypothesis
that no region of `H` meets both `H.V ∩ subBd Λ₁` and `H.V ∩ subBd Λ₂`: if an `H`-normal line `F`
meeting both `subBd Λ₁` and `subBd Λ₂` had `|F ∩ H.V| < 3`, its subline between those two boundary
points would have interior disjoint from `H.U` and hence lie in a single region meeting both
circuits. -/
theorem line_ncard_ge_three_of_no_common_region {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S)
    {H : Drawing S} {Λ₁ Λ₂ F : Set S}
    (hΛ₁ : Λ₁ ∈ H.R) (hΛ₂ : Λ₂ ∈ H.R)
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty →
      Disjoint (closure r) (H.V ∩ subBd Λ₂))
    (hF : IsLine F) (hFN : H.IsNormal F)
    (hF₁ : (F ∩ subBd Λ₁).Nonempty) (hF₂ : (F ∩ subBd Λ₂).Nonempty) :
    3 ≤ (F ∩ H.V).ncard := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hSubBd_U : ∀ {Λ : Set S}, Λ ∈ H.R → subBd Λ ⊆ H.U := by
    intro Λ hΛ z hz
    by_contra hz_not_U
    obtain ⟨r, hr, hzr⟩ := GM11.exists_region_of_notMem hz_not_U
    obtain ⟨w, hwr, hwΛ⟩ := mem_closure_iff.mp hz.1 r (GM11.region_isOpen hr) hzr
    have hrΛ : r = Λ := GM11.region_eq_of_mem hr hΛ hwr hwΛ
    have hzΛ : z ∈ Λ := hrΛ ▸ hzr
    have hz_fr : z ∈ frontier Λ := subBd_eq_frontier Λ ▸ hz
    exact ((GM11.region_isOpen hΛ).interior_eq ▸ hz_fr.2) hzΛ
  obtain ⟨z₁, hz₁F, hz₁_bd⟩ := hF₁
  obtain ⟨z₂, hz₂F, hz₂_bd⟩ := hF₂
  have hz₁V : z₁ ∈ H.V := hFN ⟨hz₁F, hSubBd_U hΛ₁ hz₁_bd⟩
  have hz₂V : z₂ ∈ H.V := hFN ⟨hz₂F, hSubBd_U hΛ₂ hz₂_bd⟩
  have hz₁₂ : z₁ ≠ z₂ := by
    intro h
    subst h
    exact disjoint_left.mp
      (hNo_common_region Λ₁ hΛ₁ ⟨z₁, hz₁_bd.1, hz₁V, hz₁_bd⟩)
      hz₁_bd.1 ⟨hz₁V, hz₂_bd⟩
  by_contra hlt
  have hFV : (F ∩ H.V).ncard ≤ 2 := by omega
  have hpair_sub : ({z₁, z₂} : Set S) ⊆ F ∩ H.V := by
    rintro z (rfl | rfl)
    · exact ⟨hz₁F, hz₁V⟩
    · exact ⟨hz₂F, hz₂V⟩
  have hFV_eq : F ∩ H.V = {z₁, z₂} := by
    refine (Set.eq_of_subset_of_ncard_le hpair_sub ?_
      (H.finite_V.subset inter_subset_right)).symm
    rw [Set.ncard_pair hz₁₂]
    exact hFV
  have hFU_sub_FV : F ∩ H.U ⊆ F ∩ H.V := fun z hz => ⟨hz.1, hFN hz⟩
  have hFU_eq : F ∩ H.U = {z₁, z₂} :=
    Subset.antisymm (hFU_sub_FV.trans hFV_eq.subset)
      (hFV_eq ▸ inter_subset_inter_right _ H.V_subset_U)
  obtain ⟨f⟩ := hF
  have hLuv : IsLineWithEnds F (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
  obtain ⟨a, ha, rfl, -, -⟩ := hLuv.exists_arc
  obtain ⟨t₁, rfl⟩ := hz₁F
  obtain ⟨t₂, rfl⟩ := hz₂F
  have ht₁₂ : (t₁ : ℝ) ≠ (t₂ : ℝ) := fun he => hz₁₂ (congrArg a (Subtype.ext he))
  have hex_sub : ∃ F₁ : Set S, F₁ ⊆ range a ∧
      (IsLineWithEnds F₁ (a t₁) (a t₂) ∨ IsLineWithEnds F₁ (a t₂) (a t₁)) := by
    rcases lt_or_gt_of_ne ht₁₂ with hlt_t | hgt_t
    · refine ⟨range (pieceA a t₁ t₂), ?_, Or.inl ?_⟩
      · rw [range_pieceA a t₁.2.1 hlt_t.le t₂.2.2]
        rintro x ⟨r, hr, rfl⟩
        exact ⟨⟨r, ⟨t₁.2.1.trans hr.1, hr.2.trans t₂.2.2⟩⟩, (extI_of_mem a _).symm⟩
      · have h := (isArcMap_pieceA ha t₁.2.1 hlt_t t₂.2.2).isLineWithEnds
        rwa [pieceA_zero, pieceA_one, extI_coe, extI_coe] at h
    · refine ⟨range (pieceA a t₂ t₁), ?_, Or.inr ?_⟩
      · rw [range_pieceA a t₂.2.1 hgt_t.le t₁.2.2]
        rintro x ⟨r, hr, rfl⟩
        exact ⟨⟨r, ⟨t₂.2.1.trans hr.1, hr.2.trans t₁.2.2⟩⟩, (extI_of_mem a _).symm⟩
      · have h := (isArcMap_pieceA ha t₂.2.1 hgt_t t₁.2.2).isLineWithEnds
        rwa [pieceA_zero, pieceA_one, extI_coe, extI_coe] at h
  obtain ⟨F₁, hF₁_sub, hF₁_ends⟩ := hex_sub
  have hF₁_line : IsLineWithEnds F₁ (a t₁) (a t₂) :=
    hF₁_ends.elim id Surface.IsLineWithEnds.symm
  obtain ⟨hz₁F₁, hz₂F₁⟩ := ends_mem_of_isLineWithEnds hF₁_line
  obtain ⟨w, hw⟩ := (GM11.isPathConnected_sdiff_pair hF₁_line).nonempty
  have hF₁_diff_U : Disjoint (F₁ \ {a t₁, a t₂}) H.U :=
    disjoint_left.mpr fun z hz hzU => hz.2 (hFU_eq ▸ ⟨hF₁_sub hz.1, hzU⟩)
  have hw_not_U : w ∉ H.U := disjoint_left.mp hF₁_diff_U hw
  obtain ⟨r, hr, hw_r⟩ := GM11.exists_region_of_notMem hw_not_U
  have hF₁_diff_r : F₁ \ {a t₁, a t₂} ⊆ r :=
    GM11.subset_region hr (GM11.isPathConnected_sdiff_pair hF₁_line).isConnected.isPreconnected
      hF₁_diff_U hw hw_r
  have hF₁_cl_r : F₁ ⊆ closure r :=
    (GM11.closure_sdiff_pair hF₁_line).symm.subset.trans (closure_mono hF₁_diff_r)
  exact disjoint_left.mp
    (hNo_common_region r hr ⟨a t₁, hF₁_cl_r hz₁F₁, hz₁V, hz₁_bd⟩)
    (hF₁_cl_r hz₂F₁) ⟨hz₂V, hz₂_bd⟩

/-- **Graph Minors XV, (3.5), Claim (1)** (page 124):
"For every $O$-arc $F \subseteq \Sigma$ with $F \cap U(H') \subseteq V(H')$ and $|F \cap
V(H')| \le 2$, there is a dial $\Delta \subseteq \Sigma$ for $F, H' \cap \Sigma_1$ with $|X
\cap \Delta| \le |F \cap V(H')|$." -/
theorem theorem_3_5_claim_1 {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {θ : ℕ} {Λ₁ Λ₂ X₁ X₂ F : Set S}
    (hRigid : IsRigid H)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ₁ : Λ₁ ∈ H.R) (hΛ₂ : Λ₂ ∈ H.R)
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty →
      Disjoint (closure r) (H.V ∩ subBd Λ₂))
    (hX₁_sub : X₁ ⊆ H.V ∩ subBd Λ₁) (hX₂_sub : X₂ ⊆ H.V ∩ subBd Λ₂)
    (hX₁_card : 2 < X₁.ncard) (hX₂_card : 2 < X₂.ncard)
    (hFree₁ : IsFreeSet H.toHypergraph T θ X₁)
    (hFree₂ : IsFreeSet H.toHypergraph T θ X₂)
    (hF : IsOArc F) (hFU : F ∩ H.U ⊆ H.V) (hFV : (F ∩ H.V).ncard ≤ 2) :
    ∃ Δ : Set S, IsDial H F Δ ∧ ((X₁ ∪ X₂) ∩ Δ).ncard ≤ (F ∩ H.V).ncard := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨Δ, hDial, hCard₁⟩ := theorem_3_3_claim_3 hS hRigid hT hθ hFree₁ hF hFU hFV
  have hMemT :
      ((H.interSet Δ).toHypergraph, (H.interSet (closure (univ \ Δ))).toHypergraph) ∈ T :=
    (theorem_3_1_proof H θ T Δ hS inferInstance hRigid hT hθ hDial.1
      (hDial.2.1 ▸ hFU) (hDial.2.1 ▸ hFV)).mpr (hDial.2.1.symm ▸ hDial)
  obtain ⟨_, hOrd⟩ := isSeparation_interSet_of_isClosed H hDial.1.isClosed (hDial.2.1 ▸ hFU)
  have hCard₂ : (X₂ ∩ Δ).ncard ≤ (F ∩ H.V).ncard := by
    have hFree_sub : IsFreeSet H.toHypergraph T θ (X₂ ∩ Δ) :=
      hFree₂.subset hT inter_subset_left
    have hSubA : X₂ ∩ Δ ⊆ (H.interSet Δ).toHypergraph.vertexSet := by
      change X₂ ∩ Δ ⊆ (H.interSet Δ).V
      rw [interSet_V_of_isClosed H hDial.1.isClosed]
      exact inter_subset_inter_left Δ hFree₂.1
    exact hDial.2.1 ▸ hOrd ▸ hFree_sub.2.2 hMemT hSubA
  refine ⟨Δ, hDial, ?_⟩
  by_cases hne₁ : (X₁ ∩ Δ).Nonempty
  · by_cases hne₂ : (X₂ ∩ Δ).Nonempty
    · exfalso
      have hSubBd_U : ∀ {Λ : Set S}, Λ ∈ H.R → subBd Λ ⊆ H.U := by
        intro Λ hΛ z hz
        by_contra hz_not_U
        obtain ⟨r, hr, hzr⟩ := GM11.exists_region_of_notMem hz_not_U
        obtain ⟨w, hwr, hwΛ⟩ := mem_closure_iff.mp hz.1 r (GM11.region_isOpen hr) hzr
        have hrΛ : r = Λ := GM11.region_eq_of_mem hr hΛ hwr hwΛ
        have hzΛ : z ∈ Λ := hrΛ ▸ hzr
        have hz_not_Λ : z ∉ Λ := by
          have hz_fr : z ∈ frontier Λ := subBd_eq_frontier Λ ▸ hz
          exact (GM11.region_isOpen hΛ).interior_eq ▸ hz_fr.2
        exact hz_not_Λ hzΛ
      have hMeets : ∀ {Λ Y : Set S}, Λ ∈ H.R → IsOArc (subBd Λ) → Y ⊆ H.V ∩ subBd Λ →
          2 < Y.ncard → (Y ∩ Δ).ncard ≤ (F ∩ H.V).ncard → (Y ∩ Δ).Nonempty →
          ∃ z, z ∈ F ∧ z ∈ H.V ∧ z ∈ subBd Λ := by
        intro Λ Y hΛ hOArc hY_sub hY_card hY_le ⟨y₀, hy₀Y, hy₀Δ⟩
        have hnot_sub : ¬ (subBd Λ ⊆ Δ) := by
          intro hsub
          have hYΔ : Y ∩ Δ = Y := inter_eq_left.mpr (hY_sub.trans (inter_subset_right.trans hsub))
          have hle2 : Y.ncard ≤ 2 := hYΔ ▸ hY_le.trans hFV
          omega
        obtain ⟨y₁, hy₁_bd, hy₁_not_Δ⟩ := not_subset.mp hnot_sub
        have hConn_bd : IsPreconnected (subBd Λ) := by
          obtain ⟨φ⟩ := hOArc
          have hEq : subBd Λ = range (fun z : Circle => (φ z).1) := by
            ext w
            exact ⟨fun hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
          rw [hEq]
          exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
        have hne_fr : (subBd Λ ∩ frontier Δ).Nonempty := by
          by_contra h
          have hdis : Disjoint (subBd Λ) (frontier Δ) :=
            disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
          exact hy₁_not_Δ (GM14.subset_of_disjoint_frontier hConn_bd hDial.1.isClosed
            hdis (hY_sub hy₀Y).2 hy₀Δ hy₁_bd)
        obtain ⟨z, hz_bd, hz_fr⟩ := hne_fr
        have hz_F : z ∈ F := hDial.2.1 ▸ (subBd_eq_frontier Δ).symm ▸ hz_fr
        have hz_U : z ∈ H.U := hSubBd_U hΛ hz_bd
        exact ⟨z, hz_F, hFU ⟨hz_F, hz_U⟩, hz_bd⟩
      obtain ⟨z₁, hz₁F, hz₁V, hz₁_bd⟩ := hMeets hΛ₁ hOArc₁ hX₁_sub hX₁_card hCard₁ hne₁
      obtain ⟨z₂, hz₂F, hz₂V, hz₂_bd⟩ := hMeets hΛ₂ hOArc₂ hX₂_sub hX₂_card hCard₂ hne₂
      have hz₁₂ : z₁ ≠ z₂ := by
        intro h
        subst h
        exact disjoint_left.mp
          (hNo_common_region Λ₁ hΛ₁ ⟨z₁, hz₁_bd.1, hz₁V, hz₁_bd⟩)
          hz₁_bd.1 ⟨hz₁V, hz₂_bd⟩
      have hpair_sub : ({z₁, z₂} : Set S) ⊆ F ∩ H.V := by
        rintro z (rfl | rfl)
        · exact ⟨hz₁F, hz₁V⟩
        · exact ⟨hz₂F, hz₂V⟩
      have hFV_eq : F ∩ H.V = {z₁, z₂} := by
        refine (Set.eq_of_subset_of_ncard_le hpair_sub ?_
          (H.finite_V.subset inter_subset_right)).symm
        rw [Set.ncard_pair hz₁₂]
        exact hFV
      have hFU_sub_FV : F ∩ H.U ⊆ F ∩ H.V := fun z hz => ⟨hz.1, hFU hz⟩
      have hFU_eq : F ∩ H.U = {z₁, z₂} :=
        Subset.antisymm (hFU_sub_FV.trans hFV_eq.subset)
          (hFV_eq ▸ inter_subset_inter_right _ H.V_subset_U)
      obtain ⟨F₁, _, hF₁_line, _, hF_union, _⟩ := hF.lines hz₁F hz₂F hz₁₂
      have hF₁_sub : F₁ ⊆ F := hF_union ▸ subset_union_left
      obtain ⟨hz₁F₁, hz₂F₁⟩ := ends_mem_of_isLineWithEnds hF₁_line
      obtain ⟨w, hw⟩ := (GM11.isPathConnected_sdiff_pair hF₁_line).nonempty
      have hF₁_diff_U : Disjoint (F₁ \ {z₁, z₂}) H.U :=
        disjoint_left.mpr fun z hz hzU => hz.2 (hFU_eq ▸ ⟨hF₁_sub hz.1, hzU⟩)
      have hw_not_U : w ∉ H.U := disjoint_left.mp hF₁_diff_U hw
      obtain ⟨r, hr, hw_r⟩ := GM11.exists_region_of_notMem hw_not_U
      have hF₁_diff_r : F₁ \ {z₁, z₂} ⊆ r :=
        GM11.subset_region hr (GM11.isPathConnected_sdiff_pair hF₁_line).isConnected.isPreconnected
          hF₁_diff_U hw hw_r
      have hF₁_cl_r : F₁ ⊆ closure r :=
        (GM11.closure_sdiff_pair hF₁_line).symm.subset.trans (closure_mono hF₁_diff_r)
      exact disjoint_left.mp
        (hNo_common_region r hr ⟨z₁, hF₁_cl_r hz₁F₁, hz₁V, hz₁_bd⟩)
        (hF₁_cl_r hz₂F₁) ⟨hz₂V, hz₂_bd⟩
    · rw [not_nonempty_iff_eq_empty] at hne₂
      rw [union_inter_distrib_right, hne₂, union_empty]
      exact hCard₁
  · rw [not_nonempty_iff_eq_empty] at hne₁
    rw [union_inter_distrib_right, hne₁, empty_union]
    exact hCard₂

end GraphMinor.GM15
