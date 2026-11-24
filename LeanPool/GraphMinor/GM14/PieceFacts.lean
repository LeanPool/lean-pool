/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.ClaimOneReduction
public import LeanPool.GraphMinor.GM14.RigidDisc
public import LeanPool.GraphMinor.GM16.NestedDiscContainment
public import LeanPool.GraphMinor.GM11.Section810

/-!
# The members of the segregation in (8.4)

"Since every graph with at most one circuit can be drawn in the plane with all its vertices incident
with the infinite region, we deduce from (2) and the rigidity of $H$ that for each $(A, \Omega) \in
\mathscr{S}$,
the drawing $H \cap A$ in the disc $\alpha(A, \Omega)$ can be extended to an embedding of $A$ in
this disc"
(page 42). Here `pieceDrawing` is this sentence, after Claim (2), which is `piece_claim_2`.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
  GraphMinor.GM06 GraphMinor.GM16 GraphMinor.GM14.Whitney

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-- A circuit of a drawing, as a graph, is a subdrawing. -/
theorem exists_circuit_drawing {H : Drawing S} {C : Graph S (Set S)}
    (hC : IsGraphCircuit H.toGraph C) :
    ∃ R : Drawing S, R.IsCircuit ∧ R.IsSubdrawing H ∧ R.V = V(C) ∧ R.E = E(C) := by
  obtain ⟨hle, u, W, hs, hlen, hV, hE⟩ := hC
  have hVC : V(C) ⊆ H.V := hle.vertexSet_mono
  have hEC : E(C) ⊆ H.E := hle.edgeSet_mono
  have hRE : (H.span V(C) E(C)).E = E(C) := by
    rw [H.span_E]
    exact inter_eq_left.mpr hEC
  have hRV : (H.span V(C) E(C)).V = V(C) := by
    rw [H.span_V]
    refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset fun e he => ?_))
      fun x hx => Or.inl ⟨hx, hVC hx⟩
    rintro x ⟨hxe, hxV⟩
    obtain ⟨a, b, hl⟩ := C.exists_isLink_of_mem_edgeSet he.1
    have hl' := hl.mono hle
    have hc : closure e ∩ H.V = {a, b} := hl'.2.2.2
    have : x ∈ ({a, b} : Set S) := hc ▸ ⟨hxe, hxV⟩
    rcases this with rfl | rfl
    · exact hl.left_mem
    · exact hl.right_mem
  obtain ⟨W', hs', he'⟩ := W.exists_transfer (G' := (H.span V(C) E(C)).toGraph)
    (fun e a b _ hl => by
      have hl' := hl.mono hle
      refine ⟨hRE.superset hl.edge_mem, hRV.superset hl.left_mem, hRV.superset hl.right_mem, ?_⟩
      have hc : closure e ∩ H.V = {a, b} := hl'.2.2.2
      rw [hRV, ← hc]
      ext z
      constructor
      · exact fun h => ⟨h.1, hVC h.2⟩
      · rintro ⟨h₁, h₂⟩
        have : z ∈ ({a, b} : Set S) := hc ▸ ⟨h₁, h₂⟩
        rcases this with rfl | rfl
        · exact ⟨h₁, hl.left_mem⟩
        · exact ⟨h₁, hl.right_mem⟩)
    (fun x hx => hRV.superset (W.mem_vertexSet_of_mem_support hx))
  refine ⟨H.span V(C) E(C), ⟨u, W', ?_, ?_, ?_, ?_⟩, ?_, hRV, hRE⟩
  · change W'.support.tail.Nodup ∧ W'.edges.Nodup
    rw [hs', he']
    exact hs
  · change 0 < W'.edges.length
    rw [he']
    exact hlen
  · exact hRV.trans (hV.trans (by rw [hs']))
  · exact hRE.trans (hE.trans (by rw [he']))
  · exact ⟨hRV.subset.trans hVC, hRE.subset.trans hEC⟩

omit [T2Space S] in
/-- A circuit of a drawing is a circuit of its graph. -/
theorem isGraphCircuit_of_isCircuit {H R : Drawing S} (hR : R.IsCircuit) (hRH : R.IsSubdrawing H) :
    IsGraphCircuit H.toGraph R.toGraph := by
  obtain ⟨u, W, hs, hlen, hV, hE⟩ := hR
  refine ⟨?_, u, W, hs, hlen, hV, hE⟩
  refine ⟨hRH.1, fun e x y hl => ?_⟩
  refine ⟨hRH.2 hl.edge_mem, hRH.1 hl.left_mem, hRH.1 hl.right_mem, ?_⟩
  rw [← hRH.closure_inter_V hl.edge_mem]
  exact hl.2.2.2

/-- A drawing that is rigid in `Cyl` is rigid in a closed disc in `Cyl`. -/
theorem isRigidIn_interSet (hS : IsClosedSurface S) {H : Drawing S} {B Cyl d : Set S}
    (hB : IsClosedDisc B) (hCyl : Cyl ⊆ B) (hrig : IsRigidIn H Cyl) (hd : IsClosedDisc d)
    (hdCyl : d ⊆ Cyl) (hbd : subBd d ∩ H.U ⊆ H.V) : IsRigidIn (H.interSet d) d := by
  have hcl : IsClosed d := hd.isClosed
  obtain ⟨hV, hU⟩ := interSet_V_and_U hcl hbd
  intro F hFd hF hFn hFc
  have hFV : F ∩ (H.interSet d).V = F ∩ H.V := by
    rw [hV]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hFd h.1⟩⟩
  have hFn' : F ∩ H.U ⊆ H.V := by
    rintro x ⟨hx, hxU⟩
    have : x ∈ F ∩ (H.interSet d).U := ⟨hx, hU.superset ⟨hxU, hFd hx⟩⟩
    have := hFn this
    rw [hV] at this
    exact this.1
  obtain ⟨Δ, hΔCyl, hΔd, hΔb, hor⟩ := hrig F (hFd.trans hdCyl) hF hFn' (hFV ▸ hFc)
  have hbdΔ : discBd Δ = F := (IsClosedDisc.subBd_eq_discBd hS hΔd).symm.trans hΔb
  have hsub : Δ ⊆ d := closedDisc_subset_of_boundary_subset hB hd hΔd (hdCyl.trans hCyl)
    (hΔCyl.trans hCyl) (hbdΔ ▸ hFd)
  refine ⟨Δ, hsub, hΔd, hΔb, ?_⟩
  rcases hor with h | ⟨u, v, huv, hcap, hp⟩
  · left
    rw [hU]
    exact fun x hx => h ⟨hx.1, hx.2.1⟩
  · right
    refine ⟨u, v, huv, hFV.trans hcap, ?_⟩
    have heq : (H.interSet d).interSet Δ = H.interSet Δ := by
      have hE₁ : ((H.interSet d).interSet Δ).E = (H.interSet Δ).E := by
        rw [interSet_E, interSet_E, interSet_E]
        ext e
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hsub⟩, h.2⟩⟩
      refine Drawing.ext_of_V_E ?_ hE₁
      ext x
      rw [GM11.mem_interSet_V_iff hΔd.isClosed, GM11.mem_interSet_V_iff hΔd.isClosed, hV]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩⟩
    rwa [heq]

omit [T2Space S] in
/-- A span embedding is an isomorphism onto its image. -/
theorem SpanEmbedding.gmap {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G) :
    GMap H.toGraph η.imageGraph η.vMap η.eMap := by
  obtain ⟨ι, hv, he⟩ := η.exists_iso
  refine ⟨η.bijOn_v, η.bijOn_e, fun {e x y} hee hx hy => ?_⟩
  have := ι.isLink_iff ⟨e, hee⟩ ⟨x, hx⟩ ⟨y, hy⟩
  rwa [he, hv, hv] at this

/-- **Claim (2) of (8.4)** for one member of the segregation. -/
theorem piece_claim_2 {H : Drawing S} {G₁ : Graph α β} {η : SpanEmbedding H G₁} {S₀ : Society α β}
    (hone : ClaimOne η S₀) (hS₀G : S₀.G ≤ G₁) {d : Set S} (hd : IsClosedDisc d)
    (hbdd : subBd d = discBd d) (η₁ : SpanEmbedding (H.interSet d) S₀.G)
    (him : η₁.imageGraph = pieceGraph η S₀.G) (hrig : IsRigidIn (H.interSet d) d)
    (h3 : S₀.Ω.bar.ncard ≤ 3)
    (hXH : ∀ v ∈ (H.interSet d).V, v ∈ subBd d ↔ η₁.vMap v ∈ S₀.Ω.bar)
    (hU : (H.interSet d).U ⊆ d) (hn : (H.interSet d).U ∩ subBd d ⊆ (H.interSet d).V) :
    S₀.G = pieceGraph η S₀.G ∨ {C : Graph α β | IsGraphCircuit S₀.G C}.ncard ≤ 1 := by
  classical
  have : Nonempty S := by
    obtain ⟨x, hx⟩ := hd.nonempty_discInt
    exact ⟨x⟩
  have m := η₁.gmap
  rw [him] at m
  have hvm : ∀ v ∈ (H.interSet d).V, η₁.vMap v ∈ V(pieceGraph η S₀.G) := fun v hv
    => m.bijV.mapsTo hv
  refine claim_2_of_8_4 (pieceGraph_le η hS₀G) h3 hone ?_ ?_
  · intro C hC
    have : Nonempty α := by
      obtain ⟨-, u, -⟩ := hC
      exact ⟨u⟩
    have ms := m.symm
    obtain ⟨R, hR, hRH, hRV, -⟩ := exists_circuit_drawing (ms.circuit hC)
    obtain ⟨Q, hdis, hQ⟩ := three_paths_of_rigid hd hbdd hU hn hrig hR hRH
    have hRV' : η₁.vMap '' R.V = V(C) := by
      rw [hRV]
      change η₁.vMap '' (Function.invFunOn η₁.vMap (H.interSet d).V '' V(C)) = V(C)
      rw [image_image]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h₁ : η₁.vMap (Function.invFunOn η₁.vMap (H.interSet d).V y) = y :=
          m.bijV.invOn_invFunOn.2 (hC.1.vertexSet_mono hy)
        change η₁.vMap (Function.invFunOn η₁.vMap (H.interSet d).V y) ∈ V(C)
        rw [h₁]
        exact hy
      · intro hx
        exact ⟨x, hx, m.bijV.invOn_invFunOn.2 (hC.1.vertexSet_mono hx)⟩
    have hend : ∀ i, ∃ x y, IsFromToPathWithEnds (pieceGraph η S₀.G) (m.sub (Q i)) V(C) S₀.Ω.bar
        x y := by
      intro i
      obtain ⟨a, b, hP⟩ := hQ i
      have h := m.fromTo hRH.1 inter_subset_left hP
      rw [hRV'] at h
      refine ⟨_, _, h.1, h.2.1, ?_⟩
      rw [← h.2.2]
      ext z
      constructor
      · rintro ⟨hz, hzb⟩
        obtain ⟨v, hv, rfl⟩ := hz
        have hvH : v ∈ (H.interSet d).V := hP.1.1.vertexSet_mono hv
        exact ⟨mem_image_of_mem _ hv, v, ⟨hvH, (hXH v hvH).mpr hzb⟩, rfl⟩
      · rintro ⟨hz, v, ⟨hvH, hvb⟩, rfl⟩
        exact ⟨hz, (hXH v hvH).mp hvb⟩
    choose x y hP using hend
    refine ⟨fun i => m.sub (Q i), x, y, hP, fun i j hij => ?_⟩
    change Disjoint (η₁.vMap '' V(Q i)) (η₁.vMap '' V(Q j))
    obtain ⟨_, _, hPi⟩ := hQ i
    obtain ⟨_, _, hPj⟩ := hQ j
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' := m.bijV.injOn (hPj.1.1.vertexSet_mono hb) (hPi.1.1.vertexSet_mono ha) hab
    exact disjoint_left.mp (hdis hij) ha (hab' ▸ hb)
  · rintro t ht htb e ⟨z, hl⟩
    obtain ⟨v, hv, rfl⟩ := m.bijV.surjOn ht
    obtain ⟨g, hg, rfl⟩ := m.bijE.surjOn hl.edge_mem
    obtain ⟨y, hy, rfl⟩ := m.bijV.surjOn hl.right_mem
    have hl' := (m.link hg hv hy).mpr hl
    have hvb : v ∉ subBd d := fun h => htb ((hXH v hv).mp h)
    obtain ⟨g', hg', y', hl''⟩ := two_edges_of_rigid hd hbdd hU hn hrig hv hvb ⟨y, hl'⟩
    refine ⟨η₁.eMap g', fun h => hg' (m.bijE.injOn hl''.edge_mem hg h), _,
      (m.link hl''.edge_mem hv hl''.right_mem).mp hl''⟩

/-- **The sentence on page 42.** Each member of the segregation has a drawing in its disc that
extends
`H ∩ A`. -/
theorem exists_member_drawing (hS : IsClosedSurface S) {H : Drawing S} {B Cyl : Set S}
    (hB : IsClosedDisc B) (hCyl : Cyl ⊆ B) (hrig : IsRigidIn H Cyl) {G₁ : Graph α β}
    {η : SpanEmbedding H G₁} {S_seg : Set (Society α β)} {α_disc : Society α β → Set S}
    {α_pt : α → S} (hseg : IsThreeSegregation G₁ S_seg)
    (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hcompat : IsCompatibleWith G₁ H η S_seg α_disc α_pt)
    (hdiscs : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Cyl) {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg)
    (hone : ClaimOne η S₀) :
    ∃ Γ : GraphDrawing S₀.G S, Γ.drawing.U ⊆ α_disc S₀ ∧
      Γ.drawing.U ∩ subBd (α_disc S₀) = α_pt '' S₀.Ω.bar ∧
      (∀ v : V(S₀.G), v.1 ∈ S₀.Ω.bar → (Γ.iso.vertexEquiv v).1 = α_pt v.1) ∧
      (∀ v ∈ H.V, v ∈ α_disc S₀ → graphDrawingVertexSet Γ (η.vMap v) = {v}) ∧
      ∀ e ∈ H.E, e ⊆ α_disc S₀ → graphDrawingEdgeSet Γ (η.eMap e) = e := by
  obtain ⟨hd, hbarpt⟩ := harr.isClosedDisc S₀ hS₀
  have hbdd : subBd (α_disc S₀) = discBd (α_disc S₀) := IsClosedDisc.subBd_eq_discBd hS hd
  have hcl : IsClosed (α_disc S₀) := hd.isClosed
  have hbd : subBd (α_disc S₀) ∩ H.U ⊆ H.V := by
    rintro x ⟨h₁, h₂⟩
    have : x ∈ H.U ∩ subBd (α_disc S₀) := ⟨h₂, h₁⟩
    rw [hcompat.bd_inter_eq S₀ hS₀] at this
    exact this.1
  obtain ⟨η₁, him, hv, he⟩ := exists_pieceEmbedding η (hseg.1.le S₀ hS₀) hcl hbd
    (hcompat.inter_V_iff S₀ hS₀) (hcompat.inter_E_iff S₀ hS₀)
  obtain ⟨hIV, hIU⟩ := interSet_V_and_U hcl hbd
  have hrig₁ := isRigidIn_interSet hS hB hCyl hrig hd (hdiscs S₀ hS₀) hbd
  have hU : (H.interSet (α_disc S₀)).U ⊆ α_disc S₀ := by
    rw [hIU]
    exact inter_subset_right
  have hn : (H.interSet (α_disc S₀)).U ∩ subBd (α_disc S₀) ⊆ (H.interSet (α_disc S₀)).V := by
    rw [hIU, hIV]
    rintro x ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨hbd ⟨h₃, h₁⟩, h₂⟩
  have hXH : ∀ v ∈ (H.interSet (α_disc S₀)).V, v ∈ subBd (α_disc S₀) ↔ η₁.vMap v ∈ S₀.Ω.bar := by
    intro v hv'
    rw [hIV] at hv'
    rw [hv]
    constructor
    · intro h
      have : v ∈ H.U ∩ subBd (α_disc S₀) := ⟨H.V_subset_U hv'.1, h⟩
      rw [hcompat.bd_inter_eq S₀ hS₀] at this
      exact this.2
    · intro h
      have : v ∈ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar} := ⟨hv'.1, h⟩
      rw [← hcompat.bd_inter_eq S₀ hS₀] at this
      exact this.2
  have hc := piece_claim_2 hone (hseg.1.le S₀ hS₀) hd hbdd η₁ him hrig₁ (hseg.2 S₀ hS₀) hXH hU hn
  have hc' : η₁.imageGraph = S₀.G ∨ {C : Graph α β | IsGraphCircuit S₀.G C}.ncard ≤ 1 := by
    rw [him]
    exact hc.imp Eq.symm id
  obtain ⟨Γ, h₁, h₂, h₃, h₄, h₅⟩ := exists_piece_drawing η₁ S₀.finite_V S₀.finite_E hd hbdd hU hn
    S₀.bar_subset (hseg.2 S₀ hS₀)
    (harr.injOn_pts.mono fun x hx => mem_iUnion₂.mpr ⟨S₀, hS₀, hx⟩) hbarpt hXH
    (fun v hv' h => by
      rw [hIV] at hv'
      rw [hv] at h ⊢
      exact hcompat.pt_eq v hv'.1 (mem_iUnion₂.mpr ⟨S₀, hS₀, h⟩))
    hrig₁ hc'
  refine ⟨Γ, h₁, h₂, h₃, fun v hv' hvd => ?_, fun e he' hed => ?_⟩
  · have := h₄ v (by rw [hIV]; exact ⟨hv', hvd⟩)
    rwa [hv] at this
  · have := h₅ e (by rw [interSet_E]; exact ⟨he', hed⟩)
    rwa [he] at this

/-- "It follows that we may assume, to simplify notation, that $G_1$ is a drawing in $\Sigma$" (page
42). -/
theorem exists_reduced_drawing (hS : IsClosedSurface S) {H : Drawing S} {B Cyl : Set S}
    (hB : IsClosedDisc B) (hCyl : Cyl ⊆ B) (hrig : IsRigidIn H Cyl) {G₁ : Graph α β}
    {η : SpanEmbedding H G₁} {S_seg : Set (Society α β)} {α_disc : Society α β → Set S}
    {α_pt : α → S} (hseg : IsThreeSegregation G₁ S_seg)
    (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hcompat : IsCompatibleWith G₁ H η S_seg α_disc α_pt)
    (hdiscs : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Cyl) (hone : ∀ S₀ ∈ S_seg, ClaimOne η S₀) :
    ∃ (Γ : GraphDrawing G₁ S) (ν : α → S), Γ.drawing.U ⊆ ⋃ S₀ ∈ S_seg, α_disc S₀ ∧
      (∀ v : V(G₁), (Γ.iso.vertexEquiv v).1 = ν v.1) ∧
      (∀ v ∈ segregationVertices S_seg, ν v = α_pt v) ∧
      (∀ v ∈ H.V, ν (η.vMap v) = v) ∧
      (∀ e ∈ H.E, graphDrawingEdgeSet Γ (η.eMap e) = e) ∧
      ∀ v ∈ V(G₁), ∃ S₀ ∈ S_seg, ν v ∈ α_disc S₀ ∧ (ν v ∈ subBd (α_disc S₀) → v ∈ S₀.Ω.bar) := by
  classical
  obtain ⟨hs, h3⟩ := id hseg
  choose Γs h₁ h₂ h₃ h₄ h₅ using fun S₀ (h : S₀ ∈ S_seg) =>
    exists_member_drawing hS hB hCyl hrig hseg harr hcompat hdiscs h (hone S₀ h)
  have hpick : ∀ v : α, ∃ p : S, ∀ S₀ (h : S₀ ∈ S_seg) (hv : v ∈ V(S₀.G)),
      ((Γs S₀ h).iso.vertexEquiv ⟨v, hv⟩).1 = p := by
    intro v
    by_cases hv : ∃ S₀ ∈ S_seg, v ∈ V(S₀.G)
    · obtain ⟨S₀, h, hv₀⟩ := hv
      refine ⟨((Γs S₀ h).iso.vertexEquiv ⟨v, hv₀⟩).1, fun S₁ h' hv₁ => ?_⟩
      by_cases he : S₁ = S₀
      · subst he
        rfl
      · obtain ⟨hb₁, hb₀⟩ := hs.vertex_inter_subset S₁ h' S₀ h he ⟨hv₁, hv₀⟩
        rw [h₃ S₁ h' ⟨v, hv₁⟩ hb₁, h₃ S₀ h ⟨v, hv₀⟩ hb₀]
    · refine ⟨α_pt v, fun S₀ h hv₀ => absurd ⟨S₀, h, hv₀⟩ hv⟩
  choose ν hν using hpick
  have hVG : V(G₁) = ⋃ S₁ ∈ S_seg, V(S₁.G) := by
    conv_lhs => rw [← hs.union_eq]
    simp [vertexSet_subgraphSUnion]
  have hEG : E(G₁) = ⋃ S₁ ∈ S_seg, E(S₁.G) := by
    conv_lhs => rw [← hs.union_eq]
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S₁, hS₁, rfl⟩; exact hs.le S₁ hS₁)]
    simp
  have hbarν : ∀ S₀ (h : S₀ ∈ S_seg), ∀ b ∈ S₀.Ω.bar, ν b = α_pt b := fun S₀ h b hb =>
    (hν b S₀ h (S₀.bar_subset hb)).symm.trans (h₃ S₀ h ⟨b, S₀.bar_subset hb⟩ hb)
  have hνU : ∀ S₀ (h : S₀ ∈ S_seg) (v : α), v ∈ V(S₀.G) → ν v ∈ (Γs S₀ h).drawing.U := by
    intro S₀ h v hv
    rw [← hν v S₀ h hv]
    exact (Γs S₀ h).drawing.V_subset_U ((Γs S₀ h).iso.vertexEquiv ⟨v, hv⟩).2
  have hinj₀ : ∀ S₀ (h : S₀ ∈ S_seg), InjOn ν V(S₀.G) := by
    intro S₀ h a ha b hb hab
    rw [← hν a S₀ h ha, ← hν b S₀ h hb] at hab
    exact congrArg Subtype.val ((Γs S₀ h).iso.vertexEquiv.injective (Subtype.ext hab))
  have hinj : InjOn ν V(G₁) := by
    intro a ha b hb hab
    rw [hVG] at ha hb
    obtain ⟨S₁, h₁', ha'⟩ := mem_iUnion₂.mp ha
    obtain ⟨S₂, h₂', hb'⟩ := mem_iUnion₂.mp hb
    by_cases he : S₁ = S₂
    · subst he
      exact hinj₀ S₁ h₁' ha' hb' hab
    · have hp : ν a ∈ α_disc S₁ ∩ α_disc S₂ :=
        ⟨h₁ S₁ h₁' (hνU S₁ h₁' a ha'), hab ▸ h₁ S₂ h₂' (hνU S₂ h₂' b hb')⟩
      obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := harr.inter_discs S₁ h₁' S₂ h₂' he hp
      have e₁ : a = c := hinj₀ S₁ h₁' ha' (S₁.bar_subset hc₁)
        ((hc.symm.trans (hbarν S₁ h₁' c hc₁).symm).symm ▸ rfl)
      have e₂ : b = c := hinj₀ S₂ h₂' hb' (S₂.bar_subset hc₂)
        (by rw [← hab, ← hc, hbarν S₂ h₂' c hc₂])
      rw [e₁, e₂]
  obtain ⟨Γ, hU, hv, he⟩ := exists_glued_drawing hs hinj Γs
    (fun S₀ h v => hν v.1 S₀ h v.2)
    (fun S₁ h₁' S₂ h₂' hne x hx => by
      have hp : x ∈ α_disc S₁ ∩ α_disc S₂ := ⟨h₁ S₁ h₁' hx.1, h₁ S₂ h₂' hx.2⟩
      obtain ⟨c, ⟨hc₁, hc₂⟩, rfl⟩ := harr.inter_discs S₁ h₁' S₂ h₂' hne hp
      exact ⟨c, ⟨S₁.bar_subset hc₁, S₂.bar_subset hc₂⟩, hbarν S₁ h₁' c hc₁⟩)
  refine ⟨Γ, ν, ?_, hv, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    refine iUnion₂_subset fun S₀ h => ?_
    exact (h₁ S₀ h).trans (subset_biUnion_of_mem (u := α_disc) h)
  · intro v hv'
    obtain ⟨S₀, h, hb⟩ := mem_iUnion₂.mp hv'
    exact hbarν S₀ h v hb
  · intro v hv'
    have hx := η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv')
    rw [hVG] at hx
    obtain ⟨S₀, h, hx⟩ := mem_iUnion₂.mp hx
    have hvd := (hcompat.inter_V_iff S₀ h v hv').mpr hx
    have h₆ := h₄ S₀ h v hv' hvd
    rw [graphDrawingVertexSet_eq_singleton (Γs S₀ h) hx, hν _ S₀ h hx] at h₆
    exact singleton_eq_singleton_iff.mp h₆
  · intro e he'
    have hx := η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he')
    rw [hEG] at hx
    obtain ⟨S₀, h, hx⟩ := mem_iUnion₂.mp hx
    rw [he S₀ h _ hx]
    exact h₅ S₀ h e he' ((hcompat.inter_E_iff S₀ h e he').mpr hx)
  · intro v hv'
    rw [hVG] at hv'
    obtain ⟨S₀, h, hx⟩ := mem_iUnion₂.mp hv'
    refine ⟨S₀, h, h₁ S₀ h (hνU S₀ h v hx), fun hb => ?_⟩
    have hm : ν v ∈ (Γs S₀ h).drawing.U ∩ subBd (α_disc S₀) := ⟨hνU S₀ h v hx, hb⟩
    rw [h₂ S₀ h] at hm
    obtain ⟨c, hc, hce⟩ := hm
    have := hinj₀ S₀ h hx (S₀.bar_subset hc) (by rw [← hce, hbarν S₀ h c hc])
    exact this ▸ hc

end GraphMinor.GM14
