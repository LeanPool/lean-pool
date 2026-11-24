/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15g
public import LeanPool.GraphMinor.GM19.CellFlat
public import LeanPool.GraphMinor.GM16.SphereRespectful
public import LeanPool.GraphMinor.GM11.Section64b
public import LeanPool.GraphMinor.GM11.Theorem61
public import LeanPool.GraphMinor.GM19.Section12c
public import LeanPool.GraphMinor.Surface.EdgeLens

/-!
# Graph Minors XIX, (15.2): the tangle on the skeleton is respectful

The proof of (15.2) applies (3.2) of Graph Minors XII to the tangle `𝒯'` in `sk(Γ)`, drawn in `Σ̂`.
That theorem asks for a
respectful tangle. The paper writes "`rep(𝒯') = n + 1`", without saying more. Here is the proof.

The argument of (6.4) of Graph Minors XI shows that the regions of `Γ` and small open sets around a
few vertices form a flat set.
The regions of `sk(Γ)` include the cells of the disc edges of `Γ`. Two corners `a, b` of a cell lie
on a side of the cell, and the
side lies on the boundary of a region of `Γ`. So a path in the cell from `a` to `b` is homotopic to
a path in that region
(`exists_class_beside_edge`), and we may add the cells to the flat set
(`TangleDatum.exists_flat_skeleton`).

Now a `sk(Γ)`-normal `O`-arc `F` with few vertices is in a flat set, so it bounds a closed disc `Δ`.
If the tangle lies on the
wrong side, then the rest of the surface lies in the insides of short circuits, and (7.5) of Graph
Minors XI gives a contradiction.
The result used later is `TangleDatum.isRespectful_skTangle`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM16 Hypergraph

universe w

/-- A line has a path along it. -/
theorem IsLineWithEnds.exists_path {T : Type} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) :
    ∃ p : Path u v, ∀ t, p t ∈ L := by
  obtain ⟨f, h0, h1⟩ := h
  exact ⟨⟨⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩, h0, h1⟩, fun t => (f t).2⟩

/-- **A path beside an edge.** If an edge of a drawing lies on the boundary of a region, then the
line of the edge is homotopic to
a path through the region. -/
theorem exists_class_beside_edge {T : Type} [TopologicalSpace T] [T2Space T]
  (hT : IsClosedSurface T) (G : Drawing T) {e r : Set T} {a b : T} (he : e ∈ G.E)
    (hL : IsLineWithEnds (closure e) a b) (hab : a ≠ b) (hV : closure e ∩ G.V = {a, b})
      (hr : r ∈ G.R) (her : e ⊆ closure r) :
    ∃ g : Cl a b, Arw (r ∪ {a, b}) g ∧ ∀ q : Path a b, (∀ t, q t ∈ closure e) → Cl.mk q = g := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have ha : a ∈ closure e ∩ G.V := hV ▸ .inl rfl
  have hb : b ∈ closure e ∩ G.V := hV ▸ .inr rfl
  let Z : Set T := G.V ∪ ⋃ f ∈ G.E \ {e}, closure f
  have hZ : IsClosed Z := G.finite_V.isClosed.union ((G.finite_edges.subset
    sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have heV : Disjoint e G.V := disjoint_left.mpr fun x hx => (he.2.1 hx).2
  have hcl : closure e ⊆ e ∪ {a, b} := fun x hx => by
    by_cases hxV : x ∈ G.V
    · exact .inr (hV ▸ ⟨hx, hxV⟩)
    · exact .inl ((G.closure_diff_V he).subset ⟨hx, hxV⟩)
  have hLZ : closure e ∩ Z ⊆ {a, b} := by
    rintro x ⟨hx, hxZ⟩
    rcases hxZ with hxV | hxf
    · exact hV ▸ ⟨hx, hxV⟩
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxf
      by_contra hn
      have hxe : x ∈ e := (hcl hx).resolve_right hn
      have hxV : x ∉ G.V := disjoint_left.mp heV hxe
      have hxf' : x ∈ f := (G.closure_diff_V hf.1).subset ⟨hxf, hxV⟩
      exact hf.2 (G.edge_eq_of_mem hf.1 he hxf' hxe)
  have hUZ : G.U ⊆ Z ∪ e := fun x hx => by
    by_cases hxV : x ∈ G.V
    · exact .inl (.inl hxV)
    obtain ⟨f, hf, hxf⟩ := G.exists_edge_of_mem hx hxV
    by_cases hfe : f = e
    · exact .inr (hfe ▸ hxf)
    · exact .inl (.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hxf⟩))
  obtain ⟨D, A, B, hD, hLD, hDZ, -, -, hbL, hDe, hAc, hBc, -, -, hAL, hBL, -, -, ⟨p, -, hp₀⟩, q, -,
    hq₀⟩ := exists_edge_lens hT hL hab hZ hLZ
  have hends : ∀ {X : Set T} (p : Path a b), (∀ t : unitInterval, 0 < t → t < 1 → p t ∈ X)
    → ∀ t, p t ∈ X ∪ {a, b} := fun {X} p h t => by
    by_cases h₀ : t = 0
    · exact .inr (.inl (by rw [h₀, p.source]))
    by_cases h₁ : t = 1
    · exact .inr (.inr (mem_singleton_iff.mpr (by rw [h₁, p.target])))
    exact .inl (h t (unitInterval.pos_iff_ne_zero.mpr h₀) (unitInterval.lt_one_iff_ne_one.mpr h₁))
  have hp := hends p hp₀
  have hq := hends q hq₀
  have hoff : ∀ X : Set T, X ⊆ D → Disjoint X (closure e) → Disjoint X G.U := fun X hXD hX
    => disjoint_left.mpr fun x hx hxU => by
    rcases hUZ hxU with hxZ | hxe
    · rcases hDZ ⟨hXD hx, hxZ⟩ with rfl | rfl
      · exact disjoint_left.mp hX hx ha.1
      · exact disjoint_left.mp hX hx hb.1
    · exact disjoint_left.mp hX hx (subset_closure hxe)
  have hAD : A ⊆ D := hDe ▸ fun x hx => .inl (.inl hx)
  have hBD : B ⊆ D := hDe ▸ fun x hx => .inl (.inr hx)
  have hfl : Flat D := IsSimplyConnectedSet.flat (IsClosedDisc.isSimplyConnectedSet hD)
  have hfin : ∀ X : Set T, X ⊆ D → X ⊆ r → ∀ p : Path a b, (∀ t, p t ∈ X ∪ {a, b}) →
      ∃ g : Cl a b, Arw (r ∪ {a, b}) g ∧ ∀ q : Path a b, (∀ t, q t ∈ closure e) → Cl.mk q = g := by
    intro X hXD hXr p hp
    refine ⟨Cl.mk p, Arw.of_path p fun t => ?_, fun q hq => ?_⟩
    · rcases hp t with h | h
      · exact .inl (hXr h)
      · exact .inr h
    · refine hfl.eq (Arw.of_path q fun t => hLD (hq t)) (Arw.of_path p fun t => ?_)
      rcases hp t with h | h | h
      · exact hXD h
      · rw [h]
        exact hLD ha.1
      · rw [h]
        exact hLD hb.1
  obtain ⟨x₀, hx₀⟩ := he.1
  have hx₀int : x₀ ∈ discInt D := by
    refine ⟨hLD (subset_closure hx₀), fun hbd => ?_⟩
    rcases hbL ⟨hbd, subset_closure hx₀⟩ with rfl | rfl
    · exact disjoint_left.mp heV hx₀ ha.2
    · exact disjoint_left.mp heV hx₀ hb.2
  obtain ⟨y, hyD, hyr⟩ := mem_closure_iff.mp (her hx₀) _ (hD.isOpen_discInt hman) hx₀int
  have hyU : y ∉ G.U := region_subset hr hyr
  have hyD' : y ∈ A ∪ B ∪ closure e := hDe ▸ hyD.1
  rcases hyD' with (hyA | hyB) | hyL
  · exact hfin A hAD (subset_region hr hAc (hoff A hAD hAL) hyA hyr) p hp
  · exact hfin B hBD (subset_region hr hBc (hoff B hBD hBL) hyB hyr) q hq
  · exact absurd (G.closure_subset_U he hyL) hyU

/-- **Claim (2) of (6.4)** of Graph Minors XI (pages 90–91), from a flat set. -/
theorem exists_oArc_of_flat {T : Type} [TopologicalSpace T] [ConnectedSpace T]
  (hS : IsClosedSurface T) (hns : ¬ IsSphere T) (Γ : Drawing T) {A B : Hypergraph T (Set T)}
    (hsep : Γ.toHypergraph.IsSeparation A B)
    (hflat : ∃ D : T → Set T, (∀ s ∈ (A ∩ B).vertexSet, IsOpen (D s)) ∧ (∀ s ∈
      (A ∩ B).vertexSet, s ∈ D s) ∧
      Flat ((⋃ r ∈ Γ.R, r) ∪ ⋃ s ∈ (A ∩ B).vertexSet, D s))
    (hA : ∀ F : Set T, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) :
    ∃ F : Set T, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
      ¬ IsNullHomotopicOArc F := by
  by_contra hno
  push Not at hno
  have ht2 : T2Space T := hS.2.1
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have hS₀V : (A ∩ B).vertexSet ⊆ Γ.V := fun x hx => hsep.left_le.vertexSet_subset hx.1
  obtain ⟨D, hDo, hsD, hfl⟩ := hflat
  set S₀ : Set T := (A ∩ B).vertexSet with hS₀
  obtain ⟨γ₀, hγ₀⟩ := exists_edgePar Γ
  obtain ⟨Q, hQc, hQn, hQU, hQc'⟩ := exists_cut_edges hγ₀ hS₀V hDo hsD
  have hcl : ∀ e ∈ (PaintingOrDrawing.drawing Γ).E, closure e \ (PaintingOrDrawing.drawing Γ).V ⊆ e
    := fun e he =>
    (Γ.closure_diff_V he).subset
  have hAc := isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ) hcl hsep.left_le
  have hBc := isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ) hcl hsep.right_le
  have hcov := U_subset_underlying (Γ := PaintingOrDrawing.drawing Γ)
    (fun x hx hxV => Γ.exists_edge_of_mem hx hxV) hsep
  have hint := underlying_inter (Γ := PaintingOrDrawing.drawing Γ)
    (fun e he f hf x hxe hxf => Γ.edge_eq_of_mem he hf hxe hxf) (fun e he x hx
      => edge_notMem_V he hx) hsep
  have hu : Q ≠ univ := fun h => by
    obtain ⟨z, -, hz⟩ := exists_notMem_U (Γ := Γ) hS isOpen_univ univ_nonempty
    exact hz (hQU (h ▸ mem_univ z)).1
  obtain ⟨Δ, hΔ, -, hQΔ⟩ := theorem_7_5_proof hS hQc hQn hu finite_empty
    (disjoint_empty _) fun F hFQ hF => by
    rw [sdiff_empty]
    have hFA : F ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B := fun x hx =>
      hcov (hQU (hFQ hx)).1
    by_cases hFa : F ⊆ PaintingOrDrawing.underlying A
    · exact hA F hFa hF
    · refine hno F hF fun x hx => ?_
      have hFB : F ⊆ PaintingOrDrawing.underlying B := by
        obtain ⟨a, ha, haA⟩ := not_subset.mp hFa
        by_contra hFb
        obtain ⟨c, hc, hcB⟩ := not_subset.mp hFb
        obtain ⟨z, hzF, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hF.isPreconnected _ _ hAc hBc hFA
          ⟨c, hc, (hFA hc).resolve_right hcB⟩ ⟨a, ha, (hFA ha).resolve_left haA⟩
        exact (hQU (hFQ hzF)).2 (hint ⟨hz₁, hz₂⟩)
      refine ⟨hFB hx, fun hxA => ?_⟩
      exact (hQU (hFQ hx)).2 (hint ⟨hxA, hFB hx⟩)
  refine not_flat_compl_disc hS hns hΔ (fun x hx => ?_) hfl
  have hxQ : x ∉ Q := fun h => hx (hQΔ h)
  by_cases hxU : x ∈ Γ.U
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hQc' ⟨hxU, hxQ⟩)
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hxs⟩)
  · obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
    exact Or.inl (mem_iUnion₂.mpr ⟨r, hr, hxr⟩)

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- The data that `RadialDrawing.exists_full` gives: `sk(Γ)` in `Σ̂`, and a radial drawing of it
that extends `Γ*`. -/
structure TangleDatum.SkData (D : TangleDatum cap χ) (H G₃ : Drawing Shat) : Prop where
  sk : IsSkHat cap D.P.Γ H
  pre : PreRad (PaintingOrDrawing.drawing H) G₃
  max : RadMax (PaintingOrDrawing.drawing H) G₃
  sub : D.rad.G.IsSubdrawing G₃
  spoke : ∀ e ∈ G₃.E, ∀ r ∈ D.P.Γ.hatRegions cap, e ⊆ r → e ∈ D.rad.G.E

/-- Two corners of a disc edge are joined by a class with a path in a region of `Γ` and a path in
the closed cell. -/
theorem IsSkHat.exists_class_of_corners {Γ : Painting S} {H : Drawing Shat} (hH : IsSkHat cap Γ H)
  (hS : IsSurface S) {c : Set S} (hc : c ∈ Γ.E) (h3 : (tilde c).ncard = 3)
    {a b : S} (ha : a ∈ tilde c) (hb : b ∈ tilde c) (hab : a ≠ b) :
    ∃ g : Cl (cap.emb a) (cap.emb b), Arw ((⋃ r ∈ Γ.hatRegions cap, r) ∪ {cap.emb a, cap.emb b}) g
      ∧ Arw (cap.emb '' closure c) g := by
  have hT := cap.isClosedSurface
  obtain ⟨f, hf, haf, hbf⟩ := Γ.exists_side_between hc h3 ha hb hab
  obtain ⟨r, hr, hfr⟩ := hH.exists_hatRegion_side hS hf h3
  have hfm := hf.mem
  obtain ⟨u, w, huw, ht, htV, hline⟩ := Γ.sk_line hfm
  have haV : a ∈ Γ.V := Γ.tilde_subset_V hc ha
  have hbV : b ∈ Γ.V := Γ.tilde_subset_V hc hb
  have hta : a ∈ tilde f := ⟨haf, fun h => (hfm.2.1 h).2 haV⟩
  have htb : b ∈ tilde f := ⟨hbf, fun h => (hfm.2.1 h).2 hbV⟩
  have hL : IsLineWithEnds (closure f) a b := by
    rw [ht] at hta htb
    rcases hta with rfl | rfl <;> rcases htb with rfl | rfl
    · exact absurd rfl hab
    · exact hline
    · exact hline.symm
    · exact absurd rfl hab
  have hcle : closure (cap.emb '' f) = cap.emb '' closure f := (cap.isClosedEmbedding
    hS).closure_image_eq f
  have hL' : IsLineWithEnds (closure (cap.emb '' f)) (cap.emb a) (cap.emb b)
    := hcle ▸ hL.map_of_embedding cap.isEmbedding
  have hfE : cap.emb '' f ∈ H.E := (hH.edge_iff hS).mpr ⟨f, hfm, rfl⟩
  have hV : closure (cap.emb '' f) ∩ H.V = {cap.emb a, cap.emb b} := by
    rw [hcle, hH.hV]
    ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
      obtain rfl := cap.isEmbedding.injective hpq
      have : q ∈ tilde f := ⟨hp, fun h => (hfm.2.1 h).2 hq⟩
      rw [ht] at this hta htb
      rcases hta with rfl | rfl <;> rcases htb with rfl | rfl <;>
        rcases this with rfl | rfl <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨mem_image_of_mem _ haf, mem_image_of_mem _ haV⟩
      · exact ⟨mem_image_of_mem _ hbf, mem_image_of_mem _ hbV⟩
  obtain ⟨g, hg, hq⟩ := exists_class_beside_edge hT H hfE hL' (cap.isEmbedding.injective.ne hab) hV
    (hH.hatRegion_mem_R hS hr) hfr
  obtain ⟨q, hq'⟩ := IsLineWithEnds.exists_path hL'
  refine ⟨g, hg.mono (union_subset_union_left _ fun x hx => mem_iUnion₂.mpr ⟨r, hr, hx⟩), ?_⟩
  rw [← hq q hq']
  refine Arw.of_path q fun t => ?_
  have h₁ := hq' t
  rw [hcle] at h₁
  refine image_mono (closure_minimal ?_ isClosed_closure) h₁
  rcases hf.2 with ⟨h2, -⟩ | ⟨-, hfb⟩
  · exact absurd h3 (by omega)
  · exact (hfb.2.1).trans (sdiff_subset.trans ((Γ.isDisc_of_three hc h3).1.isClosed.closure_eq ▸
      Surface.discBd_subset _))

/-- **The regions of `sk(Γ)` and small open sets around a few vertices form a flat set.** -/
theorem TangleDatum.exists_flat_skeleton (D : TangleDatum cap χ) {H G₃ : Drawing Shat}
  (hd : D.SkData H G₃) {S₀ : Set Shat} (hS₀ : S₀ ⊆ H.V) (hord : S₀.ncard < D.rep) :
    ∃ D' : Shat → Set Shat, (∀ s ∈ S₀, IsOpen (D' s)) ∧ (∀ s ∈ S₀, s ∈ D' s) ∧ Flat
      ((⋃ r ∈ H.R, r) ∪ ⋃ s ∈ S₀, D' s) := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have h3 := D.P.fits.internally_three_connected
  set Γ := D.P.Γ with hΓ
  have hf : S₀.Finite := H.finite_V.subset hS₀
  have hE : H.E.Nonempty := hd.sk.E_nonempty hS h3.1
  have hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing G₃ := ⟨hd.pre.1, hd.pre.2, hd.max⟩
  have hRH : Γ.hatRegions cap ⊆ H.R := fun r hr => hd.sk.hatRegion_mem_R hS hr
  have hS₀G : S₀ ⊆ D.rad.G.V := fun s hs => by
    have := hS₀ hs
    rw [hd.sk.hV] at this
    exact D.rad.isPreRadial.2.1 this
  obtain ⟨D₀, hD₀o, hsD₀, hfl⟩ := exists_flat_regions_of_sub (Γ := H) (Γ' := G₃) (θ
    := D.rep) hT hE hrad (by omega) hd.sub hRH hd.spoke
    (fun r hr c hc hcV => by
      obtain ⟨w, ⟨-, -⟩, huniq⟩ := hd.pre.2.2.2.1 r (hRH hr)
      obtain ⟨w', ⟨hw'r, hw'V⟩, -⟩ := D.rad.isPreRadial.2.2.1 r hr
      have e : c = w' := (huniq c ⟨hc, hcV⟩).trans (huniq w' ⟨hw'r, hd.sub.1 hw'V⟩).symm
      exact e ▸ hw'V)
    (fun C hC hCs hl => by
      have hi := D.ins_spec ⟨hCs, hC⟩ hl
      exact isNullHomotopicOArcIn_of_subset_disc (IsCircuit.isOArc_U hC) (subset_univ _) hi.2.2.1
        (hi.2.2.2.1 ▸ Surface.discBd_subset _))
    hS₀ hS₀G hf hord
  let 𝒟 : Set (Set Shat) := (fun c => cap.emb '' closure c) '' {c ∈ Γ.E | (tilde c).ncard = 3}
  have hdisc : ∀ c ∈ Γ.E, (tilde c).ncard = 3 → IsClosedDisc (cap.emb '' closure c) ∧ discBd
    (cap.emb '' closure c) = cap.emb '' discBd (closure c) := fun c hc h3' =>
    isClosedDisc_image (Γ.isDisc_of_three hc h3').1 cap.isEmbedding
  have hcellU : ∀ c ∈ Γ.E, (tilde c).ncard = 3 → discBd (cap.emb '' closure c) ⊆ H.U
    := fun c hc h3' => by
    rw [(hdisc c hc h3').2, hd.sk.hU]
    exact image_mono fun w hw => Or.inr (mem_iUnion₂.mpr ⟨c, ⟨hc, h3'⟩, hw⟩)
  have hcl : ∀ c ∈ Γ.E, ∀ x ∈ closure c, x ∉ Γ.V → x ∈ c := fun c hc x hx hxV => by
    by_contra hn
    exact hxV (Γ.tilde_subset_V hc ⟨hx, hn⟩)
  have htilde : ∀ c ∈ Γ.E, ∀ x ∈ closure c, x ∈ Γ.V → x ∈ tilde c := fun c hc x hx hxV
    => ⟨hx, fun h => Γ.disjoint_V hc h hxV⟩
  have hint_c : ∀ c ∈ Γ.E, (tilde c).ncard = 3 → discInt (cap.emb '' closure c) ⊆ cap.emb '' c
    := fun c hc h3' => by
    rintro _ ⟨⟨x, hx, rfl⟩, hxb⟩
    refine mem_image_of_mem _ (hcl c hc x hx fun hxV => hxb ?_)
    rw [(hdisc c hc h3').2]
    exact mem_image_of_mem _ ((Γ.isDisc_of_three hc h3').2.1 (htilde c hc x hx hxV))
  have hRopen : IsOpen (⋃ r ∈ Γ.hatRegions cap, r) := isOpen_biUnion fun r hr => region_isOpen
    (hRH hr)
  have hsame : ∀ c ∈ Γ.E, ∀ c' ∈ Γ.E, ∀ x, x ∈ c → x ∈ c' → c = c' := fun c hc c' hc' x hx hx' => by
    exact arcComp_eq_of_mem hc hc' hx hx'
  have key : ∃ D' : Shat → Set Shat, (∀ s ∈ S₀, IsOpen (D' s)) ∧ (∀ s ∈ S₀, s ∈ D' s) ∧
      Flat (((⋃ r ∈ Γ.hatRegions cap, r) ∪ ⋃ s ∈ S₀, D' s) ∪ ⋃ Δ ∈ 𝒟, discInt Δ) := by
    refine exists_flat_with_cells (𝒟 := 𝒟) (V₀ := H.V) (S₀ := S₀) (R := ⋃ r ∈ Γ.hatRegions cap,
      r) (D := D₀) hT
      ((Γ.finite_edges.subset (sep_subset _ _)).image _) ?_ H.finite_V ?_ ?_ ?_ hRopen ?_ hD₀o hsD₀
        hfl ?_
    · rintro _ ⟨c, ⟨hc, h3'⟩, rfl⟩
      exact (hdisc c hc h3').1
    · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩ hne _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
      obtain rfl := cap.isEmbedding.injective hxy
      by_contra hn
      have hxV : y ∉ Γ.V := fun h => hn (hd.sk.hV ▸ mem_image_of_mem _ h)
      exact hne (by rw [hsame c hc c' hc' y (hcl c hc y hx hxV) (hcl c' hc' y hy hxV)])
    · rintro _ ⟨c, ⟨hc, h3₁⟩, rfl⟩ _ ⟨c', ⟨hc', h3₂⟩, rfl⟩ hne
      refine disjoint_left.mpr fun x hx hx' => ?_
      obtain ⟨y, hy, rfl⟩ := hint_c c hc h3₁ hx
      obtain ⟨y', hy', hyy⟩ := hint_c c' hc' h3₂ hx'
      obtain rfl := cap.isEmbedding.injective hyy
      exact hne (by rw [hsame c hc c' hc' y' hy hy'])
    · rintro _ ⟨c, ⟨hc, h3'⟩, rfl⟩ s hs ⟨x, hx, rfl⟩
      have hxV : x ∈ Γ.V := by
        have := hS₀ hs
        rw [hd.sk.hV] at this
        obtain ⟨y, hy, hyx⟩ := this
        exact cap.isEmbedding.injective hyx ▸ hy
      rw [(hdisc c hc h3').2]
      exact mem_image_of_mem _ ((Γ.isDisc_of_three hc h3').2.1 (htilde c hc x hx hxV))
    · rintro _ ⟨c, ⟨hc, h3'⟩, rfl⟩
      refine disjoint_left.mpr fun x hx hxc => ?_
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
      obtain ⟨y, hy, rfl⟩ := hint_c c hc h3' hxc
      obtain ⟨z, hz, rfl⟩ := id hr
      exact (connectedComponentIn_subset _ _ hxr) (mem_image_of_mem _ (hc.2.1 hy).1)
    · rintro _ ⟨c, ⟨hc, h3'⟩, rfl⟩ a ha b hb ⟨a₀, ha₀, rfl⟩ ⟨b₀, hb₀, rfl⟩ hab
      have hV : ∀ x, x ∈ closure c → cap.emb x ∈ S₀ → x ∈ Γ.V := fun x _ hx => by
        have := hS₀ hx
        rw [hd.sk.hV] at this
        obtain ⟨y, hy, hyx⟩ := this
        exact cap.isEmbedding.injective hyx ▸ hy
      exact hd.sk.exists_class_of_corners hS hc h3' (htilde c hc a₀ ha₀ (hV a₀ ha₀ ha))
        (htilde c hc b₀ hb₀ (hV b₀ hb₀ hb)) fun h => hab (h ▸ rfl)
  obtain ⟨D', hD'o, hsD', hfl'⟩ := key
  refine ⟨D', hD'o, hsD', hfl'.mono (union_subset (iUnion₂_subset fun r hr => ?_) fun x hx => .inl
    (.inr hx))⟩
  intro x hx
  rcases hd.sk.region_cases hS hr with hh | ⟨c, hc, h3', hrc⟩
  · exact .inl (.inl (mem_iUnion₂.mpr ⟨r, hh, hx⟩))
  · refine .inr (mem_iUnion₂.mpr ⟨_, ⟨c, ⟨hc, h3'⟩, rfl⟩, hrc hx, fun hb => ?_⟩)
    exact region_subset hr hx (hcellU c hc h3' hb)

/-- **`𝒯'` is respectful.** The paper states this as `rep(𝒯') = n + 1` in the proof of (15.2) (page
383). See the module docstring. -/
theorem TangleDatum.isRespectful_skTangle (D : TangleDatum cap χ) {H G₃ : Drawing Shat}
  (hd : D.SkData H G₃) {m : ℕ} (hm : 1 ≤ m) (hmr : m ≤ D.rep) (h3m : 3 * m < 2 * D.ord + 3) :
    (PaintingOrDrawing.drawing H).IsRespectful m (D.skTangle H m) := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hTg := D.isTangle_skTangle hd.sk hm h3m
  have hH := hd.sk
  by_cases hsp : IsSphere Shat
  · exact drawing_tangle_isRespectful_of_isSphere hT hsp H hTg
  refine ⟨inferInstance, fun F hF hN hk => ?_⟩
  obtain ⟨D₀, -, hsD₀, hfl⟩ := D.exists_flat_skeleton hd (S₀ := F ∩ H.V) inter_subset_right
    (hk.trans_le hmr)
  have hFK : F ⊆ (⋃ r ∈ H.R, r) ∪ ⋃ s ∈ F ∩ H.V, D₀ s := fun x hx => by
    by_cases hxU : x ∈ H.U
    · have hxs : x ∈ F ∩ H.V := ⟨hx, hN ⟨hx, hxU⟩⟩
      exact .inr (mem_iUnion₂.mpr ⟨x, hxs, hsD₀ x hxs⟩)
    · obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      exact .inl (mem_iUnion₂.mpr ⟨r, hr, hxr⟩)
  have hb : bd Shat = ∅ := eq_empty_of_forall_notMem fun x hx => hx (hT.2.2 x)
  obtain ⟨Δ, -, hΔ, hbF⟩ :=
    (epstein Shat univ F cap.isSurface inferInstance hF (subset_univ _) (by simp [hb])).1
      (null_of_flat hfl hF hFK)
  have hfr : frontier Δ = F := (IsClosedDisc.frontier_eq_discBd hT hΔ).trans hbF
  have hsub : subBd Δ = F := by rw [subBd_eq_frontier, hfr]
  have hsep : H.toHypergraph.IsSeparation ((PaintingOrDrawing.drawing H).inter Δ)
    ((PaintingOrDrawing.drawing H).interOutside Δ) :=
    isSeparation_inter (Γ := PaintingOrDrawing.drawing H) hΔ.isClosed (by rw [hfr]; exact hN)
  have hsord : ((PaintingOrDrawing.drawing H).inter Δ ∩ (PaintingOrDrawing.drawing H).interOutside
    Δ).vertexSet ⊆ F ∩ H.V := fun x hx => by
    have := inter_outside_subset (Γ := PaintingOrDrawing.drawing H) hx
    rwa [hfr] at this
  have hordle : separationOrder ((PaintingOrDrawing.drawing H).inter Δ)
    ((PaintingOrDrawing.drawing H).interOutside Δ) < m :=
    lt_of_le_of_lt (ncard_le_ncard hsord (H.finite_V.subset inter_subset_right)) hk
  refine ⟨Δ, hΔ, hsub, ?_⟩
  rcases hTg.axiom1 hsep hordle with h | h
  · exact h
  exfalso
  obtain ⟨-, -, q, hq, e₁, e₂⟩ := h
  simp only at e₁ e₂
  set Ai := (PaintingOrDrawing.drawing H).inter Δ with hAi0
  set Bo := (PaintingOrDrawing.drawing H).interOutside Δ with hBo0
  have hinj := cap.isEmbedding.injective
  have hqsep := D.isTangle.isSeparation (A := q.1) (B := q.2) hq
  have hqord : separationOrder q.1 q.2 < D.rep := by
    have e : cap.emb '' (q.1 ∩ q.2).vertexSet = (Ai ∩ Bo).vertexSet := by
      change cap.emb '' (q.1.vertexSet ∩ q.2.vertexSet) = Ai.vertexSet ∩ Bo.vertexSet
      rw [image_inter hinj, e₁, e₂, Set.inter_comm]
    have h₁ : (q.1 ∩ q.2).vertexSet.ncard = (Ai ∩ Bo).vertexSet.ncard := by
      rw [← e, ncard_image_of_injective _ hinj]
    change (q.1 ∩ q.2).vertexSet.ncard < D.rep
    rw [h₁]
    exact hordle.trans_le hmr
  obtain ⟨N, hNG, hshort, -, hcov⟩ := D.exists_inside_cover (A := q.1) (B := q.2) hq hqord
  have hins : ∀ C : Drawing Shat, C.IsCircuit → C.IsSubdrawing N → IsInsOf D.rad D.ord D.𝒯 C
    (D.ins C) := fun C hC hCs =>
    D.ins_spec ⟨hCs.trans hNG, hC⟩ (hshort C hC hCs)
  obtain ⟨D₁, hD₁, hND₁⟩ := exists_disc_of_circuits hT N fun C hC hCs => by
    have hi := hins C hC hCs
    exact isNullHomotopicOArcIn_of_subset_disc (IsCircuit.isOArc_U hC) (subset_univ _) hi.2.2.1
      (hi.2.2.2.1 ▸ Surface.discBd_subset _)
  have hcov' : ∀ e ∈ q.1.edgeSet, cap.emb '' e ⊆ D₁ := fun e he => by
    obtain ⟨F', hF', hF's, hin⟩ := hcov e he
    have hi := hins F' hF' hF's
    exact hin.trans (disc_subset_of_bd hT hsp hi.2.2.1 hD₁ (by
      rw [hi.2.2.2.1]
      exact hF's.U_subset.trans hND₁))
  obtain ⟨F', hF', hF's, hnn⟩ := exists_oArc_of_flat hT hsp H hsep
    (D.exists_flat_skeleton hd (fun x hx => hsep.left_le.vertexSet_subset hx.1)
      (lt_of_lt_of_le hordle hmr))
    (fun F₂ hF₂ hO => by
      refine isNullHomotopicOArcIn_of_subset_disc hO (subset_univ _) hΔ fun x hx => ?_
      rcases hF₂ hx with hxV | ⟨e, he, hxe⟩
      · exact hxV.2
      · exact he.2 hxe)
  apply hnn
  have hF'U : F' ⊆ H.U := fun x hx => by
    rcases hF's hx |>.1 with hxV | ⟨e, he, hxe⟩
    · exact H.V_subset_U (hsep.right_le.vertexSet_subset hxV)
    · exact (he.1.2.1 hxe).1
  obtain ⟨C, hC, hCs, hCU⟩ := exists_circuit_of_oArc hF' hF'U
  refine isNullHomotopicOArcIn_of_subset_disc hF' (subset_univ _) hD₁ ?_
  refine oArc_subset_of_edges hF' hD₁.isClosed C.finite_V (E₀ := C.E) (fun e he => ?_) fun x hx
    => ?_
  · obtain ⟨f₀, hf₀, rfl⟩ := (hH.edge_iff hS).mp (hCs.2 he)
    obtain ⟨u, w, -, ht, htV, -⟩ := D.P.Γ.sk_line hf₀
    have hu : u ∈ tilde f₀ := ht ▸ .inl rfl
    have huV : u ∈ D.P.Γ.V := htV hu
    have huF : cap.emb u ∈ F' := by
      rw [← hCU]
      refine C.closure_subset_U he ?_
      rw [(cap.isClosedEmbedding hS).closure_image_eq f₀]
      exact mem_image_of_mem _ hu.1
    have huH : cap.emb u ∈ H.V := hH.hV ▸ mem_image_of_mem _ huV
    have hnA : cap.emb u ∉ Ai.vertexSet := fun h => (hF's huF).2 (.inl h)
    have hnB : u ∉ q.2.vertexSet := fun h => hnA (e₂ ▸ mem_image_of_mem _ h)
    obtain ⟨c, hc, hf₀c, huc⟩ : ∃ c ∈ D.P.Γ.E, f₀ ⊆ c ∧ u ∈ tilde c := by
      rcases D.P.Γ.sk_cases hf₀ with ⟨h₁, -⟩ | ⟨c, hc, -, h₁, -⟩
      · exact ⟨f₀, h₁, Subset.rfl, hu⟩
      · exact ⟨c, hc, h₁, closure_mono h₁ hu.1, fun h => D.P.Γ.disjoint_V hc h huV⟩
    rcases edge_cases hqsep hc with ⟨hcA, -⟩ | ⟨-, hcB⟩
    · exact (image_mono hf₀c).trans (hcov' c hcA)
    · exfalso
      apply hnB
      have hinc : u ∈ q.2.ends c := by
        rw [← hqsep.right_le.ends_eq c hcB]
        exact ⟨hc, huV, huc⟩
      exact q.2.vertex_mem_of_inc hinc
  · by_cases hxV : x ∈ C.V
    · exact .inl hxV
    · obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem (hCU ▸ hx) hxV
      exact .inr ⟨e, he, hxe⟩

end GraphMinor.GM19
