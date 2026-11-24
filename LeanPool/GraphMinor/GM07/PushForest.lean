/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ForestQuotient
public import LeanPool.GraphMinor.GM07.ForestFlat
public import LeanPool.GraphMinor.GM07.Section3
public import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
public import LeanPool.GraphMinor.GM07.DiscPlace

/-!
# The image of a forest across a cut

This file proves the second part of (4.5) of Graph Minors VII (page 223). Let `Γ` be the preimage of
a forest `H`, and let `G` be a forest homotopic to `Γ`, both in the surface obtained by cutting. We
show that the image of `G` is a forest homotopic to `H` (`exists_image_forest`).

`G` and `Γ` have the same vertices on the boundary, and join the same pairs of them. If two ends of
an edge of `G` had the same image, then the path of `Γ` between them would map to a closed walk of
`H` (`push_ne`). So the image of `G` is a drawing. It is a forest by `quotient_forest`.

For the homotopy, the steps are between boundary vertices of `G`. A walk of the image of `G`, or of
`H`, breaks at the vertices with more than one preimage, and these all lie on the boundary of the
cut surface (`chain_of_walk`). Each piece joins two boundary vertices of `G`, and `G` and `Γ` give
homotopic curves across it. Since both forests are flat by `isFlat_forest`, any curves in them with
the right ends can be used.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- The points of `X` joined to `v` by a walk of `G`. -/
def classOf (G : Drawing S') (X : Set S') (v : S') : Set S' := {y | y ∈ X ∧ Nonempty
  (GraphWalk G.toGraph v y)}

theorem classOf_eq_of_walk {G : Drawing S'} {X : Set S'} {v w : S'} (W : GraphWalk G.toGraph v w) :
  classOf G X v = classOf G X w := by
  ext y
  constructor
  · rintro ⟨hy, ⟨W'⟩⟩
    exact ⟨hy, ⟨W.reverse.append W'⟩⟩
  · rintro ⟨hy, ⟨W'⟩⟩
    exact ⟨hy, ⟨W.append W'⟩⟩

/-- Homotopic forests have the same classes on their common boundary vertices. -/
theorem classOf_eq_of_homotopic {G G' : Drawing S'} (h : ForestsHomotopic G G') {x : S'}
  (hx : x ∈ G.V ∩ bd S') : classOf G (G.V ∩ bd S') x = classOf G' (G.V ∩ bd S') x := by
  classical
  have hx' : x ∈ G'.V := (show x ∈ G'.V ∩ bd S' by rw [← h.2.2.2.2.1]; exact hx).1
  ext y
  constructor
  · rintro ⟨hy, ⟨W⟩⟩
    by_cases hxy : x = y
    · subst hxy
      exact ⟨hy, ⟨.nil hx'⟩⟩
    · obtain ⟨W', hs, -⟩ := GraphWalk.exists_isSimple W
      obtain ⟨P, -⟩ := ((h.2.2.2.2.2 x hx y hy hxy).1.mp ⟨W', hs⟩)
      exact ⟨hy, ⟨P⟩⟩
  · rintro ⟨hy, ⟨W⟩⟩
    by_cases hxy : x = y
    · subst hxy
      exact ⟨hy, ⟨.nil hx.1⟩⟩
    · obtain ⟨W', hs, -⟩ := GraphWalk.exists_isSimple W
      obtain ⟨P, -⟩ := ((h.2.2.2.2.2 x hx y hy hxy).1.mpr ⟨W', hs⟩)
      exact ⟨hy, ⟨P⟩⟩

/-- Two points with the same image both lie on the boundary of the cut surface. -/
theorem IsCutAlongGraph.bd_of_eq {J : Drawing S} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ) {p q :
  S'} (h : φ p = φ q) (hne : p ≠ q) : p ∈ bd S' ∧ q ∈ bd S' := by
  constructor
  · by_contra hp
    exact hne (hJ.interior_inj p hp q h)
  · by_contra hq
    exact hne (hJ.interior_inj q hq p h.symm).symm

theorem IsCutAlongGraph.bd_of_bd {J : Drawing S} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ) {p :
  S'} (h : φ p ∈ bd S) : p ∈ bd S' := by
  rw [← hJ.preimage_bd_union_U]
  exact .inl h

/-- The two ends of an edge of a forest. -/
theorem exists_link_of_forest {G : Drawing S'} (hF : IsGraphForest G.toGraph) {e : Set S'}
  (he : e ∈ G.E) : ∃ p q, G.toGraph.IsLink e p q ∧ p ≠ q ∧ IsLineWithEnds (closure e) p q := by
  obtain ⟨u, v, huv, hcap, hl⟩ := edge_line_of_forest hF he
  have hu : u ∈ closure e ∩ G.V := by rw [hcap]; exact .inl rfl
  have hv : v ∈ closure e ∩ G.V := by rw [hcap]; exact .inr rfl
  exact ⟨u, v, ⟨he, hu.2, hv.2, hcap⟩, huv, hl⟩

theorem trail_length_of_eq {α β : Type*} {G : Graph α β} (hG : IsGraphForest G) {a b : α} (hab : a
  = b) (W : GraphWalk G a b) (hW : W.edges.Nodup) : W.length = 0 := by
  subst hab
  exact length_eq_zero_of_trail hG _ _ W rfl hW

theorem length_pos_of_ne {α β : Type*} {G : Graph α β} {a b : α} (hab : a ≠ b)
  (W : GraphWalk G a b) : 0 < W.length := by
  cases W with
  | nil _ => exact (hab rfl).elim
  | cons _ _ => exact List.length_pos_iff.mpr (by simp [GraphWalk.edges])

/-- **The ends of an edge have different images** (first part of the proof of (4.5), page 223, for a
sequence with `k = 1`). -/
theorem push_ne {J H : Drawing S} {G Γ : Drawing S'} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ)
  (hH : IsGraphForest H.toGraph) (hV : Γ.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ Γ.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ (closure e'))
      (hG : ForestsHomotopic G Γ) {e : Set S'} {p q : S'} (hl : G.toGraph.IsLink e p q)
        (hpq : p ≠ q) : φ p ≠ φ q := by
  intro h
  obtain ⟨hp, hq⟩ := hJ.bd_of_eq h hpq
  have hs : (GraphWalk.cons hl (.nil hl.2.2.1)).IsSimple := by
    simpa [GraphWalk.IsSimple, GraphWalk.support] using hpq
  obtain ⟨Q, hQ⟩ := (hG.2.2.2.2.2 p ⟨hl.2.1, hp⟩ q ⟨hl.2.2.1, hq⟩ hpq).1.mp ⟨_, hs⟩
  obtain ⟨W₀, hW₀, hnd⟩ := pull_walk hJ.quotientMap.surjective hV hE Q
  have h0 := trail_length_of_eq hH h W₀ (hnd (nodup_edges_of_simple Q hQ))
  have h1 : W₀.length = Q.length := by
    change W₀.edges.length = Q.edges.length
    rw [hW₀, List.length_map]
  have h2 := length_pos_of_ne hpq Q
  omega

section Image

variable [CompactSpace S'] [T2Space S'] [T2Space S]

omit [T2Space S'] in
theorem IsCutAlongGraph.closure_image {J : Drawing S} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ)
  (A : Set S') : closure (φ '' A) = φ '' closure A :=
  hJ.quotientMap.continuous.isClosedMap.closure_image_eq_of_continuous hJ.quotientMap.continuous A

omit [CompactSpace S'] [T2Space S'] [T2Space S] in
/-- A point of the closure of an edge of a proper drawing, off the boundary, has only itself over
its image. So `φ` keeps vertices apart from the rest of the edge. -/
theorem push_injOn {J : Drawing S} {G : Drawing S'} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ)
  (hprop : G.IsProper) {e : Set S'} {p q : S'} (hl : G.toGraph.IsLink e p q)
    (hne : φ p ≠ φ q) : InjOn φ (closure e) := by
  intro a ha b hb hab
  by_contra hd
  obtain ⟨h1, h2⟩ := hJ.bd_of_eq hab hd
  have ha' : a ∈ closure e ∩ G.V := ⟨ha, hprop ⟨h1, G.closure_subset_U hl.1 ha⟩⟩
  have hb' : b ∈ closure e ∩ G.V := ⟨hb, hprop ⟨h2, G.closure_subset_U hl.1 hb⟩⟩
  rw [hl.2.2.2] at ha' hb'
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact hd rfl
  · exact hne hab
  · exact hne hab.symm
  · exact hd rfl

omit [CompactSpace S'] [T2Space S'] [T2Space S] in
theorem push_ends {J : Drawing S} {G : Drawing S'} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ)
  (hprop : G.IsProper) {e : Set S'} {p q : S'} (hl : G.toGraph.IsLink e p q) : φ '' closure e ∩ φ
    '' G.V = {φ p, φ q} := by
  ext z
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
    have ha' : a ∈ closure e ∩ G.V := by
      refine ⟨ha, ?_⟩
      by_cases hd : b = a
      · exact hd ▸ hb
      · exact hprop ⟨(hJ.bd_of_eq hab hd).2, G.closure_subset_U hl.1 ha⟩
    rw [hl.2.2.2] at ha'
    rcases ha' with rfl | h
    · exact .inl rfl
    · exact .inr (congrArg φ (mem_singleton_iff.mp h))
  · have hp : p ∈ closure e ∩ G.V := by rw [hl.2.2.2]; exact .inl rfl
    have hq : q ∈ closure e ∩ G.V := by rw [hl.2.2.2]; exact .inr rfl
    rintro (rfl | h)
    · exact ⟨mem_image_of_mem φ hp.1, mem_image_of_mem φ hp.2⟩
    · obtain rfl : z = φ q := h
      exact ⟨mem_image_of_mem φ hq.1, mem_image_of_mem φ hq.2⟩

omit [CompactSpace S'] [T2Space S'] [T2Space S] in
/-- The closures of two edges of a proper drawing meet in vertices over a cut. -/
theorem push_meet {J : Drawing S} {G : Drawing S'} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ)
  (hprop : G.IsProper) {e f : Set S'} (he : e ∈ G.E) (hf : f ∈ G.E) (hef : e ≠ f) : φ '' closure e
    ∩ φ '' closure f ⊆ φ '' G.V := by
  rintro _ ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  by_cases hd : a = b
  · subst hd
    by_contra hz
    have haV : a ∉ G.V := fun h => hz (mem_image_of_mem φ h)
    have h1 : a ∈ e := by rw [← G.closure_diff_V he]; exact ⟨ha, haV⟩
    have h2 : a ∈ f := by rw [← G.closure_diff_V hf]; exact ⟨hb, haV⟩
    exact hef (arcComponent_eq he hf h1 h2)
  · exact mem_image_of_mem φ (hprop ⟨(hJ.bd_of_eq hab.symm hd).1, G.closure_subset_U he ha⟩)

omit [CompactSpace S'] [T2Space S'] in
/-- **The image of a forest is a drawing**, when the ends of each edge have different images. -/
theorem exists_image_drawing {J : Drawing S} {G : Drawing S'} {φ : S' → S}
  (hJ : IsCutAlongGraph J S' φ) (hprop : G.IsProper) (hF : IsGraphForest G.toGraph)
    (hne : ∀ e p q, G.toGraph.IsLink e p q → φ p ≠ φ q) :
    ∃ P : Drawing S, P.U = φ '' G.U ∧ P.V = φ '' G.V ∧ P.E = (φ '' ·) '' G.E := by
  classical
  have hc := hJ.quotientMap.continuous
  have hch : ∀ e : G.E, ∃ p q, G.toGraph.IsLink e.1 p q ∧ p ≠ q ∧ IsLineWithEnds (closure e.1) p q
    := fun e => exists_link_of_forest hF e.2
  choose p q hl hpq hline using hch
  have hfin : (univ : Set G.E).Finite := by
    have : Finite G.E := (show G.E.Finite from G.finite_edges).to_subtype
    exact toFinite _
  have hL : ∀ i : G.E, IsLineWithEnds (φ '' closure i.1) (φ (p i)) (φ (q i)) := fun i => by
    obtain ⟨f, h0, h1⟩ := hline i
    have hinj := push_injOn hJ hprop (hl i) (hne _ _ _ (hl i))
    have ha : IsArcMap fun t => φ (f t).1 := ⟨by fun_prop, fun x y hxy => f.injective (Subtype.ext
      (hinj (f x).2 (f y).2 hxy))⟩
    have hr := isLineWithEnds_range_of_arc ha
    have hrange : range (fun t => φ (f t).1) = φ '' closure i.1 := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact mem_image_of_mem φ (f t).2
      · rintro ⟨a, ha, rfl⟩
        exact ⟨f.symm ⟨a, ha⟩, by simp⟩
    rw [hrange] at hr
    simpa [h0, h1] using hr
  obtain ⟨P, hU, hV, hE⟩ := GM12.exists_drawing_of_finite_lines (G.finite_V.image φ) hfin
    (fun i : G.E => φ '' closure i.1) (fun i => φ (p i)) (fun i => φ (q i)) (fun i _ => hL i)
      (fun i _ => hne _ _ _ (hl i))
    (fun i _ => push_ends hJ hprop (hl i)) (fun i _ j _ hij => push_meet hJ hprop i.2 j.2 fun h
      => hij (Subtype.ext h))
  refine ⟨P, ?_, hV, ?_⟩
  · rw [hU, G.U_eq, image_union, image_iUnion₂]
    congr 1
    ext z
    simp
  · have key : ∀ i : G.E, φ '' closure i.1 \ {φ (p i), φ (q i)} = φ '' i.1 := fun i => by
      ext w
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hw⟩
        refine ⟨a, ?_, rfl⟩
        rw [← G.closure_diff_V i.2]
        refine ⟨ha, fun haV => hw ?_⟩
        have : φ a ∈ φ '' closure i.1 ∩ φ '' G.V := ⟨mem_image_of_mem φ ha, mem_image_of_mem φ haV⟩
        rwa [push_ends hJ hprop (hl i)] at this
      · rintro ⟨a, ha, rfl⟩
        have ha' : a ∈ closure i.1 \ G.V := by rw [G.closure_diff_V i.2]; exact ha
        have hinj := push_injOn hJ hprop (hl i) (hne _ _ _ (hl i))
        have hp : p i ∈ closure i.1 ∩ G.V := by rw [(hl i).2.2.2]; exact .inl rfl
        have hq : q i ∈ closure i.1 ∩ G.V := by rw [(hl i).2.2.2]; exact .inr rfl
        refine ⟨mem_image_of_mem φ ha'.1, ?_⟩
        rintro (h | h)
        · exact ha'.2 (hinj ha'.1 hp.1 h ▸ hp.2)
        · exact ha'.2 (hinj ha'.1 hq.1 h ▸ hq.2)
    rw [hE]
    ext z
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨i.1, i.2, (key i).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, mem_univ _, key ⟨e, he⟩⟩

omit [T2Space S'] in
/-- An edge of `G` maps to an edge of the image, with the images of its ends. -/
theorem push_link {J : Drawing S} {G : Drawing S'} {P : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph J S' φ) (hprop : G.IsProper) (hV : P.V = φ '' G.V) (hE : P.E =
    (φ '' ·) '' G.E) {e : Set S'} {p q : S'} (hl : G.toGraph.IsLink e p q) :
    P.toGraph.IsLink (φ '' e) (φ p) (φ q) := by
  refine ⟨hE ▸ mem_image_of_mem _ hl.1, ?_, ?_, ?_⟩
  · exact hV ▸ mem_image_of_mem φ hl.2.1
  · exact hV ▸ mem_image_of_mem φ hl.2.2.1
  · rw [hJ.closure_image, hV]
    exact push_ends hJ hprop hl

omit [T2Space S'] in
/-- A walk of `G` maps to a walk of the image. -/
theorem push_walk {J : Drawing S} {G : Drawing S'} {P : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph J S' φ) (hprop : G.IsProper) (hV : P.V = φ '' G.V) (hE : P.E =
    (φ '' ·) '' G.E) {a b : S'} (W : GraphWalk G.toGraph a b) :
    Nonempty (GraphWalk P.toGraph (φ a) (φ b)) := by
  induction W with
  | @nil v h =>
    have h' : φ v ∈ P.V := hV ▸ mem_image_of_mem φ h
    exact ⟨.nil h'⟩
  | cons hl r ih =>
    obtain ⟨W⟩ := ih
    exact ⟨.cons (push_link hJ hprop hV hE hl) W⟩

omit [T2Space S'] in
/-- An edge of the image comes from an edge of `G`. -/
theorem push_lift {J : Drawing S} {G : Drawing S'} {P : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph J S' φ) (hprop : G.IsProper) (hF : IsGraphForest G.toGraph) (hV : P.V
    = φ '' G.V) (hE : P.E = (φ '' ·) '' G.E) {e : Set S} {a b : S}
    (hl : P.toGraph.IsLink e a b) : ∃ e' p q, G.toGraph.IsLink e' p q ∧ φ p = a ∧ φ q = b ∧ φ '' e'
      = e := by
  obtain ⟨e', he', rfl⟩ : e ∈ (φ '' ·) '' G.E := hE ▸ hl.1
  obtain ⟨p, q, hlink, -, -⟩ := exists_link_of_forest hF he'
  have h2 := hl.2.2.2
  rw [(push_link hJ hprop hV hE hlink).2.2.2] at h2
  rcases pair_eq_pair_iff.mp h2 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact ⟨e', p, q, hlink, h, h', rfl⟩
  · exact ⟨e', q, p, ⟨hlink.1, hlink.2.2.1, hlink.2.1, by rw [hlink.2.2.2, pair_comm]⟩, h', h, rfl⟩

/-- The class of points of `X` reached from an end of the edge over `e`. -/
def edgeClass (Γ : Drawing S') (X : Set S') (φ : S' → S) (e : Set S) : Set S' :=
  {y | y ∈ X ∧ ∃ z ∈ Γ.V, z ∈ closure (φ ⁻¹' e) ∧ Nonempty (GraphWalk Γ.toGraph z y)}

omit [TopologicalSpace S] [CompactSpace S'] [T2Space S'] [T2Space S] in
theorem edgeClass_eq {Γ : Drawing S'} {X : Set S'} {φ : S' → S} (hF : IsGraphForest Γ.toGraph) {e'
  : Set S'} (he' : e' ∈ Γ.E) (hpre : φ ⁻¹' (φ '' e') = e') {z : S'} (hz : z ∈ closure e')
    (hzV : z ∈ Γ.V) :
    edgeClass Γ X φ (φ '' e') = classOf Γ X z := by
  ext y
  constructor
  · rintro ⟨hy, z', hz'V, hz'c, ⟨W⟩⟩
    rw [hpre] at hz'c
    obtain ⟨p, q, hl, -, -⟩ := exists_link_of_forest hF he'
    have h1 : z ∈ closure e' ∩ Γ.V := ⟨hz, hzV⟩
    have h2 : z' ∈ closure e' ∩ Γ.V := ⟨hz'c, hz'V⟩
    have hpq : Nonempty (GraphWalk Γ.toGraph p q) := ⟨.cons hl (.nil hl.2.2.1)⟩
    obtain ⟨Wpq⟩ := hpq
    rw [hl.2.2.2] at h1 h2
    refine ⟨hy, ?_⟩
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact ⟨W⟩
    · exact ⟨Wpq.append W⟩
    · exact ⟨Wpq.reverse.append W⟩
    · exact ⟨W⟩
  · rintro ⟨hy, ⟨W⟩⟩
    exact ⟨hy, z, hzV, hpre.symm ▸ hz, ⟨W⟩⟩

omit [T2Space S'] in
/-- **The image is a forest** (second paragraph of the proof of (4.5), page 223). The paper's
sequence `P'₁, ..., P'ₖ` with `k` minimum becomes a circuit of the quotient graph, handled by
`quotient_forest`. -/
theorem push_forest {J H P : Drawing S} {G Γ : Drawing S'} {φ : S' → S}
  (hJ : IsCutAlongGraph J S' φ) (hH : IsGraphForest H.toGraph) (hV : Γ.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ Γ.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ (closure e'))
      (hG : ForestsHomotopic G Γ) (hPV : P.V = φ '' G.V) (hPE : P.E =
        (φ '' ·) '' G.E) : IsGraphForest P.toGraph := by
  classical
  have hsurj := hJ.quotientMap.surjective
  have hΓ : IsGraphForest Γ.toGraph := hG.2.2.2.1
  have hbd := hG.2.2.2.2.1
  refine quotient_forest (f := φ) (c := classOf G (G.V ∩ bd S')) (X := G.V ∩ bd S') (ι :=
    (φ '' ·)) hG.2.2.1 ?_ (fun e p q hl => classOf_eq_of_walk (.cons hl (.nil hl.2.2.1)))
      (fun e a b hl => push_lift hJ hG.1 hG.2.2.1 hPV hPE hl)
    (fun p hp q hq h hne => ⟨⟨hp, (hJ.bd_of_eq h hne).1⟩, ⟨hq, (hJ.bd_of_eq h hne).2⟩⟩)
  refine classGraph_forest (t := edgeClass Γ (G.V ∩ bd S') φ) hH (fun x hx
    => ?_) fun x hx y hy hc hxy => ?_
  · have h1 : x ∈ Γ.V ∩ bd S' := hbd ▸ hx
    have h2 : x ∈ Γ.V := h1.1
    rw [hV] at h2
    exact h2
  · have hyc : y ∈ classOf G (G.V ∩ bd S') y := ⟨hy, ⟨.nil hy.1⟩⟩
    rw [← hc] at hyc
    obtain ⟨-, ⟨W⟩⟩ := hyc
    obtain ⟨W', hs, -⟩ := GraphWalk.exists_isSimple W
    obtain ⟨Q, hQ⟩ := (hG.2.2.2.2.2 x hx y hy hxy).1.mp ⟨W', hs⟩
    obtain ⟨W₀, hW₀, hnd⟩ := pull_walk hsurj hV hE Q
    refine ⟨W₀, ?_, hnd (nodup_edges_of_simple Q hQ), fun e he => ?_⟩
    · have h1 : W₀.length = Q.length := by
        change W₀.edges.length = Q.edges.length
        rw [hW₀, List.length_map]
      have h2 := length_pos_of_ne hxy Q
      omega
    · rw [hW₀] at he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      have he'E := mem_E_of_mem_edges Q he'
      obtain ⟨p, q, hl, -, -⟩ := exists_link_of_forest hΓ he'E
      have hpc : p ∈ closure e' ∩ Γ.V := by rw [hl.2.2.2]; exact .inl rfl
      obtain ⟨Q', -, -⟩ := GraphWalk.exists_prefix Q hQ (mem_support_of_mem_closure Q he' hpc.1
        hpc.2)
      have hpre : φ ⁻¹' (φ '' e') = e' := by
        obtain ⟨e₀, -, rfl, -, -⟩ := hE e' he'E
        rw [image_preimage_eq _ hsurj]
      rw [edgeClass_eq hΓ he'E hpre hpc.1 hpc.2, ← classOf_eq_of_walk Q',
        classOf_eq_of_homotopic hG hx]

omit [CompactSpace S'] [T2Space S'] [T2Space S] in
/-- An edge of `H` comes from an edge of `φ⁻¹(H)`. -/
theorem pull_lift {H : Drawing S} {Γ : Drawing S'} {φ : S' → S} (hs : Function.Surjective φ)
  (hF : IsGraphForest Γ.toGraph) (hU : Γ.U = φ ⁻¹' H.U) (hV : Γ.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ Γ.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ
      (closure e')) {e : Set S} {a b : S} (hl : H.toGraph.IsLink e a b) :
    ∃ e' p q, Γ.toGraph.IsLink e' p q ∧ φ p = a ∧ φ q = b := by
  have he := hl.1
  obtain ⟨z, hz⟩ := he.1
  have hzU := he.2.1 hz
  obtain ⟨z', rfl⟩ := hs z
  obtain ⟨e', he', hz'⟩ := exists_edge_of_mem (G := Γ) (z := z')
    (by rw [hU]; exact hzU.1) (by rw [hV]; exact hzU.2)
  obtain ⟨e₀, he₀, rfl, -, -⟩ := hE e' he'
  obtain rfl : e₀ = e := arcComponent_eq he₀ he hz' hz
  obtain ⟨p, q, hlink, -, -⟩ := exists_link_of_forest hF he'
  have h2 := hl.2.2.2
  have h3 := (pull_link hs hV hE hlink).2.2.2
  rw [image_preimage_eq _ hs, h2] at h3
  rcases pair_eq_pair_iff.mp h3 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact ⟨_, p, q, hlink, h.symm, h'.symm⟩
  · exact ⟨_, q, p, ⟨hlink.1, hlink.2.2.1, hlink.2.1, by rw [hlink.2.2.2, pair_comm]⟩, h.symm,
      h'.symm⟩

end Image

/-- **A walk breaks at the vertices with more than one preimage.** Let every edge of `Q` come from
an edge of `D`, and let two vertices of `D` with the same image both lie in `X`. Then a walk of `Q`
from the image of a vertex `a'` of `D` to the image of a point of `X` first follows `D` to a point
`x` of `X`, and from `x` it goes on by steps of `R`. -/
theorem chain_of_walk {D : Drawing S'} {Q : Drawing S} {X : Set S'} {φ : S' → S} {R : S → S → Prop}
  (hsub : X ⊆ D.V) (hlift : ∀ e a b, Q.toGraph.IsLink e a b → ∃ e' p q, D.toGraph.IsLink e' p q
    ∧ φ p = a ∧ φ q = b)
    (hjump : ∀ p ∈ D.V, ∀ q ∈ D.V, φ p = φ q → p ≠ q → p ∈ X ∧ q ∈ X)
      (hbase : ∀ x ∈ X, ∀ y ∈ X, Nonempty (GraphWalk D.toGraph x y) → R (φ x) (φ y)) {a b : S}
        (W : GraphWalk Q.toGraph a b) (hb : b ∈ φ '' X) :
    ∀ a' ∈ D.V, φ a' = a → ∃ x ∈ X, Nonempty (GraphWalk D.toGraph a' x) ∧ Relation.ReflTransGen R
      (φ x) b := by
  induction W with
  | nil _ =>
    intro a' ha' h
    obtain ⟨b', hb', rfl⟩ := hb
    by_cases hd : a' = b'
    · subst hd
      exact ⟨a', hb', ⟨.nil ha'⟩, by rw [h]⟩
    · exact ⟨a', (hjump a' ha' b' (hsub hb') h hd).1, ⟨.nil ha'⟩, by rw [h]⟩
  | cons hl r ih =>
    intro a' ha' h
    obtain ⟨e', p, q, hlink, rfl, rfl⟩ := hlift _ _ _ hl
    obtain ⟨x, hx, ⟨W'⟩, hR⟩ := ih hb q hlink.2.2.1 rfl
    by_cases hd : a' = p
    · subst hd
      exact ⟨x, hx, ⟨.cons hlink W'⟩, hR⟩
    · obtain ⟨h1, h2⟩ := hjump a' ha' p hlink.2.1 h hd
      refine ⟨a', h1, ⟨.nil ha'⟩, ?_⟩
      rw [h]
      exact Relation.ReflTransGen.head (hbase p h2 x hx ⟨.cons hlink W'⟩) hR

/-- One step between images of boundary vertices of `G` that `G` joins. -/
def PushStep (G : Drawing S') (φ : S' → S) (c d : S) : Prop :=
  ∃ x ∈ G.V ∩ bd S', ∃ y ∈ G.V ∩ bd S', φ x = c ∧ φ y = d ∧ Nonempty (GraphWalk G.toGraph x y)

theorem steps_of_walk {D : Drawing S'} {Q : Drawing S} {X : Set S'} {φ : S' → S} {R : S → S → Prop}
  (hsub : X ⊆ D.V) (hlift : ∀ e a b, Q.toGraph.IsLink e a b → ∃ e' p q, D.toGraph.IsLink e' p q
    ∧ φ p = a ∧ φ q = b)
    (hjump : ∀ p ∈ D.V, ∀ q ∈ D.V, φ p = φ q → p ≠ q → p ∈ X ∧ q ∈ X)
      (hbase : ∀ x ∈ X, ∀ y ∈ X, Nonempty (GraphWalk D.toGraph x y) → R (φ x) (φ y)) {s : S'}
        (hs : s ∈ X) {b : S} (W : GraphWalk Q.toGraph (φ s) b) (hb : b ∈ φ '' X) :
    Relation.ReflTransGen R (φ s) b := by
  obtain ⟨x, hx, hW, hR⟩ := chain_of_walk hsub hlift hjump hbase W hb s (hsub hs) rfl
  exact Relation.ReflTransGen.head (hbase s hs x hx hW) hR

theorem homotopic_of_curves {T : Type} [TopologicalSpace T] {a b : T} {p q : Path a b}
  (h : CurvesHomotopic p.toContinuousMap q.toContinuousMap) : p.Homotopic q := by
  obtain ⟨ψ, -, h0, h1, h2, -, h3, -⟩ := h
  refine ⟨⟨⟨⟨fun w => ψ (w.2, w.1), by fun_prop⟩, fun x => ?_, fun x => ?_⟩, fun t x hx => ?_⟩⟩
  · exact h0 x
  · exact h1 x
  · rcases hx with rfl | hx
    · exact h2 t
    · obtain rfl : x = 1 := hx
      exact h3 t

theorem curves_of_homotopic {T : Type} [TopologicalSpace T] {a b : T} {p q : Path a b}
  (h : p.Homotopic q) : CurvesHomotopic p.toContinuousMap q.toContinuousMap := by
  obtain ⟨F⟩ := h
  refine ⟨⟨fun w => F (w.2, w.1), by fun_prop⟩, fun _ => mem_univ _, fun x => ?_, fun x => ?_,
    fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

/-- What holds between two points joined by steps: both forests join them, and they have homotopic
curves. -/
def PushJoined (P H : Drawing S) (a b : S) : Prop :=
  Nonempty (GraphWalk P.toGraph a b) ∧ Nonempty (GraphWalk H.toGraph a b) ∧ ∃ κ l : Path a b,
    (∀ u, κ u ∈ P.U) ∧ (∀ u, l u ∈ H.U) ∧ κ.Homotopic l

theorem PushJoined.refl {P H : Drawing S} {a : S} (h1 : a ∈ P.V) (h2 : a ∈ H.V) : PushJoined P H a
  a :=
  ⟨⟨.nil h1⟩, ⟨.nil h2⟩, Path.refl a, Path.refl a, fun _ => P.V_subset_U h1, fun _
    => H.V_subset_U h2, Path.Homotopic.refl _⟩

theorem mem_trans {T : Type} [TopologicalSpace T] {a b c : T} {A : Set T} {p : Path a b} {q : Path
  b c} (hp : ∀ u, p u ∈ A) (hq : ∀ u, q u ∈ A) (u : unitInterval) : p.trans q u ∈ A := by
  have h : p.trans q u ∈ range (p.trans q) := ⟨u, rfl⟩
  rw [Path.trans_range] at h
  rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hv ▸ hp v
  · exact hv ▸ hq v

theorem PushJoined.trans {P H : Drawing S} {a b c : S} (h : PushJoined P H a b)
  (h' : PushJoined P H b c) : PushJoined P H a c := by
  obtain ⟨⟨W₁⟩, ⟨W₂⟩, κ, l, h1, h2, h3⟩ := h
  obtain ⟨⟨W₁'⟩, ⟨W₂'⟩, κ', l', h1', h2', h3'⟩ := h'
  exact ⟨⟨W₁.append W₁'⟩, ⟨W₂.append W₂'⟩, κ.trans κ', l.trans l', mem_trans h1 h1',
    mem_trans h2 h2', h3.hcomp h3'⟩

theorem link_ne {G : Drawing S'} (hF : IsGraphForest G.toGraph) {e : Set S'} {p q : S'}
  (hl : G.toGraph.IsLink e p q) : p ≠ q := by
  obtain ⟨u, v, huv, hcap, -⟩ := edge_line_of_forest hF hl.1
  have h := hl.2.2.2
  rw [hcap] at h
  rintro rfl
  rcases pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact huv (by rw [h1, h2])

/-- **The core of the second part of (4.5)** (page 223). Let `Γ` be the preimage of a forest `H`,
and let `G` be a forest homotopic to `Γ`. Then the image of `G` is a forest homotopic to `H`. -/
theorem exists_image_forest [CompactSpace S'] [T2Space S] {J H : Drawing S} {G Γ :
  Drawing S'} {φ : S' → S} (hJ : IsCutAlongGraph J S' φ) (hH : IsSurfaceForest H) (hU : Γ.U
    = φ ⁻¹' H.U) (hV : Γ.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ Γ.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ (closure e'))
      (hG : ForestsHomotopic G Γ) :
    ∃ P : Drawing S, IsImageDrawing φ G P ∧ IsSurfaceForest P ∧ ForestsHomotopic P H := by
  classical
  have hsurj := hJ.quotientMap.surjective
  have hcont := hJ.quotientMap.continuous
  have hGp := hG.1
  have hGf : IsGraphForest G.toGraph := hG.2.2.1
  have hΓf : IsGraphForest Γ.toGraph := hG.2.2.2.1
  have hXΓ : G.V ∩ bd S' = Γ.V ∩ bd S' := hG.2.2.2.2.1
  obtain ⟨P, hPU, hPV, hPE⟩ := exists_image_drawing hJ hGp hGf fun e p q hl
    => push_ne hJ hH.2 hV hE hG hl (link_ne hGf hl)
  have hPf := push_forest hJ hH.2 hV hE hG hPV hPE
  have hPp : P.IsProper := by
    rintro z ⟨hzb, hzU⟩
    rw [hPU] at hzU
    obtain ⟨a, ha, rfl⟩ := hzU
    rw [hPV]
    exact mem_image_of_mem φ (hGp ⟨hJ.bd_of_bd hzb, ha⟩)
  have hXP : ∀ x ∈ G.V ∩ bd S', φ x ∈ P.V := fun x hx => by
    rw [hPV]
    exact mem_image_of_mem φ hx.1
  have hXH : ∀ x ∈ G.V ∩ bd S', φ x ∈ H.V := fun x hx => by
    have h1 : x ∈ Γ.V ∩ bd S' := hXΓ ▸ hx
    have h2 : x ∈ Γ.V := h1.1
    rw [hV] at h2
    exact h2
  have hPim : ∀ z ∈ P.V ∩ bd S, z ∈ φ '' (G.V ∩ bd S') := by
    rintro z ⟨hz, hzb⟩
    rw [hPV] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ⟨ha, hJ.bd_of_bd hzb⟩, rfl⟩
  have hHim : ∀ z ∈ H.V ∩ bd S, z ∈ φ '' (G.V ∩ bd S') := by
    rintro z ⟨hz, hzb⟩
    obtain ⟨a, rfl⟩ := hsurj z
    have ha : a ∈ Γ.V ∩ bd S' := ⟨by rw [hV]; exact hz, hJ.bd_of_bd hzb⟩
    exact ⟨a, hXΓ ▸ ha, rfl⟩
  have hbd : P.V ∩ bd S = H.V ∩ bd S := by
    refine Subset.antisymm (fun z hz => ?_) fun z hz => ?_
    · obtain ⟨a, ha, rfl⟩ := hPim z hz
      exact ⟨hXH a ha, hz.2⟩
    · obtain ⟨a, ha, rfl⟩ := hHim z hz
      exact ⟨hXP a ha, hz.2⟩
  have hone : ∀ c d, PushStep G φ c d → PushJoined P H c d := by
    rintro _ _ ⟨x, hx, y, hy, rfl, rfl, ⟨W⟩⟩
    by_cases hxy : x = y
    · subst hxy
      exact PushJoined.refl (hXP x hx) (hXH x hx)
    obtain ⟨W', hs, -⟩ := GraphWalk.exists_isSimple W
    obtain ⟨Q, hQ⟩ := (hG.2.2.2.2.2 x hx y hy hxy).1.mp ⟨W', hs⟩
    obtain ⟨g, hg⟩ := exists_curveTracesWalk W'
    obtain ⟨c, hc⟩ := exists_curveTracesWalk Q
    have hh := (hG.2.2.2.2.2 x hx y hy hxy).2 W' Q g c hs hQ hg hc
    obtain ⟨g0, g1⟩ := hg.endpoints
    obtain ⟨c0, c1⟩ := hc.endpoints
    let pg : Path x y := ⟨g, g0, g1⟩
    let pc : Path x y := ⟨c, c0, c1⟩
    have hpp : pg.Homotopic pc := homotopic_of_curves hh
    obtain ⟨W₀, -, -⟩ := pull_walk hsurj hV hE Q
    refine ⟨push_walk hJ hGp hPV hPE W, ⟨W₀⟩, pg.map hcont, pc.map hcont, fun u => ?_,
      fun u => ?_, hpp.map ⟨φ, hcont⟩⟩
    · rw [hPU]
      exact mem_image_of_mem φ (hg.range_subset_U ⟨u, rfl⟩)
    · have : pc u ∈ Γ.U := hc.range_subset_U ⟨u, rfl⟩
      rw [hU] at this
      exact this
  have hjoined : ∀ a b, Relation.ReflTransGen (PushStep G φ) a b → a ∈ φ '' (G.V ∩ bd S')
    → PushJoined P H a b := by
    intro a b h ha
    induction h with
    | refl =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact PushJoined.refl (hXP x hx) (hXH x hx)
    | tail _ h2 ih => exact ih.trans (hone _ _ h2)
  have hfromP : ∀ {s t : S'}, s ∈ G.V ∩ bd S' → t ∈ G.V ∩ bd S' → GraphWalk P.toGraph (φ s) (φ t)
    → PushJoined P H (φ s) (φ t) := fun {s t} hs ht W =>
    hjoined _ _ (steps_of_walk (D := G) (X := G.V ∩ bd S') inter_subset_left (fun e a b hl => by
        obtain ⟨e', p, q, h1, h2, h3, -⟩ := push_lift hJ hGp hGf hPV hPE hl
        exact ⟨e', p, q, h1, h2, h3⟩)
      (fun p hp q hq h hne => ⟨⟨hp, (hJ.bd_of_eq h hne).1⟩, ⟨hq, (hJ.bd_of_eq h hne).2⟩⟩)
        (fun x hx y hy h => ⟨x, hx, y, hy, rfl, rfl, h⟩) hs W ⟨t, ht, rfl⟩) ⟨s, hs, rfl⟩
  have hfromH : ∀ {s t : S'}, s ∈ G.V ∩ bd S' → t ∈ G.V ∩ bd S' → GraphWalk H.toGraph (φ s) (φ t)
    → PushJoined P H (φ s) (φ t) := fun {s t} hs ht W =>
    hjoined _ _ (steps_of_walk (D := Γ) (X := G.V ∩ bd S') (fun x hx =>
      (hXΓ ▸ hx : x ∈ Γ.V ∩ bd S').1) (fun e a b hl => pull_lift hsurj hΓf hU hV hE hl)
      (fun p hp q hq h hne => by
        rw [hXΓ]
        exact ⟨⟨hp, (hJ.bd_of_eq h hne).1⟩, ⟨hq, (hJ.bd_of_eq h hne).2⟩⟩) (fun x hx y hy h => by
        obtain ⟨W₀⟩ := h
        have hyc : y ∈ classOf Γ (G.V ∩ bd S') x := ⟨hy, ⟨W₀⟩⟩
        rw [← classOf_eq_of_homotopic hG hx] at hyc
        exact ⟨x, hx, y, hy, rfl, rfl, hyc.2⟩) hs W ⟨t, ht, rfl⟩) ⟨s, hs, rfl⟩
  refine ⟨P, ⟨hPU, hPV⟩, ⟨hPp, hPf⟩, hPp, hH.1, hPf, hH.2, hbd, fun s hs t ht hst => ?_⟩
  obtain ⟨s', hs', rfl⟩ := hPim s hs
  obtain ⟨t', ht', rfl⟩ := hPim t ht
  refine ⟨⟨fun ⟨W, _⟩ => ?_, fun ⟨W, _⟩ => ?_⟩, fun W₁ W₂ g c _ _ hg hc => ?_⟩
  · obtain ⟨-, ⟨W'⟩, -⟩ := hfromP hs' ht' W
    obtain ⟨W'', h, -⟩ := GraphWalk.exists_isSimple W'
    exact ⟨W'', h⟩
  · obtain ⟨⟨W'⟩, -, -⟩ := hfromH hs' ht' W
    obtain ⟨W'', h, -⟩ := GraphWalk.exists_isSimple W'
    exact ⟨W'', h⟩
  · obtain ⟨-, -, κ, l, h1, h2, h3⟩ := hfromP hs' ht' W₁
    obtain ⟨g0, g1⟩ := hg.endpoints
    obtain ⟨c0, c1⟩ := hc.endpoints
    let pg : Path (φ s') (φ t') := ⟨g, g0, g1⟩
    let pc : Path (φ s') (φ t') := ⟨c, c0, c1⟩
    have hpg : pg.Homotopic κ := IsFlat.flat (isFlat_forest hPf) pg κ (fun u
      => hg.range_subset_U ⟨u, rfl⟩) h1
    have hpc : l.Homotopic pc := IsFlat.flat (isFlat_forest hH.2) l pc h2 fun u
      => hc.range_subset_U ⟨u, rfl⟩
    exact curves_of_homotopic (hpg.trans (h3.trans hpc))

theorem drawing_eq {T : Type} [TopologicalSpace T] {Γ₁ Γ₂ : Drawing T} (hU : Γ₁.U = Γ₂.U)
  (hV : Γ₁.V = Γ₂.V) : Γ₁ = Γ₂ := by
  cases Γ₁
  cases Γ₂
  simp only [Drawing.mk.injEq]
  exact ⟨hU, hV⟩

/-- Graph Minors VII, (4.5) (page 223):
"(4.5) *Let $J$ be a proper graph in $\Sigma$ with no isolated vertices. Let $\Sigma'$ be the
surface obtained from $\Sigma$ by cutting along $U(J)$ and let $\phi \colon \Sigma' \to \Sigma$ be
the associated surjection. Let $H$ be a forest in $\Sigma$ such that $U(J)$ is $H$-normal. Then
$\phi^{-1}(H)$ is a forest in $\Sigma'$. Moreover, if $H'$ is a forest in $\Sigma'$ homoplastic to
$\phi^{-1}(H)$, then $\phi(H')$ is a forest in $\Sigma$ homoplastic to $H$.*" -/
theorem theorem_4_5_proof (hS : IsSurface S) (J H : Drawing S) (φ : S' → S)
  (hCut : IsCutAlongGraph J S' φ) (hH : IsSurfaceForest H) (hNorm : H.IsNormal J.U) :
    ∃ H_pull : Drawing S',
      IsPullbackDrawing φ H H_pull ∧ IsSurfaceForest H_pull ∧
      ∀ H' : Drawing S', IsSurfaceForest H' → ForestsHomoplastic H' H_pull →
        ∃ H_push : Drawing S,
          IsImageDrawing φ H' H_push ∧ IsSurfaceForest H_push ∧
          ForestsHomoplastic H_push H := by
  have hT2 : T2Space S := hS.2.1
  have hY := hCut.isSurface
  have : CompactSpace S' := hY.1
  have : T2Space S' := hY.2.1
  obtain ⟨Γ, hp, hprop, hE⟩ := exists_pullback hS hCut hH hNorm
  refine ⟨Γ, hp, ⟨hprop, isGraphForest_pullback hCut.quotientMap.surjective hH.2 hp.2 hE⟩,
    fun H' hH' ⟨α, hα, hh⟩ => ?_⟩
  obtain ⟨P, hPi, hPf, hPh⟩ := exists_image_forest hCut hH hp.1 hp.2 hE hh
  obtain ⟨β, hβ, hβφ⟩ := exists_descend hCut α hα
  have himg : ∀ A : Set S', β '' (φ '' A) = φ '' (α '' A) := fun A => by
    rw [image_image, image_image]
    exact image_congr fun y _ => hβφ y
  have hβU : β '' (φ '' H'.U) = P.U := by
    rw [himg]
    exact hPi.1.symm
  have hβV : β '' (φ '' H'.V) = P.V := by
    rw [himg]
    exact hPi.2.symm
  have hsymm : ∀ A : Set S, β.symm '' (β '' A) = A := fun A => by
    rw [image_image]
    simp
  refine ⟨mapDrawingHomeo β.symm P, ⟨?_, ?_⟩, hPf.map_homeo β.symm, β, hβ, ?_⟩
  · change β.symm '' P.U = φ '' H'.U
    rw [← hβU, hsymm]
  · change β.symm '' P.V = φ '' H'.V
    rw [← hβV, hsymm]
  · have : mapDrawingHomeo β (mapDrawingHomeo β.symm P) = P := by
      refine drawing_eq ?_ ?_
      · change β '' (β.symm '' P.U) = P.U
        rw [image_image]
        simp
      · change β '' (β.symm '' P.V) = P.V
        rw [image_image]
        simp
    rw [this]
    exact hPh

end GraphMinor.GM07
