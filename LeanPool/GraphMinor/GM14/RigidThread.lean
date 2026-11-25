/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidNoose
public import LeanPool.GraphMinor.GM14.Section6b
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.SphereRegion
import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# A small side of a rigid drawing is a path

We keep the setting of `RigidNoose`. Let `A` be a nonempty set of edges of `H` with at most two
vertices that meet both `A` and another edge of `J`. Then `A` is the edge set of a path `P` of `H`
between these two vertices, and the inner vertices of `P` have no other edges and do not lie on the
boundary of `Δ`. This is `exists_thread`.

By `exists_dial_of_edge`, each edge of `A` is on a path in a dial. If two such paths differ then
they
are disjoint inside and form a circuit `K`. We apply `exists_dial_of_edge` again, to all the edges
in
the disc that `K` bounds in `Δ`. The new `O`-arc misses the inside of that disc, since all the
regions
there are in the set. So the new dial includes the disc, and it holds the circuit `K`. But it holds
only a path, and a line includes no `O`-arc.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- A line includes no `O`-arc. -/
theorem not_oArc_subset_line {F L : Set S} {a b : S} (hF : IsOArc F) (hL : IsLineWithEnds L a b)
    (hFL : F ⊆ L) : False := by
  obtain ⟨φ⟩ := hF
  obtain ⟨ψ, -, -⟩ := hL
  let g : Circle → ℝ := fun x => (ψ.symm ⟨(φ x).1, hFL (φ x).2⟩ : unitInterval)
  have hg : Continuous g := by fun_prop
  refine GM11.not_injective_circle_real hg fun x y hxy => ?_
  have h₁ : ψ.symm ⟨(φ x).1, hFL (φ x).2⟩ = ψ.symm ⟨(φ y).1, hFL (φ y).2⟩ := Subtype.ext hxy
  have h₂ := ψ.symm.injective h₁
  exact φ.injective (Subtype.ext (congrArg (fun z : L => z.1) h₂))

omit [T2Space S] in
theorem isPathBetween_symm {P : Drawing S} {a b : S} (h : P.IsPathBetween a b) :
    P.IsPathBetween b a := by
  obtain ⟨W, hs, hV, hE⟩ := h
  refine ⟨W.reverse, hs.reverse, ?_, ?_⟩
  · rw [hV]
    ext x
    simp [GraphWalk.support_reverse]
  · rw [hE]
    ext x
    simp [GraphWalk.edges_reverse]

theorem start_mem_support {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    a ∈ W.support := by
  cases W <;> simp [GraphWalk.support]

theorem end_mem_support {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    b ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.support]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

omit [T2Space S] in
/-- All the edges of a simple walk are on the same side of `A` if no inner vertex meets both sides.
-/
theorem walk_same_side {J P : Drawing S} (hV : P.V ⊆ J.V) (hE : P.E ⊆ J.E) {A : Set (Set S)} :
    ∀ {a b : S} (W : GraphWalk P.toGraph a b), W.IsSimple →
      (∀ v ∈ W.support, v ≠ a → v ≠ b → v ∉ Whitney.bdry J.toGraph A) →
      ∀ g ∈ W.edges, ∀ g' ∈ W.edges, g ∈ A → g' ∈ A := by
  intro a b W
  induction W with
  | nil _ => simp [GraphWalk.edges]
  | @cons u v t e hl rest ih =>
    intro hs hb g hg g' hg' hgA
    have hrs : rest.IsSimple := (List.nodup_cons.mp hs).2
    have hun : u ∉ rest.support := (List.nodup_cons.mp hs).1
    have hrb : ∀ w ∈ rest.support, w ≠ v → w ≠ t → w ∉ Whitney.bdry J.toGraph A := fun w hw h₁ h₂ =>
      hb w (List.mem_cons_of_mem _ hw) (fun h' => hun (h' ▸ hw)) h₂
    have hIH := ih hrs hrb
    -- `e` and the edges of `rest` are on the same side.
    have hstep : ∀ c ∈ rest.edges, (e ∈ A ↔ c ∈ A) := by
      intro c hc
      have hfirst : ∃ c₀ ∈ rest.edges, P.toGraph.Inc c₀ v := by
        cases rest with
        | nil _ => simp [GraphWalk.edges] at hc
        | @cons _ v' _ c₀ hl' _ => exact ⟨c₀, by simp [GraphWalk.edges], v', hl'⟩
      obtain ⟨c₀, hc₀, hic⟩ := hfirst
      have hvt : v ≠ t := by
        rintro rfl
        cases rest with
        | nil _ => simp [GraphWalk.edges] at hc
        | @cons _ v' _ c₀ hl' r' =>
          exact (List.nodup_cons.mp hrs).1 (end_mem_support r')
      have hvb := hb v (List.mem_cons_of_mem _ (start_mem_support rest))
        (fun h' => hun (h' ▸ start_mem_support rest)) hvt
      have hincJ : ∀ {f : Set S}, P.toGraph.Inc f v → f ∈ P.E → J.toGraph.Inc f v := fun hi hf =>
        inc_of_mem_closure (hE hf) (mem_closure_of_inc hi) (hV hl.right_mem)
      have heE : e ∈ P.E := hl.edge_mem
      have hc₀E : c₀ ∈ P.E := hic.edge_mem
      have h₀ : e ∈ A ↔ c₀ ∈ A := by
        constructor
        · intro he
          by_contra hn
          exact hvb ⟨⟨e, he, hincJ ⟨u, hl.symm⟩ heE⟩, ⟨c₀, ⟨hE hc₀E, hn⟩, hincJ hic hc₀E⟩⟩
        · intro he
          by_contra hn
          exact hvb ⟨⟨c₀, he, hincJ hic hc₀E⟩, ⟨e, ⟨hE heE, hn⟩, hincJ ⟨u, hl.symm⟩ heE⟩⟩
      exact h₀.trans ⟨fun h' => hIH c₀ hc₀ c hc h', fun h' => hIH c hc c₀ hc₀ h'⟩
    simp only [GraphWalk.edges, List.mem_cons] at hg hg'
    rcases hg with rfl | hg <;> rcases hg' with rfl | hg'
    · exact hgA
    · exact (hstep g' hg').mp hgA
    · exact (hstep g hg).mpr hgA
    · exact hIH g hg g' hg' hgA

variable {H J Γ' : Drawing S} {Δ : Set S} {a : S}

/-- What a dial gives. -/
structure Holder (H : Drawing S) (Δ F D : Set S) (x y : S) : Prop where
  disc : IsClosedDisc D
  sub : D ⊆ Δ
  bd : discBd D = F
  ne : x ≠ y
  cap : F ∩ H.V = {x, y}
  path : (H.interSet D).IsPathBetween x y
  norm : F ∩ H.U ⊆ H.V

variable {F D : Set S} {x y : S}

theorem Holder.fr (h : Holder H Δ F D x y) (hS : IsClosedSurface S) : frontier D = F :=
  (IsClosedDisc.frontier_eq_discBd hS h.disc).trans h.bd

theorem Holder.edge_F (h : Holder H Δ F D x y) {g : Set S} (hg : g ∈ H.E) : Disjoint g F :=
  disjoint_left.mpr fun _z hz hzF =>
    edge_notMem_V hg hz (h.norm ⟨hzF, H.closure_subset_U hg (subset_closure hz)⟩)

theorem Holder.meets (h : Holder H Δ F D x y) (hS : IsClosedSurface S) {g : Set S} (hg : g ∈ H.E)
    (hm : (g ∩ D).Nonempty) : g ⊆ D := by
  rcases subset_or_disjoint_of_frontier h.disc.isClosed hg.2.2.1.isConnected.isPreconnected
    (by rw [h.fr hS]; exact h.edge_F hg) with h₁ | h₁
  · exact h₁
  · obtain ⟨z, hz, hz'⟩ := hm
    exact absurd hz' (disjoint_left.mp h₁ hz)

theorem Holder.VU (h : Holder H Δ F D x y) (hS : IsClosedSurface S) :
    (H.interSet D).V = H.V ∩ D ∧ (H.interSet D).U = H.U ∩ D :=
  interSet_V_and_U_of_edges h.disc.isClosed fun _ hg hm => h.meets hS hg hm

theorem mem_interSet_E {g : Set S} : g ∈ (H.interSet D).E ↔ g ∈ H.E ∧ g ⊆ D := by
  change g ∈ (H.span _ _).E ↔ _
  rw [H.span_E]
  constructor
  · rintro ⟨h₁, -⟩
    exact h₁
  · exact fun h₁ => ⟨h₁, h₁.1⟩

/-- A vertex of the path other than its ends is inside the disc. -/
theorem Holder.inner (h : Holder H Δ F D x y) (hS : IsClosedSurface S) {v : S}
    (hv : v ∈ (H.interSet D).V) (hx : v ≠ x) (hy : v ≠ y) : v ∈ interior D := by
  rw [(h.VU hS).1] at hv
  have hnF : v ∉ F := fun h' => by
    have : v ∈ F ∩ H.V := ⟨h', hv.1⟩
    rw [h.cap] at this
    rcases this with h₁ | h₁
    · exact hx h₁
    · exact hy h₁
  by_contra hn
  exact hnF (h.fr hS ▸ ⟨subset_closure hv.2, hn⟩)

/-- An edge of `J` that meets the interior of a disc in `Δ` is an edge of `H`. -/
theorem Frame.mem_E_of_interior (f : Frame H J Δ a) {D' : Set S} (hD' : D' ⊆ Δ) {g : Set S}
    (hg : g ∈ J.E) {q : S} (hq : q ∈ g) (hqD : q ∈ interior D') : g ∈ H.E := by
  have hqi : q ∈ interior Δ := interior_mono hD' hqD
  refine f.mem_E hg hq (interior_subset hqi) fun hb => ?_
  rw [subBd_eq_frontier] at hb
  exact hb.2 hqi

/-- Each edge of `J` at an inner vertex of the path is on the path, and the vertex is not on the
boundary of `Δ`. -/
theorem Holder.inner_edges (h : Holder H Δ F D x y) (f : Frame H J Δ a) (hS : IsClosedSurface S)
    {v : S} (hv : v ∈ (H.interSet D).V) (hx : v ≠ x) (hy : v ≠ y) :
    v ∉ subBd Δ ∧ ∀ g ∈ J.E, J.toGraph.Inc g v → g ∈ (H.interSet D).E := by
  have hi := h.inner hS hv hx hy
  refine ⟨fun hb => ?_, fun g hg hinc => ?_⟩
  · rw [subBd_eq_frontier] at hb
    exact hb.2 (interior_mono h.sub hi)
  · have hc := mem_closure_of_inc hinc
    obtain ⟨q, hqi, hqg⟩ := mem_closure_iff.mp hc _ isOpen_interior hi
    have hgH := f.mem_E_of_interior h.sub hg hqg hqi
    exact mem_interSet_E.mpr ⟨hgH, h.meets hS hgH ⟨q, hqg, interior_subset hqi⟩⟩

/-- Two holder paths with an edge belonging only to the second meet exactly at their ends
and form a circuit. -/
theorem Holder.paths_form_circuit (hS : IsClosedSurface S) {F' D' : Set S}
    (h₁ : Holder H Δ F D x y) (h₂ : Holder H Δ F' D' x y)
    {e' : Set S} (he' : e' ∈ (H.interSet D').E) (hne : e' ∉ (H.interSet D).E) :
    let P := H.interSet D
    let P' := H.interSet D'
    P.V ∩ P'.V = {x, y} ∧ Disjoint P.E P'.E ∧ (H.sup P P').IsCircuit := by
  classical
  set P := H.interSet D
  set P' := H.interSet D'
  have hPs : P.IsSubdrawing H := Drawing.span_isSubdrawing H _ _
  have hPs' : P'.IsSubdrawing H := Drawing.span_isSubdrawing H _ _
  have hxy := h₁.ne
  have hline' : IsLineWithEnds P'.U x y := isLine_of_isPathBetween h₂.path hxy
  have hxF : x ∈ F ∩ H.V := h₁.cap ▸ Or.inl rfl
  have hyF : y ∈ F ∩ H.V := h₁.cap ▸ Or.inr rfl
  have hxF' : x ∈ F' ∩ H.V := h₂.cap ▸ Or.inl rfl
  have hyF' : y ∈ F' ∩ H.V := h₂.cap ▸ Or.inr rfl
  have hFD : F ⊆ D := h₁.bd ▸ Surface.discBd_subset D
  have hFD' : F' ⊆ D' := h₂.bd ▸ Surface.discBd_subset D'
  have hxP : x ∈ P.V := (h₁.VU hS).1 ▸ ⟨hxF.2, hFD hxF.1⟩
  have hyP : y ∈ P.V := (h₁.VU hS).1 ▸ ⟨hyF.2, hFD hyF.1⟩
  have hxP' : x ∈ P'.V := (h₂.VU hS).1 ▸ ⟨hxF'.2, hFD' hxF'.1⟩
  have hyP' : y ∈ P'.V := (h₂.VU hS).1 ▸ ⟨hyF'.2, hFD' hyF'.1⟩
  -- The inside of the second path misses the first disc.
  have hoff : P'.U \ {x, y} ⊆ H.U \ F := fun z hz => by
    have hzU : z ∈ H.U := hPs'.U_subset hz.1
    refine ⟨hzU, fun hzF => hz.2 ?_⟩
    rw [← h₁.cap]
    exact ⟨hzF, h₁.norm ⟨hzF, hzU⟩⟩
  have hedge : ∀ {g}, g ∈ P'.E → g ⊆ P'.U \ {x, y} := fun {g} hg z hz => by
    refine ⟨P'.closure_subset_U hg (subset_closure hz), ?_⟩
    rintro (rfl | rfl)
    · exact edge_notMem_V hg hz hxP'
    · exact edge_notMem_V hg hz hyP'
  have hdis : Disjoint (P'.U \ {x, y}) D := by
    rcases subset_or_disjoint_of_frontier h₁.disc.isClosed
      (IsLineWithEnds.isPreconnected_sdiff_pair hline')
      (by
        rw [h₁.fr hS]
        exact disjoint_left.mpr fun z hz hzF => (hoff hz).2 hzF) with h₃ | h₃
    · exfalso
      exact hne (mem_interSet_E.mpr ⟨hPs'.2 he', (hedge he').trans h₃⟩)
    · exact h₃
  have hV : P.V ∩ P'.V = {x, y} := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      by_contra hn
      have hzD : z ∈ D := by
        rw [(h₁.VU hS).1] at hz
        exact hz.2
      exact disjoint_left.mp hdis ⟨P'.V_subset_U hz', hn⟩ hzD
    · rintro (rfl | rfl)
      · exact ⟨hxP, hxP'⟩
      · exact ⟨hyP, hyP'⟩
  have hE : Disjoint P.E P'.E := by
    refine disjoint_left.mpr fun g hg hg' => ?_
    obtain ⟨z, hz⟩ := hg.1
    exact disjoint_left.mp hdis (hedge hg' hz) ((mem_interSet_E.mp hg).2 hz)
  exact ⟨hV, hE, Drawing.isCircuit_sup h₁.path h₂.path hPs hPs' hxy hV hE⟩

/-- Two paths of dials with an edge in only one of them cannot both exist. -/
theorem no_two_paths [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ') (hS : IsClosedSurface S)
    (hsph : IsSphere S) {F' D' : Set S} (h₁ : Holder H Δ F D x y) (h₂ : Holder H Δ F' D' x y)
    {e e' : Set S} (he : e ∈ (H.interSet D).E) (he' : e' ∈ (H.interSet D').E)
    (hne : e' ∉ (H.interSet D).E) : False := by
  classical
  set P := H.interSet D
  set P' := H.interSet D'
  have hPs : P.IsSubdrawing H := Drawing.span_isSubdrawing H _ _
  have hPs' : P'.IsSubdrawing H := Drawing.span_isSubdrawing H _ _
  have hxy := h₁.ne
  obtain ⟨-, -, hK⟩ := h₁.paths_form_circuit hS h₂ he' hne
  let K := H.sup P P'
  have hKU : K.U = P.U ∪ P'.U := sup_U hPs hPs'
  have hKE : K.E = P.E ∪ P'.E := Drawing.sup_E hPs hPs'
  have hKs : K.IsSubdrawing H := Drawing.sup_isSubdrawing _ _ _
  have hPΔ : P.U ⊆ Δ := hPs.U_subset.trans f.Usub
  have hPΔ' : P'.U ⊆ Δ := hPs'.U_subset.trans f.Usub
  have hKΔ : K.U ⊆ Δ := hKU ▸ union_subset hPΔ hPΔ'
  have hKarc : IsOArc K.U := IsCircuit.isOArc_U hK
  obtain ⟨E₀, hE₀, hbE, hdE⟩ := exists_disc_missing hS hsph hKarc f.outer
    (disjoint_left.mpr fun z hz hzK => hz (hKΔ hzK))
  have hE₀Δ : E₀ ⊆ Δ := fun z hz => by
    by_contra hn
    exact disjoint_left.mp hdE hz hn
  have hfrE : frontier E₀ = K.U := (IsClosedDisc.frontier_eq_discBd hS hE₀).trans hbE
  have hKE₀ : K.U ⊆ E₀ := hbE ▸ Surface.discBd_subset E₀
  have hKJ : K.IsSubdrawing J := ⟨hKs.1.trans f.Vsub, hKs.2.trans f.Esub⟩
  let A' : Set (Set S) := {g | g ∈ H.E ∧ g ⊆ E₀}
  have hKA' : K.E ⊆ A' := fun g hg => ⟨hKs.2 hg, (K.closure_subset_U hg).trans hKE₀ |>.trans'
    subset_closure⟩
  -- An edge of `J` with a point inside `E₀` is in `A'`.
  have hinA : ∀ {g q}, g ∈ J.E → q ∈ g → q ∈ interior E₀ → g ∈ A' := by
    intro g q hg hq hqi
    by_cases hgK : g ∈ K.E
    · exact hKA' hgK
    · have hgH := f.mem_E_of_interior hE₀Δ hg hq hqi
      refine ⟨hgH, ?_⟩
      have hdisj : Disjoint g K.U := edge_disjoint_U hKJ hg hgK
      rcases subset_or_disjoint_of_frontier hE₀.isClosed hg.2.2.1.isConnected.isPreconnected
        (by rwa [hfrE]) with h₃ | h₃
      · exact h₃
      · exact absurd (interior_subset hqi) (disjoint_left.mp h₃ hq)
  have hbdry : Whitney.bdry J.toGraph A' ⊆ {x, y} := by
    rintro v ⟨⟨g, hgA, hgi⟩, ⟨g', ⟨hg'J, hg'A⟩, hg'i⟩⟩
    by_contra hvn
    have hvx : v ≠ x := fun h' => hvn (Or.inl h')
    have hvy : v ≠ y := fun h' => hvn (Or.inr h')
    have hvJ : v ∈ J.V := hgi.vertex_mem
    have hvE : v ∈ E₀ := closure_minimal hgA.2 hE₀.isClosed (mem_closure_of_inc hgi)
    by_cases hvK : v ∈ K.U
    · rw [hKU] at hvK
      rcases hvK with hv | hv
      · have hvP : v ∈ P.V := by
          rw [(h₁.VU hS).1]
          rw [(h₁.VU hS).2] at hv
          exact ⟨f.U_inter_V hv.1 hvJ, hv.2⟩
        exact hg'A (hKA' (hKE ▸ Or.inl ((h₁.inner_edges f hS hvP hvx hvy).2 g' hg'J hg'i)))
      · have hvP : v ∈ P'.V := by
          rw [(h₂.VU hS).1]
          rw [(h₂.VU hS).2] at hv
          exact ⟨f.U_inter_V hv.1 hvJ, hv.2⟩
        exact hg'A (hKA' (hKE ▸ Or.inr ((h₂.inner_edges f hS hvP hvx hvy).2 g' hg'J hg'i)))
    · have hvi : v ∈ interior E₀ := by
        by_contra hn
        exact hvK (hfrE ▸ ⟨subset_closure hvE, hn⟩)
      obtain ⟨q, hqi, hqg⟩ := mem_closure_iff.mp (mem_closure_of_inc hg'i) _ isOpen_interior hvi
      exact hg'A (hinA hg'J hqg hqi)
  have hbfin : (Whitney.bdry J.toGraph A').Finite := (toFinite ({x, y} : Set S)).subset hbdry
  have hbc : (Whitney.bdry J.toGraph A').ncard ≤ 2 :=
    (ncard_le_ncard hbdry (toFinite _)).trans (ncard_pair hxy).le
  have hA'H : A' ⊆ H.E := fun _ hg => hg.1
  have heA' : e ∈ A' := hKA' (hKE ▸ Or.inl he)
  obtain ⟨F₁, D₁, x₁, y₁, hF₁, hF₁N, hD₁Δ, hD₁, hbD₁, heD₁, hxy₁, hcap₁, hpath₁, hn₁, -⟩ :=
    exists_dial_of_edge f r hS hsph hA'H hbc hbfin heA'
  -- Regions of `Γ'` near the inside of `E₀` are in the set.
  have htile : ∀ t ∈ Γ'.R, (t ∩ interior E₀).Nonempty → t ∈ tiles Γ' A' := by
    intro t ht hm
    obtain ⟨g, hg, hgt⟩ := r.facts.1 t ht
    have hgJ : g ∈ J.E := hg
    refine ⟨ht, g, ?_, hgt⟩
    by_contra hgA
    have hgK : g ∉ K.E := fun h' => hgA (hKA' h')
    have hdisj : Disjoint g K.U := edge_disjoint_U hKJ hgJ hgK
    have htK : Disjoint t (frontier E₀) := by
      rw [hfrE]
      refine disjoint_left.mpr fun z hz hzK => ?_
      have hzU : z ∈ J.U := hKJ.U_subset hzK
      exact disjoint_left.mp hdisj (r.mem_edge hgJ ht hgt hz hzU) hzK
    rcases subset_or_disjoint_of_frontier hE₀.isClosed (region_isPreconnected ht) htK with h₃ | h₃
    · obtain ⟨q, hq⟩ := hg.1
      have hqi : q ∈ interior E₀ := by
        by_contra hn
        exact disjoint_left.mp hdisj hq (hfrE ▸ ⟨subset_closure (h₃ (hgt hq)), hn⟩)
      exact hgA (hinA hgJ hq hqi)
    · obtain ⟨z, hz, hz'⟩ := hm
      exact absurd (interior_subset hz') (disjoint_left.mp h₃ hz)
  have hF₁int : Disjoint F₁ (interior E₀) := by
    refine disjoint_left.mpr fun z hz hzi => ?_
    have hzN := hF₁N hz
    obtain ⟨t, ht, hzt⟩ : ∃ t ∈ Γ'.R \ tiles Γ' A', z ∈ closure t := by
      rw [Drawing.U_eq] at hzN
      rcases hzN with h₃ | h₃
      · obtain ⟨-, t, ht, -, -, hzt⟩ := (mem_boundaryDrawing_V hS).mp h₃
        exact ⟨t, ht, hzt⟩
      · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h₃
        obtain ⟨-, t, ht, hinc⟩ := mem_boundaryDrawing_E.mp hg
        exact ⟨t, ht, closure_minimal (edge_subset_closure_of_incident hS hinc.1 hinc.2.1 hinc.2.2)
          isClosed_closure hzg⟩
    obtain ⟨q, hqi, hqt⟩ := mem_closure_iff.mp hzt _ isOpen_interior hzi
    exact ht.2 (htile t ht.1 ⟨q, hqt, hqi⟩)
  have hfrD₁ : frontier D₁ = F₁ := (IsClosedDisc.frontier_eq_discBd hS hD₁).trans hbD₁
  have hInt : E₀ \ frontier E₀ ⊆ interior E₀ := fun z hz => by
    by_contra hn
    exact hz.2 ⟨subset_closure hz.1, hn⟩
  obtain ⟨p, hp⟩ := (hPs.2 he).1
  have hpF₁ : p ∉ F₁ := fun h' => by
    have hh : p ∈ H.U := H.closure_subset_U (hPs.2 he) (subset_closure hp)
    exact edge_notMem_V (hPs.2 he) hp (hn₁ ⟨h', hh⟩)
  have hpi : p ∈ interior D₁ := by
    by_contra hn
    exact hpF₁ (hfrD₁ ▸ ⟨subset_closure (heD₁ hp), hn⟩)
  have hpE₀ : p ∈ E₀ := hKE₀ (hKU ▸ Or.inl (P.closure_subset_U he (subset_closure hp)))
  have hsubInt : E₀ \ frontier E₀ ⊆ D₁ := by
    rcases subset_or_disjoint_of_frontier hD₁.isClosed
      (IsClosedDisc.isPreconnected_diff_frontier hS hE₀)
      (by
        rw [hfrD₁]
        exact disjoint_left.mpr fun z hz hzF => disjoint_left.mp hF₁int hzF (hInt hz)) with h₃ | h₃
    · exact h₃
    · exfalso
      obtain ⟨q, hqi, hqm⟩ := mem_closure_iff.mp
        (IsClosedDisc.subset_closure_diff_frontier hS hE₀ hpE₀) _ isOpen_interior hpi
      exact disjoint_left.mp h₃ hqm (interior_subset hqi)
  have hE₀D₁ : E₀ ⊆ D₁ := (IsClosedDisc.subset_closure_diff_frontier hS hE₀).trans
    (closure_minimal hsubInt hD₁.isClosed)
  have hh₁ : Holder H Δ F₁ D₁ x₁ y₁ := ⟨hD₁, hD₁Δ, hbD₁, hxy₁, hcap₁, hpath₁, hn₁⟩
  have hline₁ := isLine_of_isPathBetween hpath₁ hxy₁
  refine not_oArc_subset_line hKarc hline₁ fun z hz => ?_
  rw [(hh₁.VU hS).2]
  exact ⟨hKs.U_subset hz, hE₀D₁ (hKE₀ hz)⟩

/-- **A small set of edges of `H` is a path, in a disc in `Δ`.** -/
theorem exists_thread_disc [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ')
  (hS : IsClosedSurface S)
    (hsph : IsSphere S) {A : Set (Set S)} (hA : A ⊆ H.E) (hb : (Whitney.bdry J.toGraph A).ncard ≤ 2)
    (hfin : (Whitney.bdry J.toGraph A).Finite) (hne : A.Nonempty) :
    ∃ (x y : S) (P : Drawing S) (D : Set S), x ≠ y ∧ Whitney.bdry J.toGraph A = {x, y}
      ∧ P.IsSubdrawing H ∧
      P.IsPathBetween x y ∧ P.E = A ∧
      (∀ v ∈ P.V, v ≠ x → v ≠ y → v ∉ subBd Δ ∧ ∀ g ∈ J.E, J.toGraph.Inc g v → g ∈ P.E) ∧
      Holder H Δ (discBd D) D x y ∧ P = H.interSet D := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  have key : ∀ e ∈ A, ∃ F D x y, Holder H Δ F D x y ∧ e ∈ (H.interSet D).E ∧
      Whitney.bdry J.toGraph A = {x, y} := by
    intro e he
    obtain ⟨F, D, x, y, hF, -, hDΔ, hD, hbd, heD, hxy, hcap, hpath, hn, hsub⟩ :=
      exists_dial_of_edge f r hS hsph hA hb hfin he
    refine ⟨F, D, x, y, ⟨hD, hDΔ, hbd, hxy, hcap, hpath, hn⟩, mem_interSet_E.mpr ⟨hA he, heD⟩, ?_⟩
    have h₁ : ({x, y} : Set S) ⊆ Whitney.bdry J.toGraph A := hcap ▸ hsub
    exact (eq_of_subset_of_ncard_le h₁ (by rw [ncard_pair hxy]; exact hb) hfin).symm
  obtain ⟨F, D, x, y, h₁, he₀P, hbd⟩ := key e₀ he₀
  have h₀ : Holder H Δ (discBd D) D x y :=
    ⟨h₁.disc, h₁.sub, rfl, h₁.ne, by rw [h₁.bd]; exact h₁.cap, h₁.path, by rw [h₁.bd]; exact
      h₁.norm⟩
  refine ⟨x, y, H.interSet D, D, h₁.ne, hbd, Drawing.span_isSubdrawing H _ _, h₁.path,
    subset_antisymm ?_ ?_, fun v hv h₃ h₄ => h₁.inner_edges f hS hv h₃ h₄, h₀, rfl⟩
  · obtain ⟨W, hs, hV, hE⟩ := h₁.path
    intro g hg
    have hPs : (H.interSet D).IsSubdrawing H := Drawing.span_isSubdrawing H _ _
    have hg' : g ∈ W.edges := by
      rw [hE] at hg
      exact hg
    have he₀' : e₀ ∈ W.edges := by
      rw [hE] at he₀P
      exact he₀P
    refine walk_same_side (J := J) (hPs.1.trans f.Vsub) (hPs.2.trans f.Esub) W hs
      (fun v _ h₃ h₄ hvb => ?_) e₀ he₀' g hg' he₀
    rw [hbd] at hvb
    rcases hvb with h₅ | h₅
    · exact h₃ h₅
    · exact h₄ h₅
  · intro e he
    by_contra hn
    obtain ⟨F', D', x', y', h₂, heP, hbd'⟩ := key e he
    have hset : ({x, y} : Set S) = {x', y'} := hbd.symm.trans hbd'
    have hx' : x ∈ ({x', y'} : Set S) := hset ▸ Or.inl rfl
    rcases hx' with rfl | hx'
    · have hy' : y' = y := by
        have : y' ∈ ({x, y} : Set S) := hset ▸ Or.inr rfl
        rcases this with h₃ | h₃
        · exact absurd h₃.symm h₂.ne
        · exact h₃
      subst hy'
      exact no_two_paths f r hS hsph h₁ h₂ he₀P heP hn
    · obtain rfl : x = y' := hx'
      have hy' : x' = y := by
        have : x' ∈ ({x, y} : Set S) := hset ▸ Or.inl rfl
        rcases this with h₃ | h₃
        · exact absurd h₃ h₂.ne
        · exact h₃
      subst hy'
      have h₂' : Holder H Δ F' D' x x' := ⟨h₂.disc, h₂.sub, h₂.bd, h₁.ne, by
        rw [pair_comm]; exact h₂.cap, isPathBetween_symm h₂.path, h₂.norm⟩
      exact no_two_paths f r hS hsph h₁ h₂' he₀P heP hn

/-- **A small set of edges of `H` is a path.** -/
theorem exists_thread [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ') (hS : IsClosedSurface S)
    (hsph : IsSphere S) {A : Set (Set S)} (hA : A ⊆ H.E) (hb : (Whitney.bdry J.toGraph A).ncard ≤ 2)
    (hfin : (Whitney.bdry J.toGraph A).Finite) (hne : A.Nonempty) :
    ∃ (x y : S) (P : Drawing S), x ≠ y ∧ Whitney.bdry J.toGraph A = {x, y} ∧ P.IsSubdrawing H
      ∧ P.IsPathBetween x y ∧
      P.E = A ∧ ∀ v ∈ P.V, v ≠ x → v ≠ y →
        v ∉ subBd Δ ∧ ∀ g ∈ J.E, J.toGraph.Inc g v → g ∈ P.E := by
  obtain ⟨x, y, P, -, h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := exists_thread_disc f r hS hsph hA hb hfin hne
  exact ⟨x, y, P, h₁, h₂, h₃, h₄, h₅, h₆⟩

end GraphMinor.GM14.Whitney
