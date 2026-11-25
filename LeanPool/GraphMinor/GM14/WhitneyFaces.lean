/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.WhitneyGraph
public import LeanPool.GraphMinor.GM12.Section2DiscChordSplit
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM06.Section3Dual

/-!
# The faces of a drawing of a subdivision of a 3-connected graph

Let `J` be a drawing in a sphere of a subdivision of a simple 3-connected graph. We show that the
sphere is a finite union of closed discs with disjoint interiors that miss `U(J)`, and that the
boundary of each disc is a circuit of `J`.

We build the discs by adding ears. A first circuit cuts the sphere into two discs. Each later ear is
a path of `J` that has only its two ends on the part already drawn, so all of it except its ends
lies in the interior of one disc. It cuts that disc into two.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.GM09 GraphMinor.GM11 GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

theorem line_interior_nonempty {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    (L \ {a, b}).Nonempty :=
  Surface.IsLineWithEnds.nonempty_sdiff hL

variable [T2Space S]

/-- Cutting a disc along a line between the two common ends of its boundary arcs. -/
theorem disc_split {D L A B : Set S} {a b : S} (hD : IsClosedDisc D)
    (hL : IsLineWithEnds L a b) (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b)
    (hAB : A ∩ B = {a, b}) (hLA : L ∩ A = {a, b}) (hLB : L ∩ B = {a, b})
    (hbd : discBd D = A ∪ B) (hLD : L ⊆ D) (hab : a ≠ b) :
    ∃ E₁ E₂ : Set S, IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = L ∧
      discBd E₁ = A ∪ L ∧ discBd E₂ = B ∪ L := by
  have hcap : L ∩ discBd D = {a, b} := by
    rw [hbd, inter_union_distrib_left, hLA, hLB, union_self]
  obtain ⟨C₁, C₂, E₁, E₂, _, hcomponents, hE₁, hE₂, hU, hI, hb₁, hb₂, _⟩ :=
    disc_iArc D L a b hD hLD hab hL hcap
  have hcomp : componentsIn (discBd D \ {a, b}) = {A \ {a, b}, B \ {a, b}} := by
    rw [hbd]
    exact GM12.componentsIn_union_sdiff hA.isCompact.isClosed hB.isCompact.isClosed hAB.subset
      (GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff_pair hA)
      (GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff_pair hB)
      (line_interior_nonempty hA) (line_interior_nonempty hB)
  have hend : ({a, b} : Set S) ⊆ L := by
    intro x hx
    exact (hLA.symm ▸ hx).1
  have hrem : ∀ {X : Set S}, (X \ {a, b}) ∪ L = X ∪ L := by
    intro X
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx
    · rintro (hx | hx)
      · by_cases hxF : x ∈ ({a, b} : Set S)
        · exact Or.inr (hend hxF)
        · exact Or.inl ⟨hx, hxF⟩
      · exact Or.inr hx
  have hpair : ({C₁, C₂} : Set (Set S)) = {A \ {a, b}, B \ {a, b}} :=
    hcomponents.symm.trans hcomp
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨E₁, E₂, hE₁, hE₂, hU, hI, hb₁.trans (h₁ ▸ hrem), hb₂.trans (h₂ ▸ hrem)⟩
  · exact ⟨E₂, E₁, hE₂, hE₁, (union_comm _ _).trans hU, (inter_comm _ _).trans hI,
      hb₂.trans (h₂ ▸ hrem), hb₁.trans (h₁ ▸ hrem)⟩

section Basics

variable {J : Drawing S}

omit [T2Space S] in
/-- A vertex of `J` on a subdrawing is a vertex of the subdrawing. -/
theorem mem_V_of_mem_U {C : Drawing S} (hC : C.IsSubdrawing J) {v : S} (hv : v ∈ J.V)
    (hU : v ∈ C.U) : v ∈ C.V := by
  by_contra hn
  obtain ⟨e, he, hve⟩ := C.exists_edge_of_mem hU hn
  exact ((hC.2 he).2.1 hve).2 hv

theorem sup_U {P Q : Drawing S} (hP : P.IsSubdrawing J) (hQ : Q.IsSubdrawing J) :
    (J.sup P Q).U = P.U ∪ Q.U := by
  rw [Drawing.U_eq, Drawing.sup_V hP hQ, Drawing.sup_E hP hQ, P.U_eq, Q.U_eq]
  ext x
  simp only [mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro ((hx | hx) | ⟨e, he | he, hx⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl (Or.inr ⟨e, he, hx⟩)
    · exact Or.inr (Or.inr ⟨e, he, hx⟩)
  · rintro ((hx | ⟨e, he, hx⟩) | (hx | ⟨e, he, hx⟩))
    · exact Or.inl (Or.inl hx)
    · exact Or.inr ⟨e, Or.inl he, hx⟩
    · exact Or.inl (Or.inr hx)
    · exact Or.inr ⟨e, Or.inr he, hx⟩

omit [T2Space S] in
/-- `J` has no loops. -/
theorem no_loop {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) {e : Set S} {v : S} (hl : J.toGraph.IsLink e v v) : False := by
  have he := hl.edge_mem
  rw [h.eunion] at he
  obtain ⟨a, ha, hea⟩ := mem_iUnion₂.mp he
  obtain ⟨u, w, -, ⟨hle, W, hs, -, hE⟩, -⟩ := h.path a ha
  rw [hE] at hea
  have hl' : (P a).IsLink e v v := (hle.isLink_iff (by rw [hE]; exact hea)).mpr hl
  have key : ∀ {x y : S} (W : GraphWalk (P a) x y), W.IsSimple → e ∈ W.edges → False := by
    intro x y W
    induction W with
    | nil _ => intro _ h'; simp [GraphWalk.edges] at h'
    | @cons p q r f hlink rest ih =>
      intro hs hm
      have hs' : rest.IsSimple := (List.nodup_cons.mp hs).2
      simp only [GraphWalk.edges, List.mem_cons] at hm
      rcases hm with rfl | hm
      · have h₁ := (P a).eq_or_eq_of_isLink_of_isLink hlink hl'
        have h₂ := (P a).eq_or_eq_of_isLink_of_isLink hlink.symm hl'
        have hpq : p = q := by
          rcases h₁ with rfl | rfl <;> rcases h₂ with h₂ | h₂ <;> simp_all
        exact (List.nodup_cons.mp hs).1 (hpq ▸ rest.start_mem_support)
      · exact ih hs' hm
  exact key W hs hea

omit [T2Space S] in
/-- An end of an edge is in its closure. -/
theorem mem_closure_of_inc {e : Set S} {v : S} (hi : J.toGraph.Inc e v) : v ∈ closure e := by
  obtain ⟨w, -, -, -, hcap⟩ := hi
  have : v ∈ closure e ∩ J.V := by rw [hcap]; exact Or.inl rfl
  exact this.1

omit [T2Space S] in
/-- A vertex in the closure of an edge is an end of the edge. -/
theorem inc_of_mem_closure {e : Set S} (he : e ∈ J.E) {v : S} (hv : v ∈ closure e)
    (hvV : v ∈ J.V) : J.toGraph.Inc e v := by
  obtain ⟨a, b, hab⟩ := (J.toGraph.edge_mem_iff_exists_isLink e).mp he
  have hm : v ∈ closure e ∩ J.V := ⟨hv, hvV⟩
  rw [hab.2.2.2] at hm
  rcases hm with rfl | rfl
  · exact ⟨b, hab⟩
  · exact ⟨a, hab.symm⟩

/-- Each vertex of a circuit of `J` meets two edges of the circuit. -/
theorem circuit_two_edges {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) {C : Drawing S} (hC : C.IsCircuit) (hs : C.IsSubdrawing J) {v : S}
    (hv : v ∈ C.V) :
    ∃ e ∈ C.E, ∃ f ∈ C.E, e ≠ f ∧ J.toGraph.Inc e v ∧ J.toGraph.Inc f v := by
  have hb : ∃ b ∈ C.V, b ≠ v := by
    obtain ⟨u, W, -, hpos, hV, hE⟩ := id hC
    cases W with
    | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
    | @cons _ m _ f hl rest =>
      have hf : f ∈ C.E := by rw [hE]; simp [GraphWalk.edges]
      have hl' : J.toGraph.IsLink f u m := (hs.isLink_iff hf).mp hl
      have hum : u ≠ m := fun h' => no_loop h (h' ▸ hl')
      have hu : u ∈ C.V := hl.left_mem
      have hm : m ∈ C.V := hl.right_mem
      by_cases huv : u = v
      · exact ⟨m, hm, fun h' => hum (huv.trans h'.symm)⟩
      · exact ⟨u, hu, huv⟩
  obtain ⟨b, hb, hne⟩ := hb
  obtain ⟨P₁, Q, ⟨W₁, hW₁, -, hE₁⟩, ⟨W₂, hW₂, -, hE₂⟩, hP₁, hQ, -, -, -, hd, -⟩ :=
    Drawing.IsCircuit.exists_two_paths hC hv hb hne.symm
  obtain ⟨e, he, ie⟩ := exists_edge_at_start W₁ hne.symm
  obtain ⟨f, hf, if'⟩ := exists_edge_at_start W₂ hne.symm
  have he' : e ∈ P₁.E := by rw [hE₁]; exact he
  have hf' : f ∈ Q.E := by rw [hE₂]; exact hf
  have hconv : ∀ {D : Drawing S} {g : Set S}, D.IsSubdrawing J → g ∈ D.E → D.toGraph.Inc g v →
      J.toGraph.Inc g v := by
    rintro D g hD hg ⟨w, hw⟩
    exact ⟨w, (hD.isLink_iff hg).mp hw⟩
  refine ⟨e, hP₁.2 he', f, hQ.2 hf', fun hef => Set.disjoint_left.mp hd he' (hef ▸ hf'),
    hconv (hP₁.trans hs) he' ie, hconv (hQ.trans hs) hf' if'⟩

end Basics

section FaceSystem

variable {J : Drawing S}

/-- A cell structure on the sphere for a subdrawing `H` of `J`: finitely many closed discs with
disjoint interiors that cover the sphere and miss `U(H)` in their interiors, each with a circuit of
`H` as boundary. -/
structure IsFaceSys (J H : Drawing S) (𝓕 : Set (Set S)) : Prop where
  sub : H.IsSubdrawing J
  finite : 𝓕.Finite
  disc : ∀ D ∈ 𝓕, IsClosedDisc D
  circuit : ∀ D ∈ 𝓕, ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U = discBd D
  free : ∀ D ∈ 𝓕, Disjoint (D \ discBd D) H.U
  disj : ∀ D ∈ 𝓕, ∀ D' ∈ 𝓕, D ≠ D' → Disjoint (D \ discBd D) (D' \ discBd D')
  cover : ⋃₀ 𝓕 = univ
  onbd : ∀ v ∈ H.V, ∃ D ∈ 𝓕, v ∈ discBd D

/-- The first end of a simple walk is in the closure of the rest of its point set. -/
theorem ends_mem_closure_inner {a b : S} {W : GraphWalk J.toGraph a b} (hW : W.IsSimple)
    (hab : a ≠ b) : a ∈ closure ((walkDrawing J W).U \ {a, b}) := by
  obtain ⟨e, he, ie⟩ := exists_edge_at_start W hab
  have heE : e ∈ J.E := ie.edge_mem
  refine closure_mono ?_ (mem_closure_of_inc ie)
  intro x hx
  refine ⟨(mem_walkDrawing_U J W).mpr (Or.inr ⟨e, he, subset_closure hx⟩), ?_⟩
  have hxV : x ∉ J.V := (heE.2.1 hx).2
  rintro (rfl | rfl)
  · exact hxV (W.mem_vertexSet_of_mem_support W.start_mem_support)
  · exact hxV (W.mem_vertexSet_of_mem_support W.end_mem_support)

private theorem IsFaceSys.step_in_disc {H L : Drawing S} {𝓕 : Set (Set S)}
    (hF : IsFaceSys J H 𝓕) {x y : S}
    (hxy : x ≠ y) (hx : x ∈ H.V) (hy : y ∈ H.V)
    (hLs : L.IsSubdrawing J) (hLp : L.IsPathBetween x y)
    (hLl : IsLineWithEnds L.U x y) (hHL : Disjoint L.E H.E)
    (hxL : x ∈ L.V) (hyL : y ∈ L.V) (hcap : L.U ∩ H.U = {x, y})
    {D : Set S} (hD : D ∈ 𝓕) (hLD : L.U ⊆ D)
    (hin : ∀ z ∈ L.V, z ∉ H.V ∨ z = x ∨ z = y) :
    ∃ H' 𝓕', IsFaceSys J H' 𝓕' ∧ H'.E = H.E ∪ L.E := by
  classical
  have hDd := hF.disc D hD
  obtain ⟨C, hCc, hCH, hCU⟩ := hF.circuit D hD
  have hbdH : discBd D ⊆ H.U := by rw [← hCU]; exact hCH.U_subset
  have hxD := hLD (L.V_subset_U hxL)
  have hyD := hLD (L.V_subset_U hyL)
  have hbdp : ∀ {p}, p ∈ D → p ∈ H.U → p ∈ discBd D := fun {p} hp hpH => by
    by_contra hn
    exact Set.disjoint_left.mp (hF.free D hD) ⟨hp, hn⟩ hpH
  have hxH : x ∈ H.U := H.V_subset_U hx
  have hyH : y ∈ H.U := H.V_subset_U hy
  have hxC : x ∈ C.V := mem_V_of_mem_U (hCH.trans hF.sub) (hF.sub.1 hx) (hCU ▸ hbdp hxD hxH)
  have hyC : y ∈ C.V := mem_V_of_mem_U (hCH.trans hF.sub) (hF.sub.1 hy) (hCU ▸ hbdp hyD hyH)
  obtain ⟨P₁, Q₁, hP, hQ, hPC, hQC, -, -, hPQ, hdPQ, hsup⟩ :=
    Drawing.IsCircuit.exists_two_paths hCc hxC hyC hxy
  have hCs : C.IsSubdrawing J := hCH.trans hF.sub
  have hPs := hPC.trans hCs
  have hQs := hQC.trans hCs
  have hPl := isLine_of_isPathBetween hP hxy
  have hQl := isLine_of_isPathBetween hQ hxy
  have hCUeq : C.U = P₁.U ∪ Q₁.U := by
    have := sup_U (J := C) hPC hQC
    rwa [hsup] at this
  have hPQU : P₁.U ∩ Q₁.U = {x, y} := by
    rw [U_inter_of_disjoint hPC hQC hdPQ, hPQ]
  have hPH : P₁.IsSubdrawing H := hPC.trans hCH
  have hQH : Q₁.IsSubdrawing H := hQC.trans hCH
  have hxPQ : x ∈ P₁.V ∩ Q₁.V := hPQ.symm ▸ (Or.inl rfl : x ∈ ({x, y} : Set S))
  have hyPQ : y ∈ P₁.V ∩ Q₁.V := hPQ.symm ▸ (Or.inr rfl : y ∈ ({x, y} : Set S))
  have hLP : L.U ∩ P₁.U = {x, y} := by
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨h₁, h₂⟩
      rw [← hcap]
      exact ⟨h₁, hPH.U_subset h₂⟩
    · rintro p (rfl | rfl)
      · exact ⟨L.V_subset_U hxL, P₁.V_subset_U hxPQ.1⟩
      · exact ⟨L.V_subset_U hyL, P₁.V_subset_U hyPQ.1⟩
  have hLQ : L.U ∩ Q₁.U = {x, y} := by
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨h₁, h₂⟩
      rw [← hcap]
      exact ⟨h₁, hQH.U_subset h₂⟩
    · rintro p (rfl | rfl)
      · exact ⟨L.V_subset_U hxL, Q₁.V_subset_U hxPQ.2⟩
      · exact ⟨L.V_subset_U hyL, Q₁.V_subset_U hyPQ.2⟩
  obtain ⟨E₁, E₂, hE₁, hE₂, hun, hint, hb₁, hb₂⟩ := disc_split hDd hLl hPl hQl hPQU hLP hLQ
    (by rw [← hCU, hCUeq]) hLD hxy
  have hE₁D : E₁ ⊆ D := hun ▸ subset_union_left
  have hE₂D : E₂ ⊆ D := hun ▸ subset_union_right
  have hiE₁ : E₁ \ discBd E₁ ⊆ D \ discBd D := by
    rintro p ⟨hp, hn⟩
    refine ⟨hE₁D hp, fun hpb => hn ?_⟩
    rw [← hCU, hCUeq] at hpb
    rw [hb₁]
    rcases hpb with h | h
    · exact Or.inl h
    · have hpE₂ : p ∈ E₂ := Surface.discBd_subset _ (hb₂ ▸ Or.inl h)
      exact Or.inr (hint ▸ ⟨hp, hpE₂⟩)
  have hiE₂ : E₂ \ discBd E₂ ⊆ D \ discBd D := by
    rintro p ⟨hp, hn⟩
    refine ⟨hE₂D hp, fun hpb => hn ?_⟩
    rw [← hCU, hCUeq] at hpb
    rw [hb₂]
    rcases hpb with h | h
    · have hpE₁ : p ∈ E₁ := Surface.discBd_subset _ (hb₁ ▸ Or.inl h)
      exact Or.inr (hint ▸ ⟨hpE₁, hp⟩)
    · exact Or.inl h
  have hHLs : (J.sup H L).IsSubdrawing J := Drawing.sup_isSubdrawing J H L
  have hHle : H.IsSubdrawing (J.sup H L) := Drawing.le_sup_left hF.sub hLs
  have hLle : L.IsSubdrawing (J.sup H L) := Drawing.le_sup_right hF.sub hLs
  have hU' : (J.sup H L).U = H.U ∪ L.U := sup_U hF.sub hLs
  have hfree' : ∀ {Y : Set S}, Y ⊆ D \ discBd D → Y ∩ L.U = ∅ → Disjoint Y (J.sup H L).U := by
    intro Y hY hYL
    rw [hU', Set.disjoint_left]
    rintro p hp (hpH | hpL)
    · exact Set.disjoint_left.mp (hF.free D hD) (hY hp) hpH
    · have : p ∈ Y ∩ L.U := ⟨hp, hpL⟩
      rw [hYL] at this
      exact this
  have hLb₁ : L.U ⊆ discBd E₁ := by rw [hb₁]; exact subset_union_right
  have hLb₂ : L.U ⊆ discBd E₂ := by rw [hb₂]; exact subset_union_right
  have hnew : ∀ {X : Drawing S}, X.IsPathBetween x y → X.IsSubdrawing H →
      X.V ∩ L.V = {x, y} → Disjoint X.E L.E → ∃ C' : Drawing S, C'.IsCircuit ∧
        C'.IsSubdrawing (J.sup H L) ∧ C'.U = X.U ∪ L.U := by
    intro X hX hXH hV hd
    have hXJ := hXH.trans hF.sub
    refine ⟨J.sup X L, Drawing.isCircuit_sup hX hLp hXJ hLs hxy hV hd, ?_, sup_U hXJ hLs⟩
    refine ⟨?_, ?_⟩
    · rw [Drawing.sup_V hXJ hLs]
      exact union_subset (hXH.trans hHle).1 hLle.1
    · intro e he
      have he' : e ∈ (J.sup X L).E := he
      rw [Drawing.sup_E hXJ hLs] at he'
      rcases he' with he' | he'
      · exact (hXH.trans hHle).2 he'
      · exact hLle.2 he'
  have hVcap : ∀ {X : Drawing S}, X.IsSubdrawing H → x ∈ X.V → y ∈ X.V → X.V ∩ L.V = {x, y} := by
    intro X hXH hxX hyX
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨h₁, h₂⟩
      rcases hin p h₂ with h | h
      · exact (h (hXH.1 h₁)).elim
      · exact h
    · rintro p (rfl | rfl)
      · exact ⟨hxX, hxL⟩
      · exact ⟨hyX, hyL⟩
  have hPV : x ∈ P₁.V ∧ y ∈ P₁.V := by
    have h₁ : x ∈ P₁.V ∩ Q₁.V := by rw [hPQ]; exact Or.inl rfl
    have h₂ : y ∈ P₁.V ∩ Q₁.V := by rw [hPQ]; exact Or.inr rfl
    exact ⟨h₁.1, h₂.1⟩
  have hQV : x ∈ Q₁.V ∧ y ∈ Q₁.V := by
    have h₁ : x ∈ P₁.V ∩ Q₁.V := by rw [hPQ]; exact Or.inl rfl
    have h₂ : y ∈ P₁.V ∩ Q₁.V := by rw [hPQ]; exact Or.inr rfl
    exact ⟨h₁.2, h₂.2⟩
  have hdE : ∀ {X : Drawing S}, X.IsSubdrawing H → Disjoint X.E L.E := fun hX =>
    Set.disjoint_of_subset_left hX.2 hHL.symm
  refine ⟨J.sup H L, insert E₁ (insert E₂ (𝓕 \ {D})), ?_, ?_⟩
  · refine ⟨hHLs, ((hF.finite.subset sdiff_subset).insert _).insert _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro X (rfl | rfl | ⟨hX, -⟩)
      · exact hE₁
      · exact hE₂
      · exact hF.disc X hX
    · rintro X (rfl | rfl | ⟨hX, -⟩)
      · obtain ⟨C', h₁, h₂, h₃⟩ := hnew hP hPH (hVcap hPH hPV.1 hPV.2) (hdE hPH)
        exact ⟨C', h₁, h₂, by rw [h₃, hb₁]⟩
      · obtain ⟨C', h₁, h₂, h₃⟩ := hnew hQ hQH (hVcap hQH hQV.1 hQV.2) (hdE hQH)
        exact ⟨C', h₁, h₂, by rw [h₃, hb₂]⟩
      · obtain ⟨C', h₁, h₂, h₃⟩ := hF.circuit X hX
        exact ⟨C', h₁, h₂.trans hHle, h₃⟩
    · rintro X (rfl | rfl | ⟨hX, hne⟩)
      · refine hfree' hiE₁ (Set.eq_empty_iff_forall_notMem.mpr ?_)
        rintro p ⟨hp, hpL⟩
        exact hp.2 (hLb₁ hpL)
      · refine hfree' hiE₂ (Set.eq_empty_iff_forall_notMem.mpr ?_)
        rintro p ⟨hp, hpL⟩
        exact hp.2 (hLb₂ hpL)
      · rw [hU', Set.disjoint_left]
        rintro p hp (hpH | hpL)
        · exact Set.disjoint_left.mp (hF.free X hX) hp hpH
        · have hzz : p ∈ D \ discBd D := by
            by_cases hpb : p ∈ discBd D
            · have : p ∈ L.U ∩ H.U := ⟨hpL, hbdH hpb⟩
              rw [hcap] at this
              have hbp : p ∈ H.U := by
                rcases this with rfl | rfl
                · exact hxH
                · exact hyH
              exact (Set.disjoint_left.mp (hF.free X hX) hp hbp).elim
            · exact ⟨hLD hpL, hpb⟩
          exact Set.disjoint_left.mp (hF.disj X hX D hD hne) hp hzz
    · have hE₁₂ : Disjoint (E₁ \ discBd E₁) (E₂ \ discBd E₂) := by
        rw [Set.disjoint_left]
        rintro p ⟨h₁, h₂⟩ ⟨h₃, -⟩
        exact h₂ (hLb₁ (hint ▸ ⟨h₁, h₃⟩))
      have hold : ∀ X ∈ 𝓕 \ {D}, ∀ {Y : Set S}, Y ⊆ D \ discBd D →
          Disjoint Y (X \ discBd X) := by
        rintro X ⟨hX, hne⟩ Y hY
        exact Set.disjoint_of_subset_left hY (hF.disj D hD X hX (Ne.symm hne))
      rintro X (rfl | rfl | hX) X' (rfl | rfl | hX') hne
      · exact (hne rfl).elim
      · exact hE₁₂
      · exact hold X' hX' hiE₁
      · exact hE₁₂.symm
      · exact (hne rfl).elim
      · exact hold X' hX' hiE₂
      · exact (hold X hX hiE₁).symm
      · exact (hold X hX hiE₂).symm
      · exact hF.disj X hX.1 X' hX'.1 hne
    · refine eq_univ_of_univ_subset ?_
      intro p _
      have hpc : p ∈ ⋃₀ 𝓕 := by rw [hF.cover]; exact mem_univ p
      obtain ⟨X, hX, hpX⟩ := hpc
      by_cases hXD : X = D
      · subst hXD
        rw [← hun] at hpX
        rcases hpX with h | h
        · exact ⟨E₁, Or.inl rfl, h⟩
        · exact ⟨E₂, Or.inr (Or.inl rfl), h⟩
      · exact ⟨X, Or.inr (Or.inr ⟨hX, hXD⟩), hpX⟩
    · intro v hv
      rw [Drawing.sup_V hF.sub hLs] at hv
      rcases hv with hv | hv
      · obtain ⟨X, hX, hvX⟩ := hF.onbd v hv
        by_cases hXD : X = D
        · subst hXD
          rw [← hCU, hCUeq] at hvX
          rcases hvX with h | h
          · exact ⟨E₁, Or.inl rfl, hb₁ ▸ Or.inl h⟩
          · exact ⟨E₂, Or.inr (Or.inl rfl), hb₂ ▸ Or.inl h⟩
        · exact ⟨X, Or.inr (Or.inr ⟨hX, hXD⟩), hvX⟩
      · exact ⟨E₁, Or.inl rfl, hLb₁ (L.V_subset_U hv)⟩
  · exact Drawing.sup_E hF.sub hLs

/-- Adding an ear to a cell structure. The ear lies in one disc and cuts it in two. -/
theorem IsFaceSys.step (hS : IsClosedSurface S) {H : Drawing S} {𝓕 : Set (Set S)}
    (hF : IsFaceSys J H 𝓕) {x y : S} {W : GraphWalk J.toGraph x y} (hxy : x ≠ y)
    (hW : W.IsSimple) (hx : x ∈ H.V) (hy : y ∈ H.V) (hE : ∀ e ∈ W.edges, e ∉ H.E)
    (hin : ∀ z ∈ W.support, z ∉ H.V ∨ z = x ∨ z = y) :
    ∃ H' 𝓕', IsFaceSys J H' 𝓕' ∧ H'.E = H.E ∪ {e | e ∈ W.edges} := by
  classical
  set L := walkDrawing J W with hLdef
  have hLs : L.IsSubdrawing J := walkDrawing_isSubdrawing J W
  have hLp : L.IsPathBetween x y := walkDrawing_isPathBetween J hW
  have hLl : IsLineWithEnds L.U x y := isLine_of_isPathBetween hLp hxy
  have hLE : L.E = {e | e ∈ W.edges} := walkDrawing_E J W
  have hLV : L.V = {z | z ∈ W.support} := walkDrawing_V J W
  have hHL : Disjoint L.E H.E := by
    rw [hLE, Set.disjoint_left]
    exact fun e he => hE e he
  have hxL : x ∈ L.V := by rw [hLV]; exact W.start_mem_support
  have hyL : y ∈ L.V := by rw [hLV]; exact W.end_mem_support
  have hcap : L.U ∩ H.U = {x, y} := by
    rw [U_inter_of_disjoint hLs hF.sub hHL]
    ext z
    constructor
    · rintro ⟨hz, hzH⟩
      rw [hLV] at hz
      rcases hin z hz with h | h
      · exact (h hzH).elim
      · exact h
    · rintro (rfl | rfl)
      · exact ⟨hxL, hx⟩
      · exact ⟨hyL, hy⟩
  obtain ⟨z, hzL, hzn⟩ := line_interior_nonempty hLl
  have hzH : z ∉ H.U := fun h => hzn (hcap ▸ (⟨hzL, h⟩ : z ∈ L.U ∩ H.U))
  have hzc : z ∈ ⋃₀ 𝓕 := by rw [hF.cover]; exact mem_univ z
  obtain ⟨D, hD, hzD⟩ := hzc
  have hDd := hF.disc D hD
  have hDc : IsClosed D := hDd.isClosed
  obtain ⟨C, _, hCH, hCU⟩ := hF.circuit D hD
  have hbdH : discBd D ⊆ H.U := by rw [← hCU]; exact hCH.U_subset
  have hLo : IsPreconnected (L.U \ {x, y}) :=
    GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff_pair hLl
  have hofH : ∀ {p}, p ∈ L.U \ {x, y} → p ∉ H.U := fun {p} hp h =>
    hp.2 (hcap ▸ (⟨hp.1, h⟩ : p ∈ L.U ∩ H.U))
  have hsubD : L.U \ {x, y} ⊆ D := by
    rcases subset_or_disjoint_of_frontier hDc hLo (by
      rw [IsClosedDisc.frontier_eq_discBd hS hDd, Set.disjoint_left]
      exact fun p hp hb => hofH hp (hbdH hb)) with h | h
    · exact h
    · exact (Set.disjoint_left.mp h ⟨hzL, hzn⟩ hzD).elim
  have hend : ∀ {p}, p ∈ closure (L.U \ {x, y}) → p ∈ D := fun {p} hp =>
    closure_minimal hsubD hDc hp
  have hxD : x ∈ D := hend (ends_mem_closure_inner hW hxy)
  have hyD : y ∈ D := by
    have h' := ends_mem_closure_inner (W := W.reverse) (GraphWalk.IsSimple.reverse hW) hxy.symm
    have hsame : (walkDrawing J W.reverse).U = L.U := by
      ext p
      rw [mem_walkDrawing_U, hLdef, mem_walkDrawing_U, GraphWalk.support_reverse,
        GraphWalk.edges_reverse]
      simp
    rw [hsame, pair_comm] at h'
    exact hend h'
  have hLD : L.U ⊆ D := by
    intro p hp
    by_cases hpe : p ∈ ({x, y} : Set S)
    · rcases hpe with rfl | rfl
      · exact hxD
      · exact hyD
    · exact hsubD ⟨hp, hpe⟩
  obtain ⟨H', 𝓕', hsys, hE'⟩ :=
    hF.step_in_disc hxy hx hy hLs hLp hLl hHL hxL hyL hcap hD hLD
      (fun z hz => hin z (by
        change z ∈ {z | z ∈ W.support}
        rwa [← hLV]))
  exact ⟨H', 𝓕', hsys, hE'.trans (congrArg (H.E ∪ ·) hLE)⟩

/-- The vertices of a subdrawing with a cell structure meet two of its edges. -/
theorem IsFaceSys.two_edges {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) {H : Drawing S} {𝓕 : Set (Set S)} (hF : IsFaceSys J H 𝓕) {v : S}
    (hv : v ∈ H.V) :
    ∃ e ∈ H.E, ∃ f ∈ H.E, e ≠ f ∧ J.toGraph.Inc e v ∧ J.toGraph.Inc f v := by
  obtain ⟨D, hD, hvD⟩ := hF.onbd v hv
  obtain ⟨C, hCc, hCH, hCU⟩ := hF.circuit D hD
  obtain ⟨e, he, f, hf, hef, ie, if'⟩ := circuit_two_edges h hCc (hCH.trans hF.sub)
    (mem_V_of_mem_U (hCH.trans hF.sub) (hF.sub.1 hv) (hCU ▸ hvD))
  exact ⟨e, hCH.2 he, f, hCH.2 hf, hef, ie, if'⟩

/-- The start of the ear decomposition. -/
theorem exists_base (hS : IsSphere S) {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) : ∃ H 𝓕, IsFaceSys J H 𝓕 ∧ H.E.Nonempty := by
  obtain ⟨e, he⟩ : ∃ e, e ∈ E(G₀) := by
    have hpos : 0 < V(G₀).ncard := by have := h.simple.2.1; omega
    obtain ⟨v, hv⟩ := (Set.ncard_pos h.finite_V₀).mp hpos
    obtain ⟨e, -, -, ie, -⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hv
    exact ⟨e, ie.edge_mem⟩
  obtain ⟨x, y, W₁, W₂, hxy, hs₁, hs₂, hcap, hE⟩ := h.exists_two_paths he
  have hp₁ := walkDrawing_isPathBetween J hs₁
  have hp₂ := walkDrawing_isPathBetween J hs₂
  have hsub₁ := walkDrawing_isSubdrawing J W₁
  have hsub₂ := walkDrawing_isSubdrawing J W₂
  have hV : (walkDrawing J W₁).V ∩ (walkDrawing J W₂).V = {x, y} := by
    rw [walkDrawing_V, walkDrawing_V]
    refine Subset.antisymm (fun z hz => hcap z hz.1 hz.2) ?_
    rintro z (rfl | rfl)
    · exact ⟨W₁.start_mem_support, W₂.start_mem_support⟩
    · exact ⟨W₁.end_mem_support, W₂.end_mem_support⟩
  have hd : Disjoint (walkDrawing J W₁).E (walkDrawing J W₂).E := by
    rw [walkDrawing_E, walkDrawing_E, Set.disjoint_left]
    exact fun a ha => hE a ha
  have hC := Drawing.isCircuit_sup hp₁ hp₂ hsub₁ hsub₂ hxy hV hd
  set C := J.sup (walkDrawing J W₁) (walkDrawing J W₂) with hCdef
  have hCs : C.IsSubdrawing J := Drawing.sup_isSubdrawing J _ _
  obtain ⟨Δ₁, Δ₂, hne, hd₁, hd₂, hb₁, hb₂, hun, hint, -, -⟩ := sphere_disc S hS C.U
    (GM11.IsCircuit.isOArc_U hC)
  have hne' : C.E.Nonempty := by
    obtain ⟨a, ha, -⟩ := exists_edge_at_start W₁ hxy
    refine ⟨a, ?_⟩
    rw [hCdef, Drawing.sup_E hsub₁ hsub₂, walkDrawing_E]
    exact Or.inl ha
  refine ⟨C, {Δ₁, Δ₂}, ⟨hCs, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, hne'⟩
  · rintro D (rfl | rfl)
    · exact hd₁
    · exact hd₂
  · rintro D (rfl | rfl)
    · exact ⟨C, hC, ⟨fun _ h => h, fun _ h => h⟩, hb₁.symm⟩
    · exact ⟨C, hC, ⟨fun _ h => h, fun _ h => h⟩, hb₂.symm⟩
  · rintro D (rfl | rfl)
    · rw [hb₁]
      exact disjoint_sdiff_left
    · rw [hb₂]
      exact disjoint_sdiff_left
  · have hdj : Disjoint (Δ₁ \ discBd Δ₁) (Δ₂ \ discBd Δ₂) := by
      rw [Set.disjoint_left]
      rintro p ⟨h₁, h₂⟩ ⟨h₃, -⟩
      exact h₂ (by rw [hb₁, ← hint]; exact ⟨h₁, h₃⟩)
    rintro D (rfl | rfl) D' (rfl | rfl) hn
    · exact (hn rfl).elim
    · exact hdj
    · exact hdj.symm
    · exact (hn rfl).elim
  · rw [sUnion_pair]
    exact hun
  · intro v hv
    exact ⟨Δ₁, Or.inl rfl, by rw [hb₁]; exact C.V_subset_U hv⟩

/-- A drawing of a subdivision of a simple 3-connected graph in a sphere has a cell structure. -/
theorem exists_faces (hS : IsSphere S) {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) : ∃ 𝓕, IsFaceSys J J 𝓕 := by
  classical
  have hcl : IsClosedSurface S := (IsSphere.isClosedSurface hS).1
  have key : ∀ n : ℕ, ∀ H 𝓕, IsFaceSys J H 𝓕 → H.E.Nonempty → (J.E \ H.E).ncard = n →
      ∃ 𝓕', IsFaceSys J J 𝓕' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H 𝓕 hF hne hn
      by_cases hall : J.E ⊆ H.E
      · have hE : H.E = J.E := Subset.antisymm hF.sub.2 hall
        have hV : H.V = J.V := by
          refine Subset.antisymm hF.sub.1 fun v hv => ?_
          obtain ⟨e, he, -, -, -, ie, -⟩ := h.exists_two_edges (x := v) hv
          have hmem : v ∈ closure e ∩ J.V := ⟨mem_closure_of_inc ie, hv⟩
          have heH : e ∈ H.E := hall he
          rw [← hF.sub.closure_inter_V heH] at hmem
          exact hmem.2
        have heq : H = J := Drawing.ext_of_V_E hV hE
        exact ⟨𝓕, heq ▸ hF⟩
      · obtain ⟨g, hg, hgn⟩ := Set.not_subset.mp hall
        obtain ⟨x, y, W, hxy, hs, hx, hy, -, -, hE, hin⟩ := h.exists_ear (Hv := H.V) (Hs := H.E)
          hF.sub.2 hne
          (fun e he v hv => by
            have hm : v ∈ closure e ∩ J.V := ⟨mem_closure_of_inc hv, hv.vertex_mem⟩
            rw [← hF.sub.closure_inter_V he] at hm
            exact hm.2)
          (fun v hv f hf hfn hif => by
            obtain ⟨a, ha, b, hb, hab, ia, ib⟩ := hF.two_edges h hv
            exact h.mem_V₀_of_three (hF.sub.2 ha) (hF.sub.2 hb) hf ia ib hif hab
              (fun h' => hfn (h' ▸ ha)) (fun h' => hfn (h' ▸ hb)))
          hg hgn
        have hE' : ∀ e ∈ W.edges, e ∉ H.E := fun e he =>
          (cls_subset (G := J.toGraph) (B := H.V) (M := E(J.toGraph) \ H.E) ⟨hg, hgn⟩ (hE e he)).2
        obtain ⟨H', 𝓕', hF', hE''⟩ := hF.step hcl hxy hs hx hy hE' hin
        obtain ⟨a, ha, -⟩ := exists_edge_at_start W hxy
        have hsub : J.E \ H'.E ⊂ J.E \ H.E := by
          rw [hE'']
          refine ⟨fun p hp => ⟨hp.1, fun h' => hp.2 (Or.inl h')⟩, fun hc => ?_⟩
          have haJ : a ∈ J.E := by
            have := (walkDrawing_isSubdrawing J W).2 (by rw [walkDrawing_E]; exact ha)
            exact this
          exact (hc ⟨haJ, hE' a ha⟩).2 (Or.inr ha)
        have hfin : (J.E \ H.E).Finite := J.finite_edges.subset sdiff_subset
        exact ih _ (hn ▸ Set.ncard_lt_ncard hsub hfin) H' 𝓕' hF'
          (by rw [hE'']; exact hne.mono subset_union_left) rfl
  obtain ⟨H, 𝓕, hF, hne⟩ := exists_base hS h
  exact key _ H 𝓕 hF hne rfl

/-- A closed disc with boundary in `U(J)` and interior disjoint from `U(J)` is a face. -/
theorem IsFaceSys.eq_of_free (hS : IsClosedSurface S) {𝓕 : Set (Set S)} (hF : IsFaceSys J J 𝓕)
    {D₀ : Set S} (hD₀ : IsClosedDisc D₀) (hbd : discBd D₀ ⊆ J.U)
    (hfree : Disjoint (D₀ \ discBd D₀) J.U) : D₀ ∈ 𝓕 := by
  have hnonempty : (D₀ \ discBd D₀).Nonempty := by
    by_contra hemp
    have hsub : D₀ ⊆ closure (D₀ \ frontier D₀) := IsClosedDisc.subset_closure_diff_frontier hS hD₀
    rw [IsClosedDisc.frontier_eq_discBd hS hD₀, Set.not_nonempty_iff_eq_empty.mp hemp,
      closure_empty] at hsub
    obtain ⟨f⟩ := hD₀
    exact hsub (f ⟨0, by simp [ClosedUnitDisc]⟩).2
  obtain ⟨p, hpD, hpb⟩ := hnonempty
  have hpc : p ∈ ⋃₀ 𝓕 := by rw [hF.cover]; exact mem_univ p
  obtain ⟨D, hD, hpD'⟩ := hpc
  have hDd := hF.disc D hD
  have hpU : p ∉ J.U := fun h' => Set.disjoint_left.mp hfree ⟨hpD, hpb⟩ h'
  obtain ⟨C, -, hCs, hCU⟩ := hF.circuit D hD
  have hbdJ : discBd D ⊆ J.U := by rw [← hCU]; exact hCs.U_subset
  have hc₁ : IsPreconnected (D₀ \ discBd D₀) := by
    have := IsClosedDisc.isPreconnected_diff_frontier hS hD₀
    rwa [IsClosedDisc.frontier_eq_discBd hS hD₀] at this
  have hc₂ : IsPreconnected (D \ discBd D) := by
    have := IsClosedDisc.isPreconnected_diff_frontier hS hDd
    rwa [IsClosedDisc.frontier_eq_discBd hS hDd] at this
  have h₁ : D₀ \ discBd D₀ ⊆ D \ discBd D := by
    have hdisj : Disjoint (D₀ \ discBd D₀) (frontier D) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hDd]
      exact Set.disjoint_of_subset_right hbdJ hfree
    rcases subset_or_disjoint_of_frontier hDd.isClosed hc₁ hdisj with h' | h'
    · exact fun q hq => ⟨h' hq, fun hb => Set.disjoint_left.mp hfree hq (hbdJ hb)⟩
    · exact (Set.disjoint_left.mp h' ⟨hpD, hpb⟩ hpD').elim
  have hpi : p ∈ D \ discBd D := h₁ ⟨hpD, hpb⟩
  have h₂ : D \ discBd D ⊆ D₀ \ discBd D₀ := by
    have hdisj : Disjoint (D \ discBd D) (frontier D₀) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hD₀]
      exact Set.disjoint_of_subset_right hbd (hF.free D hD)
    rcases subset_or_disjoint_of_frontier hD₀.isClosed hc₂ hdisj with h' | h'
    · exact fun q hq => ⟨h' hq, fun hb => Set.disjoint_left.mp (hF.free D hD) hq (hbd hb)⟩
    · exact (Set.disjoint_left.mp h' hpi hpD).elim
  have heq : D₀ \ discBd D₀ = D \ discBd D := Subset.antisymm h₁ h₂
  have hclo : ∀ {X : Set S}, IsClosedDisc X → closure (X \ discBd X) = X := by
    intro X hX
    refine Subset.antisymm (closure_minimal sdiff_subset hX.isClosed) ?_
    have := IsClosedDisc.subset_closure_diff_frontier hS hX
    rwa [IsClosedDisc.frontier_eq_discBd hS hX] at this
  have : D₀ = D := by rw [← hclo hD₀, heq, hclo hDd]
  exact this ▸ hD

end FaceSystem

end GraphMinor.GM14.Whitney
