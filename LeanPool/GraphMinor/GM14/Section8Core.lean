/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Adapted
public import LeanPool.GraphMinor.GM09.Section11d
public import LeanPool.GraphMinor.GM09.Section9
public import LeanPool.GraphMinor.GM09.Section2e
public import LeanPool.GraphMinor.GM06.DiscRegions
public import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.DiscDrawing
import LeanPool.GraphMinor.GM07.Section8

/-!
# Graph Minors XIV, (8.1)

This file proves `(8.1)` of N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an
embedding*, J. Combin. Theory Ser. B 65 (1995) 23–50, page 40:
"A society $(G, \Omega)$ has no cross if and only if there is a 3-segregation $\mathscr{S}$ of $G$
with
$\bar{\Omega} \subseteq V(\mathscr{S})$ and an arrangement $\alpha$ of $\mathscr{S}$ in a closed
disc $\Delta$ with $\Omega = \alpha^{-1}(bd(\Delta))$."

The paper says that the proof of (11.11) of Graph Minors IX may be adapted. For the forward
direction we keep that proof, with one change. A society with no cross has a core with no cross and
no tripod, by (2.3) of Graph Minors IX. So the core is rural by (2.4), and we do not need (6.1) or
(11.5). The set `ΩBar₀` of (11.11) is then empty, so the society `(A₀, Ω₀)` also has at most three
vertices on its boundary, and the arrangement moves from the plane to `Σ` by a homeomorphism.

For the reverse direction, each path of a cross runs through the discs of the arrangement, and we
replace each passage by a chord. This gives one connected set for each path. Two disjoint paths
cannot both pass through a disc with at most three boundary vertices. So the two connected sets are
disjoint, which contradicts the way that their ends cross on `bd(Δ)`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v}

/-! ## 1. Crooked transactions of size two -/

/-- A crooked transaction `{P₁, P₂}` with `P₁ ≠ P₂` is a cross: `S.OmegaPathsCross P₁ P₂`. -/
theorem Society.omegaPathsCross_of_isCrookedTransaction_pair (S : Society α β)
    {P₁ P₂ : Graph α β} (hne : P₁ ≠ P₂) (hcr : S.IsCrookedTransaction {P₁, P₂}) :
    S.OmegaPathsCross P₁ P₂ := by
  obtain ⟨⟨A, B, hF⟩, hnp⟩ := hcr
  obtain ⟨a₁, -, b₁, -, h₁⟩ := hF.2.2 P₁ (Or.inl rfl)
  obtain ⟨a₂, -, b₂, -, h₂⟩ := hF.2.2 P₂ (Or.inr rfl)
  have hdisj : Disjoint V(P₁) V(P₂) := hF.1.2 (Or.inl rfl) (Or.inr rfl) hne
  have hends : ∀ v ∈ S.transactionEnds {P₁, P₂}, (v = a₁ ∨ v = b₁) ∨ (v = a₂ ∨ v = b₂) := by
    rintro v ⟨P, hP, b, hv⟩
    have hmem : v ∈ pathEnds S.G P := by
      rw [hv.1.pathEnds_eq]
      exact Or.inl rfl
    rcases hP with rfl | rfl
    · rw [h₁.1.pathEnds_eq] at hmem
      exact Or.inl hmem
    · rw [h₂.1.pathEnds_eq] at hmem
      exact Or.inr hmem
  have hnd₁ : ¬ Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds {P₁, P₂}) := fun hd =>
    hnp P₁ (Or.inl rfl) ⟨Or.inl rfl, a₁, b₁, h₁, Or.inl hd⟩
  have hnd₂ : ¬ Disjoint (S.Ω.interval b₁ a₁) (S.transactionEnds {P₁, P₂}) := fun hd =>
    hnp P₁ (Or.inl rfl) ⟨Or.inl rfl, a₁, b₁, h₁, Or.inr hd⟩
  obtain ⟨x, hx, hxe⟩ := Set.not_disjoint_iff.mp hnd₁
  obtain ⟨y, hy, hye⟩ := Set.not_disjoint_iff.mp hnd₂
  have hxe' : x = a₂ ∨ x = b₂ := by
    rcases hends x hxe with (rfl | rfl) | h
    · exact (S.Ω.not_mem_interval_left _ _ hx).elim
    · exact (S.Ω.not_mem_interval_right _ _ hx).elim
    · exact h
  have hye' : y = a₂ ∨ y = b₂ := by
    rcases hends y hye with (rfl | rfl) | h
    · exact (S.Ω.not_mem_interval_right _ _ hy).elim
    · exact (S.Ω.not_mem_interval_left _ _ hy).elim
    · exact h
  have hxy : x ≠ y := fun h =>
    Set.disjoint_left.mp (S.Ω.disjoint_interval_swap a₁ b₁) hx (h ▸ hy)
  refine ⟨hdisj, a₁, b₁, a₂, b₂, h₁, h₂, S.Ω.crosses_iff_interval.mpr ?_⟩
  rcases hxe' with rfl | rfl <;> rcases hye' with rfl | rfl
  · exact (hxy rfl).elim
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact (hxy rfl).elim

/-- A crooked transaction of size two is a cross. Neither path is peripheral, so each of the two
intervals between the ends of the first path holds an end of the second path. -/
theorem Society.exists_isCross_of_isCrookedTransaction {S : Society α β}
    {P_set : Set (Graph α β)} (h : S.IsCrookedTransaction P_set) (hc : P_set.ncard = 2) :
    ∃ P₁ P₂ : Graph α β, S.IsCross P₁ P₂ := by
  obtain ⟨P₁, P₂, hne, rfl⟩ := Set.ncard_eq_two.mp hc
  exact ⟨P₁, P₂, Society.omegaPathsCross_of_isCrookedTransaction_pair S hne h⟩

/-! ## 2. Moving discs by a homeomorphism -/

section Transport

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- A homeomorphism between two subsets extends to maps of the whole spaces, which are continuous
on those subsets and are inverse to each other there. -/
theorem exists_extensions [Nonempty A] [Nonempty B] {Δ : Set A} {Δ' : Set B} (e : Δ ≃ₜ Δ') :
    ∃ (f : A → B) (f' : B → A), (∀ x : Δ, f x.1 = (e x).1) ∧ ContinuousOn f Δ ∧
      ContinuousOn f' Δ' ∧ f '' Δ = Δ' ∧ LeftInvOn f' f Δ := by
  classical
  let f : A → B := fun x => if h : x ∈ Δ then (e ⟨x, h⟩).1 else Classical.arbitrary B
  let f' : B → A := fun y => if h : y ∈ Δ' then (e.symm ⟨y, h⟩).1 else Classical.arbitrary A
  have hf : ∀ x : Δ, f x.1 = (e x).1 := fun x => by simp [f]
  have hf' : ∀ y : Δ', f' y.1 = (e.symm y).1 := fun y => by simp [f']
  refine ⟨f, f', hf, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    have hc : Continuous fun x : Δ => (e x).1 := continuous_subtype_val.comp e.continuous
    exact hc.congr fun x => (hf x).symm
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    have hc : Continuous fun y : Δ' => (e.symm y).1 :=
      continuous_subtype_val.comp e.symm.continuous
    exact hc.congr fun y => (hf' y).symm
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hf ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
      rw [hf (e.symm ⟨y, hy⟩)]
      simp
  · intro x hx
    rw [hf ⟨x, hx⟩, hf' (e ⟨x, hx⟩)]
    simp

/-- The image of a line under a map with a continuous inverse. -/
theorem isLineWithEnds_image {L : Set A} {a b : A} (hL : IsLineWithEnds L a b)
    {f : A → B} {f' : B → A} (hf : ContinuousOn f L) (hf' : ContinuousOn f' (f '' L))
    (hl : LeftInvOn f' f L) : IsLineWithEnds (f '' L) (f a) (f b) := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hf hf' hl
  obtain ⟨g, h₀, h₁⟩ := hL
  refine ⟨g.trans e, ?_, ?_⟩
  · rw [Homeomorph.trans_apply, he, h₀]
  · rw [Homeomorph.trans_apply, he, h₁]

end Transport

/-- Chords of a closed disc in a space of any universe. -/
theorem exists_chord_of_isClosedDisc {D : Type w} [TopologicalSpace D] {Δ : Set D}
    (hΔ : IsClosedDisc Δ) {a b : D} (ha : a ∈ discBd Δ) (hb : b ∈ discBd Δ) (hab : a ≠ b) :
    ∃ F, IsLineWithEnds F a b ∧ F ⊆ Δ ∧ F ∩ discBd Δ = {a, b} := by
  obtain ⟨φ⟩ := id hΔ
  have hY : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl _⟩
  have : Nonempty D := ⟨a⟩
  obtain ⟨f, f', -, hf, hf', him, hl⟩ := exists_extensions φ
  have hbd : discBd Δ = f '' discBd ClosedUnitDisc := by
    have h := (IsClosedDisc.image hY hf (by rwa [him]) hl).2
    rwa [him] at h
  have hinj : InjOn f ClosedUnitDisc := hl.injOn
  have hsub : discBd ClosedUnitDisc ⊆ ClosedUnitDisc := discBd_subset _
  rw [hbd] at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hab' : a' ≠ b' := fun h => hab (h ▸ rfl)
  obtain ⟨F, hF, hFsub, hFcap⟩ := Surface.exists_chord hY ha' hb' hab'
  refine ⟨f '' F, isLineWithEnds_image hF (hf.mono hFsub) (hf'.mono ?_) (hl.mono hFsub), ?_, ?_⟩
  · rw [← him]
    exact image_mono hFsub
  · rw [← him]
    exact image_mono hFsub
  · rw [← hinj.image_inter hFsub hsub, hFcap, image_pair]

/-- If a closed disc in a space homeomorphic to `ClosedUnitDisc` has a point `x` in the closure of
its complement, then `x` is on the boundary of the disc. To see this, move the disc to the plane. -/
theorem subBd_subset_discBd {D : Type w} [TopologicalSpace D]
    (h : D ≃ₜ ClosedUnitDisc) {X : Set D} (hX : IsClosedDisc X) : subBd X ⊆ discBd X := by
  have : Nonempty ClosedUnitDisc := ⟨⟨0, by simp [ClosedUnitDisc]⟩⟩
  have : Nonempty D := ⟨h.symm (Classical.arbitrary _)⟩
  obtain ⟨f, f', hfe, hf, hf', him, hl⟩ :=
    exists_extensions ((Homeomorph.Set.univ D).trans h)
  have hfc : Continuous f := continuousOn_univ.mp hf
  have hinj : Function.Injective f := injOn_univ.mp hl.injOn
  have hl' : LeftInvOn f' f X := hl.mono (subset_univ X)
  have hf'' : ContinuousOn f' (f '' X) :=
    hf'.mono (by rw [← him]; exact image_mono (subset_univ X))
  obtain ⟨hdisc, hbd⟩ := IsClosedDisc.image hX hfc.continuousOn hf'' hl'
  rintro x ⟨hx₁, hx₂⟩
  have hc₂ : f x ∈ closure (univ \ f '' X) := by
    refine closure_mono ?_ (map_mem_closure hfc hx₂ (mapsTo_image f _))
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨mem_univ _, fun ⟨z, hz, hzy⟩ => hy (hinj hzy ▸ hz)⟩
  have hc₁ : f x ∈ closure (f '' X) := map_mem_closure hfc hx₁ (mapsTo_image f _)
  have hmem : f x ∈ subBd (f '' X) := ⟨hc₁, hc₂⟩
  rw [subBd_eq_discBd_plane hdisc, hbd] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  exact hinj hyx ▸ hy

/-! ## 3. The set of points used by a path -/

section Cover

variable {D : Type w} [TopologicalSpace D]

/-- The part of `Σ` that we use to follow a path `P`: the points of its vertices in `V(𝒮)`, and
chords of discs between two vertices of `P` on the boundary of the same disc. -/
def arrangementCover (S_seg : Set (Society α β)) (α_disc : Society α β → Set D) (α_pt : α → D)
    (P : Graph α β) : Set D :=
  (α_pt '' (V(P) ∩ segregationVertices S_seg)) ∪
    {x | ∃ T ∈ S_seg, ∃ u ∈ T.Ω.bar ∩ V(P), ∃ v ∈ T.Ω.bar ∩ V(P), u ≠ v ∧ ∃ F, x ∈ F ∧
      F ⊆ α_disc T ∧ F ∩ discBd (α_disc T) = {α_pt u, α_pt v}}

variable {G : Graph α β} {S_seg : Set (Society α β)} {α_disc : Society α β → Set D}
  {α_pt : α → D}

/-- A vertex of `V(𝒮)` in a member of `𝒮` is on the boundary of that member. -/
theorem IsGraphSegregation.mem_bar {v : α} (hseg : IsGraphSegregation G S_seg)
    (hv : v ∈ segregationVertices S_seg) {T : Society α β} (hT : T ∈ S_seg)
    (hvT : v ∈ V(T.G)) : v ∈ T.Ω.bar := by
  obtain ⟨T', hT', hvb⟩ := mem_iUnion₂.mp hv
  by_cases hTT : T' = T
  · exact hTT ▸ hvb
  · exact (hseg.vertex_inter_subset T' hT' T hT hTT ⟨T'.bar_subset hvb, hvT⟩).2

/-- Each edge of `G` lies in a member of `𝒮`. -/
theorem IsGraphSegregation.exists_mem_edgeSet {e : β} (hseg : IsGraphSegregation G S_seg)
    (he : e ∈ E(G)) : ∃ T ∈ S_seg, e ∈ E(T.G) := by
  have hle : ∀ Q ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, Q ≤ G := by
    rintro _ ⟨T, hT, rfl⟩
    exact hseg.le T hT
  rw [← hseg.union_eq, edgeSet_subgraphSUnion hle] at he
  obtain ⟨_, ⟨T, hT, rfl⟩, heT⟩ := mem_iUnion₂.mp he
  exact ⟨T, hT, heT⟩

/-- Following a walk of `P` backwards from its last vertex `b`, we build a connected set in the
cover of `P`. It holds the point of the current vertex, if that vertex is in `V(𝒮)`. Also, for each
member of `𝒮` that holds the current vertex, it holds the point of some vertex of `P` on the
boundary of that member. An edge of the walk lies in one member, so a step adds at most one chord
of that member's disc. -/
theorem exists_connected_cover (hseg : IsGraphSegregation G S_seg)
    (hbd : ∀ T ∈ S_seg, ∀ v ∈ T.Ω.bar, α_pt v ∈ discBd (α_disc T))
    (hdisc : ∀ T ∈ S_seg, IsClosedDisc (α_disc T))
    (hinj : InjOn α_pt (segregationVertices S_seg))
    {P : Graph α β} (hP : P ≤ G) {u b : α} (W : GraphWalk P u b)
    (hb : b ∈ segregationVertices S_seg) :
    ∃ K : Set D, IsCompact K ∧ IsConnected K ∧ K ⊆ arrangementCover S_seg α_disc α_pt P ∧
      α_pt b ∈ K ∧ (u ∈ segregationVertices S_seg → α_pt u ∈ K) ∧
      ∀ T ∈ S_seg, u ∈ V(T.G) → ∃ x ∈ T.Ω.bar ∩ V(P), α_pt x ∈ K := by
  induction W with
  | @nil v hv =>
    refine ⟨{α_pt v}, isCompact_singleton, isConnected_singleton, ?_, rfl, fun _ => rfl, ?_⟩
    · rintro _ rfl
      exact Or.inl ⟨v, ⟨hv, hb⟩, rfl⟩
    · exact fun T hT hvT => ⟨v, ⟨hseg.mem_bar hb hT hvT, hv⟩, rfl⟩
  | @cons u v w e hlink rest ih =>
    obtain ⟨K, hKc, hKconn, hKsub, hbK, -, hstep⟩ := ih hb
    have heG : e ∈ E(G) := (hlink.mono hP).edge_mem
    obtain ⟨T₀, hT₀, heT⟩ := hseg.exists_mem_edgeSet heG
    have hl₀ : T₀.G.IsLink e u v :=
      ((hseg.le T₀ hT₀).isLink_iff heT).mpr (hlink.mono hP)
    obtain ⟨x, hx, hxK⟩ := hstep T₀ hT₀ hl₀.right_mem
    have huP : u ∈ V(P) := hlink.left_mem
    by_cases hu : u ∈ T₀.Ω.bar
    · have huV : u ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T₀, hT₀, hu⟩
      have hfin : ∀ K' : Set D, α_pt u ∈ K' → ∀ T ∈ S_seg, u ∈ V(T.G) →
          ∃ x ∈ T.Ω.bar ∩ V(P), α_pt x ∈ K' := fun K' hK' T hT huT =>
        ⟨u, ⟨hseg.mem_bar huV hT huT, huP⟩, hK'⟩
      by_cases hxu : x = u
      · subst hxu
        exact ⟨K, hKc, hKconn, hKsub, hbK, fun _ => hxK, hfin K hxK⟩
      · have hxV : x ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T₀, hT₀, hx.1⟩
        have hne : α_pt x ≠ α_pt u := fun h => hxu (hinj hxV huV h)
        obtain ⟨F, hF, hFsub, hFcap⟩ := exists_chord_of_isClosedDisc (hdisc T₀ hT₀)
          (hbd T₀ hT₀ x hx.1) (hbd T₀ hT₀ u hu) hne
        have huK : α_pt u ∈ K ∪ F := Or.inr hF.right_mem
        refine ⟨K ∪ F, hKc.union hF.isCompact, ?_, ?_, Or.inl hbK, fun _ => huK, hfin _ huK⟩
        · exact ⟨⟨_, Or.inl hbK⟩, hKconn.isPreconnected.union (α_pt x) hxK hF.left_mem
            (GraphMinor.GM07.IsLineWithEnds.isConnected hF).isPreconnected⟩
        · rintro y (hy | hy)
          · exact hKsub hy
          · exact Or.inr ⟨T₀, hT₀, x, hx, u, ⟨hu, huP⟩, hxu, F, hy, hFsub, hFcap⟩
    · refine ⟨K, hKc, hKconn, hKsub, hbK, fun huV => ?_, fun T hT huT => ?_⟩
      · exact (hu (hseg.mem_bar huV hT₀ hl₀.left_mem)).elim
      · by_cases hTT : T = T₀
        · subst hTT
          exact ⟨x, hx, hxK⟩
        · exact (hu (hseg.vertex_inter_subset T hT T₀ hT₀ hTT ⟨huT, hl₀.left_mem⟩).2).elim

/-- A vertex of `V(𝒮)` whose point lies on a chord is an end of the chord. -/
theorem eq_or_eq_of_mem_chord (hbd : ∀ T ∈ S_seg, ∀ v ∈ T.Ω.bar, α_pt v ∈ discBd (α_disc T))
    (hinter : ∀ S₁ ∈ S_seg, ∀ S₂ ∈ S_seg, S₁ ≠ S₂ →
      α_disc S₁ ∩ α_disc S₂ ⊆ α_pt '' (S₁.Ω.bar ∩ S₂.Ω.bar))
    (hinj : InjOn α_pt (segregationVertices S_seg))
    {T : Society α β} (hT : T ∈ S_seg) {u v w : α} (hu : u ∈ T.Ω.bar) (hv : v ∈ T.Ω.bar)
    {F : Set D} (hFsub : F ⊆ α_disc T) (hcap : F ∩ discBd (α_disc T) = {α_pt u, α_pt v})
    (hw : w ∈ segregationVertices S_seg) (hwF : α_pt w ∈ F) : w = u ∨ w = v := by
  have huV : u ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T, hT, hu⟩
  have hvV : v ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T, hT, hv⟩
  have hwT : w ∈ T.Ω.bar := by
    obtain ⟨T', hT', hwb⟩ := mem_iUnion₂.mp hw
    by_cases hTT : T = T'
    · exact hTT ▸ hwb
    · obtain ⟨w', hw', hww⟩ :=
        hinter T hT T' hT' hTT ⟨hFsub hwF, discBd_subset _ (hbd T' hT' w hwb)⟩
      have hw'V : w' ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T, hT, hw'.1⟩
      exact hinj hw'V hw hww ▸ hw'.1
  have hm : α_pt w ∈ F ∩ discBd (α_disc T) := ⟨hwF, hbd T hT w hwT⟩
  rw [hcap] at hm
  rcases hm with h | h
  · exact Or.inl (hinj hw huV h)
  · exact Or.inr (hinj hw hvV h)

/-- Two disjoint paths have disjoint covers. Inside one disc, two chords would need four vertices
on its boundary. Two chords of different discs can only meet at the point of a vertex that is an
end of both chords. -/
theorem disjoint_arrangementCover (hthree : ∀ T ∈ S_seg, T.Ω.bar.ncard ≤ 3)
    (hbd : ∀ T ∈ S_seg, ∀ v ∈ T.Ω.bar, α_pt v ∈ discBd (α_disc T))
    (hinter : ∀ S₁ ∈ S_seg, ∀ S₂ ∈ S_seg, S₁ ≠ S₂ →
      α_disc S₁ ∩ α_disc S₂ ⊆ α_pt '' (S₁.Ω.bar ∩ S₂.Ω.bar))
    (hinj : InjOn α_pt (segregationVertices S_seg))
    {P₁ P₂ : Graph α β} (hdisj : Disjoint V(P₁) V(P₂)) :
    Disjoint (arrangementCover S_seg α_disc α_pt P₁) (arrangementCover S_seg α_disc α_pt P₂) := by
  classical
  have hne : ∀ {v : α}, v ∈ V(P₁) → v ∈ V(P₂) → False := fun h h' =>
    Set.disjoint_left.mp hdisj h h'
  rw [Set.disjoint_left]
  rintro x (⟨v₁, ⟨hv₁, hV₁⟩, rfl⟩ | ⟨T₁, hT₁, u₁, hu₁, w₁, hw₁, huw₁, F₁, hx₁, hF₁, hc₁⟩)
    (⟨v₂, ⟨hv₂, hV₂⟩, h₂⟩ | ⟨T₂, hT₂, u₂, hu₂, w₂, hw₂, huw₂, F₂, hx₂, hF₂, hc₂⟩)
  · exact hne hv₁ (hinj hV₂ hV₁ h₂ ▸ hv₂)
  · rcases eq_or_eq_of_mem_chord hbd hinter hinj hT₂ hu₂.1 hw₂.1 hF₂ hc₂ hV₁ hx₂ with rfl | rfl
    · exact hne hv₁ hu₂.2
    · exact hne hv₁ hw₂.2
  · subst h₂
    rcases eq_or_eq_of_mem_chord hbd hinter hinj hT₁ hu₁.1 hw₁.1 hF₁ hc₁ hV₂ hx₁ with rfl | rfl
    · exact hne hu₁.2 hv₂
    · exact hne hw₁.2 hv₂
  · by_cases hTT : T₁ = T₂
    · subst hTT
      have hne₁ : u₁ ≠ w₁ := huw₁
      have hne₂ : u₂ ≠ w₂ := huw₂
      have hsub : (({u₁, w₁, u₂, w₂} : Finset α) : Set α) ⊆ T₁.Ω.bar := by
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hu₁.1
        · exact hw₁.1
        · exact hu₂.1
        · exact hw₂.1
      have hcard : ({u₁, w₁, u₂, w₂} : Finset α).card = 4 := by
        have h₁₂ : u₁ ≠ u₂ := fun h => hne hu₁.2 (h ▸ hu₂.2)
        have h₁₃ : u₁ ≠ w₂ := fun h => hne hu₁.2 (h ▸ hw₂.2)
        have h₂₂ : w₁ ≠ u₂ := fun h => hne hw₁.2 (h ▸ hu₂.2)
        have h₂₃ : w₁ ≠ w₂ := fun h => hne hw₁.2 (h ▸ hw₂.2)
        rw [Finset.card_insert_of_notMem (by simp [hne₁, h₁₂, h₁₃]),
          Finset.card_insert_of_notMem (by simp [h₂₂, h₂₃]),
          Finset.card_insert_of_notMem (by simp [hne₂]), Finset.card_singleton]
      have hle := Set.ncard_le_ncard hsub (T₁.finite_V.subset T₁.bar_subset)
      rw [Set.ncard_coe_finset, hcard] at hle
      have := hthree T₁ hT₁
      omega
    · obtain ⟨y, hy, rfl⟩ := hinter T₁ hT₁ T₂ hT₂ hTT ⟨hF₁ hx₁, hF₂ hx₂⟩
      have hyV : y ∈ segregationVertices S_seg := mem_iUnion₂.mpr ⟨T₁, hT₁, hy.1⟩
      have hyP₁ : y ∈ V(P₁) := by
        rcases eq_or_eq_of_mem_chord hbd hinter hinj hT₁ hu₁.1 hw₁.1 hF₁ hc₁ hyV hx₁ with rfl | rfl
        · exact hu₁.2
        · exact hw₁.2
      have hyP₂ : y ∈ V(P₂) := by
        rcases eq_or_eq_of_mem_chord hbd hinter hinj hT₂ hu₂.1 hw₂.1 hF₂ hc₂ hyV hx₂ with rfl | rfl
        · exact hu₂.2
        · exact hw₂.2
      exact hne hyP₁ hyP₂

end Cover

/-- The reverse direction of (8.1): a society with an arrangement of this kind has no cross. -/
theorem not_isCross_of_arrangement {D : Type w} [TopologicalSpace D]
    (S : Society α β) (hD : Nonempty (D ≃ₜ ClosedUnitDisc)) {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set D} {α_pt : α → D} (h3 : IsThreeSegregation S.G S_seg)
    (hbar : S.Ω.bar ⊆ segregationVertices S_seg) (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hpb : IsPullbackPerm S_seg α_pt (bd D) S.Ω) {P₁ P₂ : Graph α β} (hcr : S.IsCross P₁ P₂) :
    False := by
  classical
  obtain ⟨h⟩ := id hD
  obtain ⟨hdisj, s₁, t₁, s₂, t₂, h₁, h₂, hc⟩ := hcr
  have hseg := h3.1
  have hdisc : ∀ T ∈ S_seg, IsClosedDisc (α_disc T) := fun T hT => (harr.isClosedDisc T hT).1
  have hbd : ∀ T ∈ S_seg, ∀ v ∈ T.Ω.bar, α_pt v ∈ discBd (α_disc T) := fun T hT v hv =>
    subBd_subset_discBd h (hdisc T hT) ((harr.isClosedDisc T hT).2 v hv)
  obtain ⟨W₁, -⟩ := h₁.1.2
  obtain ⟨W₂, -⟩ := h₂.1.2
  have hs₁ := hbar h₁.2.2.1
  have ht₁ := hbar h₁.2.2.2
  have hs₂ := hbar h₂.2.2.1
  have ht₂ := hbar h₂.2.2.2
  obtain ⟨K₁, hK₁c, hK₁conn, hK₁sub, hK₁t, hK₁s, -⟩ :=
    exists_connected_cover hseg hbd hdisc harr.injOn_pts h₁.1.1 W₁ ht₁
  obtain ⟨K₂, hK₂c, hK₂conn, hK₂sub, hK₂t, hK₂s, -⟩ :=
    exists_connected_cover hseg hbd hdisc harr.injOn_pts h₂.1.1 W₂ ht₂
  obtain ⟨φ, hag⟩ := hpb.2.2
  let ν : α → Set D := fun v => if v ∈ S.Ω.bar then {α_pt v} else ∅
  have hν : ∀ {v p}, p ∈ ν v → v ∈ S.Ω.bar ∧ p = α_pt v := by
    intro v p hp
    by_cases hv : v ∈ S.Ω.bar
    · simpa [ν, hv] using hp
    · simp [ν, hv] at hp
  have hνm : ∀ {v}, v ∈ S.Ω.bar → α_pt v ∈ ν v := fun {v} hv => by simp [ν, hv]
  have hagν : SetAgreesWithOArcHomeo ν S.Ω (bd D) φ := by
    refine ⟨fun v _ p hp => (hν hp).2 ▸ hag.1 v (hν hp).1, fun v₁ v₂ v₃ hcl => ?_⟩
    obtain ⟨t₁, t₂, t₃, h12, h23, h31, e₁, e₂, e₃⟩ := hag.2 v₁ v₂ v₃ hcl
    have hcl' := S.Ω.isClockwise3_iff.mp hcl
    refine ⟨t₁, t₂, t₃, h12, h23, h31, ?_, ?_, ?_⟩
    · rw [e₁]; exact hνm hcl'.2.2.2.1
    · rw [e₂]; exact hνm hcl'.2.2.2.2.1
    · rw [e₃]; exact hνm hcl'.2.2.2.2.2.1
  have hcross : PairsCrossOn (bd D) (α_pt s₁) (α_pt t₁) (α_pt s₂) (α_pt t₂) :=
    pairsCrossOn_of_crosses_set (fun hp hq => (hν hp).2.trans (hν hq).2.symm)
      (fun hp hq => harr.injOn_pts (hbar (hν hp).1) (hbar (hν hq).1)
        ((hν hp).2.symm.trans (hν hq).2)) hagν hc
      (hνm h₁.2.2.1) (hνm h₁.2.2.2) (hνm h₂.2.2.1) (hνm h₂.2.2.2)
  rw [← discBd_univ] at hcross
  obtain ⟨x, hx₁, hx₂⟩ := disc_crossing (univ : Set D) K₁ K₂ (α_pt s₁) (α_pt t₁) (α_pt s₂) (α_pt t₂)
    ⟨h.symm.trans (Homeomorph.Set.univ D).symm⟩ (subset_univ _) (subset_univ _) hK₁c hK₂c hK₁conn
    hK₂conn (hK₁s hs₁) hK₁t (hK₂s hs₂) hK₂t hcross
  exact Set.disjoint_left.mp
    (disjoint_arrangementCover (fun T hT => h3.2 T hT) hbd harr.inter_discs harr.injOn_pts
      hdisj) (hK₁sub hx₁) (hK₂sub hx₂)

/-! ## 4. Moving an arrangement from the plane to `Σ` -/

/-- Let `X` be a closed disc inside a closed disc `Δ` of the plane, meeting `bd(Δ)` in a finite set.
Then the points of `X` that are limits of points of `Δ \ X` are the boundary of `X`. At an interior
point of `Δ` this is the same as being on the boundary of `X` in the plane. A point of `bd(Δ)` is a
limit of the other points of `bd(Δ)`, and only finitely many of those are in `X`. -/
theorem inter_closure_sdiff_eq_discBd {X Δ : Set EuclideanPlane} (hX : IsClosedDisc X)
    (hΔ : IsClosedDisc Δ) (hsub : X ⊆ Δ) (hfin : (X ∩ discBd Δ).Finite) :
    X ∩ closure (Δ \ X) = discBd X := by
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hx, hc⟩
    rw [← subBd_eq_discBd_plane hX]
    exact ⟨subset_closure hx, closure_mono (show Δ \ X ⊆ univ \ X from fun y hy => ⟨mem_univ _,
      hy.2⟩) hc⟩
  · intro x hx
    have hxX : x ∈ X := discBd_subset _ hx
    refine ⟨hxX, ?_⟩
    rw [← subBd_eq_discBd_plane hX] at hx
    by_cases hi : x ∈ interior Δ
    · have hc : x ∈ closure (interior Δ ∩ (univ \ X)) := isOpen_interior.inter_closure ⟨hi, hx.2⟩
      exact closure_mono (show interior Δ ∩ (univ \ X) ⊆ Δ \ X from
        fun y hy => ⟨interior_subset hy.1, hy.2.2⟩) hc
    · have hxb : x ∈ discBd Δ := by
        rw [interior_eq_discInt_plane hΔ] at hi
        by_contra hn
        exact hi ⟨hsub hxX, hn⟩
      obtain ⟨φ⟩ := hΔ.isOArc_discBd
      let g : Circle → EuclideanPlane := fun z => (φ z).1
      have hg : Continuous g := continuous_subtype_val.comp φ.continuous
      have hginj : Function.Injective g := fun a b hab => φ.injective (Subtype.ext hab)
      have hF : {z | g z ∈ X}.Finite :=
        (hfin.preimage hginj.injOn).subset fun z hz => ⟨hz, (φ z).2⟩
      have hn : Nontrivial Circle := ⟨1, Circle.exp Real.pi, fun h => by
        have h' := congrArg (fun z : Circle => (z : ℂ)) h
        norm_num [Circle.coe_exp, Complex.exp_pi_mul_I] at h'⟩
      have hd : Dense (univ \ {z | g z ∈ X}) := dense_univ.sdiff_finite hF
      have hc := map_mem_closure (t := Δ \ X) hg (hd (φ.symm ⟨x, hxb⟩))
        (fun z hz => ⟨discBd_subset _ (φ z).2, hz.2⟩)
      have hz : g (φ.symm ⟨x, hxb⟩) = x := by simp [g]
      rwa [hz] at hc

/-- The closure of the complement of a set, under a map that is a homeomorphism from a compact set
`Δ` onto all of `D`. -/
theorem subBd_image_eq {D : Type w} [TopologicalSpace D] [T2Space D] {Δ X : Set EuclideanPlane}
    {f : EuclideanPlane → D} (hΔ : IsCompact Δ) (hX : IsCompact X) (hsub : X ⊆ Δ)
    (hf : ContinuousOn f Δ) (hinj : InjOn f Δ) (him : f '' Δ = univ) :
    subBd (f '' X) = f '' (X ∩ closure (Δ \ X)) := by
  have hcl : closure (Δ \ X) ⊆ Δ := closure_minimal sdiff_subset hΔ.isClosed
  have hXc : IsClosed (f '' X) := (hX.image_of_continuousOn (hf.mono hsub)).isClosed
  have hcompl : univ \ f '' X = f '' (Δ \ X) := by
    ext y
    constructor
    · rintro ⟨-, hy⟩
      have hy' : y ∈ f '' Δ := by rw [him]; exact mem_univ _
      obtain ⟨x, hx, rfl⟩ := hy'
      exact ⟨x, ⟨hx, fun h => hy ⟨x, h, rfl⟩⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, fun ⟨z, hz, hzx⟩ => hx.2 (hinj hx.1 (hsub hz) hzx.symm ▸ hz)⟩
  have hclo : closure (f '' (Δ \ X)) = f '' closure (Δ \ X) := by
    refine Subset.antisymm (closure_minimal (image_mono subset_closure) ?_)
      ((hf.mono hcl).image_closure)
    exact ((hΔ.of_isClosed_subset isClosed_closure hcl).image_of_continuousOn
      (hf.mono hcl)).isClosed
  unfold subBd
  rw [hXc.closure_eq, hcompl, hclo, hinj.image_inter hsub hcl]

/-- Clockwise agreement moves along a map with a continuous inverse, with the same angles. -/
theorem isNaturalOrderFrom_image {D : Type w} [TopologicalSpace D] {F : Set EuclideanPlane}
    {f : EuclideanPlane → D} {f' : D → EuclideanPlane} (hf : ContinuousOn f F)
    (hf' : ContinuousOn f' (f '' F)) (hl : LeftInvOn f' f F) {ν : α → EuclideanPlane}
    {Ω : CyclicPerm α} {φ : Circle ≃ₜ F} (hag : AgreesWithOArcHomeo ν Ω F φ) :
    IsNaturalOrderFrom (f ∘ ν) Ω (f '' F) := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hf hf' hl
  refine ⟨⟨φ.trans e⟩, φ.trans e, fun v hv => ⟨_, hag.1 v hv, rfl⟩, fun v₁ v₂ v₃ hcl => ?_⟩
  obtain ⟨t₁, t₂, t₃, h12, h23, h31, e₁, e₂, e₃⟩ := hag.2 v₁ v₂ v₃ hcl
  refine ⟨t₁, t₂, t₃, h12, h23, h31, ?_, ?_, ?_⟩
  · rw [Homeomorph.trans_apply, he, e₁]; rfl
  · rw [Homeomorph.trans_apply, he, e₂]; rfl
  · rw [Homeomorph.trans_apply, he, e₃]; rfl

/-- A feasible segregation of Graph Minors IX in which every member has at most three boundary
vertices gives the data on the right side of (8.1). We put `(A₀, Ω₀), …, (A_k, Ω_k)` into one
family, and move discs and points by a homeomorphism from `Δ` to `Σ`. The discs stay away from
`bd(Δ)` except at finitely many points, so the boundary of a disc in `Σ` is the image of its
boundary in the plane. -/
theorem exists_surface_arrangement {D : Type w} [TopologicalSpace D] [T2Space D]
    (S : Society α β) (h : D ≃ₜ ClosedUnitDisc) {k : ℕ} {A₀ : Society α β}
    {A : Fin k → Society α β} (hF : IsFeasibleSegregation S A₀ A)
    (h₀ : A₀.Ω.bar.ncard ≤ 3) (hA : ∀ i : Fin k, (A i).Ω.bar.ncard ≤ 3) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set D) (α_pt : α → D),
      IsThreeSegregation S.G S_seg ∧ S.Ω.bar ⊆ segregationVertices S_seg ∧
        IsSurfaceArrangement S_seg α_disc α_pt ∧ IsPullbackPerm S_seg α_pt (bd D) S.Ω := by
  classical
  obtain ⟨hs, Δ, α₀, α_d, α_p, ha⟩ := hF
  let B : Option (Fin k) → Society α β := fun o => o.elim A₀ A
  let E : Option (Fin k) → Set EuclideanPlane := fun o => o.elim α₀ α_d
  have hEd : ∀ o, IsClosedDisc (E o) ∧ E o ⊆ Δ := by
    rintro (_ | i)
    · exact ha.isClosedDisc_zero
    · exact ha.isClosedDisc_succ i
  have hEag : ∀ o, ∃ φ : Circle ≃ₜ subBd (E o), AgreesWithOArcHomeo α_p (B o).Ω (subBd (E o)) φ
    := by
    rintro (_ | i)
    · obtain ⟨φ, _, hφ⟩ := ha.bd_zero; exact ⟨φ, hφ⟩
    · obtain ⟨φ, _, hφ⟩ := ha.bd_succ i; exact ⟨φ, hφ⟩
  have hEint : ∀ o o', o ≠ o' → E o ∩ E o' ⊆ α_p '' ((B o).Ω.bar ∩ (B o').Ω.bar) := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact ha.inter_zero j
    · change α_d i ∩ α₀ ⊆ α_p '' ((A i).Ω.bar ∩ A₀.Ω.bar)
      rw [inter_comm, inter_comm (A i).Ω.bar]
      exact ha.inter_zero i
    · exact ha.inter_succ i j fun h => hne (h ▸ rfl)
  have hEbd : ∀ o, E o ∩ subBd Δ ⊆ α_p '' ((B o).Ω.bar ∩ S.Ω.bar) := by
    rintro (_ | i)
    · exact ha.inter_bd_zero
    · exact ha.inter_bd_succ i
  have hinj : InjOn α_p (⋃ o, (B o).Ω.bar) := by
    rw [iUnion_option]
    exact ha.injOn_pts
  have hVint : ∀ o o', o ≠ o' → V((B o).G) ∩ V((B o').G) ⊆ (B o).Ω.bar ∩ (B o').Ω.bar := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact hs.inter_zero_subset j
    · change V((A i).G) ∩ V(A₀.G) ⊆ (A i).Ω.bar ∩ A₀.Ω.bar
      rw [inter_comm, inter_comm (A i).Ω.bar]
      exact hs.inter_zero_subset i
    · exact hs.inter_succ_subset i j fun h => hne (h ▸ rfl)
  have hEdisj : ∀ o o', o ≠ o' → Disjoint E((B o).G) E((B o').G) := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact hs.disjoint_zero j
    · exact (hs.disjoint_zero i).symm
    · exact hs.disjoint_succ fun h => hne (h ▸ rfl)
  have hle : ∀ o, (B o).G ≤ S.G := by
    rintro (_ | i)
    · exact hs.le_zero
    · exact hs.le_succ i
  have hVun : (⋃ o, V((B o).G)) = V(S.G) := by
    rw [iUnion_option]
    exact hs.vertexSet_union
  have hEun : (⋃ o, E((B o).G)) = E(S.G) := by
    rw [iUnion_option]
    exact hs.edgeSet_union
  have hbaru : S.Ω.bar ⊆ ⋃ o, (B o).Ω.bar := by
    rw [iUnion_option]
    exact hs.bar_subset_union
  have hb3 : ∀ o, (B o).Ω.bar.ncard ≤ 3 := by
    rintro (_ | i)
    · exact h₀
    · exact hA i
  have hsegV : segregationVertices (range B) = ⋃ o, (B o).Ω.bar := by
    simp [segregationVertices]
  have hBne : ∀ {o o'}, B o ≠ B o' → o ≠ o' := fun h h' => h (h' ▸ rfl)
  have hseg : IsGraphSegregation S.G (range B) := by
    have hle' : ∀ Q ∈ (fun S₀ : Society α β => S₀.G) '' range B, Q ≤ S.G := by
      rintro _ ⟨_, ⟨o, rfl⟩, rfl⟩
      exact hle o
    refine ⟨finite_range B, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨o, rfl⟩
      exact hle o
    · refine (Compatible.of_le_le (subgraphSUnion_le hle') le_rfl).ext ?_ ?_
      · rw [vertexSet_subgraphSUnion, ← hVun]
        simp
      · rw [edgeSet_subgraphSUnion hle', ← hEun]
        simp
    · rintro _ ⟨o, rfl⟩ _ ⟨o', rfl⟩ hne
      exact hVint o o' (hBne hne)
    · rintro _ ⟨o, rfl⟩ _ ⟨o', rfl⟩ hne
      exact hEdisj o o' (hBne hne)
  have h3 : IsThreeSegregation S.G (range B) := by
    refine ⟨hseg, ?_⟩
    rintro _ ⟨o, rfl⟩
    exact hb3 o
  obtain ⟨φ⟩ := id ha.isClosedDisc_Δ
  let ψ : Δ ≃ₜ D := φ.symm.trans h.symm
  have : Nonempty ClosedUnitDisc := ⟨⟨0, by simp [ClosedUnitDisc]⟩⟩
  have : Nonempty D := ⟨h.symm (Classical.arbitrary _)⟩
  obtain ⟨f, f', hfe, hf, hf', him, hl⟩ :=
    exists_extensions (ψ.trans (Homeomorph.Set.univ D).symm)
  have hfe' : ∀ x : Δ, f x.1 = ψ x := hfe
  have hfinj : InjOn f Δ := hl.injOn
  have hΔc : IsCompact Δ := ha.isClosedDisc_Δ.isCompact
  have hbdD : bd D = f '' subBd Δ := by
    rw [subBd_eq_discBd_plane ha.isClosedDisc_Δ, ← image_bd_homeomorph ψ]
    unfold discBd
    rw [image_image]
    exact (image_congr fun x _ => hfe' x).symm
  have hsubBd : ∀ o, subBd (f '' E o) = f '' subBd (E o) := by
    intro o
    have hfin : (E o ∩ discBd Δ).Finite := by
      rw [← subBd_eq_discBd_plane ha.isClosedDisc_Δ]
      exact (((B o).finite_V.subset (B o).bar_subset).image α_p).subset fun x hx =>
        image_mono inter_subset_left (hEbd o hx)
    rw [subBd_image_eq hΔc (hEd o).1.isCompact (hEd o).2 hf hfinj him,
      inter_closure_sdiff_eq_discBd (hEd o).1 ha.isClosedDisc_Δ (hEd o).2 hfin,
      subBd_eq_discBd_plane (hEd o).1]
  have hfEl : ∀ {F : Set EuclideanPlane}, F ⊆ Δ →
      ContinuousOn f F ∧ ContinuousOn f' (f '' F) ∧ LeftInvOn f' f F := fun hF =>
    ⟨hf.mono hF, hf'.mono (subset_univ _), hl.mono hF⟩
  have hsubE : ∀ o, subBd (E o) ⊆ E o := fun o => by
    rw [subBd_eq_discBd_plane (hEd o).1]
    exact discBd_subset _
  have hmemE : ∀ o, ∀ v ∈ (B o).Ω.bar, α_p v ∈ subBd (E o) := fun o v hv => by
    obtain ⟨φ₀, hφ₀⟩ := hEag o
    exact hφ₀.1 v hv
  have hmemΔ : ∀ o, ∀ v ∈ (B o).Ω.bar, α_p v ∈ Δ := fun o v hv =>
    (hEd o).2 (hsubE o (hmemE o v hv))
  have hmemΔ' : ∀ v ∈ ⋃ o, (B o).Ω.bar, α_p v ∈ Δ := fun v hv => by
    obtain ⟨o, hv⟩ := mem_iUnion.mp hv
    exact hmemΔ o v hv
  let α_disc' : Society α β → Set D := fun T => f '' E (Function.invFun B T)
  have hrep : ∀ T ∈ range B, ∃ o, B o = T ∧ α_disc' T = f '' E o := fun T hT =>
    ⟨Function.invFun B T, Function.invFun_eq hT, rfl⟩
  have hinjf' : InjOn (f ∘ α_p) (⋃ o, (B o).Ω.bar) := fun v hv w hw hvw =>
    hinj hv hw (hfinj (hmemΔ' v hv) (hmemΔ' w hw) hvw)
  have hbarV : S.Ω.bar ⊆ segregationVertices (range B) := by
    rw [hsegV]
    exact hbaru
  obtain ⟨φ₁, _, hφ₁⟩ := ha.bd_outer
  have harr : IsSurfaceArrangement (range B) α_disc' (f ∘ α_p) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro T hT
      obtain ⟨o, rfl, hd⟩ := hrep T hT
      rw [hd, hsubBd o]
      obtain ⟨h₁, h₂, h₃⟩ := hfEl (hEd o).2
      exact ⟨(IsClosedDisc.image (hEd o).1 h₁ h₂ h₃).1, fun x hx => ⟨_, hmemE o x hx, rfl⟩⟩
    · intro T₁ hT₁ T₂ hT₂ hne
      obtain ⟨o₁, rfl, hd₁⟩ := hrep T₁ hT₁
      obtain ⟨o₂, rfl, hd₂⟩ := hrep T₂ hT₂
      rw [hd₁, hd₂, ← hfinj.image_inter (hEd o₁).2 (hEd o₂).2]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hEint o₁ o₂ (hBne hne) hy
      exact ⟨w, hw, rfl⟩
    · intro T hT
      obtain ⟨o, rfl, hd⟩ := hrep T hT
      rw [hd, hbdD]
      rintro _ ⟨⟨y, hy, rfl⟩, ⟨z, hz, hzy⟩⟩
      have hsΔ : subBd Δ ⊆ Δ := by
        rw [subBd_eq_discBd_plane ha.isClosedDisc_Δ]
        exact discBd_subset _
      have hzeq : z = y := hfinj (hsΔ hz) ((hEd o).2 hy) hzy
      obtain ⟨w, hw, rfl⟩ := hEbd o ⟨hy, hzeq ▸ hz⟩
      exact ⟨w, hw.1, rfl⟩
    · rw [hsegV]
      exact hinjf'
    · intro T hT
      obtain ⟨o, rfl, hd⟩ := hrep T hT
      obtain ⟨φ₀, hφ₀⟩ := hEag o
      rw [hd, hsubBd o]
      have hs' : subBd (E o) ⊆ Δ := (hsubE o).trans (hEd o).2
      obtain ⟨h₁, h₂, h₃⟩ := hfEl hs'
      exact isNaturalOrderFrom_image h₁ h₂ h₃ hφ₀
  have hpb : IsPullbackPerm (range B) (f ∘ α_p) (bd D) S.Ω := by
    have hsΔ : subBd Δ ⊆ Δ := by
      rw [subBd_eq_discBd_plane ha.isClosedDisc_Δ]
      exact discBd_subset _
    refine ⟨?_, ?_⟩
    · ext v
      refine ⟨fun hv => ⟨hbarV hv, ?_⟩, ?_⟩
      · rw [hbdD]
        exact ⟨_, hφ₁.1 v hv, rfl⟩
      · rintro ⟨hv, hvb⟩
        rw [hsegV] at hv
        obtain ⟨o, hvo⟩ := mem_iUnion.mp hv
        rw [hbdD] at hvb
        obtain ⟨z, hz, hzv⟩ := hvb
        have hzeq : z = α_p v := hfinj (hsΔ hz) (hmemΔ o v hvo) hzv
        obtain ⟨w, hw, hwv⟩ := hEbd o ⟨hsubE o (hmemE o v hvo), hzeq ▸ hz⟩
        have hwv' : w = v := hinj (mem_iUnion.mpr ⟨o, hw.1⟩) (mem_iUnion.mpr ⟨o, hvo⟩) hwv
        exact hwv' ▸ hw.2
    · rw [hbdD]
      obtain ⟨h₁, h₂, h₃⟩ := hfEl hsΔ
      exact isNaturalOrderFrom_image h₁ h₂ h₃ hφ₁
  exact ⟨range B, α_disc', f ∘ α_p, h3, hbarV, harr, hpb⟩

/-! ## 5. Proof of (8.1) -/

/-- The forward direction of (8.1), in the language of Graph Minors IX. We follow the proof of
(11.11) of that paper. The core of a least consolidation is 4-connected and has no cross. It has no
tripod, because (2.3) would then give a cross or a 3-separation. So it is rural by (2.4), and
`C₁` of the split may be dropped. -/
theorem exists_feasibleSegregation_of_no_cross (S : Society α β)
    (hno : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ 2) :
    ∃ (k : ℕ) (S₀ : Society α β) (S_fam : Fin k → Society α β),
      IsFeasibleSegregation S S₀ S_fam ∧ S₀.Ω.bar = ∅ ∧
        ∀ i : Fin k, (S_fam i).Ω.bar.ncard ≤ 3 := by
  obtain ⟨D_set, hD, hmin_core, hmin_card⟩ := exists_minimal_consolidation S
  let CS := consolidationCoreSociety S D_set hD
  have hCS_conn : CS.IsKConnected 4 := GraphMinor.GM09.theorem_11_9_proof S D_set hD hmin_core
  have hCS_no_crooked : ∀ Q_set : Set (Graph α (Sym2 α)),
      CS.IsCrookedTransaction Q_set → Q_set.ncard ≠ 2 :=
    no_crooked_transaction_consolidationCoreSociety hD hno
  have hsimple : IsSimpleGraph CS.G := isSimpleGraph_consolidationCore S D_set
  have hnocross : ¬ ∃ Q₁ Q₂ : Graph α (Sym2 α), CS.IsCross Q₁ Q₂ := by
    rintro ⟨Q₁, Q₂, hQ⟩
    obtain ⟨hc, hn⟩ := Society.OmegaPathsCross.isCrookedTransaction_pair CS hQ
    exact hCS_no_crooked _ hc hn
  have hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α (Sym2 α), CS.IsTripod T₁ T₂ T₃ := by
    rintro ⟨T₁, T₂, T₃, ht⟩
    rcases GraphMinor.GM09.theorem_2_3_proof CS ht with hc | ⟨G₁, G₂, hsep, -⟩
    · exact hnocross hc
    · exact hCS_conn 3 (by omega) G₁ G₂ hsep.1
  obtain ⟨Ω₀, h₀, -, hr⟩ :=
    GraphMinor.GM09.theorem_2_4_proof CS (fun k' hk' => hCS_conn k' (by omega)) hnocross hnotripod
  obtain ⟨S₁, N, P, hdec, hT, hΔ, hbar⟩ := exists_core_decomposition_of_eq hsimple hr rfl rfl 0
  obtain ⟨k, S₀, S_fam, hF, hΩ, hfam, -⟩ :=
    exists_feasible_of_core_decomposition S hD hmin_card hCS_conn hsimple hdec hT (Or.inl hΔ)
  exact ⟨k, S₀, S_fam, hF, by rw [hΩ, hbar], hfam⟩

/-- **Graph Minors XIV, (8.1)** (page 40):
"A society $(G, \Omega)$ has no cross if and only if there is a 3-segregation $\mathscr{S}$
of $G$ with $\bar{\Omega} \subseteq V(\mathscr{S})$ and an arrangement $\alpha$ of
$\mathscr{S}$ in a closed disc $\Delta$ with $\Omega = \alpha^{-1}(bd(\Delta))$." -/
theorem theorem_8_1_proof : Theorem81Statement.{u, v, w} := by
  intro D _ _ α β S _ hD
  refine ⟨fun hno => ?_, ?_⟩
  · obtain ⟨h⟩ := hD
    obtain ⟨k, S₀, S_fam, hF, h₀, hfam⟩ := exists_feasibleSegregation_of_no_cross S hno
    exact exists_surface_arrangement S h hF (by simp [h₀]) hfam
  · rintro ⟨S_seg, α_disc, α_pt, h3, hbar, harr, hpb⟩ P_set hP hc
    obtain ⟨P₁, P₂, hcr⟩ := Society.exists_isCross_of_isCrookedTransaction hP hc
    exact not_isCross_of_arrangement S hD h3 hbar harr hpb hcr

end GraphMinor.GM14
