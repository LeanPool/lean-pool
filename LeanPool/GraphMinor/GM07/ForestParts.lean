/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutConnected
public import LeanPool.GraphMinor.GM19.FragmentOuter
public import LeanPool.GraphMinor.GM19.FragmentCapping
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Preparing a forest for (4.4)

Here are the first steps of (4.4) of Graph Minors VII. A forest `L` with no `O`-arc and no `I`-arc
falls into finitely many parts (`exists_parts`), and one move carries each part into any open set
around a finite set of points of that part (`exists_gather`). Also, a move can take a finite set of
points off the boundary away from a given forest (`exists_move_off`). This needs that a forest holds
no open set (`exists_off_drawing`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S T : Type} [TopologicalSpace S] [TopologicalSpace T]

/-- A line of a closed surface holds no open set. Unlike `line_subset_closure_compl_of_closed`, the
surface need not be connected. -/
theorem line_subset_closure_compl_cap (hT : IsClosedSurface T) {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) : L ⊆ closure Lᶜ := by
  intro p hp
  rw [closure_compl]
  intro hi
  have ht2 : T2Space T := hT.2.1
  have hO : IsOpen (interior L) := isOpen_interior
  have : LocallyConnectedSpace T := IsSurface.locallyConnected hT.isSurface
  set G := connectedComponentIn (interior L) p with hG
  have hGo : IsOpen G := hO.connectedComponentIn
  have hGc : IsPreconnected G := isPreconnected_connectedComponentIn
  have hGL : G ⊆ L := (connectedComponentIn_subset _ _).trans interior_subset
  have hpG : p ∈ G := mem_connectedComponentIn hi
  obtain ⟨f, -, -⟩ := hl
  let g : unitInterval → T := fun t ↦ (f t).1
  have hgi : IsEmbedding g := IsEmbedding.subtypeVal.comp f.isEmbedding
  have hrg : ∀ x ∈ L, ∃ t, g t = x := fun x hx ↦ ⟨f.symm ⟨x, hx⟩, by simp [g]⟩
  have hdn := GM19.dense_compl_finite hT.2.2 (finite_singleton p)
  obtain ⟨q, hqG, hqp⟩ := hdn.inter_open_nonempty G hGo ⟨p, hpG⟩
  obtain ⟨s, rfl⟩ := hrg p hp
  obtain ⟨t, rfl⟩ := hrg q (hGL hqG)
  have hst : s ≠ t := fun h ↦ hqp (by rw [h]; rfl)
  have key : ∀ {s t : unitInterval}, s < t → g s ∈ G → g t ∈ G → False := by
    intro s t hlt hs ht
    obtain ⟨m, hsm, hmt⟩ := exists_between hlt
    have him : ∀ {W : Set T}, W ⊆ range g → g '' (g ⁻¹' W) = W := fun h ↦
      image_preimage_eq_of_subset h
    have hGr : G ⊆ range g := fun x hx ↦ hrg x (hGL hx)
    have hJ : IsPreconnected (g ⁻¹' G) := by
      rw [← hgi.isInducing.isPreconnected_image, him hGr]
      exact hGc
    have hmG : g m ∈ G := hJ.ordConnected.out hs ht ⟨hsm.le, hmt.le⟩
    have hJ' : IsPreconnected (g ⁻¹' (G \ {g m})) := by
      rw [← hgi.isInducing.isPreconnected_image, him (sdiff_subset.trans hGr)]
      exact IsPreconnected.diff_point hT hGc hGo _
    have hmem := hJ'.ordConnected.out (x := s) (y := t)
      ⟨hs, fun h ↦ hsm.ne (hgi.injective h)⟩ ⟨ht, fun h ↦ hmt.ne' (hgi.injective h)⟩ ⟨hsm.le,
        hmt.le⟩
    exact hmem.2 rfl
  rcases lt_or_gt_of_ne hst with h | h
  · exact key h hpG hqG
  · exact key h hqG hpG

/-- **A forest holds no open set.** Every nonempty open set has a point off the forest. Pass to the
capped closed surface. The complement of each line there is open and dense, and there are finitely
many lines. -/
theorem exists_off_drawing (hS : IsSurface S) {H : Drawing S} (hH : IsGraphForest H.toGraph) {X :
  Set S} (hX : IsOpen X) (hne : X.Nonempty) : ∃ x ∈ X, x ∉ H.U := by
  classical
  have ht2S : T2Space S := hS.2.1
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hu, hi', -⟩ := exists_capAll S hS
  have ht2 : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  have hEfin : H.E.Finite := H.finite_edges
  have hline : ∀ e ∈ H.E, IsOpen (j '' closure e)ᶜ ∧ Dense (j '' closure e)ᶜ := fun e he => by
    obtain ⟨u, v, -, -, hl⟩ := edge_line_of_forest hH he
    have hl' : IsLineWithEnds (j '' closure e) (j u) (j v) := by
      obtain ⟨f, h0, h1⟩ := hl
      exact ⟨f.trans (hj.isEmbedding.homeomorphImage _), congrArg j h0, congrArg j h1⟩
    have hc : IsClosed (j '' closure e) := hj.isClosedMap _ isClosed_closure
    refine ⟨hc.isOpen_compl, ?_⟩
    rw [dense_iff_closure_eq, eq_univ_iff_forall]
    intro p
    by_cases hp : p ∈ j '' closure e
    · exact line_subset_closure_compl_cap hT hl' hp
    · exact subset_closure hp
  let D : Set T := ⋂ e ∈ H.E, (j '' closure e)ᶜ
  have hDd : Dense D := dense_biInter_of_isOpen (fun e he => (hline e he).1) hEfin.countable fun e
    he => (hline e he).2
  have hDo : IsOpen D := hEfin.isOpen_biInter fun e he => (hline e he).1
  have hVd : Dense (j '' H.V)ᶜ := GM19.dense_compl_finite hT.2.2 (H.finite_V.image j)
  have hVo : IsOpen (j '' H.V)ᶜ := (H.finite_V.image j).isClosed.isOpen_compl
  have hDD : Dense (D ∩ (j '' H.V)ᶜ) := hDd.inter_of_isOpen_left hVd hDo
  -- The image of the open set off the boundary.
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀X, hy₀b⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hS.2.2 x₀)) X hX hx₀
  let Y : Set S := X \ bd S
  have hYo : IsOpen Y := hX.sdiff (isClosed_bd S)
  obtain ⟨N', hN', hNe⟩ := hj.isInducing.isOpen_iff.mp hYo
  have himg : j '' Y = N' ∩ Kcᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(hNe ▸ hx : x ∈ j ⁻¹' N'), fun hk => ?_⟩
      have : j x ∈ j '' bd S := by
        rw [← hi']
        exact ⟨mem_range_self _, hk⟩
      obtain ⟨x', hx', he⟩ := this
      exact hx.2 (hj.injective he ▸ hx')
    · rintro ⟨h1, h2⟩
      rcases hu.symm ▸ mem_univ y with ⟨x, rfl⟩ | h
      · exact ⟨x, hNe ▸ (h1 : x ∈ j ⁻¹' N'), rfl⟩
      · exact (h2 h).elim
  obtain ⟨_, ⟨x, hx, rfl⟩, hxD, hxV⟩ := hDD.inter_open_nonempty (j '' Y)
    (by rw [himg]; exact hN'.inter hKc.isOpen_compl) ⟨j y₀, y₀, ⟨hy₀X, hy₀b⟩, rfl⟩
  refine ⟨x, hx.1, fun hU => ?_⟩
  rw [H.U_eq] at hU
  rcases hU with h | h
  · exact hxV (mem_image_of_mem j h)
  · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
    exact mem_iInter₂.mp hxD e he (mem_image_of_mem j h)

/-- **Moving points off a forest.** A move takes a finite set of points off the boundary away from a
forest `H`. Points are done one at a time, each by a slide along a short line from a point off `H`.
-/
theorem exists_move_off (hS : IsSurface S) {H : Drawing S} (hH : IsGraphForest H.toGraph) {A : Set
  S} (hA : A.Finite) (hAb : ∀ a ∈ A, a ∉ bd S) : ∃ M : S ≃ₜ S, IsMove M ∧ ∀ a ∈ A, M a ∉ H.U := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hlc := hS.locallyConnected
  induction A, hA using Set.Finite.induction_on with
  | empty => exact ⟨Homeomorph.refl S, IsMove.refl, by simp⟩
  | @insert a A₀ ha₀ hA₀ ih =>
    obtain ⟨M₀, hm₀, h₀⟩ := ih fun x hx => hAb x (mem_insert_of_mem _ hx)
    set b := M₀ a with hb
    have hbb : b ∉ bd S := fun h => hAb a (mem_insert _ _) (by
      have h1 : M₀ b = b := hm₀.1 b h
      have h2 : b = a := M₀.injective h1
      exact h2 ▸ h)
    let Z : Set S := M₀ '' A₀
    have hZf : Z.Finite := hA₀.image _
    have hbZ : b ∉ Z := by
      rintro ⟨x, hx, he⟩
      exact ha₀ (M₀.injective he ▸ hx)
    by_cases hbU : b ∉ H.U
    · refine ⟨M₀, hm₀, fun x hx => ?_⟩
      rcases hx with rfl | hx
      · exact hbU
      · exact h₀ x hx
    rw [not_not] at hbU
    have hXo : IsOpen (bd S ∪ Z)ᶜ := ((isClosed_bd S).union hZf.isClosed).isOpen_compl
    have hbX : b ∈ (bd S ∪ Z)ᶜ := by
      rintro (h | h)
      · exact hbb h
      · exact hbZ h
    let W : Set S := connectedComponentIn (bd S ∪ Z)ᶜ b
    have hWo : IsOpen W := hXo.connectedComponentIn
    have hbW : b ∈ W := mem_connectedComponentIn hbX
    have hWX : W ⊆ (bd S ∪ Z)ᶜ := connectedComponentIn_subset _ _
    have hWp : IsPathConnected W := isPathConnected_of_isOpen hS hWo ⟨⟨b, hbW⟩,
      isPreconnected_connectedComponentIn⟩
    obtain ⟨r, hrW, hrU⟩ := exists_off_drawing hS hH hWo ⟨b, hbW⟩
    have hrb : r ≠ b := fun h => hrU (h ▸ hbU)
    rcases (joinedIn_iff_eq_or_exists_isLineWithEnds hrW hbW).mp (hWp.joinedIn r hrW b hbW) with h
      | ⟨L, hLW, hL⟩
    · exact (hrb h).elim
    obtain ⟨f, hf0, hf1⟩ := hL
    have hc : IsArcMap fun t => (f t).1 := ⟨by fun_prop, fun x y h => f.injective (Subtype.ext h)⟩
    have hcW : ∀ t, (f t).1 ∈ W := fun t => hLW (f t).2
    let N : Set S := (H.U ∪ Z)ᶜ
    have hNo : IsOpen N := (H.isClosed_U.union hZf.isClosed).isOpen_compl
    obtain ⟨α, hmα, hz, hl⟩ := exists_line_slide hS hc (fun t h => hWX (hcW t)
      (.inl h)) hZf.isClosed (fun t _ h => hWX (hcW t) (.inr h)) hNo (by
      show (f 0).1 ∈ N
      rw [hf0]
      rintro (h | h)
      · exact hrU h
      · exact hWX hrW (.inr h))
    refine ⟨M₀.trans α, hm₀.trans hmα, fun x hx => ?_⟩
    rw [Homeomorph.trans_apply]
    rcases hx with rfl | hx
    · have h1 := hl 1
      simp only [hf1] at h1
      exact fun h => h1 (.inl h)
    · have hxZ : M₀ x ∈ Z := mem_image_of_mem _ hx
      rcases hz _ hxZ with h | h
      · rw [h]
        exact h₀ x hx
      · exact (h.1 (.inr hxZ)).elim

/-- **The parts of a drawing with no isolated vertices.** They are the connected components of
`U(L)`. -/
theorem exists_parts {L : Drawing S} (hn : HasNoIsolatedVertices L) : ∃ K : Set
  (Set S), K.Finite ∧ (∀ C ∈ K, IsPreconnected C ∧ IsClosed C ∧ IsClosed (L.U \ C) ∧ C ⊆ L.U) ∧
    (∀ x ∈ L.U, ∃ C ∈ K, x ∈ C) ∧
    (∀ C ∈ K, ∀ D ∈ K, C ≠ D → Disjoint C D) ∧ ∀ A, A ⊆ L.U → IsPreconnected A → ∀ C ∈ K, A ⊆ C
      ∨ Disjoint A C := by
  classical
  have hEfin : L.E.Finite := L.finite_edges
  have hcl : ∀ e ∈ L.E, IsPreconnected (closure e) := fun e he =>
    he.2.2.1.isConnected.isPreconnected.closure
  have hne : ∀ e : L.E, ∃ x, x ∈ e.1 := fun e => e.2.2.2.1.nonempty
  choose p hp using hne
  have hpU : ∀ e : L.E, p e ∈ L.U := fun e => L.closure_subset_U e.2 (subset_closure (hp e))
  let comp : S → Set S := fun x => connectedComponentIn L.U x
  have hc0 : ∀ x ∈ L.U, x ∈ comp x := fun x hx => mem_connectedComponentIn hx
  have hsame : ∀ x ∈ L.U, ∀ A, A ⊆ L.U → IsPreconnected A → x ∈ A → A ⊆ comp x
    := fun x _ A hA hp hxA => hp.subset_connectedComponentIn hxA hA
  have heq : ∀ {x y : S}, y ∈ comp x → comp x = comp y := fun h => connectedComponentIn_eq h
  let K : Set (Set S) := range fun e : L.E => comp (p e)
  have hUe : ∀ x ∈ L.U, ∃ e : L.E, x ∈ closure e.1 := fun x hx => by
    rw [U_eq_biUnion_closure hn] at hx
    obtain ⟨e, he, h⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨e, he⟩, h⟩
  have hclsub : ∀ e : L.E, closure e.1 ⊆ comp (p e) := fun e => hsame _ (hpU e) _
    (L.closure_subset_U e.2) (hcl e.1 e.2) (subset_closure (hp e))
  have hdich : ∀ A, A ⊆ L.U → IsPreconnected A → ∀ x ∈ L.U, A ⊆ comp x ∨ Disjoint A (comp x)
    := fun A hA hAp x hx => by
    by_cases h : Disjoint A (comp x)
    · exact .inr h
    · obtain ⟨y, hyA, hyC⟩ := not_disjoint_iff.mp h
      left
      rw [heq hyC]
      exact hsame y (hA hyA) A hA hAp hyA
  have hK : ∀ C ∈ K, ∃ x ∈ L.U, C = comp x := by
    rintro _ ⟨e, rfl⟩
    exact ⟨p e, hpU e, rfl⟩
  have : Finite L.E := hEfin.to_subtype
  refine ⟨K, finite_range _, ?_, fun x hx => ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨x, hx, rfl⟩ := hK C hC
    have hsub : comp x ⊆ L.U := connectedComponentIn_subset _ _
    refine ⟨isPreconnected_connectedComponentIn, ?_, ?_, hsub⟩
    · refine isClosed_of_closure_subset ?_
      exact hsame x hx _ (closure_minimal hsub L.isClosed_U)
        isPreconnected_connectedComponentIn.closure (subset_closure (hc0 x hx))
    · have he : L.U \ comp x = ⋃ e ∈ {e ∈ L.E | Disjoint (closure e) (comp x)}, closure e := by
        ext z
        constructor
        · rintro ⟨hz, hzc⟩
          obtain ⟨e, hz'⟩ := hUe z hz
          refine mem_iUnion₂.mpr ⟨e.1, ⟨e.2, ?_⟩, hz'⟩
          rcases hdich _ (L.closure_subset_U e.2) (hcl e.1 e.2) x hx with h | h
          · exact absurd (h hz') hzc
          · exact h
        · intro hz
          obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hz
          exact ⟨L.closure_subset_U he.1 hz, disjoint_left.mp he.2 hz⟩
      rw [he]
      exact (hEfin.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  · obtain ⟨e, he⟩ := hUe x hx
    exact ⟨comp (p e), ⟨e, rfl⟩, hclsub e he⟩
  · intro C hC D hD hne
    obtain ⟨x, hx, rfl⟩ := hK C hC
    obtain ⟨y, hy, rfl⟩ := hK D hD
    rcases hdich _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn y hy with
      h | h
    · exact (hne ((heq (h (hc0 x hx))).trans (heq (hc0 x hx)).symm).symm).elim
    · exact h
  · intro A hA hAp C hC
    obtain ⟨x, hx, rfl⟩ := hK C hC
    exact hdich A hA hAp x hx

/-- **One move gathers every part.** Each part `C` of a forest `L` with no `O`-arc and no `I`-arc
has a finite subset `R C`, such that one move carries each part `C` into any open set `N C` around
`R C`, provided these open sets are disjoint and miss the other parts. A part is moved while all
other parts stay fixed, so the moves for different parts do not interfere. -/
theorem exists_gather (hS : IsSurface S) {L : Drawing S} (hP : L.IsProper)
  (hn : HasNoIsolatedVertices L) (hNo : NoArcs L) {K : Set (Set S)} (hK : K.Finite)
    (hparts : ∀ C ∈ K, IsPreconnected C ∧ IsClosed C ∧ IsClosed (L.U \ C) ∧ C ⊆ L.U)
    (hcover : ∀ x ∈ L.U, ∃ C ∈ K, x ∈ C) (hdis : ∀ C ∈ K, ∀ D ∈ K, C ≠ D → Disjoint C D)
      (hdich : ∀ A, A ⊆ L.U → IsPreconnected A → ∀ C ∈ K, A ⊆ C ∨ Disjoint A C) :
    ∃ R : Set S → Set S, (∀ C ∈ K, (R C).Finite ∧ R C ⊆ C) ∧ ∀ N : Set S → Set S, (∀ C ∈ K, IsOpen
      (N C) ∧ R C ⊆ N C) → (∀ C ∈ K, ∀ D ∈ K, C ≠ D → Disjoint (N C) (N D) ∧ Disjoint (N C) D) →
      ∃ G : S ≃ₜ S, IsMove G ∧ ∀ C ∈ K, ∀ z ∈ C, G z ∈ N C := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨l, k, hg, hun, -⟩ := exists_growth _ L rfl hP hNo
  have hUl : listUnion l = L.U := by rw [hun, ← U_eq_biUnion_closure hn]
  have hlines : ∀ A ∈ l, A ⊆ L.U := fun A hA z hz => hUl ▸ (mem_sUnion_of_mem hz hA : z ∈ listUnion
    l)
  have hpart : ∀ C, C ∈ K → ∃ R : Set S, R.Finite ∧ R ⊆ C ∧ ∀ W : Set S, IsClosed W → Disjoint W C
    → ∀ N, IsOpen N → R ⊆ N → Disjoint N W → ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈ C, α z ∈ N)
      ∧ ∀ z ∈ W, α z = z := fun C hC => by
    obtain ⟨R, hRf, hRC, -, h⟩ := exists_shrink_part hS hg ∅ C isClosed_empty (by simp) (by
        rintro z ⟨h1, -⟩
        simpa using h1) fun A hA => hdich A (hlines A hA) (IsLine.isPreconnected
          (hg.isLine A hA)) C hC
    refine ⟨R, hRf, hRC, fun W hW hWC N hN hRN hNW => ?_⟩
    obtain ⟨α, hm, h1, h2⟩ := h W hW hWC N hN (empty_subset _) hRN hNW
    refine ⟨α, hm, fun z hz => h1 z (.inr ⟨?_, hz⟩), h2⟩
    rw [hUl]
    exact (hparts C hC).2.2.2 hz
  choose! R hR using hpart
  refine ⟨R, fun C hC => ⟨(hR C hC).1, (hR C hC).2.1⟩, fun N hN hND => ?_⟩
  have key : ∀ J : Set (Set S), J.Finite → J ⊆ K → ∃ G : S ≃ₜ S, IsMove G ∧
    (∀ C ∈ J, ∀ z ∈ C, G z ∈ N C) ∧ ∀ C ∈ K, C ∉ J → ∀ z ∈ C, G z = z := by
    intro J hJ
    induction J, hJ using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨Homeomorph.refl S, IsMove.refl, by simp, fun _ _ _ _ _ => rfl⟩
    | @insert C₀ J hC₀ _ ih =>
      intro hsub
      obtain ⟨G, hm, h1, h2⟩ := ih fun x hx => hsub (mem_insert_of_mem _ hx)
      have hC₀K := hsub (mem_insert _ _)
      obtain ⟨-, -, hrest, hC₀U⟩ := hparts C₀ hC₀K
      have hC₀fix : ∀ z ∈ C₀, G z = z := h2 C₀ hC₀K hC₀
      obtain ⟨α, hmα, ha1, ha2⟩ := (hR C₀ hC₀K).2.2 (L.U \ C₀) hrest disjoint_sdiff_left
        (G ⁻¹' N C₀) ((hN C₀ hC₀K).1.preimage G.continuous) (fun r hr => by
          have hrC := (hR C₀ hC₀K).2.1 hr
          change G r ∈ N C₀
          rw [hC₀fix r hrC]
          exact (hN C₀ hC₀K).2 hr) (disjoint_left.mpr fun z hz hzW => by
          obtain ⟨D, hDK, hzD⟩ := hcover z hzW.1
          have hne : C₀ ≠ D := fun h => hzW.2 (h ▸ hzD)
          have hz' : G z ∈ N C₀ := hz
          by_cases hDJ : D ∈ J
          · exact disjoint_left.mp (hND C₀ hC₀K D hDK hne).1 hz' (h1 D hDJ z hzD)
          · rw [h2 D hDK hDJ z hzD] at hz'
            exact disjoint_left.mp (hND C₀ hC₀K D hDK hne).2 hz' hzD)
      refine ⟨α.trans G, hmα.trans hm, fun C hC z hz => ?_, fun C hC hCn z hz => ?_⟩
      · rw [Homeomorph.trans_apply]
        rcases hC with rfl | hC
        · exact ha1 z hz
        · have hCK := hsub (mem_insert_of_mem _ hC)
          have hne : C ≠ C₀ := fun h => hC₀ (h ▸ hC)
          rw [ha2 z ⟨(hparts C hCK).2.2.2 hz, disjoint_left.mp (hdis C hCK C₀ hC₀K hne) hz⟩]
          exact h1 C hC z hz
      · rw [Homeomorph.trans_apply]
        have hCJ : C ∉ J := fun h => hCn (mem_insert_of_mem _ h)
        have hne : C ≠ C₀ := fun h => hCn (h ▸ mem_insert _ _)
        rw [ha2 z ⟨(hparts C hC).2.2.2 hz, disjoint_left.mp (hdis C hC C₀ hC₀K hne) hz⟩,
          h2 C hC hCJ z hz]
  obtain ⟨G, hm, h1, -⟩ := key K hK subset_rfl
  exact ⟨G, hm, h1⟩

end GraphMinor.GM07
