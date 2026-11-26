/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46DeficientDisc
public import LeanPool.GraphMinor.GM07.Section46DeficientPath
public import LeanPool.GraphMinor.GM07.Section2
import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM07.Section46JPlus
import LeanPool.GraphMinor.GM07.Section46NullCircle
import LeanPool.GraphMinor.GM07.PullForest
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.Section3
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Separate
import LeanPool.GraphMinor.Surface.ChartCells
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.DiscFan
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.EdgeLoop

/-!
# Step 8 of VII (4.6): the disc misses the seam

Pages 228-229. Let `Z` be a closed disc in `Σ` whose boundary `A` passes through `φ(F)` and lies in
`φ(F) ∪ U(J)`. The seam has only one region, so `Z` contains no circle of `U(J)`. The part of `A`
in `U(J)` is the arc `U(Q)` (or the single point `φ(s) = φ(t)`), and each edge of
`J' = (U(J), V(J) ∪ {φ(s), φ(t)})` either lies in `U(Q)` or misses `A`. By (2.3), each vertex
of `J'` inside `Z` has two edges there. The maximal path argument then gives a path in `Z` between
two
points of `U(Q)`, and this path closes up to a circle in `U(J)`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A line is connected. -/
theorem line_preconnected {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected hL

/-- No circle of the seam lies in a closed disc of `Σ`, because `Σ - U(J)` is connected and dense.
This is the use of "`J'` has only one region" on page 228. -/
theorem Net.not_circle_in_disc (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {Z O : Set S} (hZ : IsClosedDisc Z) (hO : IsOArc O) (hOZ : O ⊆ Z) (hOU : O ⊆ N.seamU) :
    False := by
  refine N.not_nullHomotopic_circle_in_seam hS hcuffs hO hOU ?_
  obtain ⟨e⟩ := id hO
  refine ⟨e, ?_⟩
  obtain ⟨c, hc, hom⟩ := hZ.isSimplyConnectedSet.2
    ⟨fun x => (e x).1, continuous_subtype_val.comp e.continuous⟩
    (by rintro _ ⟨x, rfl⟩; exact hOZ (e x).2)
  exact ⟨c, mem_univ c, hom.mono (subset_univ _)⟩

/-- A path-connected set of `U - V` that meets an edge lies in that edge. -/
theorem subset_edge_of_meets {Γ : Drawing S} {e D : Set S} (he : e ∈ Γ.E) (hD : IsPathConnected D)
    (hsub : D ⊆ Γ.U \ Γ.V) (hmeet : (D ∩ e).Nonempty) : D ⊆ e := by
  obtain ⟨x, hxD, hxe⟩ := hmeet
  have := he.2.2.2 (e ∪ D) (union_subset he.2.1 hsub) (he.2.2.1.union hD ⟨x, hxe, hxD⟩)
    subset_union_left
  exact fun y hy => this ▸ Or.inr hy

/-- A line of `U(Γ)` with its ends at vertices, and with no other vertices, that passes through an
edge is the closure of that edge. -/
theorem closure_edge_eq_of_gap [T2Space S] {Γ : Drawing S} {B e : Set S} {a b x : S} (he : e ∈ Γ.E)
    (hB : IsLineWithEnds B a b) (hab : a ≠ b) (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) (hBU : B ⊆ Γ.U)
    (hBV : ∀ y ∈ B, y ∈ Γ.V → y = a ∨ y = b) (hxB : x ∈ B) (hxe : x ∈ e) (hxV : x ∉ Γ.V) :
    B = closure e := by
  have hin : B \ {a, b} ⊆ Γ.U \ Γ.V := fun y hy =>
    ⟨hBU hy.1, fun hv => hy.2 (hBV y hy.1 hv)⟩
  have hxin : x ∈ B \ {a, b} := ⟨hxB, by
    rintro (rfl | rfl)
    · exact hxV ha
    · exact hxV hb⟩
  have hsub : B \ {a, b} ⊆ e :=
    subset_edge_of_meets he (isPathConnected_sdiff_pair hB) hin ⟨x, hxin, hxe⟩
  have hBc : B ⊆ closure e := hB.subset_closure_diff.trans (closure_mono hsub)
  have haC : a ∈ closure e ∩ Γ.V := ⟨hBc hB.left_mem, ha⟩
  have hbC : b ∈ closure e ∩ Γ.V := ⟨hBc hB.right_mem, hb⟩
  rcases Γ.edge_cond e he with ⟨u, v, -, hcap, hl⟩ | ⟨u, hcap, -⟩
  · rw [hcap] at haC hbC
    have hbC' : b = u ∨ b = v := hbC
    have haC' : a = u ∨ a = v := haC
    have hu : u ∈ B := by
      rcases haC' with h | h
      · exact h ▸ hB.left_mem
      · rcases hbC' with h' | h'
        · exact h' ▸ hB.right_mem
        · exact (hab (h.trans h'.symm)).elim
    have hv : v ∈ B := by
      rcases haC' with h | h
      · rcases hbC' with h' | h'
        · exact (hab (h.trans h'.symm)).elim
        · exact h' ▸ hB.right_mem
      · exact h ▸ hB.left_mem
    exact hl.eq_of_subset (line_preconnected hB) hBc hu hv
  · rw [hcap] at haC hbC
    exact (hab ((mem_singleton_iff.mp haC).trans (mem_singleton_iff.mp hbC).symm)).elim

/-- The inner points of a test arc map off the seam. -/
theorem Net.image_inner_notMem_seam {N : Net S} {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    {F : Set N.D} {s t : N.D} (hFbd : F ∩ bd N.D = {s, t}) {x : S}
    (hx : x ∈ N.φ '' (F \ {s, t})) : x ∉ J.U := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro hxU
  have hybd : y ∈ bd N.D := by
    have : N.φ y ∈ N.seamU := hJ.2.1 ▸ hxU
    rwa [← mem_preimage, N.preimage_seamU] at this
  exact hy.2 (hFbd ▸ ⟨hy.1, hybd⟩)

/-- The part of `A` in `U(J)`, page 228. We write `X` for this set: it is the arc `U(Q)`, or the
single point `φ(s)` if `φ(s) = φ(t)`. Each edge of `J'` that meets `A` lies in `X`. -/
theorem Net.exists_seam_arc [T2Space S] (N : Net S) {G J J' : Drawing S} {G_D : Drawing N.D}
    (hJ : N.IsSeamGraphFor J) (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} {s t : N.D} {A : Set S} (hFn : G_D.IsNormal F)
    (hEnds : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t}) (hAo : IsOArc A)
    (hFA : N.φ '' F ⊆ A) (hAF : A ⊆ N.φ '' F ∪ J.U) (hU : J'.U = J.U)
    (hs : N.φ s ∈ J'.V) (ht : N.φ t ∈ J'.V) :
    ∃ X : Set S, IsPreconnected X ∧ X ⊆ J.U ∧ X ⊆ A ∧ A ⊆ N.φ '' (F \ {s, t}) ∪ X ∧
      N.φ s ∈ X ∧ N.φ t ∈ X ∧ (∀ e ∈ J'.E, (e ∩ A).Nonempty → e ⊆ X) ∧
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ∃ L, IsLineWithEnds L a b ∧ L ⊆ X := by
  have : T2Space N.D := N.isSurface_D.2.1
  have hsU : N.φ s ∈ J.U := hU ▸ J'.V_subset_U hs
  have htU : N.φ t ∈ J.U := hU ▸ J'.V_subset_U ht
  have hoff : ∀ {x}, x ∈ N.φ '' (F \ {s, t}) → x ∉ J.U := fun hx => N.image_inner_notMem_seam hJ
    hFbd hx
  have hsplit : ∀ {x}, x ∈ N.φ '' F → x = N.φ s ∨ x = N.φ t ∨ x ∈ N.φ '' (F \ {s, t}) := by
    rintro _ ⟨y, hy, rfl⟩
    by_cases h₁ : y = s
    · exact .inl (congrArg _ h₁)
    by_cases h₂ : y = t
    · exact .inr (.inl (congrArg _ h₂))
    exact .inr (.inr ⟨y, ⟨hy, by rintro (h | h); exacts [h₁ h, h₂ h]⟩, rfl⟩)
  have hedge : ∀ e ∈ J'.E, e ⊆ J.U \ J'.V := fun e he => hU ▸ he.2.1
  by_cases heq : N.φ s = N.φ t
  · have hO := (lemma_2_6_of_equal_endpoint_images N hPull hEnds hFbd hFn heq).2.1
    have hA : N.φ '' F = A := eq_of_oArc_subset hO hAo hFA
    refine ⟨{N.φ s}, isPreconnected_singleton, singleton_subset_iff.mpr hsU, ?_, ?_, rfl,
      heq.symm, ?_, ?_⟩
    · exact singleton_subset_iff.mpr (hFA (mem_image_of_mem _ hEnds.left_mem))
    · intro x hx
      rcases hsplit (hA.symm ▸ hx) with h | h | h
      · exact .inr h
      · exact .inr (h.trans heq.symm)
      · exact .inl h
    · rintro e he ⟨x, hxe, hxA⟩
      rcases hsplit (hA.symm ▸ hxA) with h | h | h
      · exact ((hedge e he hxe).2 (h ▸ hs)).elim
      · exact ((hedge e he hxe).2 (h ▸ ht)).elim
      · exact (hoff h (hedge e he hxe).1).elim
    · rintro a rfl b rfl hab
      exact (hab rfl).elim
  have hL := lemma_2_6_image_line N hEnds hFbd heq
  have hsA : N.φ s ∈ A := hFA (mem_image_of_mem _ hEnds.left_mem)
  have htA : N.φ t ∈ A := hFA (mem_image_of_mem _ hEnds.right_mem)
  obtain ⟨L₁, L₂, hL₁, hL₂, hu, hi⟩ := IsOArc.lines hAo hsA htA heq
  have key : ∀ {L₁ L₂ : Set S}, IsLineWithEnds L₁ (N.φ s) (N.φ t) →
      IsLineWithEnds L₂ (N.φ s) (N.φ t) → L₁ ∪ L₂ = A → L₁ ∩ L₂ = {N.φ s, N.φ t} →
      N.φ '' (F \ {s, t}) ⊆ L₂ → ∃ X : Set S, IsPreconnected X ∧ X ⊆ J.U ∧ X ⊆ A ∧
        A ⊆ N.φ '' (F \ {s, t}) ∪ X ∧ N.φ s ∈ X ∧ N.φ t ∈ X ∧
        (∀ e ∈ J'.E, (e ∩ A).Nonempty → e ⊆ X) ∧
        ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ∃ L, IsLineWithEnds L a b ∧ L ⊆ X := by
    intro L₁ L₂ hL₁ hL₂ hu hi hWL
    have hFL : N.φ '' F = L₂ := by
      refine hL₂.eq_of_subset (line_preconnected hL) ?_ (mem_image_of_mem _ hEnds.left_mem)
        (mem_image_of_mem _ hEnds.right_mem)
      intro x hx
      rcases hsplit hx with h | h | h
      · exact h ▸ hL₂.left_mem
      · exact h ▸ hL₂.right_mem
      · exact hWL h
    have hXU : L₁ ⊆ J.U := by
      intro x hx
      rcases hAF (by rw [← hu]; exact .inl hx) with h | h
      · have : x ∈ L₁ ∩ L₂ := ⟨hx, hFL ▸ h⟩
        rw [hi] at this
        rcases this with h | h
        · exact h ▸ hsU
        · exact (mem_singleton_iff.mp h) ▸ htU
      · exact h
    have hAW : A ⊆ N.φ '' (F \ {s, t}) ∪ L₁ := by
      intro x hx
      rcases (hu ▸ hx : x ∈ L₁ ∪ L₂) with h | h
      · exact .inr h
      · rcases hsplit (hFL ▸ h) with h | h | h
        · exact .inr (h ▸ hL₁.left_mem)
        · exact .inr (h ▸ hL₁.right_mem)
        · exact .inl h
    refine ⟨L₁, line_preconnected hL₁, hXU, hu ▸ subset_union_left, hAW, hL₁.left_mem,
      hL₁.right_mem, ?_, ?_⟩
    · rintro e he ⟨x, hxe, hxA⟩
      have hxU := hedge e he hxe
      have hxL : x ∈ L₁ := (hAW hxA).resolve_left fun h => hoff h hxU.1
      obtain ⟨B, a, b, hab, hB, hBL, ha, hb, hxB, hBV⟩ := exists_gap_of_line hL₁
        J'.finite_V.isClosed hs ht isPreconnected_singleton (singleton_nonempty x)
        (singleton_subset_iff.mpr ⟨hxL, hxU.2⟩)
      have heq' := closure_edge_eq_of_gap he hB hab ha hb (fun y hy => hU ▸ hXU (hBL hy)) hBV
        (hxB rfl) hxe hxU.2
      exact fun y hy => hBL (heq' ▸ subset_closure hy)
    · intro a ha b hb hab
      obtain ⟨k, hk, hkr, hk0, hk1⟩ := hL₁.exists_arc
      obtain ⟨u, rfl⟩ : a ∈ range k := hkr ▸ ha
      obtain ⟨v, rfl⟩ : b ∈ range k := hkr ▸ hb
      have huv : u ≠ v := fun h => hab (congrArg k h)
      have hinj := hk.2.injOn (s := univ)
      rcases lt_or_gt_of_ne huv with h | h
      · exact ⟨k '' Icc u v, isLineWithEnds_image_Icc_of_injOn hk.1 h hk.2.injOn,
          by rintro _ ⟨r, -, rfl⟩; exact hkr ▸ mem_range_self r⟩
      · exact ⟨k '' Icc v u, GM07.IsLineWithEnds.symm
          (isLineWithEnds_image_Icc_of_injOn hk.1 h hk.2.injOn),
          by rintro _ ⟨r, -, rfl⟩; exact hkr ▸ mem_range_self r⟩
  have hW : IsPreconnected (N.φ '' (F \ {s, t})) :=
    hEnds.isPreconnected_diff.image _ N.quotientMap_φ.continuous.continuousOn
  rcases subset_one_line hL₁ hL₂ hi hW
    (fun x hx => hu.symm ▸ hFA (image_mono sdiff_subset hx)) (fun h => hoff h hsU)
    (fun h => hoff h htU) with h | h
  · exact key hL₂ hL₁ (by rwa [union_comm]) (by rwa [inter_comm]) h
  · exact key hL₁ hL₂ hu hi h

/-- A vertex of `J` of valency at least three has two different edges of `J'`. Each of the two
edges of `J` that end there contains an edge of `J'` that ends there, since `J'` adds only finitely
many vertices. -/
theorem exists_two_edges_at [T2Space S] {J J' : Drawing S} (hU : J'.U = J.U) (hV : J.V ⊆ J'.V)
    {u : S} (hu : u ∈ J.V) (h3 : 3 ≤ vertexValency J u) :
    ∃ e₁ ∈ J'.E, ∃ e₂ ∈ J'.E, e₁ ≠ e₂ ∧ u ∈ closure e₁ ∧ u ∈ closure e₂ := by
  have htwo : ∃ g₁ ∈ J.E, ∃ g₂ ∈ J.E, g₁ ≠ g₂ ∧ u ∈ closure g₁ ∧ u ∈ closure g₂ := by
    by_contra hno
    push Not at hno
    have hsub : ∀ a ∈ J.E, J.VertexIncident u a → ∀ b ∈ J.E, J.VertexIncident u b → a = b := by
      intro a ha hia b hb hib
      by_contra hne
      exact hno a ha b hb hne hia.2.2 hib.2.2
    unfold vertexValency at h3
    set P₂ := {e ∈ J.E | J.VertexIncident u e ∧ (tilde e).ncard = 2}
    set P₁ := {e ∈ J.E | J.VertexIncident u e ∧ (tilde e).ncard = 1}
    have hs₂ : P₂.Subsingleton := fun a ha b hb => hsub a ha.1 ha.2.1 b hb.1 hb.2.1
    have hs₁ : P₁.Subsingleton := fun a ha b hb => hsub a ha.1 ha.2.1 b hb.1 hb.2.1
    have h₂ : P₂.ncard ≤ 1 := by
      have := hs₂.finite.to_subtype
      exact ncard_le_one_iff_subsingleton.mpr hs₂
    have h₁ : P₁.ncard ≤ 1 := by
      have := hs₁.finite.to_subtype
      exact ncard_le_one_iff_subsingleton.mpr hs₁
    rcases P₁.eq_empty_or_nonempty with hP | ⟨a, ha⟩
    · rw [hP, ncard_empty] at h3
      omega
    · have hP₂ : P₂ = ∅ := eq_empty_of_forall_notMem fun b hb => by
        have := hsub a ha.1 ha.2.1 b hb.1 hb.2.1
        have h1 := ha.2.2
        have h2 := hb.2.2
        rw [this, h2] at h1
        omega
      rw [hP₂, ncard_empty] at h3
      omega
  have hin : ∀ g ∈ J.E, u ∈ closure g → ∃ e ∈ J'.E, e ⊆ g ∧ u ∈ closure e := by
    intro g hg hug
    have hgoff : ∀ x ∈ g, x ∈ J.U \ J.V := fun x hx => hg.2.1 hx
    have hsep : ∀ e ∈ J'.E, e ⊆ J.U \ J.V := fun e he x hx => by
      have := he.2.1 hx
      exact ⟨hU ▸ this.1, fun h => this.2 (hV h)⟩
    let E' : Set (Set S) := {e ∈ J'.E | e ⊆ g}
    have hE' : E'.Finite := J'.finite_edges.subset fun e he => he.1
    have hcov : g \ J'.V ⊆ ⋃ e ∈ E', e := by
      rintro x ⟨hx, hxV⟩
      obtain ⟨e, he, hxe⟩ := exists_edge_of_mem (G := J') (hU ▸ (hgoff x hx).1) hxV
      refine mem_iUnion₂.mpr ⟨e, ⟨he, ?_⟩, hxe⟩
      exact subset_edge_of_meets hg he.2.2.1 (hsep e he) ⟨x, hxe, hx⟩
    have hclosed : IsClosed (J'.V ∩ g) := (J'.finite_V.subset inter_subset_left).isClosed
    have hsplit : g ⊆ (g \ J'.V) ∪ (J'.V ∩ g) := fun x hx => by
      by_cases h : x ∈ J'.V
      · exact .inr ⟨h, hx⟩
      · exact .inl ⟨hx, h⟩
    have hc := closure_mono hsplit hug
    rw [closure_union, hclosed.closure_eq] at hc
    rcases hc with h | h
    · have h' := closure_mono hcov h
      rw [hE'.closure_biUnion] at h'
      obtain ⟨e, he, hue⟩ := mem_iUnion₂.mp h'
      exact ⟨e, he.1, he.2, hue⟩
    · exact ((hgoff u h.2).2 hu).elim
  obtain ⟨g₁, hg₁, g₂, hg₂, hne, h₁, h₂⟩ := htwo
  obtain ⟨e₁, he₁, hs₁, hu₁⟩ := hin g₁ hg₁ h₁
  obtain ⟨e₂, he₂, hs₂, hu₂⟩ := hin g₂ hg₂ h₂
  refine ⟨e₁, he₁, e₂, he₂, ?_, hu₁, hu₂⟩
  rintro rfl
  obtain ⟨x, hx⟩ := he₁.1
  exact hne (J.edge_eq_of_mem hg₁ hg₂ (hs₁ hx) (hs₂ hx))

/-- Step 8 of VII (4.6), pages 228-229: the open disc `S` misses `U(J)`. -/
theorem Net.disc_misses_seam (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J : Drawing S} {G_D : Drawing N.D} (hJ : N.IsSeamGraphFor J)
    (hval : ∀ v ∈ J.V, 3 ≤ vertexValency J v) (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} {s t : N.D} (hFn : G_D.IsNormal F) (hEnds : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) {Z : Set S} (hZ : IsClosedDisc Z) (hFZ : N.φ '' F ⊆ discBd Z)
    (hZF : discBd Z ⊆ N.φ '' F ∪ J.U) : Disjoint (discInt Z) J.U := by
  have : T2Space S := hS.2.1
  have hman := hS.2.2
  have hbdZ : discBd Z ⊆ Z := Surface.discBd_subset Z
  have hsbd : s ∈ F ∩ bd N.D := hFbd.symm ▸ Or.inl rfl
  have htbd : t ∈ F ∩ bd N.D := hFbd.symm ▸ Or.inr rfl
  have hsU : N.φ s ∈ J.U := hJ.2.1 ▸ mem_image_of_mem N.φ hsbd.2
  have htU : N.φ t ∈ J.U := hJ.2.1 ▸ mem_image_of_mem N.φ htbd.2
  have hsA : N.φ s ∈ discBd Z := hFZ (mem_image_of_mem _ hsbd.1)
  have htA : N.φ t ∈ discBd Z := hFZ (mem_image_of_mem _ htbd.1)
  have hfin : (J.V ∪ {N.φ s, N.φ t}).Finite := J.finite_V.union (by simp)
  have hsub : J.V ∪ {N.φ s, N.φ t} ⊆ J.U := by
    refine union_subset J.V_subset_U ?_
    rintro x (rfl | h)
    · exact hsU
    · exact (mem_singleton_iff.mp h) ▸ htU
  obtain ⟨J', hU, hV⟩ := exists_drawing_with_more_vertices J hfin subset_union_left hsub
  have hsV : N.φ s ∈ J'.V := hV ▸ Or.inr (Or.inl rfl)
  have htV : N.φ t ∈ J'.V := hV ▸ Or.inr (Or.inr rfl)
  obtain ⟨X, -, hXU, hXA, hAX, -, -, hXe, hXl⟩ := N.exists_seam_arc hJ hPull hFn hEnds hFbd
    hZ.isOArc_discBd hFZ hZF hU hsV htV
  rw [disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨x₀, hx₀S, hx₀U⟩ := nonempty_iff_ne_empty.mpr hne
  have hSo : IsOpen (discInt Z) := hZ.isOpen_discInt hman
  have hE1 : ∀ e ∈ J'.E, (e ∩ discInt Z).Nonempty → e ⊆ discInt Z := by
    rintro e he ⟨y, hye, hyS⟩
    have hdis : Disjoint e (discBd Z) := by
      rw [disjoint_iff_inter_eq_empty]
      by_contra hn
      exact hyS.2 (hXA (hXe e he (nonempty_iff_ne_empty.mpr hn) hye))
    rcases hZ.side hman he.2.2.1.isConnected.isPreconnected hdis with h | h
    · exact h
    · exact (disjoint_left.mp h hye hyS.1).elim
  have hmeet : ∀ e, ∀ u ∈ discInt Z, u ∈ closure e → (e ∩ discInt Z).Nonempty := by
    intro e u huS hu
    obtain ⟨y, hyS, hye⟩ := mem_closure_iff.mp hu _ hSo huS
    exact ⟨y, hye, hyS⟩
  have hV'S : ∀ u ∈ J'.V, u ∈ discInt Z → u ∈ J.V := by
    intro u hu huS
    rcases (hV ▸ hu : u ∈ J.V ∪ {N.φ s, N.φ t}) with h | h | h
    · exact h
    · exact (huS.2 (h ▸ hsA)).elim
    · exact (huS.2 ((mem_singleton_iff.mp h) ▸ htA)).elim
  have htwo : ∀ u ∈ J'.V, u ∈ discInt Z → ∃ e₁ ∈ J'.E, ∃ e₂ ∈ J'.E, e₁ ≠ e₂ ∧
      e₁ ⊆ discInt Z ∧ e₂ ⊆ discInt Z ∧ u ∈ closure e₁ ∧ u ∈ closure e₂ := by
    intro u hu huS
    have huJ := hV'S u hu huS
    obtain ⟨e₁, he₁, e₂, he₂, hne', h₁, h₂⟩ := exists_two_edges_at hU
      (hV ▸ subset_union_left) huJ (hval u huJ)
    exact ⟨e₁, he₁, e₂, he₂, hne', hE1 e₁ he₁ (hmeet e₁ u huS h₁),
      hE1 e₂ he₂ (hmeet e₂ u huS h₂), h₁, h₂⟩
  let ES : Set (Set S) := {e ∈ J'.E | e ⊆ discInt Z}
  have hcl : ∀ e ∈ ES, closure e ⊆ Z := fun e he =>
    closure_minimal (he.2.trans (discInt_subset Z)) hZ.isClosed
  obtain ⟨T, hTs, hTV, hTE⟩ : ∃ T : Drawing S, T.IsSubdrawing J' ∧ T.V = J'.V ∩ Z ∧ T.E = ES := by
    refine ⟨J'.span (J'.V ∩ Z) ES, J'.span_isSubdrawing _ _, ?_, ?_⟩
    · rw [J'.span_V]
      unfold Drawing.spanV
      refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset fun e he x hx =>
        ⟨hx.2, hcl e he.1 hx.1⟩)) fun z hz => .inl ⟨hz, hz.1⟩
    · have hES : ES ⊆ J'.E := fun _ he => he.1
      rw [J'.span_E, inter_eq_left.mpr hES]
  have hTZ : T.U ⊆ Z := by
    rw [Drawing.U_eq]
    rintro x (h | h)
    · exact (hTV ▸ h : x ∈ J'.V ∩ Z).2
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h
      exact hcl e (hTE ▸ he) hxe
  have hTJ : T.U ⊆ N.seamU := fun x hx => hJ.2.1 ▸ hU ▸ hTs.U_subset hx
  have hforest : Surface.IsGraphForest T.toGraph := by
    intro u W hW
    by_contra hpos
    obtain ⟨W', hs, he⟩ := (walkDrawing_isSubdrawing T W).exists_walk_down W
      (by rw [walkDrawing_V]; exact fun x hx => hx) (by rw [walkDrawing_E]; exact fun e he => he)
    have hC : (walkDrawing T W).IsCircuit := by
      refine ⟨u, W', ⟨by rw [hs]; exact hW.1, by rw [he]; exact hW.2⟩, ?_, ?_, ?_⟩
      · change 0 < W'.edges.length
        rw [he]
        exact Nat.pos_of_ne_zero hpos
      · rw [walkDrawing_V, hs]
      · rw [walkDrawing_E, he]
    have hsubT := (walkDrawing_isSubdrawing T W).U_subset
    exact N.not_circle_in_disc hS hcuffs hZ (IsCircuit.isOArc_U hC) (hsubT.trans hTZ)
      (hsubT.trans hTJ)
  have hTEmem : ∀ e, e ∈ J'.E → e ⊆ discInt Z → e ∈ T.E := fun e he hs => hTE ▸ ⟨he, hs⟩
  have hdeg : ∀ u ∈ T.toGraph.vertexSet, u ∉ discBd Z → ∀ e x, T.toGraph.IsLink e u x →
      ∃ e' x', e' ≠ e ∧ T.toGraph.IsLink e' u x' := by
    intro u hu huA e x _
    have huV : u ∈ J'.V ∩ Z := hTV ▸ hu
    obtain ⟨e₁, he₁, e₂, he₂, hne', hs₁, hs₂, h₁, h₂⟩ := htwo u huV.1 ⟨huV.2, huA⟩
    have pick : ∀ e' ∈ J'.E, e' ⊆ discInt Z → u ∈ closure e' → e' ≠ e →
        ∃ e' x', e' ≠ e ∧ T.toGraph.IsLink e' u x' := by
      intro e' he' hs' hu' hn
      obtain ⟨p, q, hpq⟩ := (T.toGraph.edge_mem_iff_exists_isLink e').mp (hTEmem e' he' hs')
      have : u ∈ closure e' ∩ T.V := ⟨hu', hu⟩
      rw [hpq.2.2.2] at this
      rcases this with rfl | h
      · exact ⟨e', q, hn, hpq⟩
      · rw [mem_singleton_iff.mp h]
        exact ⟨e', p, hn, hpq.symm⟩
    by_cases h : e₁ = e
    · exact pick e₂ he₂ hs₂ h₂ (fun h' => hne' (h.trans h'.symm))
    · exact pick e₁ he₁ hs₁ h₁ h
  obtain ⟨e₀, he₀⟩ : ∃ e₀, e₀ ∈ J'.E ∧ e₀ ⊆ discInt Z := by
    by_cases hx : x₀ ∈ J'.V
    · obtain ⟨e₁, he₁, -, -, -, hs₁, -⟩ := htwo x₀ hx hx₀S
      exact ⟨e₁, he₁, hs₁⟩
    · obtain ⟨e, he, hxe⟩ := exists_edge_of_mem (G := J') (hU ▸ hx₀U) hx
      exact ⟨e, he, hE1 e he ⟨x₀, hxe, hx₀S⟩⟩
  obtain ⟨p, q, hpq⟩ := (T.toGraph.edge_mem_iff_exists_isLink e₀).mp (hTEmem e₀ he₀.1 he₀.2)
  obtain ⟨a, b, W, ha, hb, hab, hW, hin⟩ := exists_path_between_of_forest (B := discBd Z)
    T.finite_V hforest hdeg hpq
  have hP := walkDrawing_isPathBetween T hW
  have hline := isLine_of_isPathBetween hP hab
  have hsubP := (walkDrawing_isSubdrawing T W).U_subset
  have hmemX : ∀ y ∈ W.support, y ∈ discBd Z → y ∈ X := by
    intro y hy hyA
    have hyU : y ∈ J.U := by
      have hyV : y ∈ T.V := W.mem_vertexSet_of_mem_support hy
      exact hU ▸ hTs.U_subset (T.V_subset_U hyV)
    exact (hAX hyA).resolve_left fun h => N.image_inner_notMem_seam hJ hFbd h hyU
  obtain ⟨L, hL, hLX⟩ := hXl a (hmemX a W.start_mem_support ha) b
    (hmemX b W.end_mem_support hb) hab
  have hcap : (walkDrawing T W).U ∩ L ⊆ {a, b} := by
    rintro x ⟨hxP, hxL⟩
    have hxA : x ∈ discBd Z := hXA (hLX hxL)
    rcases (mem_U_iff_edge _).mp hxP with h | ⟨e, he, hxe⟩
    · rw [walkDrawing_V] at h
      exact hin x h hxA
    · have heT : e ∈ T.E := (walkDrawing_isSubdrawing T W).2 he
      exact (((hTE ▸ heT : e ∈ ES).2 hxe).2 hxA).elim
  refine N.not_circle_in_disc hS hcuffs hZ (isOArc_union hline hL hcap)
    (union_subset (hsubP.trans hTZ) (hLX.trans (hXA.trans hbdZ)))
    (union_subset (hsubP.trans hTJ) fun x hx => hJ.2.1 ▸ hXU (hLX hx))

end GraphMinor.GM07
