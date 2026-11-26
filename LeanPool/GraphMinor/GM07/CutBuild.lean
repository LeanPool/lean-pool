/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutEdge
public import LeanPool.GraphMinor.GM07.CutDraw
import LeanPool.GraphMinor.GM19.Section6a
import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.GM06.Euler
import LeanPool.GraphMinor.Surface.AddCrosscap
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.PasteModel

/-!
# Cutting along an edge

A non-loop edge off the boundary can be cut along (`exists_cut`). The cut surface is `S` with the
inside of the disc of the slit
removed, and the cutting map is the end of the homotopy of the slit (`IsSlit`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S : Type u} [TopologicalSpace S]

/-- `remove_disc` for a surface in any universe. -/
theorem remove_disc_homeo {M : Type} [TopologicalSpace M] (hS : IsSurface S)
  (h : S ≃ₜ M) {E : Set S} (hE : IsClosedDisc E)
    (hint : ∀ x ∈ discBd E, IsInteriorPoint x) :
    IsClosed (discInt E)ᶜ ∧ IsSurface ↥(discInt E)ᶜ ∧ bd ↥(discInt E)ᶜ = Subtype.val ⁻¹'
      (bd S ∪ discBd E) := by
  have ht2 : T2Space S := hS.2.1
  have hM : IsSurface M := isSurface_of_homeo h hS
  have hl : LeftInvOn h.symm h E := fun x _ => h.symm_apply_apply x
  obtain ⟨hE', hbd'⟩ := hE.image h.continuous.continuousOn h.symm.continuous.continuousOn hl
  have hmem : ∀ {x : S} {A : Set S}, h x ∈ h '' A ↔ x ∈ A := h.injective.mem_set_image
  have hint' : ∀ x ∈ discBd (h '' E), IsInteriorPoint x := fun x hx => by
    rw [hbd'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    by_contra hb
    have h1 : h y ∈ bd M := hb
    rw [← image_bd_homeomorph h] at h1
    exact (show y ∈ bd S from hmem.mp h1) (hint y hy)
  obtain ⟨-, hs', hb'⟩ := remove_disc hM hE' hint'
  have hin : ∀ x, x ∈ (discInt E)ᶜ ↔ h x ∈ (discInt (h '' E))ᶜ := fun x => by
    simp only [mem_compl_iff, discInt, mem_sdiff, hbd', hmem]
  let β : ↥(discInt E)ᶜ ≃ₜ ↥(discInt (h '' E))ᶜ := h.subtype hin
  refine ⟨(hE.isOpen_discInt hS.2.2).isClosed_compl, isSurface_of_homeo β.symm hs', ?_⟩
  ext y
  have h1 : y ∈ bd ↥(discInt E)ᶜ ↔ β y ∈ bd ↥(discInt (h '' E))ᶜ := by
    rw [← image_bd_homeomorph β]
    exact β.injective.mem_set_image.symm
  rw [h1, hb']
  change h y.1 ∈ bd M ∪ discBd (h '' E) ↔ y.1 ∈ bd S ∪ discBd E
  rw [hbd', ← image_bd_homeomorph h, mem_union, mem_union, hmem, hmem]

/-- Removing the inside of a closed disc off the boundary keeps a surface connected. -/
theorem connectedSpace_remove (hS : IsSurface S) [ConnectedSpace S] {E : Set S}
  (hE : IsClosedDisc E)
    (hcl : IsClosed (discInt E)ᶜ) : ConnectedSpace ↥(discInt E)ᶜ := by
  have ht2 : T2Space S := hS.2.1
  have hO := hE.isOArc_discBd
  have hNc : IsConnected (discBd E) := isConnected_of_isOArc hO
  have hsub : discBd E ⊆ (discInt E)ᶜ := fun x hx hi => hi.2 hx
  obtain ⟨x₀, hx₀⟩ := hNc.nonempty
  let n : ↥(discInt E)ᶜ := ⟨x₀, hsub hx₀⟩
  have hNp : IsPreconnected (Subtype.val ⁻¹' discBd E : Set ↥(discInt E)ᶜ) := by
    rw [Topology.IsInducing.subtypeVal.isPreconnected_image.symm,
      image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩)]
    exact hNc.isPreconnected
  have key : ∀ B : Set ↥(discInt E)ᶜ, IsClopen B → Disjoint B (Subtype.val ⁻¹' discBd E) → B = ∅
    := by
    intro B hB hd
    have hemb := hcl.isClosedEmbedding_subtypeVal
    have hc : IsClosed (Subtype.val '' B) := hemb.isClosedMap B hB.1
    obtain ⟨O, hO', rfl⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hB.2
    have heq : Subtype.val '' (Subtype.val ⁻¹' O : Set ↥(discInt E)ᶜ) = O ∩ Eᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hy, fun hyE => ?_⟩
        by_cases hb : y.1 ∈ discBd E
        · exact disjoint_left.mp hd hy hb
        · exact y.2 ⟨hyE, hb⟩
      · rintro ⟨hx, hxE⟩
        exact ⟨⟨x, fun hi => hxE hi.1⟩, hx, rfl⟩
    have ho : IsOpen (O ∩ Eᶜ) := hO'.inter hE.isCompact.isClosed.isOpen_compl
    rw [heq] at hc
    have hcl' : IsClopen (O ∩ Eᶜ) := ⟨hc, ho⟩
    rcases isClopen_iff.mp hcl' with h | h
    · rw [eq_empty_iff_forall_notMem]
      intro y hy
      have : y.1 ∈ O ∩ Eᶜ := heq ▸ mem_image_of_mem _ hy
      rw [h] at this
      exact this
    · have : x₀ ∈ O ∩ Eᶜ := h ▸ mem_univ _
      exact (this.2 (Surface.discBd_subset _ hx₀)).elim
  have hpc : PreconnectedSpace ↥(discInt E)ᶜ := by
    rw [preconnectedSpace_iff_clopen]
    intro B hB
    have hn := hNp.subset_isClopen (t := B) hB
    by_cases hnB : n ∈ B
    · refine .inr ?_
      have h1 := key Bᶜ hB.compl (by
        rw [disjoint_left]
        intro y hy hyN
        exact hy (hn ⟨n, hx₀, hnB⟩ hyN))
      exact compl_empty_iff.mp h1
    · refine .inl (key B hB ?_)
      have hnc := hNp.subset_isClopen (t := Bᶜ) hB.compl ⟨n, hx₀, hnB⟩
      rw [disjoint_left]
      exact fun y hy hyN => hnc hyN hy
  exact { toPreconnectedSpace := hpc, toNonempty := ⟨n⟩ }

theorem exists_cut [T1Space S] (hS : IsSurface S) {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) (G : Drawing S)
    (hG : G.IsProper) {e : Set S} (he : e ∈ G.E) (hl : (tilde e).ncard = 2) (hd : closure e ∩ bd S
      = ∅) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T1Space Y) (φ : Y → S) (G' : Drawing Y),
      IsCutAlongEdge G e a b c Y φ G' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hconn : ConnectedSpace S := by
    obtain ⟨h⟩ := id hm
    have := (modelCriterion.1 a b c).2
    exact h.symm.surjective.connectedSpace h.symm.continuous
  obtain ⟨h⟩ := id hm
  have hM : IsSurface (SurfaceModel a b c) := (modelCriterion.1 a b c).1
  have hline : ∃ u v : S, u ≠ v ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    rcases G.edge_cond e he with h1 | ⟨u, hcap, -⟩
    · exact h1
    · rw [GraphMinor.GM19.tilde_eq_inter_V G he, hcap] at hl
      simp at hl
  obtain ⟨u, v, huv, hcap, hL⟩ := hline
  obtain ⟨E, κ, hs⟩ := exists_slit hM h hL hd
  have hmemV : ∀ s, s ∈ closure e → s ∉ e → s = u ∨ s = v := fun s hs1 hs2 => by
    have h1 : s ∉ closure e \ G.V := fun h2 => hs2 (by rw [G.closure_diff_V he] at h2; exact h2)
    have h2 : s ∈ closure e ∩ G.V := ⟨hs1, by_contra fun h3 => h1 ⟨hs1, h3⟩⟩
    rw [hcap] at h2
    simpa using h2
  have hint : ∀ x ∈ discBd E, IsInteriorPoint x := fun x hx => by
    by_contra hb
    have h1 : x ∈ E ∩ bd S := ⟨Surface.discBd_subset _ hx, hb⟩
    rw [hs.off_bd] at h1
    exact h1
  obtain ⟨hcl, hYs, hbdY⟩ := remove_disc_homeo hS h hs.disc hint
  have : CompactSpace ↥(discInt E)ᶜ := hYs.1
  have : T2Space ↥(discInt E)ᶜ := hYs.2.1
  have hYc := connectedSpace_remove hS hs.disc hcl
  let φ : ↥(discInt E)ᶜ → S := fun y => κ (1, y.1)
  have hφc : Continuous φ := hs.cont.comp (continuous_const.prodMk continuous_subtype_val)
  have hφs : Function.Surjective φ := fun y => by
    obtain ⟨x, hx, he'⟩ := hs.onto y
    exact ⟨⟨x, hx⟩, he'⟩
  have hpre : ∀ y, φ y ∈ closure e ↔ y.1 ∈ discBd E := fun y => by
    constructor
    · intro hy
      have h1 : y.1 ∈ E := by
        by_contra hn
        exact hs.off _ hn hy
      by_contra hn
      exact y.2 ⟨h1, hn⟩
    · exact hs.fold _
  have hinj : ∀ x y, φ x = φ y → x = y ∨ φ x ∈ e := fun x y he' => by
    rcases hs.inj x.1 y.1 x.2 y.2 he' with h1 | ⟨h1, -, h2, h3⟩
    · exact .inl (Subtype.ext h1)
    · refine .inr (by_contra fun hn => ?_)
      rcases hmemV _ ((hpre x).mpr h1) hn with h4 | h4
      · exact h2 h4
      · exact h3 h4
  have hU₁ : (G.deleteEdge e).U = G.U \ e := deleteEdge_U G he
  have hV₁ : (G.deleteEdge e).V = G.V := deleteEdge_V G e
  have hi : InjOn φ (φ ⁻¹' (G.deleteEdge e).U) := fun x hx y _ he' => by
    rw [mem_preimage, hU₁] at hx
    exact (hinj x y he').resolve_right hx.2
  let G' := pullDrawing (G.deleteEdge e) hφc hφs hi
  have hbd_eq : bd ↥(discInt E)ᶜ = φ ⁻¹' (bd S ∪ closure e) := by
    rw [hbdY]
    ext y
    simp only [mem_preimage, mem_union]
    rw [hpre, hs.bd_iff]
  have hNeq : φ ⁻¹' closure e = Subtype.val ⁻¹' discBd E := by
    ext y
    exact hpre y
  have hNc : IsConnected (discBd E) := isConnected_of_isOArc hs.disc.isOArc_discBd
  have hsub : discBd E ⊆ (discInt E)ᶜ := fun x hx hi => hi.2 hx
  have hvN : Subtype.val '' (Subtype.val ⁻¹' discBd E : Set ↥(discInt E)ᶜ) = discBd E :=
    image_preimage_eq_of_subset fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩
  have hNcp : IsPreconnected (Subtype.val ⁻¹' discBd E : Set ↥(discInt E)ᶜ) := by
    rw [Topology.IsInducing.subtypeVal.isPreconnected_image.symm, hvN]
    exact hNc.isPreconnected
  have hN : φ ⁻¹' closure e ∈ cuffs ↥(discInt E)ᶜ := by
    rw [hNeq]
    obtain ⟨x₀, hx₀⟩ := hNc.nonempty
    have hnb : (⟨x₀, hsub hx₀⟩ : ↥(discInt E)ᶜ) ∈ bd ↥(discInt E)ᶜ := by
      rw [hbdY]
      exact .inr hx₀
    refine ⟨⟨x₀, hsub hx₀⟩, hnb, Subset.antisymm ?_ ?_⟩
    · have hconn' : IsPreconnected (connectedComponentIn (bd ↥(discInt E)ᶜ) ⟨x₀, hsub hx₀⟩) :=
        isPreconnected_connectedComponentIn
      intro y hy
      by_contra hyN
      have h1 := connectedComponentIn_subset _ _ hy
      rw [hbdY] at h1
      have hyb : y.1 ∈ bd S := h1.resolve_right hyN
      have hP : IsClosed (Subtype.val ⁻¹' bd S : Set ↥(discInt E)ᶜ) :=
        (isClosed_bd S).preimage continuous_subtype_val
      have hQ : IsClosed (Subtype.val ⁻¹' discBd E : Set ↥(discInt E)ᶜ) :=
        hs.disc.isOArc_discBd.isCompact.isClosed.preimage continuous_subtype_val
      obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp hconn' _ _ hP hQ (fun z hz => by
        have h2 := connectedComponentIn_subset _ _ hz
        rw [hbdY] at h2
        exact h2) ⟨y, hy, hyb⟩ ⟨_, mem_connectedComponentIn hnb, hx₀⟩
      have h3 : z.1 ∈ E ∩ bd S := ⟨Surface.discBd_subset _ hz2, hz1⟩
      rw [hs.off_bd] at h3
      exact h3
    · refine hNcp.subset_connectedComponentIn hx₀ fun y hy => ?_
      rw [hbdY]
      exact .inr hy
  have hcap' : IsCappedCuff (φ ⁻¹' closure e) S Subtype.val E := by
    have hI : Subtype.val '' (φ ⁻¹' closure e) = discBd E := by rw [hNeq, hvN]
    have hran : range (Subtype.val : ↥(discInt E)ᶜ → S) = (discInt E)ᶜ := Subtype.range_coe
    refine ⟨hN, hS, Topology.IsEmbedding.subtypeVal, hs.disc, hI.symm, ?_, ?_⟩
    · rw [hran]
      ext x
      simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
      by_cases hx : x ∈ discInt E
      · exact .inr hx.1
      · exact .inl hx
    · rw [hran, hI]
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        by_contra h3
        exact h1 ⟨h2, h3⟩
      · exact fun hx => ⟨hsub hx, Surface.discBd_subset _ hx⟩
  refine ⟨↥(discInt E)ᶜ, inferInstance, inferInstance, φ, G', he, hl, hd, hYs, ?_, ?_, ?_, ?_,
    ?_, hinj, hN, hbd_eq, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a', b', c', ⟨m⟩⟩ := classification _ hYs hYc
    obtain ⟨h0, ⟨m'⟩⟩ := paste_model hYs hN hS hcl.isClosedEmbedding_subtypeVal hs.disc
      hcap'.union_eq hcap'.inter_eq
      hcap'.discBd_eq m
    obtain ⟨h1, h2, h3⟩ := (modelCriterion.2 a' b' (c' - 1) a b c).mp ⟨m'.symm.trans h⟩
    obtain ⟨m''⟩ := (modelCriterion.2 a' b' c' a b (c + 1)).mpr ⟨by omega, h2, h3⟩
    exact ⟨m.trans m''⟩
  · exact hφc.isClosedMap.isQuotientMap hφc hφs
  · rintro y ⟨hy, hU⟩
    change φ y ∈ (G.deleteEdge e).V
    change φ y ∈ (G.deleteEdge e).U at hU
    rw [hU₁] at hU
    rw [hV₁]
    rw [hbd_eq] at hy
    rcases hy with hy | hy
    · exact hG ⟨hy, hU.1⟩
    · have h2 : φ y ∈ closure e ∩ G.V := by
        refine ⟨hy, ?_⟩
        have h3 : φ y ∈ ({u, v} : Set S) := by simpa using hmemV _ hy hU.2
        rw [← hcap] at h3
        exact h3.2
      exact h2.2
  · change φ ⁻¹' (G.deleteEdge e).U = φ ⁻¹' (G.U \ e)
    rw [hU₁]
  · change φ ⁻¹' (G.deleteEdge e).V = φ ⁻¹' G.V
    rw [hV₁]
  · exact ⟨Subtype.val, E, fun q => κ (q.1, q.2.1), hcap', hs.cont.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)),
      fun y => hs.c0 y.1, fun y => rfl⟩
  · intro x
    refine (Set.Finite.preimage Subtype.val_injective.injOn (hs.fiber x)).subset ?_
    intro y hy
    exact ⟨y.2, hy⟩
  · intro x
    obtain ⟨a, b, hab⟩ := hs.pair x
    refine (ncard_le_ncard_of_injOn Subtype.val (fun y hy => hab ⟨y.2, hy⟩)
      Subtype.val_injective.injOn (toFinite _)).trans ?_
    exact (ncard_insert_le a {b}).trans (by rw [ncard_singleton])
  · intro x hx
    have hxV : x ∉ G.V := (he.2.1 hx).2
    have huv : u ∈ G.V ∧ v ∈ G.V := by
      have hu : u ∈ closure e ∩ G.V := hcap ▸ (Or.inl rfl : u ∈ ({u, v} : Set S))
      have hv : v ∈ closure e ∩ G.V := hcap ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
      exact ⟨hu.2, hv.2⟩
    obtain ⟨y, y', hne, hy, hy', h1, h2⟩ := hs.two x (subset_closure hx)
      (fun h => hxV (h ▸ huv.1)) (fun h => hxV (h ▸ huv.2))
    have hyi : ∀ z ∈ discBd E, z ∉ discInt E := fun z hz hi => hi.2 hz
    have hsub : ({⟨y, hyi y hy⟩, ⟨y', hyi y' hy'⟩} : Set ↥(discInt E)ᶜ) ⊆ φ ⁻¹' {x} := by
      rintro z (rfl | rfl)
      · exact h1
      · exact h2
    have hfin : (φ ⁻¹' {x}).Finite :=
      (Set.Finite.preimage Subtype.val_injective.injOn (hs.fiber x)).subset fun z hz => ⟨z.2, hz⟩
    refine le_trans (le_of_eq ?_) (ncard_le_ncard hsub hfin)
    rw [ncard_pair fun h => hne (congrArg Subtype.val h)]

end GraphMinor.GM07
