/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10e
public import LeanPool.GraphMinor.GM09.Section9
import LeanPool.GraphMinor.GM16.CircleListing
import LeanPool.GraphMinor.GM16.CyclicOrderTransport

/-!
# Graph Minors IX, (10.4): tools

This file has the three tools that (10.4) needs.

* A crooked transaction stays crooked when its paths are extended and the crossings of its ends do
  not change: `Society.isCrookedTransaction_image`.
* The finite set of vertices of a circuit has a cyclic order that agrees with its drawing:
  `exists_cyclicPerm_agrees_of_injOn`.
* A disc bounded by a circuit splits the drawn graph: `exists_separation_of_disc`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11
  GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-- If each path of a crooked transaction is replaced by a path with new ends, the new paths are
disjoint, and crossings of the ends do not change, then the new set is a crooked transaction. -/
theorem Society.isCrookedTransaction_image {S₁ S : Society α β} {T : Set (Graph α β)}
    (hT : S₁.IsCrookedTransaction T) {ψ : α → α} {f : Graph α β → Graph α β}
    (hends : ∀ P ∈ T, ∀ a b, S₁.IsOmegaPathWithEnds P a b →
      S.IsOmegaPathWithEnds (f P) (ψ a) (ψ b))
    (hd : ∀ P ∈ T, ∀ P' ∈ T, P ≠ P' → Disjoint V(f P) V(f P'))
    (hinj : InjOn ψ (S₁.transactionEnds T))
    (hcr : ∀ a ∈ S₁.transactionEnds T, ∀ b ∈ S₁.transactionEnds T, ∀ c ∈ S₁.transactionEnds T,
      ∀ d ∈ S₁.transactionEnds T, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (S₁.Ω.Crosses a b c d ↔ S.Ω.Crosses (ψ a) (ψ b) (ψ c) (ψ d))) :
    S.IsCrookedTransaction (f '' T) := by
  set W := S₁.transactionEnds T
  obtain ⟨A₀, B₀, hdis, hfe, hab⟩ := hT.1
  have hψW : ∀ a ∈ W, ψ a ∈ S.transactionEnds (f '' T) := by
    rintro a ⟨P, hP, b, hPab⟩
    exact ⟨f P, mem_image_of_mem f hP, ψ b, hends P hP a b hPab⟩
  have hW_sub : ψ '' W ⊆ S.Ω.bar :=
    image_subset_iff.mpr fun a ha => S.transactionEnds_subset_bar _ (hψW a ha)
  have hWb : W ⊆ S₁.Ω.bar := S₁.transactionEnds_subset_bar T
  set Y := ψ '' W
  have hbarY : (S.Ω.restrict Y hW_sub).bar = Y := S.Ω.restrict_bar hW_sub
  have hfence' : (S.Ω.restrict Y hW_sub).IsFence (ψ '' (W ∩ A₀)) (ψ '' (W ∩ B₀)) := by
    have hA' : ψ '' (W ∩ A₀) ⊆ Y := image_mono inter_subset_left
    have hB' : ψ '' (W ∩ B₀) ⊆ Y := image_mono inter_subset_left
    have hdAB : Disjoint A₀ B₀ := hfe.2.2.1
    refine ⟨hbarY.symm ▸ hA', hbarY.symm ▸ hB', ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨a, ⟨haW, haA⟩, rfl⟩ ⟨b, ⟨hbW, hbB⟩, e⟩
      exact Set.disjoint_left.mp hdAB haA (hinj haW hbW e.symm ▸ hbB)
    · rw [hbarY, ← image_union, ← inter_union_distrib_left]
      have : W ⊆ A₀ ∪ B₀ := by
        rw [hfe.2.2.2.1]
        exact hWb
      rw [inter_eq_left.mpr this]
    · rintro _ ⟨a₁, ⟨ha₁, hA₁⟩, rfl⟩ _ ⟨a₂, ⟨ha₂, hA₂⟩, rfl⟩ hne _ ⟨b₁, ⟨hb₁, hB₁⟩, rfl⟩
        _ ⟨b₂, ⟨hb₂, hB₂⟩, rfl⟩ hne' hc
      have hc' := ((S.Ω.crosses_restrict_iff hW_sub).mp hc).2.2.2.2
      have hna : a₁ ≠ a₂ := fun e => hne (congrArg ψ e)
      have hnb : b₁ ≠ b₂ := fun e => hne' (congrArg ψ e)
      have hdist : ∀ {x y}, x ∈ A₀ → y ∈ B₀ → x ≠ y := fun hx hy e =>
        Set.disjoint_left.mp hdAB hx (e ▸ hy)
      exact hfe.2.2.2.2 a₁ hA₁ a₂ hA₂ hna b₁ hB₁ b₂ hB₂ hnb
        ((hcr a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ hna (hdist hA₁ hB₁) (hdist hA₁ hB₂) (hdist hA₂ hB₁)
          (hdist hA₂ hB₂) hnb).mpr hc')
  obtain ⟨A, B, hfence, hA, hB⟩ := S.Ω.exists_isFence_of_restrict hW_sub hfence'
  refine ⟨⟨A, B, ⟨?_, ?_⟩, hfence, ?_⟩, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, -, b, -, hPab⟩ := hab P hP
    exact ⟨_, _, hends P hP a b hPab⟩
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩ hne
    exact hd P hP P' hP' fun e => hne (congrArg f e)
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, haA, b, hbB, hPab⟩ := hab P hP
    exact ⟨ψ a, hA ⟨a, ⟨⟨P, hP, b, hPab⟩, haA⟩, rfl⟩, ψ b,
      hB ⟨b, ⟨⟨P, hP, a, IsOmegaPathWithEnds.symm S₁ hPab⟩, hbB⟩, rfl⟩, hends P hP a b hPab⟩
  · rintro _ ⟨P, hP, rfl⟩ ⟨-, a', b', hP', hdisj⟩
    obtain ⟨a, -, b, -, hPab⟩ := hab P hP
    have haW : a ∈ W := ⟨P, hP, b, hPab⟩
    have hbW : b ∈ W := ⟨P, hP, a, IsOmegaPathWithEnds.symm S₁ hPab⟩
    have hnot : ¬ (Disjoint (S₁.Ω.interval a b) W ∨ Disjoint (S₁.Ω.interval b a) W) := fun h =>
      hT.2 P hP ⟨hP, a, b, hPab, h⟩
    push Not at hnot
    obtain ⟨hn₁, hn₂⟩ := hnot
    obtain ⟨c, hc, hcW⟩ := Set.not_disjoint_iff.mp hn₁
    obtain ⟨d, hd', hdW⟩ := Set.not_disjoint_iff.mp hn₂
    have hab_ne : a ≠ b := hPab.2.1
    have hne_c : c ≠ a ∧ c ≠ b := by
      refine ⟨fun e => hc.1.2 (Or.inl e), fun e => hc.1.2 (Or.inr e)⟩
    have hne_d : d ≠ b ∧ d ≠ a := by
      refine ⟨fun e => hd'.1.2 (Or.inl e), fun e => hd'.1.2 (Or.inr e)⟩
    have hcd : c ≠ d := fun e =>
      Set.disjoint_right.mp (S₁.Ω.isFence_interval_compl (hWb haW) (hWb hbW) hab_ne).2.2.1 (e ▸ hd')
        (Or.inr hc)
    have hcross : S₁.Ω.Crosses a b c d := S₁.Ω.crosses_iff_interval.mpr (Or.inl ⟨hc, hd'⟩)
    have hcross' := (hcr a haW b hbW c hcW d hdW hab_ne hne_c.1.symm hne_d.2.symm hne_c.2.symm
      hne_d.1.symm hcd).mp hcross
    have hboth : (S.Ω.interval (ψ a) (ψ b) ∩ S.transactionEnds (f '' T)).Nonempty ∧
        (S.Ω.interval (ψ b) (ψ a) ∩ S.transactionEnds (f '' T)).Nonempty := by
      rcases S.Ω.crosses_iff_interval.mp hcross' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨⟨_, h₁, hψW c hcW⟩, ⟨_, h₂, hψW d hdW⟩⟩
      · exact ⟨⟨_, h₁, hψW d hdW⟩, ⟨_, h₂, hψW c hcW⟩⟩
    have hbad : ∀ {u w : α}, (S.Ω.interval u w ∩ S.transactionEnds (f '' T)).Nonempty →
        ¬ Disjoint (S.Ω.interval u w) (S.transactionEnds (f '' T)) :=
      fun ⟨x, h₁, h₂⟩ h => Set.disjoint_left.mp h h₁ h₂
    rcases IsOmegaPathWithEnds.ends_eq S (hends P hP a b hPab) hP' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hdisj with h | h
      · exact hbad hboth.1 h
      · exact hbad hboth.2 h
    · rcases hdisj with h | h
      · exact hbad hboth.2 h
      · exact hbad hboth.1 h

/-- A finite set of vertices with distinct points on a circle has a cyclic order that agrees with a
given parametrization of the circle. -/
theorem exists_cyclicPerm_agrees_of_injOn {S : Type*} [TopologicalSpace S] {F : Set S}
    (φ : Circle ≃ₜ F) (ν : α → S) {Y : Set α} (hY : Y.Finite) (hNe : Y.Nonempty)
    (hinj : InjOn ν Y) (hYF : ∀ v ∈ Y, ν v ∈ F) :
    ∃ Ω : CyclicPerm α, Ω.bar = Y ∧ AgreesWithOArcHomeo ν Ω F φ := by
  classical
  let : Fintype Y := hY.fintype
  have hCard : Fintype.card Y = Y.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  let e₀ : Fin Y.ncard ≃ Y := (finCongr hCard.symm).trans (Fintype.equivFin Y).symm
  let ν₀ : Fin Y.ncard → S := fun i => ν (e₀ i).val
  have hν₀ : Function.Injective ν₀ := fun i j h =>
    e₀.injective (Subtype.ext (hinj (e₀ i).2 (e₀ j).2 h))
  obtain ⟨perm, τ, hPerm, hτ, hBounds, hEq⟩ := exists_increasing_circle_angles φ ν₀ hν₀
    (fun i => hYF _ (e₀ i).property)
  let e : Fin Y.ncard ≃ Y := (Equiv.ofBijective perm hPerm).trans e₀
  let Ω := cyclicPermOnSet hY e
  have hNeCard : 0 < Y.ncard := (Set.ncard_pos hY).mpr hNe
  have hEq' : ∀ i, (φ (Circle.exp (τ i))).val = ν (e i).val := hEq
  have hTurn : ∀ i, τ i < τ ⟨0, hNeCard⟩ + 2 * Real.pi := by
    intro i
    have hi := hBounds i
    have hzero := hBounds ⟨0, hNeCard⟩
    linarith
  have hAgreeFin := finCyclicPerm_agrees_of_angles φ hNeCard (fun i => ν (e i).val) τ hτ hTurn hEq'
  refine ⟨Ω, rfl, fun x hx => hYF x hx, ?_⟩
  intro x y z hCW
  have hMem := CyclicPerm.isClockwise3_iff.mp hCW
  let i := e.symm ⟨x, hMem.2.2.2.1⟩
  let j := e.symm ⟨y, hMem.2.2.2.2.1⟩
  let k := e.symm ⟨z, hMem.2.2.2.2.2.1⟩
  have hi : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hMem.2.2.2.1⟩)
  have hj : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hMem.2.2.2.2.1⟩)
  have hk : (e k).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hMem.2.2.2.2.2.1⟩)
  have hCW' : (cyclicPermOnSet hY e).IsClockwise3 (e i).val (e j).val (e k).val := by
    rw [hi, hj, hk]
    exact hCW
  have hFin := (cyclicPermOnSet_clockwise3_iff hY e i j k).mp hCW'
  simpa only [hi, hj, hk] using hAgreeFin.2 i j k hFin

/-- A closed disc whose boundary is the drawing of `K` splits the drawn graph at `V(K)`. -/
theorem exists_separation_of_disc {G K : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    {Δ D : Set EuclideanPlane} (hΔ : IsClosed Δ) (hU : Γ.drawing.U ⊆ Δ) (hK : K ≤ G)
    (hD : IsClosedDisc D) (hDΔ : D ⊆ Δ) (hbd : subBd D = graphDrawingSubgraphU Γ K) :
    ∃ H₁ H₂ : Graph α β, IsGraphSeparation G H₁ H₂ ∧ V(H₁) ∩ V(H₂) = V(K) ∧ K ≤ H₁ ∧
      (∀ v ∈ V(G), graphDrawingVertexSet Γ v ⊆ D \ subBd D → v ∈ V(H₁)) ∧
      (∀ v ∈ V(G), graphDrawingVertexSet Γ v ⊆ Δ \ D → v ∈ V(H₂)) ∧
      graphDrawingSubgraphU Γ H₁ ⊆ D ∧ graphDrawingSubgraphU Γ H₂ ⊆ Δ \ interior D := by
  have hfr : frontier D = subBd D := by
    rw [frontier_eq_discBd_plane hD, subBd_eq_discBd_plane hD]
  have hcl : IsClosed D := isClosed_of_isClosedDisc hD
  have hint : D \ subBd D = interior D := by
    rw [← hfr, hcl.frontier_eq, sdiff_sdiff_cancel_left interior_subset]
  have hsides : IsArcSides Δ (graphDrawingSubgraphU Γ K) ∅ ∅ (D \ subBd D) (Δ \ D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hbd]
      ext x
      constructor
      · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
        · exact ⟨hDΔ h₁, h₂⟩
        · exact ⟨h₁, fun h => h₂ (subBd_subset_of_isClosed hcl h)⟩
      · rintro ⟨h₁, h₂⟩
        by_cases hx : x ∈ D
        · exact Or.inl ⟨hx, h₂⟩
        · exact Or.inr ⟨h₁, hx⟩
    · rw [Set.disjoint_left]
      rintro x ⟨h₁, -⟩ ⟨-, h₂⟩
      exact h₂ h₁
    · intro Z hZ hc
      have hopen₁ : IsOpen (D \ subBd D) := by
        rw [hint]
        exact isOpen_interior
      have hdisj : Disjoint (D \ subBd D) Dᶜ := Set.disjoint_left.mpr fun x h₁ h₂ => h₂ h₁.1
      have hcov : Z ⊆ (D \ subBd D) ∪ Dᶜ := by
        intro x hx
        by_cases hxD : x ∈ D
        · refine Or.inl ⟨hxD, fun h => (hZ hx).2 ?_⟩
          rwa [← hbd]
        · exact Or.inr hxD
      rcases hc.subset_or_subset hopen₁ hcl.isOpen_compl hdisj hcov with h | h
      · left
        rw [hbd] at h ⊢
        exact h
      · right
        exact fun x hx => ⟨(hZ hx).1, h hx⟩
    · simp
    · simp
  obtain ⟨H₁, H₂, hsep, hcut, hKH₁, hY₁, hY₂, hV₁, hV₂, hE₁, hE₂⟩ :=
    exists_separation_of_sides Γ hU hK hsides
  have hKD : graphDrawingSubgraphU Γ K ⊆ D := by
    rw [← hbd]
    exact subBd_subset_of_isClosed hcl
  have hΔ_cl : IsClosed Δ := hΔ
  refine ⟨H₁, H₂, hsep, hcut, hKH₁, hY₁, hY₂, ?_, ?_⟩
  · rintro x (hx | hx)
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rcases hV₁ v hv with h | h
      · exact hKD (graphDrawingVertexSet_subset_subgraphU_of_mem Γ h hxv)
      · exact (h hxv).1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      rcases hE₁ e he with h | h
      · exact hKD (Or.inr (mem_iUnion₂.mpr ⟨e, h, hxe⟩))
      · exact closure_minimal (h.trans sdiff_subset) hcl hxe
  · have hint' : Disjoint (interior D) (graphDrawingSubgraphU Γ K) := by
      rw [← hbd, ← hint]
      exact Set.disjoint_left.mpr fun x h₁ h₂ => h₁.2 h₂
    have hKΔ : graphDrawingSubgraphU Γ K ⊆ Δ := hKD.trans hDΔ
    have hnot : ∀ {x}, x ∈ graphDrawingSubgraphU Γ K → x ∈ Δ \ interior D := fun hx =>
      ⟨hKΔ hx, fun h => Set.disjoint_left.mp hint' h hx⟩
    rintro x (hx | hx)
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rcases hV₂ v hv with h | h
      · exact hnot (graphDrawingVertexSet_subset_subgraphU_of_mem Γ h hxv)
      · exact ⟨(h hxv).1, fun hi => (h hxv).2 (interior_subset hi)⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      have hsub := hE₂ e he
      refine ⟨closure_minimal (hsub.trans sdiff_subset) hΔ_cl hxe, fun hi => ?_⟩
      have : closure (graphDrawingEdgeSet Γ e) ⊆ (interior D)ᶜ :=
        closure_minimal (fun y hy hyi => (hsub hy).2 (interior_subset hyi))
          isOpen_interior.isClosed_compl
      exact this hxe hi

/-- A path whose only vertex in the cut is its last vertex, and whose first vertex is on the second
side, lies in the second side. -/
theorem IsGraphPathWithEnds.le_right_of_inter_subset {G H₁ H₂ R : Graph α β} {a z : α}
    (hsep : IsGraphSeparation G H₁ H₂) (hR : IsGraphPathWithEnds G R a z)
    (hV : V(R) ∩ (V(H₁) ∩ V(H₂)) ⊆ {z}) (ha : a ∈ V(H₂)) (hz : z ∈ V(H₂)) : R ≤ H₂ := by
  have hvert : ∀ w ∈ V(R), w ∈ V(H₂) := by
    intro w hw
    by_cases hwz : w = z
    · exact hwz ▸ hz
    obtain ⟨R₁, R₂, hR₁, -, hp₁, hp₂, -, hVi, -⟩ := hR.exists_split_at hw
    have hzR₁ : z ∉ V(R₁) := fun h => by
      have : z ∈ V(R₁) ∩ V(R₂) := ⟨h, hp₂.right_mem⟩
      rw [hVi] at this
      exact hwz this.symm
    have hle : R₁ ≤ G := hR₁.trans hR.le
    have hav : Disjoint V(R₁) (V(H₁) ∩ V(H₂)) := by
      rw [Set.disjoint_left]
      intro x hx hxc
      have := hV ⟨hR₁.vertexSet_mono hx, hxc⟩
      exact hzR₁ ((show x = z from this) ▸ hx)
    have := Society.connected_subset_right_of_avoids_inter hsep hle hp₁.isGraphConnected hav
      ⟨a, hp₁.left_mem, ha⟩
    exact (this hp₁.right_mem).1
  refine (Compatible.of_le_le hR.le hsep.2.1).le_iff.mpr ⟨hvert, fun e he => ?_⟩
  obtain ⟨u, w, hl⟩ : ∃ u w, R.IsLink e u w := exists_isLink_of_mem_edgeSet he
  have hG : e ∈ E(H₁) ∪ E(H₂) := by
    rw [hsep.2.2.2.1]
    exact hR.le.edgeSet_mono he
  refine hG.resolve_left fun he₁ => ?_
  obtain ⟨x, y, hl₁⟩ : ∃ x y, H₁.IsLink e x y := exists_isLink_of_mem_edgeSet he₁
  have hl₁' := hl₁.mono hsep.1
  have hlG := hl.mono hR.le
  have hu₁ : u ∈ V(H₁) := by
    rcases hlG.left_eq_or_eq hl₁' with e' | e'
    · exact e' ▸ hl₁.left_mem
    · exact e' ▸ hl₁.right_mem
  have hw₁ : w ∈ V(H₁) := by
    rcases hlG.symm.left_eq_or_eq hl₁' with e' | e'
    · exact e' ▸ hl₁.left_mem
    · exact e' ▸ hl₁.right_mem
  have hu : u = z := hV ⟨hl.left_mem, hu₁, hvert u hl.left_mem⟩
  have hw : w = z := hV ⟨hl.right_mem, hw₁, hvert w hl.right_mem⟩
  subst hu
  subst hw
  exact hR.not_isLoopAt he _ (hl.mono hR.le)

end GraphMinor.GM09
