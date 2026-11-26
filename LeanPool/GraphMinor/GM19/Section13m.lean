/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13l

/-!
# Graph Minors XIX, Section 13: the circuit `C` in the proof of (13.6)

After step (4) the paper says that there is a circuit `C ⊆ F ∪ D_v` whose disc in `Δ₀` holds `ins(F)
∪ Δ_v`. We take `Δ'` in `Δ₀` as large as
possible among the discs that hold `Δ_v` and are bounded by a circuit of `F ∪ D_v`. If some edge of
`F` is outside `Δ'` and some edge of `F`
is in `Δ'`, then a piece of `F` is an ear on `Δ'`, and `exists_larger_circuit` gives a larger disc.
If no edge of `F` is in `Δ'` then
`Δ' ⊆ ins(F)`, and `ins(F)` itself is a larger disc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

omit [T2Space Shat] in
/-- A simple walk with ends in `X`, through an edge `g`, has a piece through `g` that has only its
ends in `X`. -/
theorem GraphWalk.exists_piece {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hs : K.IsSimple) {X : Set Shat} (ha : a ∈ X) (hb : b ∈ X)
    {g : Set Shat} (hg : g ∈ K.edges) : ∃ (u v : Shat) (M : GraphWalk G.toGraph u v), u ∈ X ∧ v ∈ X
      ∧ M.IsSimple ∧ g ∈ M.edges ∧ (∀ e ∈ M.edges, e ∈ K.edges) ∧
      ∀ x ∈ M.support, x ∈ X → x = u ∨ x = v := by
  obtain ⟨x, y, hl, A, B, rfl⟩ := GraphWalk.exists_split_edge K hg
  obtain ⟨u, hu, A₁, A₂, rfl, h₁⟩ := GraphWalk.exists_last_mem A (X := X) ⟨a, A.start_mem_support,
    ha⟩
  obtain ⟨v, hv, B₁, B₂, rfl, h₂⟩ := GraphWalk.exists_first_mem B (X := X) ⟨b, B.end_mem_support,
    hb⟩
  have hnd := hs
  unfold GraphWalk.IsSimple at hnd
  rw [GraphWalk.support_append, GraphWalk.support_cons, List.tail_cons, List.nodup_append] at hnd
  obtain ⟨hn₁, hn₂, hn₃⟩ := hnd
  have hs₁ := (isSimple_of_append hs).1
  have hs₂ := (isSimple_of_append hs).2
  have hA₂ := (isSimple_of_append hs₁).2
  have hc : (GraphWalk.cons hl (B₁.append B₂)).support.Nodup := hs₂
  rw [GraphWalk.support_cons, List.nodup_cons] at hc
  have hB₁ := (isSimple_of_append (show (B₁.append B₂).IsSimple from hc.2)).1
  have hcons : (GraphWalk.cons hl B₁).IsSimple := by
    refine List.nodup_cons.mpr ⟨fun h' ↦ hc.1 ((GraphWalk.mem_support_append _ _).mpr (.inl h')),
      hB₁⟩
  refine ⟨u, v, A₂.append (GraphWalk.cons hl B₁), hu, hv, isSimple_append' hA₂ hcons fun z hz hz₂ ↦
    ?_, ?_, fun e he ↦ ?_, fun z hz hzX ↦ ?_⟩
  · rcases List.mem_cons.mp hz₂ with rfl | hz₂
    · rfl
    · exact absurd ((GraphWalk.mem_support_append B₁ B₂).mpr (.inl hz₂)) (hn₃ _
        ((GraphWalk.mem_support_append _ _).mpr (.inr hz)) _ · rfl)
  · rw [GraphWalk.edges_append, GraphWalk.edges_cons]
    exact List.mem_append_right _ List.mem_cons_self
  · simp only [GraphWalk.edges_append, GraphWalk.edges_cons, List.mem_append, List.mem_cons] at he ⊢
    tauto
  · rcases (GraphWalk.mem_support_append _ _).mp hz with hz | hz
    · exact .inl (h₁ z hz hzX)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact .inl (h₁ _ A₂.end_mem_support hzX)
      · exact .inr (h₂ z hz hzX)

omit [T2Space Shat] in
/-- Each edge of a simple walk with distinct ends has an end that is not an end of the walk, or else
it is the only edge. -/
theorem GraphWalk.edge_has_middle {G : Drawing Shat} {u v : Shat} (M : GraphWalk G.toGraph u v)
  (hs : M.IsSimple) (huv : u ≠ v) {e : Set Shat}
    (he : e ∈ M.edges) : M.edges = [e] ∨ ∃ x ∈ M.support, x ∈ closure e ∧ x ≠ u ∧ x ≠ v := by
  obtain ⟨x, y, hl, A, B, rfl⟩ := GraphWalk.exists_split_edge M he
  have hnd := hs
  unfold GraphWalk.IsSimple at hnd
  rw [GraphWalk.support_append, GraphWalk.support_cons, List.tail_cons, List.nodup_append] at hnd
  obtain ⟨hn₁, hn₂, hn₃⟩ := hnd
  have hs₂ := (isSimple_of_append hs).2
  have hc : (GraphWalk.cons hl B).support.Nodup := hs₂
  rw [GraphWalk.support_cons, List.nodup_cons] at hc
  have hx : x ∈ closure e ∩ G.V := by
    rw [hl.2.2.2]
    exact .inl rfl
  have hy : y ∈ closure e ∩ G.V := by
    rw [hl.2.2.2]
    exact .inr rfl
  have hxs : x ∈ (A.append (GraphWalk.cons hl B)).support := (GraphWalk.mem_support_append _ _).mpr
    (.inl A.end_mem_support)
  have hys : y ∈ (A.append (GraphWalk.cons hl B)).support := (GraphWalk.mem_support_append _ _).mpr
    (.inr (by simp [B.start_mem_support]))
  by_cases h₁ : x ≠ u ∧ x ≠ v
  · exact .inr ⟨x, hxs, hx.1, h₁⟩
  by_cases h₂ : y ≠ u ∧ y ≠ v
  · exact .inr ⟨y, hys, hy.1, h₂⟩
  have hxy : x ≠ y := fun h' ↦ hc.1 (h' ▸ B.start_mem_support)
  left
  have h₁' : x = u ∨ x = v := by tauto
  have h₂' : y = u ∨ y = v := by tauto
  rcases h₁' with rfl | rfl
  · rcases h₂' with rfl | rfl
    · exact absurd rfl hxy
    · rw [GraphWalk.edges_append, GraphWalk.edges_cons, (simple_self (isSimple_of_append hs).1).1,
        (simple_self hc.2).1]
      rfl
  · rcases h₂' with rfl | rfl
    · exact absurd (B.start_mem_support) (hn₃ _ A.start_mem_support _ · rfl)
    · exact absurd rfl hxy

universe w

variable {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- An edge of `G` off `C` is inside the disc bounded by `C` or misses the disc. -/
theorem edge_inside_or_off (hT : IsClosedSurface Shat) {G C : Drawing Shat}
  {Δ : Set Shat} (hC : C.IsSubdrawing G) (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = C.U) {e : Set Shat} (he : e ∈ G.E) (heC : e ∉ C.E) : e ⊆ discInt Δ
      ∨ Disjoint e Δ := by
  have hd := edge_disjoint_U hC he heC
  by_cases hm : (e ∩ Δ).Nonempty
  · left
    obtain ⟨x, hxe, hxΔ⟩ := hm
    refine (isSide_int hT hΔ hbd).subset he.2.2.1.isConnected.isPreconnected hd ⟨x, hxe, hxΔ,
      fun hb ↦ disjoint_left.mp hd hxe (hbd ▸ hb)⟩
  · right
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hm)

/-- **The circuit `C` of the proof of (13.6).** Two discs in `Δ₀` bounded by circuits of `G`, whose
interiors meet, lie in a disc in `Δ₀` bounded by a circuit
in the union of the two circuits. -/
theorem exists_enclosing_circuit [ConnectedSpace Shat] (hT : IsClosedSurface Shat) {G F Dv :
  Drawing Shat} {Δ₀ Δf Δv : Set Shat} (h₀ : IsClosedDisc Δ₀)
    (hF : F.IsCircuitOf G) (hDv : Dv.IsCircuitOf G) (hΔf : IsClosedDisc Δf) (hΔv : IsClosedDisc Δv)
      (hf₀ : Δf ⊆ Δ₀) (hv₀ : Δv ⊆ Δ₀)
    (hbf : discBd Δf = F.U) (hbv : discBd Δv = Dv.U) (hmeet : (discInt Δf ∩ discInt Δv).Nonempty)
    (hG : ∀ e ∈ G.E, ∃ a b, a ≠ b ∧ closure e ∩ G.V = {a, b}) :
    ∃ (C : Drawing Shat) (Δ : Set Shat), C.IsCircuitOf G ∧ (∀ e ∈ C.E, e ∈ F.E ∨ e ∈ Dv.E)
      ∧ IsClosedDisc Δ ∧ Δ ⊆ Δ₀ ∧ discBd Δ = C.U ∧ Δf ⊆ Δ ∧ Δv ⊆ Δ := by
  classical
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  let 𝓕 : Set (Set Shat) := {Δ | Δ ⊆ Δ₀ ∧ IsClosedDisc Δ ∧ Δv ⊆ Δ ∧ ∃ C : Drawing Shat,
    C.IsCircuitOf G ∧ (∀ e ∈ C.E, e ∈ F.E ∨ e ∈ Dv.E) ∧ discBd Δ = C.U}
  have hfin : 𝓕.Finite := by
    refine Set.Finite.of_finite_image (f := discBd) ?_ ?_
    · refine ((finite_circuits G).image fun C ↦ C.U).subset ?_
      rintro _ ⟨W, ⟨-, -, -, C, hC, -, hb⟩, rfl⟩
      exact ⟨C, ⟨hC.2, hC.1⟩, hb.symm⟩
    · rintro A ⟨hA, hAd, -⟩ B ⟨hB, hBd, -⟩ he
      exact disc_eq_of_subset_disc hT h₀ hAd hBd hA hB he
  obtain ⟨Δ', ⟨hsub, hd, hvs, C, hC, hCE, hb⟩, hmax⟩ := hfin.exists_maximal ⟨Δv, hv₀, hΔv,
    subset_rfl, Dv, hDv, fun e he ↦ .inr he, hbv⟩
  have hmax' : ∀ {A : Set Shat}, A ∈ 𝓕 → Δ' ⊆ A → A = Δ' := fun hA hle ↦ Subset.antisymm
    (hmax hA hle) hle
  have hCU : C.U ⊆ Δ' := hb ▸ Surface.discBd_subset _
  have hclosed : IsClosed Δ' := hd.isClosed
  have hint : discInt Δv ⊆ discInt Δ' := by
    intro x hx
    refine ⟨hvs hx.1, fun hxb ↦ ?_⟩
    have hf : x ∈ frontier Δ' := by
      rw [IsClosedDisc.frontier_eq_discBd hT hd]
      exact hxb
    exact hf.2 (mem_interior.mpr ⟨_, (discInt_subset _).trans hvs, hΔv.isOpen_discInt hman, hx⟩)
  have hFs : ∀ e ∈ F.E, e ∈ G.E := fun e he ↦ hF.1.2 he
  have hcase : ∀ e ∈ F.E, closure e ⊆ Δ' ∨ Disjoint e Δ' := fun e he ↦ by
    by_cases heC : e ∈ C.E
    · exact .inl ((C.closure_subset_U heC).trans hCU)
    · rcases edge_inside_or_off hT hC.1 hd hb (hFs e he) heC with h | h
      · exact .inl (closure_minimal (h.trans (discInt_subset _)) hclosed)
      · exact .inr h
  have hkey : Δf ⊆ Δ' := by
    by_cases hall : ∀ e ∈ F.E, closure e ⊆ Δ'
    · have hU : F.U ⊆ Δ' := U_of_edges hF.2 hclosed fun e he ↦ subset_closure.trans (hall e he)
      obtain ⟨Δ'', ⟨hs₁, hd₁, hb₁, -⟩, -⟩ := disc_oArc Δ' F.U hd hU (GM14.isOArc_of_isCircuit hF.2)
      rw [disc_eq_of_subset_disc hT h₀ hΔf hd₁ hf₀ (hs₁.trans hsub) (hbf.trans hb₁.symm)]
      exact hs₁
    push Not at hall
    obtain ⟨e₀, he₀, hout⟩ := hall
    have he₀d := (hcase e₀ he₀).resolve_left hout
    by_cases hin : ∃ e ∈ F.E, closure e ⊆ Δ'
    · exfalso
      obtain ⟨e₁, he₁, hcl⟩ := hin
      obtain ⟨a, b, hne, hcap⟩ := hG e₁ (hFs e₁ he₁)
      have ham : a ∈ closure e₁ ∩ G.V := by
        rw [hcap]
        exact .inl rfl
      have hbm : b ∈ closure e₁ ∩ G.V := by
        rw [hcap]
        exact .inr rfl
      have hl : G.toGraph.IsLink e₁ a b := ⟨hFs e₁ he₁, ham.2, hbm.2, hcap⟩
      have hends := Drawing.IsLink.mem_V_of_sub hF.1 hl he₁
      obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 hends.1 hends.2 hne
      obtain ⟨u, v, M, hu, hv, hMs, he₀M, hME, hinner⟩ : ∃ (u v : Shat)
        (M : GraphWalk G.toGraph u v), u ∈ Δ' ∧ v ∈ Δ' ∧ M.IsSimple ∧ e₀ ∈ M.edges ∧
          (∀ e ∈ M.edges, e ∈ F.E) ∧ ∀ x ∈ M.support, x ∈ Δ' → x = u ∨ x = v := by
        rcases (hs.E e₀).mp he₀ with h | h
        · obtain ⟨u, v, M, h₁, h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₁ hs.s₁ (hcl ham.1)
            (hcl hbm.1) h
          exact ⟨u, v, M, h₁, h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inl (h₅ e he)), h₆⟩
        · obtain ⟨u, v, M, h₁, h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₂ hs.s₂ (hcl hbm.1)
            (hcl ham.1) h
          exact ⟨u, v, M, h₁, h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inr (h₅ e he)), h₆⟩
      have huv : u ≠ v := by
        rintro rfl
        rw [(simple_self hMs).1] at he₀M
        cases he₀M
      have hMoff : ∀ e ∈ M.edges, Disjoint e Δ' := fun e he ↦ by
        rcases GraphWalk.edge_has_middle M hMs huv he with h | ⟨x, hxs, hxc, hxu, hxv⟩
        · rw [h] at he₀M
          obtain rfl : e₀ = e := by simpa using he₀M
          exact he₀d
        · refine (hcase e (hME e he)).resolve_left fun h' ↦ ?_
          rcases hinner x hxs (h' hxc) with h'' | h''
          · exact hxu h''
          · exact hxv h''
      have hstart : ∀ {a b : Shat} (N : GraphWalk G.toGraph a b), a ≠ b → (∀ e ∈ N.edges, e ∈ F.E)
        → (∀ e ∈ N.edges, Disjoint e Δ') → a ∈ Δ' → a ∈ F.V ∧ a ∈ C.V := by
        intro a b N hab hE hD haΔ
        cases N with
        | nil _ => exact absurd rfl hab
        | @cons _ y _ e hl r =>
          have heF := hE e (by simp)
          have haF := (Drawing.IsLink.mem_V_of_sub hF.1 hl heF).1
          refine ⟨haF, ?_⟩
          have hdis := hD e (by simp)
          have hac : a ∈ closure e := by
            have : a ∈ closure e ∩ G.V := by
              rw [hl.2.2.2]
              exact .inl rfl
            exact this.1
          have haf : a ∈ frontier Δ' := by
            refine ⟨subset_closure haΔ, fun hi ↦ ?_⟩
            obtain ⟨y, hyi, hye⟩ := mem_closure_iff.mp hac _ isOpen_interior hi
            exact disjoint_left.mp hdis hye (interior_subset hyi)
          rw [IsClosedDisc.frontier_eq_discBd hT hd, hb] at haf
          by_contra hnV
          obtain ⟨g, hg, hag⟩ := C.exists_edge_of_mem haf hnV
          exact ((hC.1.2 hg).2.1 hag).2 hl.2.1
      obtain ⟨huF, huC⟩ := hstart M huv hME hMoff hu
      obtain ⟨hvF, hvC⟩ := hstart M.reverse huv.symm (fun e he ↦ hME e
        (by simpa [GraphWalk.edges_reverse] using he))
        (fun e he ↦ hMoff e (by simpa [GraphWalk.edges_reverse] using he)) hv
      have hMV := support_subset_of_edges hF.1 M huF hME
      have hPF : (walkDrawing G M).U ⊆ F.U := by
        intro x hx
        rw [mem_walkDrawing_U] at hx
        rcases hx with hx | ⟨e, he, hxe⟩
        · exact F.V_subset_U (hMV x hx)
        · exact F.closure_subset_U (hME e he) hxe
      have hPU : (walkDrawing G M).U ∩ Δ' = {u, v} := by
        apply Subset.antisymm
        · rintro x ⟨hx, hxΔ⟩
          rw [mem_walkDrawing_U] at hx
          rcases hx with hx | ⟨e, he, hxe⟩
          · exact hinner x hx hxΔ
          · rcases closure_edge_subset (hF.1.2 (hME e he)) hxe with h' | h'
            · exact absurd hxΔ (disjoint_left.mp (hMoff e he) h')
            · obtain ⟨p, q, hl', A, B, rfl⟩ := GraphWalk.exists_split_edge M he
              have hxm : x ∈ closure e ∩ G.V := ⟨hxe, h'⟩
              rw [hl'.2.2.2] at hxm
              refine hinner x ?_ hxΔ
              rcases hxm with rfl | rfl
              · exact (GraphWalk.mem_support_append _ _).mpr (.inl A.end_mem_support)
              · exact (GraphWalk.mem_support_append _ _).mpr (.inr (by simp [B.start_mem_support]))
        · rintro x (rfl | rfl)
          · exact ⟨(mem_walkDrawing_U _ _).mpr (.inl M.start_mem_support), hu⟩
          · exact ⟨(mem_walkDrawing_U _ _).mpr (.inl M.end_mem_support), hv⟩
      have hFΔf : F.U ⊆ Δf := hbf ▸ Surface.discBd_subset _
      obtain ⟨F', W', hF', hW'Δ, hW', hlt, hbd', hU', -⟩ := exists_larger_circuit hT h₀ hd hsub hC
        hb huC hvC huv
        (P := walkDrawing G M) ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hMs⟩
          ((hPF.trans hFΔf).trans hf₀) hPU
      have hF'E : ∀ e ∈ F'.E, e ∈ F.E ∨ e ∈ Dv.E := fun e he ↦ by
        by_cases heC : e ∈ C.E
        · exact hCE e heC
        by_cases heM : e ∈ (walkDrawing G M).E
        · rw [walkDrawing_E] at heM
          exact .inl (hME e heM)
        · exfalso
          have heG := hF'.1.2 he
          obtain ⟨x, hx⟩ := heG.1
          have hxU : x ∈ F'.U := F'.closure_subset_U he (subset_closure hx)
          rcases hU' hxU with h' | h'
          · exact disjoint_left.mp (edge_disjoint_U (walkDrawing_isSubdrawing _ _) heG heM) hx h'
          · exact disjoint_left.mp (edge_disjoint_U hC.1 heG heC) hx h'
      have hmem : W' ∈ 𝓕 := ⟨hW'Δ, hW', hvs.trans hlt.1, F', hF', hF'E, hbd'⟩
      exact hlt.ne (hmax' hmem hlt.1).symm
    · push Not at hin
      have hoff : ∀ e ∈ F.E, Disjoint e Δ' := fun e he ↦ (hcase e he).resolve_left (hin e he)
      have hUd : F.U ⊆ (discInt Δ')ᶜ := U_of_edges hF.2 (hd.isOpen_discInt hman).isClosed_compl fun
        e he x hxe hxi ↦
        disjoint_left.mp (hoff e he) hxe hxi.1
      obtain ⟨x, hx₁, hx₂⟩ := hmeet
      have hsubi : discInt Δ' ⊆ discInt Δf := (isSide_int hT hΔf hbf).subset
        hd.isPreconnected_discInt
        (disjoint_left.mpr fun y hy hyU ↦ hUd hyU hy) ⟨x, hint hx₂, hx₁⟩
      have hle : Δ' ⊆ Δf := by
        rw [← closure_discInt hd]
        exact closure_minimal (hsubi.trans (discInt_subset _)) hΔf.isClosed
      have hmem : Δf ∈ 𝓕 := ⟨hf₀, hΔf, hvs.trans hle, F, hF, fun e he ↦ .inl he, hbf⟩
      exact (hmax' hmem hle).le
  exact ⟨C, Δ', hC, hCE, hd, hsub, hb, hkey, hvs⟩

end GraphMinor.GM19
