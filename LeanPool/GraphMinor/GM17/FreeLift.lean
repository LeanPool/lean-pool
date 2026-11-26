/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Bigon

/-!
# The free side of a curve at a node

We cut a closed surface along a curve through a node `n`. The cells at `n` and the disc on the cuff
of `n` all come to `n` from one side, so one lift of `n` stays away
from the lift of the paint and the discs (`exists_free_lift`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S T : Type} [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T]

theorem cutMap_of_cutting {ψ : Y → T} {F : Set T} (h : IsCutting ψ F)
  (hF : IsClosed F) : CutMap ψ F := by
  refine ⟨h.1, h.2.2.1, ?_, hF, fun x hx => cut_encard_le h hx, h.2.2.2.2⟩
  rw [h.2.1.range_eq, ← compl_eq_univ_sdiff]
  exact hF.isOpen_compl

theorem disc_diff_finite [T2Space T] {D P : Set T} (hD : IsClosedDisc D)
  (hP : P ∩ D ⊆ discBd D) : closure (D \ P) = D ∧ tilde (D \ P) ⊆ P ∩ D := by
  have hcl := (hD.sdiff_of_inter_subset_discBd hP).2.2
  refine ⟨hcl, ?_⟩
  rintro x ⟨hx, hn⟩
  rw [hcl] at hx
  refine ⟨?_, hx⟩
  by_contra hc
  exact hn ⟨hx, hc⟩

theorem mem_closure_line_diff {L P : Set T} {u v x : T} (hL : IsLineWithEnds L u v)
  (hx : x ∈ L) (hP : P.Finite) : x ∈ closure (L \ P) := by
  obtain ⟨a, ha, rfl, -, -⟩ := hL.exists_arc
  obtain ⟨t, rfl⟩ := hx
  have hfin : (a ⁻¹' P).Finite := hP.preimage ha.2.injOn
  have hd : Dense (univ \ a ⁻¹' P) := dense_univ.sdiff_finite hfin
  have h1 : t ∈ closure (univ \ a ⁻¹' P) := hd t
  refine image_closure_subset_closure_image ha.1 (mem_image_of_mem _ h1) |> closure_mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨mem_range_self s, hs.2⟩

/-- Every point in the closure of a set has a lift in the closure of the preimage. -/
theorem exists_lift_closure [CompactSpace Y] [T2Space T] {ψ : Y → T} (hc : Continuous ψ)
  (hs : Function.Surjective ψ) {Q : Set T} {x : T} (hx : x ∈ closure Q) :
    ∃ y ∈ closure (ψ ⁻¹' Q), ψ y = x := by
  have h1 : IsClosed (ψ '' closure (ψ ⁻¹' Q)) := (isClosed_closure.isCompact.image hc).isClosed
  have h2 : Q ⊆ ψ '' closure (ψ ⁻¹' Q) := fun z hz => by
    obtain ⟨y, rfl⟩ := hs z
    exact ⟨y, subset_closure hz, rfl⟩
  exact closure_minimal h2 h1 hx

theorem exists_free_lift [CompactSpace Y] [T2Space Y]
  [T2Space T] (hS : IsSurface S) {Γ : Painting S} {F : Set S}
    (hnorm : Γ.IsNormal F) (hint : ∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F) {n : S}
      (hnF : n ∈ F) (hnN : n ∈ Γ.N) {j : S → T} {cap : Set S → Set T}
    (hj : IsClosedEmbedding j) (hcap : ∀ C ∈ cuffs S, IsClosedDisc (cap C) ∧ discBd (cap C)
      = j '' C ∧ range j ∩ cap C = j '' C) {ψ : Y → T}
    (hψ : IsCutting ψ (j '' F)) (hFc : IsClosed (j '' F)) :
    ∃ y, ψ y = j n ∧ y ∉ closure (ψ ⁻¹' ((j '' Γ.U ∪ ⋃ C ∈ cuffs S, cap C) \ j '' F)) := by
  classical
  have hm := cutMap_of_cutting hψ hFc
  have hneY : Nonempty Y := ⟨(hψ.2.1 (j n)).choose⟩
  have hfinC := (cuff_statement.{0} S hS).2.1
  have hsurj : ∀ x, x ∈ range ψ := fun x => hψ.2.1 x
  have hcell : ∀ c ∈ Γ.C, Disjoint c F := fun c hc => disjoint_left.mpr fun x hx hxF =>
    (arcComponentsIn_subset hc hx).2 (hnorm ⟨hxF, (arcComponentsIn_subset hc hx).1⟩)
  have hinj_c : ∀ c ∈ Γ.C, InjOn ψ (closure (ψ ⁻¹' (j '' c))) := fun c hc => by
    obtain ⟨h1, h2, h3, -⟩ := Γ.cell_disc c hc
    refine hm.injOn_closure ?_ ?_ ?_ ?_ ?_
    · exact (disjoint_image_iff hj.injective).mpr (hcell c hc)
    · rw [hj.closure_image_eq]
      exact image_emb_disc hj.isEmbedding h1
    · rw [tilde_image_emb hj, hj.closure_image_eq, discBd_image hj.isEmbedding]
      exact image_mono h2
    · rw [tilde_image_emb hj]
      exact h3.image _
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hsurj _, fun h => disjoint_left.mp ((disjoint_image_iff hj.injective).mpr
        (hcell c hc)) (mem_image_of_mem _ hx) h⟩
  have hbC : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun {C} hC => by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hPE : ∀ C ∈ cuffs S, (j '' F ∩ cap C ⊆ discBd (cap C)) ∧ (j '' F ∩ cap C).Finite := fun C hC
    => by
    obtain ⟨h1, h2, h3⟩ := hcap C hC
    have h4 : j '' F ∩ cap C ⊆ j '' (F ∩ Γ.N) := by
      rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
      obtain ⟨y, hy, he⟩ := (h3 ▸ ⟨⟨x, rfl⟩, hx'⟩ : j x ∈ j '' C)
      obtain rfl := hj.injective he
      exact mem_image_of_mem _ ⟨hx, hnorm ⟨hx, Γ.bd_subset (hbC hC hy)⟩⟩
    refine ⟨?_, ((Γ.finite_N.subset inter_subset_right).image _).subset h4⟩
    rw [h2]
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    exact h3 ▸ (⟨⟨x, rfl⟩, hx'⟩ : j x ∈ range j ∩ cap C)
  have hinj_E : ∀ C ∈ cuffs S, InjOn ψ (closure (ψ ⁻¹' (cap C \ j '' F))) := fun C hC => by
    obtain ⟨h1, -, -⟩ := hcap C hC
    obtain ⟨h5, h6⟩ := hPE C hC
    have hP : j '' F ∩ cap C ⊆ discBd (cap C) := h5
    obtain ⟨h7, h8⟩ := disc_diff_finite h1 hP
    refine hm.injOn_closure disjoint_sdiff_left ?_ ?_ (h6.subset h8) fun x hx => ⟨hsurj _, hx.2⟩
    · rw [h7]
      exact h1
    · rw [h7]
      exact h8.trans h5
  have hfar : ∀ Q, j n ∉ closure Q → ∀ y, ψ y = j n → y ∉ closure (ψ ⁻¹' Q) := fun Q hQ y hy hc
    => hQ (hy ▸ hψ.1.closure_preimage_subset Q hc)
  let 𝒬 : Set (Set T) := (fun c => j '' c) '' Γ.C ∪ (fun C => cap C \ j '' F) '' cuffs S
  have hfinQ : 𝒬.Finite := (Γ.finite_cells.image _).union (hfinC.image _)
  have htil : ∀ c ∈ Γ.C, n ∈ closure c → n ∈ tilde c := fun c hc h => ⟨h, fun hn =>
    (arcComponentsIn_subset hc hn).2 hnN⟩
  have hbord : ∀ c ∈ Γ.C, n ∈ tilde c → (c ∩ bd S).Nonempty := fun c hc ht => by
    by_contra hn
    exact disjoint_left.mp (hint c hc ⟨hc, hn⟩) ht hnF
  have hfree : ∃ y, ψ y = j n ∧ ∀ Q ∈ 𝒬, y ∉ closure (ψ ⁻¹' Q) := by
    by_cases hnb : n ∈ bd S
    · have hΘ : connectedComponentIn (bd S) n ∈ cuffs S := ⟨n, hnb, rfl⟩
      set Θ := connectedComponentIn (bd S) n with hΘdef
      have hnΘ : n ∈ Θ := mem_connectedComponentIn hnb
      obtain ⟨h1, h2, h3⟩ := hcap Θ hΘ
      have hmE : j n ∈ cap Θ := discBd_subset _ (h2 ▸ mem_image_of_mem _ hnΘ)
      have hcl₀ := (disc_diff_finite h1 (hPE Θ hΘ).1).1
      obtain ⟨y₀, hy₀, hy₀m⟩ := exists_lift_closure hψ.1 hψ.2.1 (hcl₀.symm ▸ hmE : j n ∈ closure
        (cap Θ \ j '' F))
      have hmF : j n ∈ j '' F := mem_image_of_mem _ hnF
      obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.mp (hψ.2.2.2.1 _ hmF)
      have hother : ∃ y, ψ y = j n ∧ y ≠ y₀ := by
        have ha : ψ a = j n := (show a ∈ ψ ⁻¹' {j n} from he ▸ mem_insert _ _)
        have hb : ψ b = j n := (show b ∈ ψ ⁻¹' {j n} from he ▸ mem_insert_of_mem _ rfl)
        by_cases h : a = y₀
        · exact ⟨b, hb, fun h' => hab (h.trans h'.symm)⟩
        · exact ⟨a, ha, h⟩
      obtain ⟨y, hy, hyne⟩ := hother
      refine ⟨y, hy, ?_⟩
      rintro Q (⟨c, hc, rfl⟩ | ⟨C, hC, rfl⟩)
      · simp only
        by_cases hnc : n ∈ closure c
        · intro hyc
          obtain ⟨u, v, -, htc, hl, hce, -, -⟩ := Γ.border_cell_exists_ends hc (hbord c hc
            (htil c hc hnc))
          have hnL : n ∈ closure c ∩ bd S := ⟨hnc, hnb⟩
          have hLΘ : closure c ∩ bd S ⊆ Θ := subset_cuff hΘ (isPreconnected_line hl)
            inter_subset_right hnΘ hnL
          have hfinP : (F ∩ Γ.N ∪ {u, v}).Finite := (Γ.finite_N.subset inter_subset_right).union
            (by simp)
          let M : Set T := j '' ((closure c ∩ bd S) \ (F ∩ Γ.N ∪ {u, v}))
          have hMc : M ⊆ j '' c := image_mono fun x hx => by
            have h4 : x ∈ c ∩ bd S := hce ▸ ⟨hx.1, fun h => hx.2 (.inr h)⟩
            exact h4.1
          have hMQ : M ⊆ cap Θ \ j '' F := by
            rintro _ ⟨x, hx, rfl⟩
            refine ⟨discBd_subset _ (h2 ▸ mem_image_of_mem _ (hLΘ hx.1)), ?_⟩
            rintro ⟨z, hz, he⟩
            obtain rfl := hj.injective he
            exact hx.2 (.inl ⟨hz, hnorm ⟨hz, Γ.bd_subset hx.1.2⟩⟩)
          have hmM : j n ∈ closure M := image_closure_subset_closure_image hj.continuous
            (mem_image_of_mem _ (mem_closure_line_diff hl hnL hfinP))
          obtain ⟨y', hy', hy'm⟩ := exists_lift_closure hψ.1 hψ.2.1 hmM
          have h5 := hinj_c c hc (closure_mono (preimage_mono hMc) hy') hyc (hy'm.trans hy.symm)
          have h6 := hinj_E Θ hΘ (closure_mono (preimage_mono hMQ) hy') hy₀ (hy'm.trans hy₀m.symm)
          exact hyne (h5.symm.trans h6)
        · refine hfar _ ?_ y hy
          rw [hj.closure_image_eq]
          exact fun h => hnc (hj.injective.mem_set_image.mp h)
      · simp only
        by_cases hCe : C = Θ
        · subst hCe
          exact fun hyc => hyne (hinj_E _ hΘ hyc hy₀ (hy.trans hy₀m.symm))
        · refine hfar _ ?_ y hy
          rw [(disc_diff_finite (hcap C hC).1 (hPE C hC).1).1]
          intro hmem
          obtain ⟨z, hz, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨n, rfl⟩, hmem⟩ : j n ∈ j '' C)
          obtain rfl := hj.injective he
          exact hCe (cuffs_disjoint_eq hC hΘ hz hnΘ)
    · obtain ⟨y, hy⟩ := hψ.2.1 (j n)
      refine ⟨y, hy, ?_⟩
      rintro Q (⟨c, hc, rfl⟩ | ⟨C, hC, rfl⟩)
      · refine hfar _ ?_ y hy
        simp only
        rw [hj.closure_image_eq]
        intro h
        have hnc := hj.injective.mem_set_image.mp h
        obtain ⟨u, v, -, htc, -, -, hu, hv⟩ := Γ.border_cell_exists_ends hc (hbord c hc
          (htil c hc hnc))
        rcases (htc ▸ htil c hc hnc : n ∈ ({u, v} : Set S)) with rfl | rfl
        · exact hnb hu.2
        · exact hnb hv.2
      · refine hfar _ ?_ y hy
        simp only
        rw [(disc_diff_finite (hcap C hC).1 (hPE C hC).1).1]
        intro hmem
        obtain ⟨z, hz, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨n, rfl⟩, hmem⟩ : j n ∈ j '' C)
        obtain rfl := hj.injective he
        exact hnb (hbC hC hz)
  obtain ⟨y, hy, hyQ⟩ := hfree
  refine ⟨y, hy, ?_⟩
  let B : Set Y := (⋃ Q ∈ 𝒬, closure (ψ ⁻¹' Q)) ∪ ψ ⁻¹' (j '' (Γ.N \ {n}))
  have hBc : IsClosed B := (hfinQ.isClosed_biUnion fun _ _ => isClosed_closure).union
    ((((Γ.finite_N.subset sdiff_subset).image _).isClosed).preimage hψ.1)
  have hsub : ψ ⁻¹' ((j '' Γ.U ∪ ⋃ C ∈ cuffs S, cap C) \ j '' F) ⊆ B := by
    rintro w ⟨h1 | h1, hwF⟩
    · obtain ⟨x, hx, hxw⟩ := h1
      by_cases hxN : x ∈ Γ.N
      · refine .inr ⟨x, ⟨hxN, ?_⟩, hxw⟩
        rintro rfl
        exact hwF ⟨_, hnF, hxw⟩
      · obtain ⟨c, hc, hxc⟩ := exists_mem_arcComponentsIn (F := Γ.U \ Γ.N) (x := x) ⟨hx, hxN⟩
        exact .inl (mem_biUnion (.inl (mem_image_of_mem _ hc)) (subset_closure ⟨x, hxc, hxw⟩))
    · obtain ⟨C, hC, hw⟩ := mem_iUnion₂.mp h1
      exact .inl (mem_biUnion (.inr (mem_image_of_mem _ hC)) (subset_closure ⟨hw, hwF⟩))
  intro hc
  rcases closure_minimal hsub hBc hc with h1 | h1
  · obtain ⟨Q, hQ, h2⟩ := mem_iUnion₂.mp h1
    exact hyQ Q hQ h2
  · obtain ⟨x, hx, he⟩ := h1
    have := hj.injective (he.trans hy)
    exact hx.2 this

end GraphMinor.GM17
