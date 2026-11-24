/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.ArcDisc

/-!
# Replacing a disc by one border cell

We prove `NormalIArcReplaceDiscPaintingStatement`, the surface part of (7.4) of Graph Minors XVII
(pages 180–181): the part of a painting
inside a disc cut off by an `I`-arc can be replaced by one border cell.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- The ends of a line are the two points given. -/
theorem lineEnds_eq {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : lineEnds L
  = {u, v} := by
  apply subset_antisymm _ (ends_subset_of_isLineWithEnds h).2
  rintro x ⟨y, f', h1, -⟩
  obtain ⟨f, rfl, rfl⟩ := h
  let g : unitInterval ≃ₜ unitInterval := f'.trans f.symm
  have hg : ∀ t, (f (g t)).1 = (f' t).1 := fun t => by simp [g]
  rcases g.continuous.strictMono_of_inj g.injective with hm | ha
  · left
    obtain ⟨t, ht⟩ := g.surjective 0
    have : g 0 = 0 := le_antisymm ((hm.monotone unitInterval.nonneg').trans_eq ht)
      unitInterval.nonneg'
    rw [← h1, ← hg, this]
  · right
    obtain ⟨t, ht⟩ := g.surjective 1
    have : g 0 = 1 := le_antisymm unitInterval.le_one' (ht.symm.le.trans
      (ha.antitone unitInterval.nonneg'))
    rw [← h1, ← hg, this]
    rfl

/-- A boundary point of a closed disc that is an inner point of the space is a limit of points off
the disc. -/
theorem mem_closure_compl {Δ : Set S} {x : S} (hx : x ∈ discBd Δ) (hi : IsInteriorPoint x) : x ∈
  closure Δᶜ := by
  by_contra hn
  have hint : x ∈ interior Δ := by
    rw [interior_eq_compl_closure_compl]
    exact hn
  obtain ⟨V, hV, hxV, hsub, ⟨e⟩⟩ := hi.exists_subset isOpen_interior hint
  obtain ⟨z, hz, rfl⟩ := hx
  have h1 : Subtype.val '' (Subtype.val ⁻¹' V : Set Δ) = V :=
    image_preimage_eq_of_subset fun y hy => by
      rw [Subtype.range_val]
      exact interior_subset (hsub hy)
  exact hz ⟨_, hV.preimage continuous_subtype_val, hxV,
    ⟨(IsEmbedding.subtypeVal.homeomorphImage _).trans ((Homeomorph.setCongr h1).trans e)⟩⟩

private theorem nodes_outside_cut_disc
    (S : Type)
    [TopologicalSpace S]
    (Γ : Painting S)
    (n₁ : S)
    (n₂ : S)
    (F : Set S)
    (Δ : Set S)
    (hFN : F ∩ Γ.N = {n₁, n₂})
    (hnb : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x)
    (hFΔ : F ⊆ closure Δᶜ)
    (hnF : {n₁, n₂} ⊆ F ∩ Γ.N) :
    Γ.N ∩ closure Δᶜ = Γ.N \ Δ ∪ {n₁, n₂} := by
  apply subset_antisymm
  · rintro x ⟨hx, hxc⟩
    by_cases h : x ∈ Δ
    · right
      by_cases hxF : x ∈ F
      · exact hFN ▸ ⟨hxF, hx⟩
      · have h3 := hnb x ⟨h, hxF⟩
        obtain ⟨y, hy, hy'⟩ := mem_closure_iff_nhds.mp hxc _ h3
        exact absurd hy hy'
    · exact .inl ⟨hx, h⟩
  · rintro x (⟨hx, h⟩ | hx)
    · exact ⟨hx, subset_closure h⟩
    · have h3 := hnF hx
      exact ⟨h3.2, hFΔ h3.1⟩

/-- The surface part of (7.4) of Graph Minors XVII, pages 180–181. -/
theorem normalIArcReplaceDisc : NormalIArcReplaceDiscPaintingStatement := by
  unfold NormalIArcReplaceDiscPaintingStatement
  intro S _ hS Γ n₁ n₂ F Δ hnorm hF hb hFN hΔ h1 h2
  have ht2 : T2Space S := hS.2.1
  obtain ⟨I, I', Θ, hΘ, hI, hI', hu', hi', hu, hi, hmeet, hnb⟩ := arc_disc_data hS hF hb hΔ h1 h2
  have hcl := hΔ.isClosed
  have hIΘ : I ⊆ Θ := fun z hz => hu' ▸ .inl hz
  have hΘb : Θ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hIΔ : I ⊆ Δ := fun z hz => (hmeet ▸ hz : z ∈ Δ ∩ bd S).1
  have hbdΔ : discBd Δ ⊆ Δ := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hside : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ := fun c hc => cell_side hc hnorm hΔ hnb
  have hFΔ : F ⊆ closure Δᶜ := by
    have h3 : F \ {n₁, n₂} ⊆ closure Δᶜ := fun x hx => by
      refine mem_closure_compl (h1 hx.1) ?_
      by_contra hn
      exact hx.2 (hb ▸ ⟨hx.1, hn⟩)
    exact (hF.subset_closure_diff).trans (closure_minimal h3 isClosed_closure)
  have hnF : ({n₁, n₂} : Set S) ⊆ F ∩ Γ.N := hFN.symm.subset
  have hn₁N : n₁ ∈ Γ.N := (hnF (mem_insert _ _)).2
  have hn₂N : n₂ ∈ Γ.N := (hnF (mem_insert_of_mem _ rfl)).2
  have hn₁F : n₁ ∈ F := (hnF (mem_insert _ _)).1
  have hn₂F : n₂ ∈ F := (hnF (mem_insert_of_mem _ rfl)).1
  have hn₁Δ : n₁ ∈ Δ := hbdΔ (h1 hn₁F)
  have hn₂Δ : n₂ ∈ Δ := hbdΔ (h1 hn₂F)
  have hNeq : Γ.N ∩ closure Δᶜ = (Γ.N \ Δ) ∪ {n₁, n₂} := by
    exact nodes_outside_cut_disc S Γ n₁ n₂ F Δ hFN hnb hFΔ hnF
  let c' : Set S := Δ \ {n₁, n₂}
  let N' : Set S := (Γ.N \ Δ) ∪ {n₁, n₂}
  have hc'cl : closure c' = Δ := by
    apply subset_antisymm (closure_minimal sdiff_subset hcl)
    refine hΔ.subset_closure_discInt.trans (closure_mono ?_)
    rintro x ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    rintro (rfl | rfl)
    · exact hn (h1 hn₁F)
    · exact hn (h1 hn₂F)
  have hc't : tilde c' = {n₁, n₂} := by
    rw [tilde, hc'cl]
    ext x
    simp only [c', mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨h3, h4⟩
      exact h4 h3
    · rintro h3
      refine ⟨?_, fun _ => h3⟩
      rcases h3 with rfl | rfl
      · exact hn₁Δ
      · exact hn₂Δ
  have hne₂ : n₁ ≠ n₂ := hF.ne'
  have hdΔ : Disjoint N' c' := by
    rw [disjoint_left]
    rintro x (⟨-, h⟩ | h) hx
    · exact h hx.1
    · exact hx.2 h
  have hIne : ∃ z, z ∈ I \ {n₁, n₂} := by
    by_contra h
    push Not at h
    have h3 := hI.subset_closure_diff hI.left_mem
    rw [show I \ {n₁, n₂} = ∅ from eq_empty_iff_forall_notMem.mpr fun z hz => h z hz,
      closure_empty] at h3
    exact h3
  obtain ⟨z, hzI⟩ := hIne
  have hzc' : z ∈ c' := ⟨hIΔ hzI.1, hzI.2⟩
  have hc'ne : c'.Nonempty := ⟨z, hzc'⟩
  have hc'pc : IsPathConnected c' := isPathConnected_of_isClosedDisc_finite_diff hΔ sdiff_subset
    ((finite_singleton _ |>.insert _).subset fun x hx => by
      by_contra h
      exact hx.2 ⟨hx.1, h⟩)
  let J : Set (Set S) := insert c' {c ∈ Γ.C | c ⊆ Δᶜ}
  have hJ_finite : J.Finite := by
    have hfinite : {c ∈ Γ.C | c ⊆ Δᶜ}.Finite :=
      Γ.finite_cells.subset fun _ hc => hc.1
    exact hfinite.insert _
  have hJ : arcComponentsIn ((Γ.U ∪ Δ) \ N') = J := by
    refine arcComponentsIn_eq_of_finite_cover hJ_finite ?_ ?_ ?_ ?_ ?_
    · ext x
      constructor
      · rintro ⟨d, (rfl | ⟨hd, hdc⟩), hx⟩
        · exact ⟨.inr hx.1, fun h => disjoint_left.mp hdΔ h hx⟩
        · refine ⟨.inl (arcComponentsIn_subset hd hx).1, ?_⟩
          rintro (h | h)
          · exact (arcComponentsIn_subset hd hx).2 h.1
          · exact hdc hx (hbdΔ (h1 (hnF h).1))
      · rintro ⟨hx | hx, hxN⟩
        · by_cases h : x ∈ Δ
          · exact ⟨c', .inl rfl, h, fun h3 => hxN (.inr h3)⟩
          · have hxN' : x ∉ Γ.N := fun h3 => hxN (.inl ⟨h3, h⟩)
            obtain ⟨c, hc, hxc⟩ := exists_mem_arcComponentsIn (show x ∈ Γ.U \ Γ.N from ⟨hx, hxN'⟩)
            exact ⟨c, .inr ⟨hc, (hside c hc).resolve_left fun h3 => h (h3 hxc)⟩, hxc⟩
        · exact ⟨c', .inl rfl, hx, fun h3 => hxN (.inr h3)⟩
    · rintro d (rfl | ⟨hd, -⟩)
      · exact hc'ne
      · exact arcComponentsIn_nonempty hd
    · rintro d (rfl | ⟨hd, -⟩)
      · exact hc'pc
      · exact arcComponentsIn_isPathConnected hd
    · rintro d (rfl | ⟨hd, hdc⟩) d' (rfl | ⟨hd', hdc'⟩) hne
      · exact absurd rfl hne
      · exact disjoint_left.mpr fun x hx hx' => hdc' hx' hx.1
      · exact disjoint_left.mpr fun x hx hx' => hdc hx hx'.1
      · exact arcComponentsIn_disjoint hd hd' hne
    · rintro d (rfl | ⟨hd, hdc⟩)
      · rw [hc'cl]
        ext x
        constructor
        · rintro ⟨hx, -, hxN⟩
          exact ⟨hx, fun h3 => hxN (.inr h3)⟩
        · intro hx
          exact ⟨hx.1, .inr hx.1, fun h3 => disjoint_left.mp hdΔ h3 hx⟩
      · ext x
        constructor
        · rintro ⟨hx, -, hxN⟩
          by_contra h
          have hxt : x ∈ tilde d := ⟨hx, h⟩
          have h3 : x ∈ Γ.N ∩ closure Δᶜ := ⟨Γ.tilde_subset_N hd hxt, closure_mono hdc hx⟩
          exact hxN (show x ∈ (Γ.N \ Δ) ∪ {n₁, n₂} from hNeq ▸ h3)
        · intro hx
          refine ⟨subset_closure hx, .inl (arcComponentsIn_subset hd hx).1, ?_⟩
          rintro (h | h)
          · exact (arcComponentsIn_subset hd hx).2 h.1
          · exact hdc hx (hbdΔ (h1 (hnF h).1))
  have hF'eq : discBd Δ ∩ Θ = I := by
    apply subset_antisymm
    · rintro x ⟨hx, hxΘ⟩
      exact hmeet ▸ ⟨hbdΔ hx, hΘb hxΘ⟩
    · exact fun x hx => ⟨hu ▸ .inr hx, hIΘ hx⟩
  let Γ' : Painting S :=
    { U := Γ.U ∪ Δ
      N := N'
      isClosed_U := Γ.isClosed_U.union hcl
      N_subset := by
        rintro x (h | h)
        · exact .inl (Γ.N_subset h.1)
        · exact .inr (hbdΔ (h1 (hnF h).1))
      finite_N := (Γ.finite_N.subset sdiff_subset).union (by simp)
      finite_cells := by
        rw [hJ]
        exact hJ_finite
      cell_disc := by
        rw [hJ]
        rintro d (rfl | ⟨hd, -⟩)
        · rw [hc'cl, hc't]
          refine ⟨hΔ, fun x hx => ?_, by simp, ?_⟩
          · exact h1 (hnF hx).1
          · rw [ncard_pair hne₂]
            omega
        · exact Γ.cell_disc d hd
      bd_subset := fun x hx => .inl (Γ.bd_subset hx)
      border_cell := by
        rw [hJ]
        rintro d (rfl | ⟨hd, -⟩) h
        · rw [hc'cl, hc't, hmeet, lineEnds_eq hI, ncard_pair hne₂]
          exact ⟨rfl, by simp, ⟨hI.choose⟩, rfl⟩
        · exact Γ.border_cell d hd h }
  have hΓC : Γ'.C = J := hJ
  obtain ⟨c₁, hc₁, h3, h4, h5, -⟩ := exists_border_cell hI (hIΘ.trans hΘb) hIΔ hn₁N hside
  obtain ⟨c₂, hc₂, h6, h7, h8, -⟩ := exists_border_cell hI.symm (hIΘ.trans hΘb) hIΔ hn₂N hside
  refine ⟨Γ', Θ, I', ?_⟩
  intro c'' F'
  have hc'' : c'' = c' := rfl
  have hF' : F' = I := hF'eq
  refine ⟨rfl, hNeq.symm, rfl, hΘ, ⟨hn₁N, hIΘ hI.left_mem⟩, ⟨hn₂N, hIΘ hI.right_mem⟩, ?_, ?_, ?_,
    ?_, hI', ?_, ?_, hside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu]
    exact union_subset_union_right _ hIΘ
  · rw [hF']
    exact hmeet
  · rw [hF']
    exact hI
  · rw [← hu']
    exact subset_union_right
  · rw [hF']
    exact hu'
  · rw [hF']
    exact hi'
  · intro c hc hcΔ x hx
    have h9 : x ∈ Γ.N ∩ closure Δᶜ := ⟨Γ.tilde_subset_N hc hx, closure_mono hcΔ hx.1⟩
    rw [hNeq] at h9
    exact h9
  · rw [hc'', hΓC]
    exact .inl rfl
  · exact ⟨z, hzc', hIΘ hzI.1⟩
  · exact hc't
  · exact hΓC
  · rintro ⟨-, h9⟩
    exact h9 hzc' hzc'.1
  · exact ⟨c₁, hc₁, h3, h4, h5⟩
  · exact ⟨c₂, hc₂, h6, h7, h8⟩

end GraphMinor.GM17
