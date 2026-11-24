/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffLines

/-!
# From the core of a cuff to its collar

Graph Minors VII, (5.9), page 235. The boxes of the core, with the height over `N(C)` and the ramps
over the pieces `N_i(C)`, make the collar of the cuff.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [T2Space S]

variable {G : Drawing S} {C : Set S} {j : S → T} {D : Set T} {r v ks m : ℕ} {Y E₀ Δ' Do : Set T}
  {Nk Bo : Drawing S} {R : Fin ks → Drawing S} {x t : Fin ks → S} {Q : ∀ i, GraphWalk G.toGraph
    (x i) (t i)} {L : Fin m → Drawing S} {El : Fin m → Set T} {N : Drawing S}

/-- The graph with the edges of `N(C)` taken out. -/
noncomputable def withoutEdges (G N : Drawing S) : Drawing S := G.span G.V (G.E \ N.E)

theorem withoutEdges_V (G N : Drawing S) : (withoutEdges G N).V = G.V := by
  refine subset_antisymm ?_ fun v hv => ?_
  · exact (G.span_isSubdrawing _ _).1
  · change v ∈ G.spanV _ _
    exact Or.inl ⟨hv, hv⟩

theorem withoutEdges_E (G N : Drawing S) : (withoutEdges G N).E = G.E \ N.E := by
  rw [withoutEdges, G.span_E]
  exact inter_eq_left.mpr sdiff_subset

theorem mem_withoutEdges_or {z : S} (hz : z ∈ G.U) : z ∈
  (withoutEdges G N).U ∨ z ∈ N.U := by
  by_cases hV : z ∈ G.V
  · exact .inl ((withoutEdges G N).V_subset_U (by rw [withoutEdges_V]; exact hV))
  · obtain ⟨e, he, hze⟩ := G.exists_edge_of_mem hz hV
    by_cases heN : e ∈ N.E
    · exact .inr (N.closure_subset_U heN (subset_closure hze))
    · exact .inl ((withoutEdges G N).closure_subset_U
        (by rw [withoutEdges_E]; exact ⟨he, heN⟩) (subset_closure hze))

theorem mem_V_of_withoutEdges (hN : N.IsSubdrawing G) {z : S} (hz : z ∈ (withoutEdges G N).U)
  (hzN : z ∈ N.U) : z ∈ G.V := by
  by_contra hV
  have hV' : z ∉ (withoutEdges G N).V := by rwa [withoutEdges_V]
  obtain ⟨e, he, hze⟩ := (withoutEdges G N).exists_edge_of_mem hz hV'
  have hVN : z ∉ N.V := fun h1 => hV (hN.1 h1)
  obtain ⟨e', he', hze'⟩ := N.exists_edge_of_mem hzN hVN
  rw [withoutEdges_E] at he
  exact he.2 (arcComponent_eq he.1 (hN.2 he') hze hze' ▸ he')

private theorem cuff_box_lies_in_uncapped_surface
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {ks : ℕ}
    {E₀ : Set T}
    {Δ' : Set T}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    (hc : IsCappedCuff C T j D)
    (F : Set (CellRec T (Fin ks)))
    (Φ : CellRec T (Fin ks) → ℝ × ℝ → T)
    (Sd : Fin ks → ℝ → T)
    (μ : CellRec T (Fin ks) → ℝ → T)
    (hfam : IsCellFamily D E₀ (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) univ F)
    (hb : IsCuffBoxes D E₀ Δ' (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) F Φ Sd μ)
    (c : CellRec T (Fin ks))
    (hcF : c ∈ F)
    (p : ℝ × ℝ)
    (hp : p ∈ cuffBox) :
    Φ c p ∈ range j := by
  by_contra hn
  have h1 : Φ c p ∈ D := by
    rcases hc.union_eq.ge (mem_univ (Φ c p)) with h2 | h2
    · exact absurd h2 hn
    · exact h2
  have h2 : p.2 = 0 := (hb.inD c hcF p hp).mp h1
  have h3 : Φ c p ∈ c.R ∩ D := ⟨hb.inR c hcF p hp (by rw [h2]; exact zero_le_one), h1⟩
  rw [(hfam.cell c hcF).botCap] at h3
  have h4 := (hfam.cell c hcF).aBd h3
  rw [hc.discBd_eq] at h4
  exact hn (image_subset_range _ _ h4)

private theorem cuff_box_height_set_closed
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    {ks : ℕ}
    (F : Set (CellRec T (Fin ks)))
    (φ : ↥F → ℝ × ℝ → S)
    (hbs : IsBoxSystem φ)
    (Go : Drawing S) :
    let Z : ↥F → Set (ℝ × ℝ) := fun c => {p | p ∈ cuffBox ∧ 1 ≤ p.2 ∧ φ c p ∈ Go.U}
    ∀ (c : ↥F),
    IsClosed (Z c) := by
  intro Z c
  have h1 : IsClosed {p : ℝ × ℝ | p ∈ cuffBox ∧ 1 ≤ p.2} := isCompact_cuffBox.isClosed.inter
    (isClosed_le continuous_const continuous_snd)
  have hs : {p : ℝ × ℝ | p ∈ cuffBox ∧ 1 ≤ p.2} ⊆ cuffBox := fun _ hp => hp.1
  have h2 := ((hbs.cont c).mono hs).preimage_isClosed_of_isClosed h1 Go.isClosed_U
  convert h2 using 1
  ext p
  exact ⟨fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩

private theorem cuff_box_top_graph_points_are_vertices
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (F : Set (CellRec T (Fin ks)))
    (φ : ↥F → ℝ × ℝ → S) :
    let Go : Drawing S := withoutEdges G Nk
    let Z : ↥F → Set (ℝ × ℝ) := fun c => {p | p ∈ cuffBox ∧ 1 ≤ p.2 ∧ φ c p ∈ Go.U}
    (∀ (c : ↥F), IsClosed (Z c)) →
    (∀ (c : ↥F), (0, 1) ∈ Z c) →
    let f : ↥F → ℝ → ℝ := fun c => topHeight (Z c)
    (∀ (c : ↥F), ∀ p ∈ cuffBox, φ c p ∈ Nk.U ↔ p.2 = 1) →
    (∀ (c : ↥F), ∀ p ∈ cuffBox, φ c p ∈ G.U → 1 < p.2 → f c p.1 < p.2) →
    (∀ (c : ↥F) (m : ℝ), 1 ≤ f c m) →
    ∀ (c : ↥F),
    ∀ (p : ℝ × ℝ),
    (p ∈ cuffBox) →
    (p.2 = f c p.1) →
    (φ c p ∈ G.U) →
    p.2 = 1 ∧ φ c p ∈ G.V := by
  intro Go Z hZcl hZ0 f hNk hF1 hfge c p hp he hU
  have h1 : p.2 = 1 := by
    by_contra hne
    have hgt : 1 < p.2 := lt_of_le_of_ne (he ▸ hfge c _) (Ne.symm hne)
    exact absurd (hF1 c p hp hU hgt) (he ▸ lt_irrefl _)
  refine ⟨h1, ?_⟩
  have h2 : topHeight (Z c) p.1 = 1 := by
    have h3 : f c p.1 = 1 := he ▸ h1
    exact h3
  have h3 := topHeight_eq_one (hZcl c) ⟨_, hZ0 c⟩ h2
  have hpeq : (p.1, (1 : ℝ)) = p := Prod.ext rfl h1.symm
  rw [hpeq] at h3
  exact mem_V_of_withoutEdges h.nkSub h3.2.2 ((hNk c p hp).mpr h1)

private theorem every_radial_line_is_a_box_side
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {j : S → T}
    {D : Set T}
    {ks : ℕ}
    {E₀ : Set T}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    (F : Set (CellRec T (Fin ks)))
    (Sd : Fin ks → ℝ → T)
    (hfam : IsCellFamily D E₀ (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) univ F)
    (φ : ↥F → ℝ × ℝ → S)
    (hL : ∀ (c : ↥F), ∀ w ∈ Icc 0 2, j (φ c (0, w)) = Sd c.1.i w)
    (hRt : ∀ (c : ↥F), ∀ w ∈ Icc 0 2, j (φ c (1, w)) = Sd c.1.i' w)
    (i : Fin ks) :
    ∃ (c : ↥F) (e : ℝ), (e = 0 ∨ e = 1) ∧ (∀ w ∈ Icc 0 2, j (φ c (e, w)) = Sd i w) ∧ (e = 0 → c.1.i
      = i) ∧ (e
      = 1 → c.1.i' = i) := by
  obtain ⟨c, hcF, hci | hci⟩ := hfam.used i (mem_univ i)
  · refine ⟨⟨c, hcF⟩, 0, .inl rfl, fun w hw => ?_, fun _ => hci, fun h1 => absurd h1 zero_ne_one⟩
    rw [hL _ w hw]
    exact hci ▸ rfl
  · refine ⟨⟨c, hcF⟩, 1, .inr rfl, fun w hw => ?_, fun h1 => absurd h1 one_ne_zero, fun _ => hci⟩
    rw [hRt _ w hw]
    exact hci ▸ rfl

private theorem box_top_orders_radial_trees
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (F : Set (CellRec T (Fin ks)))
    (Sd : Fin ks → ℝ → T)
    (φ : ↥F → ℝ × ℝ → S)
    (hbs : IsBoxSystem φ)
    (hbx : ∀ {m w : ℝ}, m ∈ Icc 0 1 → w ∈ Icc 0 2 → (m, w) ∈ cuffBox)
    (h0I : (0 : ℝ) ∈ Icc 0 1)
    (h1I : (1 : ℝ) ∈ Icc 0 1)
    (h12 : (1 : ℝ) ∈ Icc 0 2)
    (hφ01 : ∀ (c : ↥F), φ c (0, 1) = t c.1.i)
    (hφ11 : ∀ (c : ↥F), φ c (1, 1) = t c.1.i')
    (hNk : ∀ (c : ↥F), ∀ p ∈ cuffBox, φ c p ∈ Nk.U ↔ p.2 = 1)
    (hRp : ∀ (i : Fin ks), IsPreconnected (R i).U)
    (hRd : ∀ (i i' : Fin ks), i ≠ i' → Disjoint (R i).U (R i').U)
    (htinj : Injective t)
    (hused : ∀ (i : Fin ks), ∃ (c : ↥F) (e : ℝ), (e = 0 ∨ e = 1) ∧ (∀ w ∈ Icc 0 2, j (φ c (e, w))
      = Sd i w) ∧
      (e = 0 → c.1.i = i) ∧ (e = 1 → c.1.i' = i))
    (hφside : ∀ (i : Fin ks) (c : ↥F) (e : ℝ), (∀ w ∈ Icc 0 2, j (φ c (e, w)) = Sd i w) → φ c (e,
      0) = x i ∧ φ c (e, 1) = t i)
    (c : ↥F) :
    ∃ a b, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ ∀ m ∈ Icc 0 1, ∀ (i : Fin ks), φ c (m, 1) ∈ (R i).U → i =
      c.1.i ∧ m ≤ a ∨ i = c.1.i' ∧ b ≤ m := by
  have hmem : ∀ m ∈ Icc (0 : ℝ) 1, (m, (1 : ℝ)) ∈ cuffBox := fun m hm => hbx hm h12
  let τ : ℝ → S := fun m => φ c (m, 1)
  have hτ : IsParam (τ '' Icc 0 1) (t c.1.i) (t c.1.i') τ := by
    refine ⟨(hbs.cont c).comp (Continuous.continuousOn (by fun_prop)) hmem, fun m hm m' hm' he
      => congrArg Prod.fst (hbs.inj c (hmem m hm) (hmem m' hm') he), rfl, hφ01 c, hφ11 c⟩
  have hP : τ '' Icc 0 1 ⊆ Nk.U := by
    rintro _ ⟨m, hm, rfl⟩
    exact (hNk c _ (hmem m hm)).mpr rfl
  have hlr : c.1.i ≠ c.1.i' := fun he => by
    have h1 : φ c (0, 1) = φ c (1, 1) := by rw [hφ01, hφ11, he]
    have h2 := congrArg Prod.fst (hbs.inj c (hmem 0 h0I) (hmem 1 h1I) h1)
    exact zero_ne_one h2
  have hoff : ∀ i, i ≠ c.1.i → i ≠ c.1.i' → t i ∉ τ '' Icc 0 1 := by
    rintro i h1 h2 ⟨m, hm, he⟩
    obtain ⟨c', e, he', hs, h3, h4⟩ := hused i
    have heI : e ∈ Icc (0 : ℝ) 1 := by
      rcases he' with rfl | rfl
      · exact h0I
      · exact h1I
    have h5 : φ c (m, 1) = φ c' (e, 1) := he.trans (hφside i c' e hs).2.symm
    rcases hbs.meet c c' _ _ (hmem m hm) (hmem e heI) h5 with ⟨rfl, h6⟩ | ⟨-, h6, -⟩
    · rcases he' with rfl | rfl
      · exact h1 (h3 rfl).symm
      · exact h2 (h4 rfl).symm
    · rcases h6 with h6 | h6
      · have h7 : m = 0 := h6
        rw [h7] at he
        exact h1 (htinj (he.symm.trans (hφ01 c)))
      · have h7 : m = 1 := h6
        rw [h7] at he
        exact h2 (htinj (he.symm.trans (hφ11 c)))
  exact exists_top_split (IsCircuit.isOArc_U h.nkCirc) h.Rsub hRp hRd h.tmem hlr hτ hP hoff

private theorem cuff_tree_union_is_forest
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    [T2Space T]
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    [ConnectedSpace S]
    (hman : ∀ (x : T), IsManifoldPoint x)
    (hj : Continuous j)
    (hji : Injective j)
    (hCD : ∀ z ∈ C, j z ∈ D)
    (Tdr : Fin ks → Drawing S)
    (hT4 : ∀ (i : Fin ks), (Tdr i).U = (R i).U ∪ (walkDrawing G (Q i)).U)
    (hRT : ∀ (i : Fin ks), (R i).IsSubdrawing (Tdr i))
    (hWp : ∀ (i : Fin ks), (walkDrawing G (Q i)).IsPathBetween (x i) (t i))
    (htW : ∀ (i : Fin ks), t i ∈ (walkDrawing G (Q i)).V)
    (i : Fin ks) :
    IsGraphForest (Tdr i).toGraph := by
  obtain ⟨a', b', hp⟩ := h.Rpath i
  refine isForest_of_two_paths hp (hWp i) (hRT i) (hT4 i) (h.tmem i) ((walkDrawing G
    (Q i)).V_subset_U (htW i)) ?_
  rintro z ⟨hz, hz'⟩
  rcases h.Q_inside hman hj hji hCD i z hz' with h1 | h1
  · exact h1
  · exact absurd (h.bdE ▸ mem_image_of_mem j ((h.Rsub i).U_subset hz)) h1.2

private theorem cuff_tree_vertices_reach_collar_vertex
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (Tdr : Fin ks → Drawing S)
    (hT2 : ∀ (i : Fin ks), (Tdr i).V = (R i).V ∪ (walkDrawing G (Q i)).V)
    (hRT : ∀ (i : Fin ks), (R i).IsSubdrawing (Tdr i))
    (hWT : ∀ (i : Fin ks), (walkDrawing G (Q i)).IsSubdrawing (Tdr i))
    (hWp : ∀ (i : Fin ks), (walkDrawing G (Q i)).IsPathBetween (x i) (t i))
    (htW : ∀ (i : Fin ks), t i ∈ (walkDrawing G (Q i)).V)
    (i : Fin ks)
    (y : S)
    (hy : y ∈ (Tdr i).V) :
    Nonempty (GraphWalk (Tdr i).toGraph y (t i)) := by
  rw [hT2 i] at hy
  rcases hy with hy | hy
  · obtain ⟨a', b', hp⟩ := h.Rpath i
    obtain ⟨W⟩ := exists_walk_of_isPathBetween hp hy (h.tmem i)
    obtain ⟨W', -, -⟩ := (hRT i).exists_walk_up W
    exact ⟨W'⟩
  · obtain ⟨W⟩ := exists_walk_of_isPathBetween (hWp i) hy (htW i)
    obtain ⟨W', -, -⟩ := (hWT i).exists_walk_up W
    exact ⟨W'⟩

private theorem cuff_tree_points_have_box_coordinates
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    [T2Space T]
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D)
    (hG : G.IsProper)
    (hman : ∀ (x : T), IsManifoldPoint x)
    (hji : Injective j)
    (F : Set (CellRec T (Fin ks)))
    (Φ : CellRec T (Fin ks) → ℝ × ℝ → T)
    (Sd : Fin ks → ℝ → T)
    (μ : CellRec T (Fin ks) → ℝ → T)
    (hfam : IsCellFamily D E₀ (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) univ F)
    (hb : IsCuffBoxes D E₀ Δ' (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) F Φ Sd μ)
    (φ : ↥F → ℝ × ℝ → S)
    (hφ : ∀ (c : ↥F), ∀ p ∈ cuffBox, j (φ c p) = Φ (↑c) p)
    (hbx : ∀ {m w : ℝ}, m ∈ Icc 0 1 → w ∈ Icc 0 2 → (m, w) ∈ cuffBox)
    (h0I : (0 : ℝ) ∈ Icc 0 1)
    (h1I : (1 : ℝ) ∈ Icc 0 1)
    (h12 : (1 : ℝ) ∈ Icc 0 2)
    (f : ↥F → ℝ → ℝ)
    (hfge : ∀ (c : ↥F) (m : ℝ), 1 ≤ f c m)
    (hused : ∀ (i : Fin ks), ∃ (c : ↥F) (e : ℝ), (e = 0 ∨ e = 1) ∧ (∀ w ∈ Icc 0 2, j (φ c (e, w))
      = Sd i w) ∧
      (e = 0 → c.1.i = i) ∧ (e = 1 → c.1.i' = i))
    (hφside : ∀ (i : Fin ks) (c : ↥F) (e : ℝ), (∀ w ∈ Icc 0 2, j (φ c (e, w)) = Sd i w) → φ c (e,
      0) = x i ∧ φ c (e, 1) = t i)
    (g : ↥F → ℝ → ℝ)
    (hd : ∀ (c : ↥F), IsCollapseData (g c) (f c))
    (hg3 : ∀ (c : ↥F), ∀ m ∈ Icc 0 1, ∀ (i : Fin ks), φ c (m, 1) ∈ (R i).U → φ c (g c m, 0) = x i)
    (Tdr : Fin ks → Drawing S)
    (hT4 : ∀ (i : Fin ks), (Tdr i).U = (R i).U ∪ (walkDrawing G (Q i)).U)
    (i : Fin ks)
    (a' : S)
    (ha' : a' ∈ (Tdr i).U) :
    ∃ c, ∃ p ∈ cuffBox, φ c p = a' ∧ p.2 ≤ f c p.1 ∧ φ c (g c p.1, 0) = x i := by
  rw [hT4 i] at ha'
  rcases ha' with ha' | ha'
  · have hb1 : j a' ∈ discBd E₀ := h.bdE ▸ mem_image_of_mem j ((h.Rsub i).U_subset ha')
    obtain ⟨c, hcF, hab'⟩ := hfam.topCover _ hb1
    obtain ⟨m', hm', he⟩ := (hb.param c hcF).exists_of_mem hab'
    have hbm := hbx hm' h12
    have he' : φ ⟨c, hcF⟩ (m', 1) = a' := hji (by rw [hφ ⟨c, hcF⟩ _ hbm, hb.top c hcF m' hm', he])
    exact ⟨⟨c, hcF⟩, (m', 1), hbm, he', hfge _ _, hg3 ⟨c, hcF⟩ m' hm' i (he' ▸ ha')⟩
  · obtain ⟨w, hw, he⟩ := (h.crossLine hG hC hman hc i) |> fun hl => hb.sideOf i (j a')
      (mem_image_of_mem j ha')
    obtain ⟨c, e, he', hs, h3, h4⟩ := hused i
    have hw2 : w ∈ Icc (0 : ℝ) 2 := ⟨hw.1, by linarith [hw.2]⟩
    have heI : e ∈ Icc (0 : ℝ) 1 := by
      rcases he' with rfl | rfl
      · exact h0I
      · exact h1I
    have hge : g c e = e := by
      rcases he' with rfl | rfl
      · exact (hd c).g0
      · exact (hd c).g1
    refine ⟨c, (e, w), hbx heI hw2, hji (by rw [hs w hw2, he]), hw.2.trans (hfge _ _), ?_⟩
    change φ c (g c e, 0) = x i
    rw [hge]
    exact (hφside i c e hs).1

private theorem boundary_in_collar_maps_into_cap
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D)
    (hbT : bd T = j '' (bd S \ C))
    (hji : Injective j)
    (hCD : ∀ z ∈ C, j z ∈ D)
    (z : S)
    (hz : j z ∈ Δ') :
    z ∈ bd S ↔ j z ∈ D := by
  constructor
  · intro hb1
    by_cases hzC : z ∈ C
    · exact hCD z hzC
    · exfalso
      have h1 : j z ∈ bd T := hbT ▸ mem_image_of_mem j ⟨hb1, hzC⟩
      exact disjoint_left.mp h.offO (h.ΔO hz).1 h1
  · intro hzD
    have hzr : j z ∈ range j ∩ D := ⟨mem_range_self z, hzD⟩
    rw [hc.inter_eq] at hzr
    obtain ⟨z', hz', he⟩ := hzr
    exact cuff_subset_bd hC (hji he ▸ hz')

private theorem box_bottom_lies_on_cuff
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {ks : ℕ}
    {E₀ : Set T}
    {Δ' : Set T}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    (hc : IsCappedCuff C T j D)
    (hji : Injective j)
    (F : Set (CellRec T (Fin ks)))
    (Φ : CellRec T (Fin ks) → ℝ × ℝ → T)
    (Sd : Fin ks → ℝ → T)
    (μ : CellRec T (Fin ks) → ℝ → T)
    (hb : IsCuffBoxes D E₀ Δ' (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) F Φ Sd μ)
    (φ : ↥F → ℝ × ℝ → S)
    (hφ : ∀ (c : ↥F), ∀ p ∈ cuffBox, j (φ c p) = Φ (↑c) p)
    (c : ↥F)
    (p : ℝ × ℝ)
    (hp : p ∈ cuffBox)
    (h0 : p.2 = 0) :
    φ c p ∈ C := by
  have h1 : j (φ c p) ∈ range j ∩ D := ⟨mem_range_self _, by
    rw [hφ c p hp]
    exact (hb.inD c.1 c.2 p hp).mpr h0⟩
  rw [hc.inter_eq] at h1
  obtain ⟨z', hz', he⟩ := h1
  exact hji he ▸ hz'

private theorem cuff_collar_inner_arc_obstruction
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (hc : IsCappedCuff C T j D)
    (hji : Injective j)
    (F : Set (CellRec T (Fin ks)))
    (Φ : CellRec T (Fin ks) → ℝ × ℝ → T)
    (Sd : Fin ks → ℝ → T)
    (μ : CellRec T (Fin ks) → ℝ → T)
    (hb : IsCuffBoxes D E₀ Δ' (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) F Φ Sd μ)
    (φ : ↥F → ℝ × ℝ → S)
    (hφ : ∀ (c : ↥F), ∀ p ∈ cuffBox, j (φ c p) = Φ (↑c) p)
    (f : ↥F → ℝ → ℝ)
    (hfge : ∀ (c : ↥F) (m : ℝ), 1 ≤ f c m)
    (B : Set S)
    (hO : IsOArc B)
    (hn : G.IsNormal B)
    (hcard : (G.V ∩ B).ncard ≤ v)
    (hs : SurroundsCuff B C)
    (hbelow : ∀ z ∈ B, ¬IsBelowGraph φ f z) :
    False := by
  refine h.inner B hO hn hcard hs (disjoint_left.mpr fun z hz hzB => ?_)
  have hzE := hz
  have h1 : j z ∈ Δ' := (h.EΔ hz.1).1
  obtain ⟨c, hcF, p, hp, he⟩ := hb.cover (j z) ⟨h1, not_mem_discInt_cap hc z⟩
  have hz' : φ ⟨c, hcF⟩ p = z := hji (by rw [hφ ⟨c, hcF⟩ p hp, he])
  refine hbelow z hzB ⟨⟨c, hcF⟩, p, hp, hz', ?_⟩
  have h2 : p.2 ≤ 1 := (hb.inE c hcF p hp).mp (he ▸ hzE.1)
  have h3 : p.2 ≠ 1 := fun h4 => hzE.2 (he ▸ (hb.onBd c hcF p hp).mpr h4)
  exact lt_of_lt_of_le (lt_of_le_of_ne h2 h3) (hfge _ _)

private theorem assemble_cuff_collar
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    {G : Drawing S}
    {C : Set S}
    {j : S → T}
    {D : Set T}
    {r : ℕ}
    {v : ℕ}
    {ks : ℕ}
    {m : ℕ}
    {Y : Set T}
    {E₀ : Set T}
    {Δ' : Set T}
    {Do : Set T}
    {Nk : Drawing S}
    {Bo : Drawing S}
    {R : Fin ks → Drawing S}
    {x : Fin ks → S}
    {t : Fin ks → S}
    {Q : (i : Fin ks) → GraphWalk G.toGraph (x i) (t i)}
    {L : Fin m → Drawing S}
    {El : Fin m → Set T}
    [T2Space T]
    (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
    (hS : IsSurface S)
    [ConnectedSpace S]
    (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D)
    (hns : ¬IsSphere T)
    (hT : IsSurface T)
    (hj : Continuous j)
    (hji : Injective j)
    (hCD : ∀ z ∈ C, j z ∈ D)
    (F : Set (CellRec T (Fin ks)))
    (Φ : CellRec T (Fin ks) → ℝ × ℝ → T)
    (Sd : Fin ks → ℝ → T)
    (μ : CellRec T (Fin ks) → ℝ → T)
    (hb : IsCuffBoxes D E₀ Δ' (fun k => j '' (walkDrawing G (Q k)).U) (fun k => j (x k)) (fun k =>
      j (t k)) F Φ Sd μ)
    (φ : ↥F → ℝ × ℝ → S)
    (hφ : ∀ (c : ↥F), ∀ p ∈ cuffBox, j (φ c p) = Φ (↑c) p)
    (hbs : IsBoxSystem φ)
    (hφ00 : ∀ (c : ↥F), φ c (0, 0) = x c.1.i)
    (hφ10 : ∀ (c : ↥F), φ c (1, 0) = x c.1.i')
    (f : ↥F → ℝ → ℝ)
    (hF1 : ∀ (c : ↥F), ∀ p ∈ cuffBox, φ c p ∈ G.U → 1 < p.2 → f c p.1 < p.2)
    (hF2 : ∀ (c : ↥F), ∀ p ∈ cuffBox, p.2 = f c p.1 → φ c p ∈ G.U → p.2 = 1 ∧ φ c p ∈ G.V)
    (hused : ∀ (i : Fin ks), ∃ (c : ↥F) (e : ℝ), (e = 0 ∨ e = 1) ∧ (∀ w ∈ Icc 0 2, j (φ c (e, w))
      = Sd i w) ∧
      (e = 0 → c.1.i = i) ∧ (e = 1 → c.1.i' = i))
    (hφside : ∀ (i : Fin ks) (c : ↥F) (e : ℝ), (∀ w ∈ Icc 0 2, j (φ c (e, w)) = Sd i w) → φ c (e,
      0) = x i ∧ φ c (e, 1) = t i)
    (a : ↥F → ℝ)
    (b : ↥F → ℝ)
    (hab : ∀ (c : ↥F), a c < b c) :
    let g : ↥F → ℝ → ℝ := fun c => clampRamp (a c) (b c)
    (∀ (c : ↥F), IsCollapseData (g c) (f c)) →
    ∀ (Tdr : Fin ks → Drawing S),
    (∀ (i : Fin ks), (Tdr i).IsSubdrawing G) →
    (∀ (i : Fin ks), (Tdr i).V = (R i).V ∪ (walkDrawing G (Q i)).V) →
    (∀ (i : Fin ks), (Tdr i).U = (R i).U ∪ (walkDrawing G (Q i)).U) →
    (∀ (i : Fin ks), x i ∈ (walkDrawing G (Q i)).V) →
    (∀ (i : Fin ks), IsGraphForest (Tdr i).toGraph) →
    (∀ (i : Fin ks), ∀ y ∈ (Tdr i).V, Nonempty (GraphWalk (Tdr i).toGraph y (t i))) →
    ∀ (Tr : S → Drawing S),
    (∀ (i : Fin ks), Tr (x i) = Tdr i) →
    (∀ (i : Fin ks), ∀ a' ∈ (Tdr i).U, ∃ c, ∃ p ∈ cuffBox, φ c p = a' ∧ p.2 ≤ f c p.1 ∧ φ
      c (g c p.1, 0) = x i) →
    (D ⊆ Δ') →
    (D ⊆ Do) →
    (∀ z ∈ C, z ∈ j ⁻¹' Do) →
    (j ⁻¹' discBd Do = Bo.U) →
    (∀ (c : ↥F), ∀ p ∈ cuffBox, φ c p ∈ bd S ↔ p.2 = 0) →
    (∀ (c : ↥F), ∀ p ∈ cuffBox, p.2 = 0 → φ c p ∈ C) →
    (∀ (c : ↥F), ∀ p ∈ cuffBox, p.2 = f c p.1 → φ c p ∈ G.V → φ c (g c p.1, 0) ∈ G.V ∩ C ∧
      φ c p ∈ (Tr (φ c (g c p.1, 0))).V) →
    (∀ (B : Set S), IsOArc B → G.IsNormal B → (G.V ∩ B).ncard ≤ v → SurroundsCuff B C →
      (∀ z ∈ B, ¬IsBelowGraph φ f z) → False) →
    IsCuffCollar G C r v (j ⁻¹' Do) Bo.U (j ⁻¹' (Do \ E₀)) (j ⁻¹' (Do \ Δ')) φ g f Tr := by
  intro g hd Tdr hT1 hT2 hT4 hxW hforest hreach Tr hTr hrep hDΔ hDO hCMo hpreO hbottom hbottomC
    hgV hinner
  exact
    { box := hbs
      data := hd
      bottom := hbottom
      bottomC := hbottomC
      allBottom := fun z hz => by
        obtain ⟨c, hcF, p, hp, he⟩ := hb.cover (j z) ⟨hDΔ (hCD z hz), not_mem_discInt_cap hc z⟩
        have h2 : p.2 = 0 := (hb.inD c hcF p hp).mp (he ▸ hCD z hz)
        have hpeq : (p.1, (0 : ℝ)) = p := Prod.ext rfl h2.symm
        refine mem_iUnion.mpr ⟨⟨c, hcF⟩, p.1, hp.1, hji ?_⟩
        change j (φ ⟨c, hcF⟩ (p.1, 0)) = j z
        rw [hpeq, hφ ⟨c, hcF⟩ p hp, he]
      graphU := fun c p hp he hU => (hF2 c p hp he hU).2
      graphV := hgV
      corner := fun y hy => by
        obtain ⟨i, rfl⟩ := h.x_surj y hy
        obtain ⟨c, e, he', hs, -, -⟩ := hused i
        exact ⟨c, e, he', (hφside i c e hs).1, by rw [(hφside i c e hs).2]; exact h.tV i⟩
      cornerV := fun c e he => by
        rcases he with rfl | rfl
        · rw [hφ00]
          exact h.xmem _
        · rw [hφ10]
          exact h.xmem _
      gstrict := fun c m _ m' _ he h0 h1 => clampRamp_strict (hab c) he h0 h1
      tree := fun y hy => by
        obtain ⟨i, rfl⟩ := h.x_surj y hy
        rw [hTr]
        refine ⟨hT1 i, hforest i, hT2 i ▸ .inr (hxW i), hrep i, fun a' ha' b' hb'' => ?_⟩
        obtain ⟨W₁⟩ := hreach i a' ha'
        obtain ⟨W₂⟩ := hreach i b' hb''
        exact ⟨W₁.append W₂.reverse⟩
      closedMo := h.discO.isClosed.preimage hj
      openMo := by
        have heq : j ⁻¹' Do \ Bo.U = j ⁻¹' discInt Do := by
          rw [← hpreO]
          rfl
        rw [heq]
        exact (h.discO.isOpen_discInt hT.2.2).preimage hj
      cMo := hCMo
      inMo := fun c p hp => by
        have h1 := h.ΔO (hb.mapsΔ c.1 c.2 hp)
        rw [← hpreO]
        refine ⟨?_, ?_⟩
        · change j (φ c p) ∈ Do
          rw [hφ c p hp]
          exact h1.1
        · change j (φ c p) ∉ discBd Do
          rw [hφ c p hp]
          exact h1.2
      circ := ⟨Bo, h.boSub, h.boCirc, rfl⟩
      surrounds := hpreO ▸ surrounds_of_disc hS hC hc hns h.discO hDO
      planarMo := isPlanarInCappedCuff_of_cap hS hc ⟨Do, h.discO, image_preimage_subset _ _⟩
      reach := fun y hy hV => h.reach y (mem_V_of_subdrawing h.boSub hy hV)
      inner := hinner
      mo₂ := preimage_mono sdiff_subset
      mo₃ := preimage_mono sdiff_subset
      above₂ := fun z hz hU c p hp he => by
        have h1 : ¬ p.2 ≤ 1 := fun h2 => hz.2 (by
          rw [← he, hφ c p hp]
          exact (hb.inE c.1 c.2 p hp).mpr h2)
        exact hF1 c p hp (he ▸ hU) (not_le.mp h1)
      off₃ := fun z hz c => by
        rintro ⟨p, hp, rfl⟩
        refine hz.2 ?_
        rw [hφ c p hp]
        exact hb.mapsΔ c.1 c.2 hp
      touch := fun ρ A B hρ _ htr hnorm hcount hab' hid hO hne => h.touch hS hc hns hρ
        (fun i a' ha' => htr (x i) (h.xmem i) a' (by
          rw [hTr, hT4 i]
          exact .inl ha')) hnorm hcount (fun z h1 h2 h3 => hab' z ⟨h1,
            h2⟩ h3) (fun z h1 h2 h3 => hid z ⟨h1, h2⟩ h3) h.x_surj hO hne }

/-- **The collar of a cuff.** -/
theorem IsCuffCore.exists_collar [T2Space T] (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L
  El) (hS : IsSurface S) [ConnectedSpace S] (hC : C ∈ cuffs S) (hc : IsCappedCuff C T j D)
    (hbT : bd T = j '' (bd S \ C)) (hG : G.IsProper) (hns : ¬ IsSphere T) :
    ∃ (ι : Type u) (_ : Finite ι) (Mo AC Mo₂ Mo₃ : Set S) (φ : ι → ℝ × ℝ → S) (g f : ι → ℝ → ℝ)
      (Tr : S → Drawing S), IsCuffCollar G C r v Mo AC Mo₂ Mo₃ φ g f Tr := by
  classical
  have hT := hc.isSurface
  have : CompactSpace S := hS.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have : Nonempty S := ConnectedSpace.toNonempty
  have hman := hT.2.2
  have hj := hc.isEmbedding.continuous
  have hji := hc.isEmbedding.injective
  have hCD : ∀ z ∈ C, j z ∈ D := fun z hz => Surface.discBd_subset D (hc.discBd_eq ▸
    mem_image_of_mem j hz)
  have hDE : D ⊆ E₀ \ discBd E₀ := h.DinE
  have hk := h.ks2
  obtain ⟨F, Φ, Sd, μ, hfam, hb⟩ :=
    exists_cuff_boxes hman hc.isClosedDisc h.discE h.discΔ hDE h.EΔ (h.crossLine hG hC hman hc)
      (fun _ _ hne => h.lines_disjoint hji hne)
      (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩) (by simp)
  have hFf : Finite F := hfam.finite.to_subtype
  have hrange : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ range j := fun c hcF p hp => by
    exact cuff_box_lies_in_uncapped_surface (S := S) (T := T) (G := G) (C := C) (j := j) (D := D)
      (ks := ks) (E₀ := E₀) (Δ' := Δ') (x := x) (t := t) (Q := Q) hc F Φ Sd μ hfam hb c hcF p hp
  let φ : F → ℝ × ℝ → S := fun c p => invFun j (Φ c.1 p)
  have hφ : ∀ c p, p ∈ cuffBox → j (φ c p) = Φ c.1 p := fun c p hp => invFun_eq
    (hrange c.1 c.2 p hp)
  have hbs : IsBoxSystem φ := isBoxSystem_of_lift hc hb hman h.discΔ hφ
  have hbx : ∀ {m w : ℝ}, m ∈ Icc (0 : ℝ) 1 → w ∈ Icc (0 : ℝ) 2 → (m, w) ∈ cuffBox := fun hm hw
    => ⟨hm, hw⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h02 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have h12 : (1 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨zero_le_one, by norm_num⟩
  have hL : ∀ (c : F), ∀ w ∈ Icc (0 : ℝ) 2, j (φ c (0, w)) = Sd c.1.i w := fun c w hw => by
    rw [hφ c _ (hbx h0I hw)]
    exact hb.left c.1 c.2 w hw
  have hRt : ∀ (c : F), ∀ w ∈ Icc (0 : ℝ) 2, j (φ c (1, w)) = Sd c.1.i' w := fun c w hw => by
    rw [hφ c _ (hbx h1I hw)]
    exact hb.right c.1 c.2 w hw
  have hφ00 : ∀ c : F, φ c (0, 0) = x c.1.i := fun c => hji (by rw [hL c 0 h02, hb.sideZero])
  have hφ01 : ∀ c : F, φ c (0, 1) = t c.1.i := fun c => hji (by rw [hL c 1 h12, hb.sideOne])
  have hφ10 : ∀ c : F, φ c (1, 0) = x c.1.i' := fun c => hji (by rw [hRt c 0 h02, hb.sideZero])
  have hφ11 : ∀ c : F, φ c (1, 1) = t c.1.i' := fun c => hji (by rw [hRt c 1 h12, hb.sideOne])
  -- the heights
  set Go := withoutEdges G Nk with hGo
  let Z : F → Set (ℝ × ℝ) := fun c => {p | p ∈ cuffBox ∧ 1 ≤ p.2 ∧ φ c p ∈ Go.U}
  have hZcl : ∀ c, IsClosed (Z c) := fun c => by
    exact cuff_box_height_set_closed (S := S) (T := T) (ks := ks) F φ hbs Go c
  have hZ0 : ∀ c, ((0 : ℝ), (1 : ℝ)) ∈ Z c := fun c => ⟨hbx h0I h12, le_rfl, by
    rw [hφ01 c]
    exact Go.V_subset_U (by rw [hGo, withoutEdges_V]; exact h.tV _)⟩
  have hZ1 : ∀ c, ((1 : ℝ), (1 : ℝ)) ∈ Z c := fun c => ⟨hbx h1I h12, le_rfl, by
    rw [hφ11 c]
    exact Go.V_subset_U (by rw [hGo, withoutEdges_V]; exact h.tV _)⟩
  let f : F → ℝ → ℝ := fun c => topHeight (Z c)
  have hNk : ∀ c p, p ∈ cuffBox → (φ c p ∈ Nk.U ↔ p.2 = 1) := fun c p hp => by
    rw [← hb.onBd c.1 c.2 p hp, ← hφ c p hp, h.bdE]
    exact hji.mem_set_image.symm
  have hF1 : ∀ c p, p ∈ cuffBox → φ c p ∈ G.U → 1 < p.2 → f c p.1 < p.2 := fun c p hp hU hlt => by
    rcases mem_withoutEdges_or (N := Nk) hU with h1 | h1
    · have h2 := topHeight_le (Z := Z c) (m := p.1) (w := p.2) ⟨hp, hlt.le, h1⟩ hlt.le
      change topHeight (Z c) p.1 < p.2
      linarith
    · exact absurd ((hNk c p hp).mp h1) hlt.ne'
  have hfge : ∀ c m, 1 ≤ f c m := fun c m => (topHeight_bounds _ m).1
  have hF2 : ∀ c p, p ∈ cuffBox → p.2 = f c p.1 → φ c p ∈ G.U → p.2 = 1 ∧ φ c p ∈ G.V
    := fun c p hp he hU => by
    exact cuff_box_top_graph_points_are_vertices (S := S) (T := T) (G := G) (C := C) (j := j) (D
      := D) (r := r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk :=
      Nk) (Bo := Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h F φ   hZcl hZ0
      hNk hF1 hfge c p hp he hU
  -- the ramps
  have hRp : ∀ i, IsPreconnected (R i).U := fun i => by
    obtain ⟨a, b, hp⟩ := h.Rpath i
    exact isPreconnected_of_isPathBetween hp
  have hRd : ∀ i i', i ≠ i' → Disjoint (R i).U (R i').U := fun i i' hne => disjoint_U_of_disjoint_V
    (h.Rsub i) (h.Rsub i') (h.Rdis i i' hne)
  have htinj : Injective t := fun i i' he => by
    by_contra hne
    exact disjoint_left.mp (h.Rdis i i' hne) (h.tmem i) (he ▸ h.tmem i')
  have hused : ∀ i, ∃ (c : F) (e : ℝ), (e = 0 ∨ e = 1) ∧ (∀ w ∈ Icc (0 : ℝ) 2, j (φ c (e, w))
    = Sd i w) ∧ (e = 0 → c.1.i = i) ∧ (e = 1 → c.1.i' = i) := fun i => by
    exact every_radial_line_is_a_box_side (S := S) (T := T) (G := G) (j := j) (D := D) (ks := ks)
      (E₀ := E₀) (x := x) (t := t) (Q := Q) F Sd hfam φ hL hRt i
  have hφside : ∀ (i) (c : F) (e : ℝ), (∀ w ∈ Icc (0 : ℝ) 2, j (φ c (e, w)) = Sd i w) → φ c (e, 0)
    = x i ∧ φ c (e, 1) = t i := fun i c e hs => ⟨hji (by rw [hs 0 h02, hb.sideZero]), hji
      (by rw [hs 1 h12, hb.sideOne])⟩
  have hsplit : ∀ c : F, ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ ∀ m ∈ Icc (0 : ℝ) 1, ∀ i, φ c (m, 1) ∈
    (R i).U → (i = c.1.i ∧ m ≤ a) ∨ (i = c.1.i' ∧ b ≤ m) := fun c => by
    exact box_top_orders_radial_trees (S := S) (T := T) (G := G) (C := C) (j := j) (D := D) (r :=
      r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk := Nk) (Bo :=
      Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h F Sd φ hbs hbx h0I h1I h12
      hφ01 hφ11 hNk hRp hRd htinj hused hφside c
  choose a b ha hab hb' hsp using hsplit
  let g : F → ℝ → ℝ := fun c => clampRamp (a c) (b c)
  have hd : ∀ c, IsCollapseData (g c) (f c) := fun c => isCollapseData_ramp (ha c) (hab c) (hb' c)
    (hZ0 c) (hZ1 c)
  have hg3 : ∀ c, ∀ m ∈ Icc (0 : ℝ) 1, ∀ i, φ c (m, 1) ∈ (R i).U → φ c (g c m, 0) = x i
    := fun c m hm i hi => by
    rcases hsp c m hm i hi with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
    · rw [show g c m = 0 from clampRamp_low (hab c) h1]
      exact hφ00 c
    · rw [show g c m = 1 from clampRamp_high (hab c) h1]
      exact hφ10 c
  -- the trees
  have hRG : ∀ i, (R i).IsSubdrawing G := fun i => (h.Rsub i).trans h.nkSub
  have hWs := fun i => walkDrawing_isSubdrawing G (Q i)
  have hunion := fun i => exists_union_drawing (hRG i) (hWs i)
  choose Tdr hT1 hT2 hT3 hT4 using hunion
  have hRT : ∀ i, (R i).IsSubdrawing (Tdr i) := fun i => ⟨hT2 i ▸ subset_union_left, hT3 i ▸
    subset_union_left⟩
  have hWT : ∀ i, (walkDrawing G (Q i)).IsSubdrawing (Tdr i) := fun i
    => ⟨hT2 i ▸ subset_union_right, hT3 i ▸ subset_union_right⟩
  have hWp := fun i => walkDrawing_isPathBetween G (h.Qsimple i)
  have htW : ∀ i, t i ∈ (walkDrawing G (Q i)).V := fun i => by
    rw [walkDrawing_V]
    exact (Q i).end_mem_support
  have hxW : ∀ i, x i ∈ (walkDrawing G (Q i)).V := fun i => by
    rw [walkDrawing_V]
    exact (Q i).start_mem_support
  have hforest : ∀ i, IsGraphForest (Tdr i).toGraph := fun i => by
    exact cuff_tree_union_is_forest (S := S) (T := T) (G := G) (C := C) (j := j) (D := D) (r := r)
      (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk := Nk) (Bo := Bo)
      (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h hman hj hji hCD Tdr hT4 hRT hWp
      htW i
  have hreach : ∀ i, ∀ y ∈ (Tdr i).V, Nonempty (GraphWalk (Tdr i).toGraph y (t i)) := fun i y hy
    => by
    exact cuff_tree_vertices_reach_collar_vertex (S := S) (T := T) (G := G) (C := C) (j := j) (D
      := D) (r := r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk :=
      Nk) (Bo := Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h Tdr hT2 hRT hWT hWp
      htW i y hy
  let Tr : S → Drawing S := fun y => if hy : ∃ i, x i = y then Tdr hy.choose else G
  have hTr : ∀ i, Tr (x i) = Tdr i := fun i => by
    have hy : ∃ i', x i' = x i := ⟨i, rfl⟩
    have h1 : hy.choose = i := h.x_injective hy.choose_spec
    change (if hy : ∃ i', x i' = x i then Tdr hy.choose else G) = Tdr i
    rw [dite_eq_left hy, h1]
  have hrep : ∀ i, ∀ a' ∈ (Tdr i).U, ∃ c p, p ∈ cuffBox ∧ φ c p = a' ∧ p.2 ≤ f c p.1 ∧ φ c
    (g c p.1, 0) = x i := fun i a' ha' => by
    exact cuff_tree_points_have_box_coordinates (S := S) (T := T) (G := G) (C := C) (j := j) (D :=
      D) (r := r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk :=
      Nk) (Bo := Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h hC hc hG hman hji F
      Φ Sd μ hfam hb φ hφ hbx h0I h1I h12 f hfge hused hφside g hd hg3 Tdr hT4 i a' ha'
  have hbdΔ : ∀ z, j z ∈ Δ' → (z ∈ bd S ↔ j z ∈ D) := fun z hz => by
    exact boundary_in_collar_maps_into_cap (S := S) (T := T) (G := G) (C := C) (j := j) (D := D)
      (r := r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk := Nk)
      (Bo := Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h hC hc hbT hji hCD z hz
  have hDΔ : D ⊆ Δ' := hDE.trans (sdiff_subset.trans (h.EΔ.trans sdiff_subset))
  have hDO : D ⊆ Do := hDΔ.trans (h.ΔO.trans sdiff_subset)
  have hCMo : ∀ z ∈ C, z ∈ j ⁻¹' Do := fun z hz => hDO (hCD z hz)
  have hpreO : j ⁻¹' discBd Do = Bo.U := by
    rw [h.bdO]
    exact preimage_image_eq _ hji
  have hbottom : ∀ c p, p ∈ cuffBox → (φ c p ∈ bd S ↔ p.2 = 0) := fun c p hp => by
    have h1 : j (φ c p) ∈ Δ' := by
      rw [hφ c p hp]
      exact hb.mapsΔ c.1 c.2 hp
    rw [hbdΔ _ h1, hφ c p hp]
    exact hb.inD c.1 c.2 p hp
  have hbottomC : ∀ c p, p ∈ cuffBox → p.2 = 0 → φ c p ∈ C := fun c p hp h0 => by
    exact box_bottom_lies_on_cuff (S := S) (T := T) (G := G) (C := C) (j := j) (D := D) (ks := ks)
      (E₀ := E₀) (Δ' := Δ') (x := x) (t := t) (Q := Q) hc hji F Φ Sd μ hb φ hφ c p hp h0
  have hgV : ∀ c p, p ∈ cuffBox → p.2 = f c p.1 → φ c p ∈ G.V → φ c (g c p.1, 0) ∈ G.V ∩ C
    ∧ φ c p ∈ (Tr (φ c (g c p.1, 0))).V := fun c p hp he hV => by
    obtain ⟨h1, -⟩ := hF2 c p hp he (G.V_subset_U hV)
    have hp1 : (p.1, (1 : ℝ)) = p := Prod.ext rfl h1.symm
    have hN := mem_V_of_subdrawing h.nkSub ((hNk c p hp).mpr h1) hV
    obtain ⟨i, hi⟩ := h.Rcov _ hN
    have h3 := hg3 c p.1 hp.1 i (by rw [hp1]; exact (R i).V_subset_U hi)
    rw [h3, hTr, hT2 i]
    exact ⟨h.xmem i, .inl hi⟩
  have hinner : ∀ B : Set S, IsOArc B → G.IsNormal B → (G.V ∩ B).ncard ≤ v → SurroundsCuff B C →
    (∀ z ∈ B, ¬ IsBelowGraph φ f z) → False := fun B hO hn hcard hs hbelow => by
    exact cuff_collar_inner_arc_obstruction (S := S) (T := T) (G := G) (C := C) (j := j) (D := D)
      (r := r) (v := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk := Nk)
      (Bo := Bo) (R := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h hc hji F Φ Sd μ hb φ hφ
      f hfge B hO hn hcard hs hbelow
  have collar : IsCuffCollar G C r v (j ⁻¹' Do) Bo.U (j ⁻¹' (Do \ E₀)) (j ⁻¹' (Do \ Δ'))
      φ g f Tr := by
    exact assemble_cuff_collar (S := S) (T := T) (G := G) (C := C) (j := j) (D := D) (r := r) (v
      := v) (ks := ks) (m := m) (Y := Y) (E₀ := E₀) (Δ' := Δ') (Do := Do) (Nk := Nk) (Bo := Bo) (R
      := R) (x := x) (t := t) (Q := Q) (L := L) (El := El) h hS hC hc hns hT hj hji hCD F Φ Sd μ
      hb φ hφ hbs hφ00 hφ10 f hF1 hF2 hused hφside a b hab  hd Tdr hT1 hT2 hT4 hxW hforest hreach
      Tr hTr hrep hDΔ hDO hCMo hpreO hbottom hbottomC hgV hinner
  exact ⟨F, inferInstance, j ⁻¹' Do, Bo.U, j ⁻¹' (Do \ E₀), j ⁻¹' (Do \ Δ'), φ, g, f, Tr, collar⟩

end GraphMinor.GM07
