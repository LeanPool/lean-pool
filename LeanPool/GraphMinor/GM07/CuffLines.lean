/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffTree

/-!
# The lines of the paths `Q_i` and the boxes in `Σ`

Graph Minors VII, (5.9), page 235. The paths `Q_i` give lines in the capped surface that cut the
disc `E₀` in cells, so the box construction applies. We then bring the boxes back to `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

variable {G : Drawing S} {C : Set S} {j : S → T} {D : Set T} {r v ks m : ℕ} {Y E₀ Δ' Do : Set T}
  {Nk Bo : Drawing S} {R : Fin ks → Drawing S} {x t : Fin ks → S} {Q : ∀ i, GraphWalk G.toGraph
    (x i) (t i)} {L : Fin m → Drawing S} {El : Fin m → Set T}

theorem IsCuffCore.x_injective (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El) :
  Injective x := fun i i' he => by
  by_contra hne
  have h1 : x i ∈ {z | z ∈ (Q i).support} := (Q i).start_mem_support
  have h2 : x i ∈ {z | z ∈ (Q i').support} := by
    rw [he]
    exact (Q i').start_mem_support
  exact disjoint_left.mp (h.Qdis i i' hne) h1 h2

theorem IsCuffCore.x_surj (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El) : ∀ y ∈ G.V ∩
  C, ∃ i, x i = y := by
  have hsub : range x ⊆ G.V ∩ C := by
    rintro _ ⟨i, rfl⟩
    exact h.xmem i
  have hfin : (G.V ∩ C).Finite := G.finite_V.subset inter_subset_left
  have hcard : (G.V ∩ C).ncard ≤ (range x).ncard := by
    rw [← image_univ, h.x_injective.injOn.ncard_image, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    exact h.kcard.ge
  have heq := eq_of_subset_of_ncard_le hsub hcard hfin
  intro y hy
  rw [← heq] at hy
  exact hy

theorem IsCuffCore.tU (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
  (i : Fin ks) : t i ∈ Nk.U := (h.Rsub i).U_subset ((R i).V_subset_U (h.tmem i))

theorem IsCuffCore.tV (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
  (i : Fin ks) : t i ∈ G.V := h.nkSub.1 ((h.Rsub i).1 (h.tmem i))

/-- The points of `Q i` other than `t i` are strictly inside the disc of `N(C)`. -/
theorem IsCuffCore.Q_inside (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El) [T2Space S]
  [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) (hj : Continuous j) (hji : Injective j)
    (hCD : ∀ z ∈ C, j z ∈ D) (i : Fin ks) : ∀ z ∈ (walkDrawing G (Q i)).U, z = t i
      ∨ j z ∈ discInt E₀ := by
  have hbU : ∀ z, j z ∈ discBd E₀ ↔ z ∈ Nk.U := fun z => by
    rw [h.bdE]
    exact hji.mem_set_image
  have hd : Disjoint (discInt E₀) E₀ᶜ := disjoint_left.mpr fun z hz hz' => hz' hz.1
  refine walk_U_stays_side h.nkSub hj (h.discE.isOpen_discInt hman)
    h.discE.isClosed.isOpen_compl hd (fun z hz => ?_) (fun z hz hU => hz.2 ((hbU z).mpr hU)) (Q i)
      (h.Qsimple i) (fun z hz hne hzN => ?_) (h.DinE (hCD _ (h.xmem i).2))
  · by_cases h1 : j z ∈ E₀
    · exact .inl ⟨h1, fun h2 => hz ((hbU z).mp h2)⟩
    · exact .inr h1
  · rcases h.Qin i z hz with h1 | h1
    · exact hne h1
    · exact h1.2.2 ((hbU z).mpr (Nk.V_subset_U hzN))

/-- The line of `Q i` in the capped surface crosses from `D` to the boundary of `E₀`. -/
theorem IsCuffCore.crossLine (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El) [T2Space S]
  [T2Space T] (hG : G.IsProper) (hC : C ∈ cuffs S) (hman : ∀ x : T, IsManifoldPoint x)
    (hc : IsCappedCuff C T j D) (i : Fin ks) : IsCrossLine D E₀ (j '' (walkDrawing G (Q i)).U) (j
      (x i)) (j (t i)) := by
  have hj := hc.isEmbedding.continuous
  have hji := hc.isEmbedding.injective
  have hCD : ∀ z ∈ C, j z ∈ D := fun z hz => Surface.discBd_subset D (hc.discBd_eq ▸
    mem_image_of_mem j hz)
  have hin := h.Q_inside hman hj hji hCD i
  have hxint := h.DinE (hCD _ (h.xmem i).2)
  have htb : j (t i) ∈ discBd E₀ := h.bdE ▸ mem_image_of_mem j (h.tU i)
  have hne : x i ≠ t i := fun he => hxint.2 (he ▸ htb)
  have hpath := walkDrawing_isPathBetween G (h.Qsimple i)
  have hline := isLine_of_isPathBetween hpath hne
  have hxU : x i ∈ (walkDrawing G (Q i)).U := hline.left_mem
  have htU : t i ∈ (walkDrawing G (Q i)).U := hline.right_mem
  refine ⟨isLineWithEnds_image hline hj.continuousOn hji.injOn, ?_, ?_, ?_,
    Surface.discBd_subset D |> fun _ => hc.discBd_eq ▸ mem_image_of_mem j (h.xmem i).2⟩
  · rintro _ ⟨z, hz, rfl⟩
    rcases hin z hz with rfl | h1
    · exact Surface.discBd_subset _ htb
    · exact h1.1
  · refine subset_antisymm ?_ (singleton_subset_iff.mpr ⟨mem_image_of_mem j hxU,
      hCD _ (h.xmem i).2⟩)
    rintro _ ⟨⟨z, hz, rfl⟩, hzD⟩
    have hzr : j z ∈ range j ∩ D := ⟨mem_range_self z, hzD⟩
    rw [hc.inter_eq] at hzr
    obtain ⟨z', hz', he⟩ := hzr
    have hzC : z ∈ C := hji he ▸ hz'
    have hzG : z ∈ G.U := (walkDrawing_isSubdrawing G (Q i)).U_subset hz
    have hzV : z ∈ G.V := hG ⟨cuff_subset_bd hC hzC, hzG⟩
    obtain ⟨i', rfl⟩ := h.x_surj z ⟨hzV, hzC⟩
    have hs : x i' ∈ (Q i).support := by
      have h1 := mem_V_of_subdrawing (walkDrawing_isSubdrawing G (Q i)) hz hzV
      rwa [walkDrawing_V] at h1
    by_cases hii : i = i'
    · subst hii
      rfl
    · exact absurd (Q i').start_mem_support (disjoint_left.mp (h.Qdis i i' hii) hs)
  · refine subset_antisymm ?_ (singleton_subset_iff.mpr ⟨mem_image_of_mem j htU, htb⟩)
    rintro _ ⟨⟨z, hz, rfl⟩, hzb⟩
    rcases hin z hz with rfl | h1
    · rfl
    · exact absurd hzb h1.2

theorem IsCuffCore.lines_disjoint (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
  [T2Space S] (hji : Injective j) {i i' : Fin ks} (hne : i ≠ i') : Disjoint (j '' (walkDrawing G
    (Q i)).U) (j '' (walkDrawing G (Q i')).U) := by
  rw [disjoint_image_iff hji]
  refine disjoint_U_of_disjoint_V (walkDrawing_isSubdrawing G (Q i)) (walkDrawing_isSubdrawing G
    (Q i')) ?_
  rw [walkDrawing_V, walkDrawing_V]
  exact h.Qdis i i' hne

variable {ι : Type*} {F : Set (CellRec T ι)} {Φ : CellRec T ι → ℝ × ℝ → T} {Sd : ι → ℝ
  → T} {μ : CellRec T ι → ℝ → T} {q : ι → Set T} {tx tt : ι → T} {φ : F → ℝ × ℝ → S}

/-- The boxes, brought back to `Σ`, are a box system. -/
theorem isBoxSystem_of_lift (hc : IsCappedCuff C T j D) (hb : IsCuffBoxes D E₀ Δ' q tx tt F Φ Sd μ)
  (hman : ∀ x : T, IsManifoldPoint x) (hΔ : IsClosedDisc Δ') (hφ : ∀ c p, p ∈ cuffBox → j (φ c p)
    = Φ c.1 p) : IsBoxSystem φ := by
  have hj := hc.isEmbedding.continuous
  have hji := hc.isEmbedding.injective
  refine ⟨fun c => ?_, fun c p hp p' hp' he => hb.inj c.1 c.2 hp hp' ?_,
    fun c c' p p' hp hp' he => ?_, ?_⟩
  · rw [hc.isEmbedding.isInducing.continuousOn_iff]
    exact (hb.cont c.1 c.2).congr fun p hp => hφ c p hp
  · rw [← hφ c p hp, ← hφ c p' hp', he]
  · have he' : Φ c.1 p = Φ c'.1 p' := by rw [← hφ c p hp, ← hφ c' p' hp', he]
    rcases hb.meet c.1 c.2 c'.1 c'.2 p p' hp hp' he' with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · exact .inl ⟨Subtype.ext h1, h2⟩
    · refine .inr ⟨h1, h2, h3, fun w hw => hji ?_⟩
      rw [hφ c (p.1, w) ⟨hp.1, hw⟩, hφ c' (p'.1, w) ⟨hp'.1, hw⟩]
      exact h4 w hw
  · have heq : (⋃ c, φ c '' {p ∈ cuffBox | p.2 < 2}) = j ⁻¹' discInt Δ' := by
      ext z
      simp only [mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨c, p, ⟨hp, hlt⟩, rfl⟩
        rw [hφ c p hp]
        exact ⟨hb.mapsΔ c.1 c.2 hp, fun h1 => hlt.ne ((hb.bdΔ c.1 c.2 p hp).mp h1)⟩
      · intro hz
        obtain ⟨c, hcF, p, hp, he⟩ := hb.cover (j z) ⟨hz.1, not_mem_discInt_cap hc z⟩
        refine ⟨⟨c, hcF⟩, p, ⟨hp, lt_of_le_of_ne hp.2.2 fun h1 => hz.2 (he ▸
          (hb.bdΔ c hcF p hp).mpr h1)⟩, hji ?_⟩
        rw [hφ ⟨c, hcF⟩ p hp]
        exact he
    rw [heq]
    exact (hΔ.isOpen_discInt hman).preimage hj

end GraphMinor.GM07
