/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Perimeter
public import LeanPool.GraphMinor.GM11.RadialCorners
public import LeanPool.GraphMinor.GM11.RadialExists
public import Mathlib.Topology.Separation.Connected

/-!
# Each vertex in the closure of a region has a spoke to the centre of the region

`GM11.exists_spoke_at` says this for a radial drawing of a drawing of Graph Minors XI. A radial
drawing of a painting of XIX has no spokes in the discs of the edges of size 3, so it is not a
radial
drawing of `sk(Γ)`. We add the missing centres and extend to a radial drawing of `sk(Γ)`. A spoke of
that in a region of `Γ` can be added to the first drawing, so by maximality that drawing has a spoke
with the same ends.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface unitInterval

/-- A spoke can be added unless there is already one with the same ends. The proof follows
`GM11.exists_parallel_spoke`. -/
theorem exists_spoke_of_line {T : Type} [TopologicalSpace T] [T2Space T] {U V : Set T} {G : Drawing
  T}
    (hpre : IsPreRadial U V G)
    (hmax : ∀ G' : Drawing T, IsPreRadial U V G' → G.IsSubdrawing G' → G'.IsSubdrawing G)
    {r : Set T} (_hr : r ∈ componentsIn Uᶜ) {c x : T} (hcr : c ∈ r) (hc : c ∈ G.V) (hx : x ∈ V)
    {K : Set T} (hK : IsLineWithEnds K c x) (hcx : c ≠ x) (hKr : K \ {c, x} ⊆ r)
    (hKU : Disjoint (K \ {c, x}) G.U) (hrU : Disjoint r U) (hVU : V ⊆ U) :
    ∃ h ∈ G.E, closure h ∩ G.V = {x, c} := by
  classical
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hpre
  have hxV : x ∈ G.V := h₂ hx
  have hVsub : (GM11.lineDrawing hK hcx).V ⊆ G.V := by
    rintro y (rfl | rfl)
    · exact hc
    · exact hxV
  have hmeet : G.U ∩ (GM11.lineDrawing hK hcx).U ⊆ G.V ∩ (GM11.lineDrawing hK hcx).V := by
    rintro y ⟨hy, hyK⟩
    have : y ∈ ({c, x} : Set T) := by
      by_contra hn
      exact disjoint_left.mp hKU ⟨hyK, hn⟩ hy
    exact ⟨hVsub this, this⟩
  let G₂ : Drawing T := G.glue (GM11.lineDrawing hK hcx) hmeet
  have hGV : G₂.V = G.V := union_eq_left.mpr hVsub
  have hGE : G₂.E = G.E ∪ {K \ {c, x}} := by
    change (G.glue (GM11.lineDrawing hK hcx) hmeet).E = _
    rw [Drawing.glue_E, GM11.lineDrawing_E]
  have hKcl : closure (K \ {c, x}) = K := GM11.closure_sdiff_pair hK
  have hKV : K ∩ G.V = {x, c} := by
    apply subset_antisymm
    · rintro y ⟨hyK, hyV⟩
      by_contra hn
      have hn' : y ∉ ({c, x} : Set T) := fun h ↦ hn (by rw [pair_comm]; exact h)
      exact disjoint_left.mp hKU ⟨hyK, hn'⟩ (G.V_subset_U hyV)
    · have hend : ({c, x} : Set T) ⊆ K := (GM11.lineDrawing hK hcx).V_subset_U
      rintro y (rfl | rfl)
      · exact ⟨hend (Or.inr rfl), hxV⟩
      · exact ⟨hend (Or.inl rfl), hc⟩
  have hcnV : c ∉ V := fun h ↦ disjoint_left.mp hrU hcr (hVU h)
  by_contra hno
  have key : ∀ f ∈ G.E, ∀ v w, K ∩ G.V = {v, w} → closure f ∩ G.V = {v, w} → False :=
    fun f hf v w hKe hfe ↦ hno ⟨f, hf, hfe.trans (hKe.symm.trans hKV)⟩
  have hiv : ∀ e ∈ G₂.E, ∀ f ∈ G₂.E, e ≠ f → ∀ v ∈ V, ∀ r' ∈ componentsIn Uᶜ, ∀ w ∈ r' ∩ G₂.V,
      closure e ∩ G₂.V = {v, w} → closure f ∩ G₂.V = {v, w} →
      ¬ ∃ Δ : Set T, IsClosedDisc Δ ∧ Δ ⊆ r' ∪ {v} ∧ subBd Δ = closure e ∪ closure f := by
    rw [hGE, hGV]
    rintro e (he | rfl) f (hf | rfl) hef v hv r' hr' w hw hee hfe hΔ
    · exact h₆ e he f hf hef v hv r' hr' w hw hee hfe hΔ
    · rw [hKcl] at hfe
      exact key e he v w hfe hee
    · rw [hKcl] at hee
      exact key f hf v w hee hfe
    · exact hef rfl
  have hpre' : IsPreRadial U V G₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hiv⟩
    · apply subset_antisymm
      · rintro y ⟨hyU, hyG | hyK⟩
        · rw [← h₁]
          exact ⟨hyU, hyG⟩
        · by_cases hym : y ∈ ({c, x} : Set T)
          · rcases hym with rfl | rfl
            · exact (disjoint_left.mp hrU hcr hyU).elim
            · exact hx
          · exact (disjoint_left.mp hrU (hKr ⟨hyK, hym⟩) hyU).elim
      · intro y hy
        rw [← h₁] at hy
        exact ⟨hy.1, Or.inl hy.2⟩
    · rw [hGV]
      exact h₂
    · rw [hGV]
      exact h₃
    · rw [hGV]
      exact h₄
    · intro e he
      rw [hGE] at he
      rw [hGV]
      rcases he with he | rfl
      · exact h₅ e he
      · exact ⟨x, hx, c, ⟨hc, hcnV⟩, by rw [hKcl]; exact hKV⟩
  have hsub : G.IsSubdrawing G₂ := ⟨by rw [hGV], by rw [hGE]; exact subset_union_left⟩
  have hback := hmax G₂ hpre' hsub
  have hmem : K \ {c, x} ∈ G.E := hback.2 (by rw [hGE]; exact Or.inr rfl)
  obtain ⟨y, hy⟩ := (GM11.isPathConnected_sdiff_pair hK).nonempty
  exact disjoint_left.mp hKU hy (G.closure_subset_U hmem (subset_closure hy))

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]

theorem IsSkHat.E_nonempty {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}
 (hD : IsSkHat cap Γ D) (hE : Γ.E.Nonempty) : D.E.Nonempty := by
  obtain ⟨c, hc⟩ := hE
  have hy : ∃ y, y ∈ Γ.skU \ Γ.V := by
    rcases Γ.size_cases hc with h2 | h3
    · obtain ⟨y, hy⟩ := hc.1
      exact ⟨y, Or.inl (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h2⟩, hy⟩)), Γ.disjoint_V hc hy⟩
    · obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
      have htl : tilde c ⊆ discBd (closure c) := hT
      have hnt : (discBd (closure c)).Nontrivial := by
        obtain ⟨a, b, z, hab, -, -, hset⟩ := Set.ncard_eq_three.mp h3
        exact ⟨a, htl (hset ▸ Or.inl rfl), b, htl (hset ▸ Or.inr (Or.inl rfl)), hab⟩
      have hinf : (discBd (closure c)).Infinite := by
        obtain ⟨φ⟩ := hdisc.isOArc_discBd
        have hconn : IsPreconnected (discBd (closure c)) := by
          have : discBd (closure c) = range fun z ↦ (φ z).1 := by
            ext x
            exact ⟨fun hx ↦ ⟨φ.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨z, rfl⟩; exact (φ z).2⟩
          rw [this]
          exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
        exact IsPreconnected.infinite_of_nontrivial hconn hnt
      obtain ⟨y, hy, hyn⟩ := hinf.exists_notMem_finite hfin
      refine ⟨y, Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hy⟩), fun hyV ↦ hyn ?_⟩
      have := discBd_subset _ hy
      exact ⟨this, fun hyc ↦ Γ.disjoint_V hc hyc hyV⟩
  obtain ⟨y, hy⟩ := hy
  obtain ⟨e, he, -⟩ := exists_arcComp_superset (isPathConnected_singleton y)
    (singleton_subset_iff.2 hy)
  exact ⟨_, hD.edge_iff.mpr ⟨e, he, rfl⟩⟩

theorem closure_edge_subset {T : Type} [TopologicalSpace T] [T2Space T] {G : Drawing T} {e : Set T}
    (he : e ∈ G.E) : closure e ⊆ e ∪ G.V := by
  have hne : Nonempty T := he.1.to_subtype.map Subtype.val
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar G
  have hcl : closure e ⊆ range (γ e) := by
    refine closure_minimal ?_ (isCompact_range (hγ.cont e he)).isClosed
    intro x hx
    rw [← hγ.image e he] at hx
    obtain ⟨t, -, rfl⟩ := hx
    exact mem_range_self t
  intro x hx
  obtain ⟨t, rfl⟩ := hcl hx
  by_cases h0 : t = 0
  · exact Or.inr (h0 ▸ hγ.zero e he)
  by_cases h1 : t = 1
  · exact Or.inr (h1 ▸ hγ.one e he)
  refine Or.inl ((hγ.image e he).subset ?_)
  exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩, rfl⟩

/-- **A spoke at each vertex in the closure of a region.** -/
theorem RadialDrawing.exists_spoke {cap : IsCappedSurface S Shat} {Γ : Painting S}
    (rad : RadialDrawing cap Γ) (hS : IsSurface S) (h2 : ∀ r ∈ Γ.hatRegions cap, IsOpenDisc r)
    (hE : Γ.E.Nonempty) {w : Shat} (hw : w ∈ rad.Rstar) {v : S} (hv : v ∈ Γ.V)
    (hcl : cap.emb v ∈ closure (rad.regionOf w)) :
    ∃ e ∈ rad.G.E, closure e ∩ rad.G.V = {cap.emb v, w} := by
  classical
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨D, W, hDU, hDV, hD2, -, hG'⟩ := Γ.exists_hubDrawing hS cap h2
  have hD : IsSkHat cap Γ D := ⟨hDU, hDV⟩
  obtain ⟨G', hpre, hU', hV', hE'⟩ := hG' rad.G rad.isPreRadial
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := id rad.isPreRadial
  have hhat : ∀ x ∈ Γ.hatRegions cap, Disjoint x (Γ.hatU cap) := by
    rintro _ ⟨y, hy, rfl⟩
    exact disjoint_left.mpr fun z hz hzU ↦ connectedComponentIn_subset _ _ hz hzU
  obtain ⟨r₀, hr₀, hwr₀⟩ := hG4 w hw
  have hwU : w ∈ (Γ.hatU cap)ᶜ := fun hc ↦ disjoint_left.mp (hhat r₀ hr₀) hwr₀ hc
  set r := rad.regionOf w with hrdef
  have hrhat : r ∈ Γ.hatRegions cap := ⟨w, hwU, rfl⟩
  have hwr : w ∈ r := mem_connectedComponentIn hwU
  have hrD := hD.hatRegion_mem_R hrhat
  have hvhat : cap.emb v ∈ Γ.hatV cap := mem_image_of_mem _ hv
  have hvD : cap.emb v ∈ D.V := by
    rw [hDV]
    exact hvhat
  have hGsub : rad.G.IsSubdrawing G' := ⟨by rw [hV']; exact subset_union_left, by rw [hE']⟩
  let A : Set ℕ := {n | ∃ G₄ : Drawing Shat, (GM11.PaintingOrDrawing.drawing D).IsPreRadialDrawing
    G₄ ∧
    G'.IsSubdrawing G₄ ∧ G₄.E.ncard = n}
  have hAne : A.Nonempty := ⟨_, G', hpre, ⟨subset_rfl, subset_rfl⟩, rfl⟩
  have hAb : BddAbove A := ⟨D.V.ncard + 2 * D.E.ncard, by
    rintro _ ⟨G₄, h₄, -, rfl⟩
    exact GM11.ncard_spokes_le (Γ := D) (Γ' := G₄) ⟨hD2, h₄⟩ hT⟩
  obtain ⟨G₃, hpre₃, hsub₃, hc₃⟩ := Nat.sSup_mem hAne hAb
  have hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing D) G₃ := ⟨hD2, hpre₃⟩
  have hmax : GM11.RadMax (GM11.PaintingOrDrawing.drawing D) G₃ := by
    intro G₄ h₄ hs
    refine ⟨fun y hy ↦ ?_, ?_⟩
    · by_cases hyV : y ∈ D.V
      · exact hpre₃.2.1 hyV
      obtain ⟨p, hp, hyp⟩ := h₄.2.2.2.1 y ⟨hy, hyV⟩
      obtain ⟨y', ⟨hy'p, hy'⟩, -⟩ := hpre₃.2.2.1 p hp
      rw [(h₄.2.2.1 p hp).unique ⟨hyp, hy⟩ ⟨hy'p, hs.1 hy'⟩]
      exact hy'
    · have hle : G₄.E.ncard ≤ G₃.E.ncard := by
        rw [hc₃]
        exact le_csSup hAb ⟨G₄, h₄, ⟨hsub₃.1.trans hs.1, hsub₃.2.trans hs.2⟩, rfl⟩
      exact (eq_of_subset_of_ncard_le hs.2 hle G₄.finite_edges).ge
  have hsub : rad.G.IsSubdrawing G₃ := ⟨hGsub.1.trans hsub₃.1, hGsub.2.trans hsub₃.2⟩
  have hw₃ : w ∈ G₃.V := hsub.1 hw.1
  obtain ⟨h, hh, hcap⟩ := GM11.exists_spoke_at hrad hmax hT (hD.E_nonempty hE) hrD hwr hw₃ hvD
    hcl
  have hwv : w ≠ cap.emb v := fun he ↦ hw.2 (he ▸ hvhat)
  have hvG : cap.emb v ∈ rad.G.V := hG2 hvhat
  by_cases hhG : h ∈ rad.G.E
  · refine ⟨h, hhG, Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hy, hyG⟩
      have : y ∈ closure h ∩ G₃.V := ⟨hy, hsub.1 hyG⟩
      rwa [hcap] at this
    · rintro y (rfl | rfl)
      · have : cap.emb v ∈ closure h ∩ G₃.V := by rw [hcap]; exact Or.inl rfl
        exact ⟨this.1, hvG⟩
      · have : y ∈ closure h ∩ G₃.V := by rw [hcap]; exact Or.inr rfl
        exact ⟨this.1, hw.1⟩
  have hK : IsLineWithEnds (closure h) w (cap.emb v) :=
    GM11.isLine_closure hh hwv (by rw [hcap, pair_comm])
  obtain ⟨v', hv', r', hr', w', hw', hw'V, hset, hsubr⟩ := GM11.spoke_ends hrad hT hh
  have hw'D : w' ∉ D.V := fun hc ↦ GM11.region_subset hr' hw' (D.V_subset_U hc)
  have hwD : w ∉ D.V := fun hc ↦ hw.2 (by rw [hDV] at hc; exact hc)
  have hww : w' = w := by
    have h₁ : w' ∈ closure h ∩ G₃.V := by rw [hset]; exact Or.inr rfl
    rw [hcap] at h₁
    rcases h₁ with h₁ | h₁
    · exact absurd (h₁ ▸ hvD) hw'D
    · exact h₁
  subst hww
  have hrr : r' = r := GM11.region_eq_of_mem hr' hrD hw' hwr
  subst hrr
  have hKsd : closure h \ {w', cap.emb v} ⊆ h := by
    rintro y ⟨hy, hyn⟩
    rcases closure_edge_subset hh hy with h₁ | h₁
    · exact h₁
    · have h₂ : y ∈ closure h ∩ G₃.V := ⟨hy, h₁⟩
      rw [hcap] at h₂
      exact absurd (show y ∈ ({w', cap.emb v} : Set Shat) by rw [pair_comm]; exact h₂) hyn
  have hKU : Disjoint (closure h \ {w', cap.emb v}) rad.G.U := by
    refine disjoint_left.mpr fun y hy hyG ↦ ?_
    have hyh := hKsd hy
    have hyV : y ∉ rad.G.V := fun hc ↦ (hh.2.1 hyh).2 (hsub.1 hc)
    obtain ⟨e, he, hye⟩ := exists_arcComp_superset (F := rad.G.U \ rad.G.V)
      (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hyG, hyV⟩)
    exact hhG (arcComp_eq_of_mem hh (hsub.2 he) hyh (hye rfl) ▸ he)
  exact exists_spoke_of_line rad.isPreRadial rad.maximal hrhat hwr hw.1 hvhat hK hwv
    (hKsd.trans hsubr) hKU (hhat _ hrhat) (image_mono Γ.V_subset)

end GraphMinor.GM19
