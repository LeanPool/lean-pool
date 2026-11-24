/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Section8c
public import LeanPool.GraphMinor.GM11.Section5b
public import LeanPool.GraphMinor.GM11.RadialFacts
public import LeanPool.GraphMinor.GM11.CircuitRegions
public import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# Graph Minors XIX, (8.1): the edges of `Γ*` split by a separation

Let `(A, B)` be a separation of `Γ`. We extend `Γ*` to a radial drawing `G₃` of `sk(Γ)`, which adds
spokes only inside the discs of the edges of size 3. Each region of `G₃` contains one edge of
`sk(Γ)`,
and so one edge of `Γ`, and we colour the region by whether that edge is in `A`. The edges of `G₃`
between regions of different colours are the edges of `Γ*` split by `(A, B)` (`boundary_split`).
So these edges form the drawing `N(Z)` of Graph Minors XI, and its vertices have even valency.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

omit [T2Space S] in
/-- **`Γ*` extends to a radial drawing of `sk(Γ)`**, with no new spokes in the regions of `Γ`. -/
theorem RadialDrawing.exists_full (rad : RadialDrawing cap Γ) (hS : IsSurface S)
    (h2 : ∀ r ∈ Γ.hatRegions cap, IsOpenDisc r) (_hE : Γ.E.Nonempty) :
    ∃ D G₃ : Drawing Shat, IsSkHat cap Γ D ∧ PreRad (PaintingOrDrawing.drawing D) G₃ ∧
      RadMax (PaintingOrDrawing.drawing D) G₃ ∧ rad.G.IsSubdrawing G₃ ∧
      ∀ e ∈ G₃.E, ∀ r ∈ Γ.hatRegions cap, e ⊆ r → e ∈ rad.G.E := by
  classical
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨D, W, hDU, hDV, hD2, -, hG'⟩ := Γ.exists_hubDrawing hS cap h2
  have hD : IsSkHat cap Γ D := ⟨hDU, hDV⟩
  obtain ⟨G', hpre, hU', hV', hE'⟩ := hG' rad.G rad.isPreRadial
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := id rad.isPreRadial
  have hGsub : rad.G.IsSubdrawing G' := ⟨by rw [hV']; exact subset_union_left, by rw [hE']⟩
  let A : Set ℕ := {n | ∃ G₄ : Drawing Shat, (PaintingOrDrawing.drawing D).IsPreRadialDrawing G₄ ∧
    G'.IsSubdrawing G₄ ∧ G₄.E.ncard = n}
  have hAne : A.Nonempty := ⟨_, G', hpre, ⟨subset_rfl, subset_rfl⟩, rfl⟩
  have hAb : BddAbove A := ⟨D.V.ncard + 2 * D.E.ncard, by
    rintro _ ⟨G₄, h₄, -, rfl⟩
    exact ncard_spokes_le (Γ := D) (Γ' := G₄) ⟨hD2, h₄⟩ hT⟩
  obtain ⟨G₃, hpre₃, hsub₃, hc₃⟩ := Nat.sSup_mem hAne hAb
  have hrad : PreRad (PaintingOrDrawing.drawing D) G₃ := ⟨hD2, hpre₃⟩
  have hmax : RadMax (PaintingOrDrawing.drawing D) G₃ := by
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
  refine ⟨D, G₃, hD, hrad, hmax, hsub, ?_⟩
  have hhat : ∀ x ∈ Γ.hatRegions cap, Disjoint x (Γ.hatU cap) := by
    rintro _ ⟨y, hy, rfl⟩
    exact disjoint_left.mpr fun z hz hzU ↦ connectedComponentIn_subset _ _ hz hzU
  let E₄ : Set (Set Shat) := {e | e ∈ G₃.E ∧ ∃ r ∈ Γ.hatRegions cap, e ⊆ r}
  let G₄ : Drawing Shat := G₃.span rad.G.V E₄
  have hends : ∀ e ∈ E₄, ∃ v ∈ Γ.hatV cap, ∃ w ∈ rad.G.V \ Γ.hatV cap,
      closure e ∩ G₃.V = {v, w} := by
    rintro e ⟨he, r, hr, her⟩
    obtain ⟨v, hv, r', hr', w, hw, hwV, hset, hsubr⟩ := spoke_ends hrad hT he
    obtain ⟨x, hx⟩ := he.1
    have hrD := hD.hatRegion_mem_R hS hr
    obtain rfl : r' = r := region_eq_of_mem hr' hrD (hsubr hx) (her hx)
    obtain ⟨w₀, ⟨hw₀r, hw₀⟩, -⟩ := hG3 r' hr
    have hww : w = w₀ := (hpre₃.2.2.1 r' hrD).unique ⟨hw, hwV⟩ ⟨hw₀r, hsub.1 hw₀⟩
    subst hww
    refine ⟨v, ?_, w, ⟨hw₀, fun hc ↦ disjoint_left.mp (hhat _ hr) hw (image_mono Γ.V_subset hc)⟩,
      hset⟩
    rw [hD.hV] at hv
    exact hv
  have hG4V : G₄.V = rad.G.V := by
    apply Subset.antisymm
    · rw [Drawing.span_V]
      rintro y (hy | hy)
      · exact hy.1
      · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
        obtain ⟨v, hv, w, hw, hset⟩ := hends e he.1
        have : y ∈ closure e ∩ G₃.V := hye
        rw [hset] at this
        rcases this with rfl | rfl
        · exact hG2 hv
        · exact hw.1
    · intro y hy
      rw [Drawing.span_V]
      exact Or.inl ⟨hy, hsub.1 hy⟩
  have hG4E : G₄.E = E₄ := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr fun _ h ↦ h.1
  have hcap : ∀ e ∈ E₄, closure e ∩ G₄.V = closure e ∩ G₃.V := by
    intro e he
    obtain ⟨v, hv, w, hw, hset⟩ := hends e he
    apply Subset.antisymm
    · rintro y ⟨hy, hyV⟩
      exact ⟨hy, hsub.1 (hG4V ▸ hyV)⟩
    · rintro y hy
      refine ⟨hy.1, ?_⟩
      rw [hset] at hy
      rw [hG4V]
      rcases hy with rfl | rfl
      · exact hG2 hv
      · exact hw.1
  have hpre₄ : IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G₄ := by
    refine ⟨?_, hG4V ▸ hG2, hG4V ▸ hG3, hG4V ▸ hG4, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro y ⟨hyU, hyG⟩
        by_cases hyV : y ∈ G₄.V
        · rw [← hG1]
          exact ⟨hyU, rad.G.V_subset_U (hG4V ▸ hyV)⟩
        · obtain ⟨e, he, hye⟩ := G₄.exists_edge_of_mem hyG hyV
          rw [hG4E] at he
          obtain ⟨-, r, hr, her⟩ := he
          exact absurd hyU (disjoint_left.mp (hhat r hr) (her hye))
      · intro y hy
        exact ⟨image_mono Γ.V_subset hy, G₄.V_subset_U (hG4V ▸ hG2 hy)⟩
    · intro e he
      rw [hG4E] at he
      obtain ⟨v, hv, w, hw, hset⟩ := hends e he
      exact ⟨v, hv, w, hG4V ▸ hw, by rw [hcap e he, hset]⟩
    · intro e he f hf hne v hv r hr w hw h₁ h₂
      rw [hG4E] at he hf
      rw [hcap e he] at h₁
      rw [hcap f hf] at h₂
      refine hpre₃.2.2.2.2.2 e he.1 f hf.1 hne v ?_ r (hD.hatRegion_mem_R hS hr) w
        ⟨hw.1, hsub.1 (hG4V ▸ hw.2)⟩ h₁ h₂
      change v ∈ D.V
      rw [hD.hV]
      exact hv
  have hup : rad.G.IsSubdrawing G₄ := by
    refine ⟨hG4V.ge, fun e he ↦ ?_⟩
    rw [hG4E]
    refine ⟨hsub.2 he, ?_⟩
    obtain ⟨x, hx⟩ := he.1
    have hdis : ∀ y ∈ e, y ∉ Γ.hatU cap := by
      intro y hy hyU
      have : y ∈ Γ.hatU cap ∩ rad.G.U := ⟨hyU, (he.2.1 hy).1⟩
      rw [hG1] at this
      exact (he.2.1 hy).2 (hG2 this)
    have hxc : x ∈ (Γ.hatU cap)ᶜ := hdis x hx
    refine ⟨connectedComponentIn (Γ.hatU cap)ᶜ x, ⟨x, hxc, rfl⟩, ?_⟩
    exact he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hx hdis
  intro e he r hr her
  have := (rad.maximal G₄ hpre₄ hup).2
  exact this (hG4E ▸ ⟨he, r, hr, her⟩)

section Colour

variable {D G₃ : Drawing Shat}

/-- The regions of `G₃` coloured by a property `t` of the edges of `Γ`. -/
def colourSet (cap : IsCappedSurface S Shat) (Γ : Painting S) (G₃ : Drawing Shat)
    (t : Set S → Prop) : Set (Set Shat) :=
  {s | s ∈ G₃.R ∧ ∃ f c, Γ.IsSkEdgeIn f c ∧ cap.emb '' f ⊆ s ∧ t c}

variable [ConnectedSpace Shat] [T2Space Shat]

omit [T2Space S] in
/-- Each region of `G₃` contains an edge of `sk(Γ)`. -/
theorem exists_colour (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hE : D.E.Nonempty) {s : Set Shat}
      (hs : s ∈ G₃.R) :
    ∃ f c, Γ.IsSkEdgeIn f c ∧ cap.emb '' f ⊆ s := by
  have hF := regionFacts_of_radial hrad cap.isClosedSurface hmax hE
  obtain ⟨g, hg, hgs⟩ := hF.1 s hs
  obtain ⟨f, hf, rfl⟩ := (hD.edge_iff hS).mp hg
  obtain ⟨c, hc⟩ := Γ.exists_isSkEdgeIn hf
  exact ⟨f, c, hc, hgs⟩

omit [T2Space S] in
theorem colour_unique (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hE : D.E.Nonempty) {s : Set Shat}
      (hs : s ∈ G₃.R)
    {f f' c c' : Set S} (h : Γ.IsSkEdgeIn f c) (h' : Γ.IsSkEdgeIn f' c') (hf : cap.emb '' f ⊆ s)
    (hf' : cap.emb '' f' ⊆ s) : f = f' ∧ c = c' := by
  have hF := regionFacts_of_radial hrad cap.isClosedSurface hmax hE
  have hg := (hD.edge_iff hS).mpr ⟨f, h.mem, rfl⟩
  have hg' := (hD.edge_iff hS).mpr ⟨f', h'.mem, rfl⟩
  have := hF.2.1 s hs _ hg _ hg' hf hf'
  obtain rfl : f = f' := cap.isEmbedding.injective.image_injective this
  exact ⟨rfl, h.unique h'⟩

omit [T2Space S] in
theorem notMem_colourSet (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hE : D.E.Nonempty) {t : Set S
      → Prop} {s : Set Shat}
    (hs : s ∈ G₃.R \ colourSet cap Γ G₃ t) : ∃ f c, Γ.IsSkEdgeIn f c ∧ cap.emb '' f ⊆ s ∧ ¬ t c
      := by
  obtain ⟨f, c, hc, hf⟩ := exists_colour hS hD hrad hmax hE hs.1
  exact ⟨f, c, hc, hf, fun ht ↦ hs.2 ⟨hs.1, f, c, hc, hf, ht⟩⟩

/-- An edge of `sk(Γ)` in a region of `G₃` with `e` on its boundary lies in the closure of the
region
of `sk(Γ)` that contains `e`. -/
theorem sub_closure_region (hE : D.E.Nonempty) (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hT : IsClosedSurface Shat) {e g s r : Set
      Shat} (hs : s ∈ G₃.R) (hg : g ∈ D.E) (hgs : g ⊆ s)
    (hr : r ∈ D.R) (her : e ⊆ r) (hes : e ⊆ closure s) (hne : e.Nonempty) : g ⊆ closure r := by
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨y, hy⟩ := hne
  have hsub := region_eq_faceUnion hrad hT hmax hE hs hg hgs
  obtain ⟨z, hzr, hzs⟩ := mem_closure_iff.mp (hes hy) r (region_isOpen hr) (her hy)
  rcases hsub hzs with hzg | hzp
  · have : z ∈ D.U := (hg.2.1 hzg).1
    exact absurd this (region_subset hr hzr)
  · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hzp
    obtain ⟨hpR, -, hgp⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hpR
    have hdis : Disjoint (connectedComponentIn (univ \ (radialUnion hrad).U) x) D.U := by
      refine disjoint_left.mpr fun w hw hwD ↦ ?_
      have := connectedComponentIn_subset _ _ hw
      exact this.2 (Or.inl hwD)
    have hsubr := subset_region hr isPreconnected_connectedComponentIn hdis hzp hzr
    exact hgp.trans (closure_mono hsubr)

omit [ConnectedSpace Shat] [T2Space Shat] in
omit [T2Space S] in
/-- An edge of `sk(Γ)` in the disc of an edge `c₀` of `Γ` is inside `c₀`. -/
theorem Painting.IsSkEdgeIn.eq_of_subset {f c c₀ : Set S} (h : Γ.IsSkEdgeIn f c) (hc₀ : c₀ ∈ Γ.E)
    (hsub : cap.emb '' f ⊆ cap.emb '' closure c₀) : c = c₀ := by
  obtain ⟨x, hx⟩ := h.mem.1
  obtain ⟨y, hy, hyx⟩ := hsub (mem_image_of_mem _ hx)
  obtain rfl := cap.isEmbedding.injective hyx
  have hxc : y ∈ c₀ := by
    by_contra hn
    exact (h.mem.2.1 hx).2 (Γ.tilde_subset_V hc₀ ⟨hy, hn⟩)
  exact arcComp_eq_of_mem h.1 hc₀ (h.subset hx) hxc

omit [T2Space S] in
/-- **The edges of `G₃` between regions of different colours are split.** -/
theorem boundary_split (hS : IsSurface S) (hE : D.E.Nonempty) (rad : RadialDrawing cap Γ)
    (hD : IsSkHat cap Γ D) (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hsub : rad.G.IsSubdrawing G₃)
    (hhat : ∀ e ∈ G₃.E, ∀ r ∈ Γ.hatRegions cap, e ⊆ r → e ∈ rad.G.E) {t : Set S → Prop}
    {e : Set Shat} (he : e ∈ (boundaryDrawing G₃ (colourSet cap Γ G₃ t)).E) :
    e ∈ rad.G.E ∧ ∃ (v₀ : S) (w : Shat), v₀ ∈ Γ.V ∧ w ∈ rad.Rstar ∧
      closure e ∩ G₃.V = {cap.emb v₀, w} ∧ ∃ f₁ f₂ c₁ c₂ : Set S,
        rad.PairOf e c₁ c₂ ∧ Γ.IsSkEdgeIn f₁ c₁ ∧ Γ.IsSkEdgeIn f₂ c₂ ∧ v₀ ∈ tilde f₁
          ∧ v₀ ∈ tilde f₂ ∧
        ¬ (t c₁ ↔ t c₂) := by
  have hT := cap.isClosedSurface
  have : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hF := regionFacts_of_radial hrad hT hmax hE
  obtain ⟨⟨s, hsZ, hinc⟩, ⟨s', hs', hinc'⟩⟩ := mem_boundaryDrawing_E.mp he
  have heG := hinc.1
  have hes : e ⊆ closure s := edge_subset_closure_of_incident hT heG hinc.2.1 hinc.2.2
  have hes' : e ⊆ closure s' := edge_subset_closure_of_incident hT heG hinc'.2.1 hinc'.2.2
  obtain ⟨f, c, hc, hfs, ht⟩ := hsZ.2
  obtain ⟨f', c', hc', hfs', ht'⟩ := notMem_colourSet hS hD hrad hmax hE hs'
  obtain ⟨v, hv, r, hr, w, hw, hwV, hset, her⟩ := spoke_ends hrad hT heG
  have hne : e.Nonempty := heG.1
  have hg := (hD.edge_iff hS).mpr ⟨f, hc.mem, rfl⟩
  have hg' := (hD.edge_iff hS).mpr ⟨f', hc'.mem, rfl⟩
  have h₁ := sub_closure_region hE hrad hmax hT hsZ.1 hg hfs hr her hes hne
  have h₂ := sub_closure_region hE hrad hmax hT hs'.1 hg' hfs' hr her hes' hne
  have hcc : c ≠ c' := fun h ↦ ht' (h ▸ ht)
  rcases hD.region_cases hS hr with hhr | ⟨c₀, hc₀, -, hrsub⟩
  · have heR := hhat e heG r hhr her
    obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := id rad.isPreRadial
    have hvhat : v ∈ Γ.hatV cap := by
      have : v ∈ D.V := hv
      rwa [hD.hV] at this
    obtain ⟨v₀, hv₀, rfl⟩ := hvhat
    have hdis : Disjoint r (Γ.hatU cap) := by
      obtain ⟨y, hy, rfl⟩ := hhr
      exact disjoint_left.mpr fun z hz hzU ↦ connectedComponentIn_subset _ _ hz hzU
    obtain ⟨w₀, ⟨hw₀r, hw₀⟩, -⟩ := hG3 r hhr
    obtain rfl : w = w₀ := (hrad.2.2.2.1 r hr).unique ⟨hw, hwV⟩ ⟨hw₀r, hsub.1 hw₀⟩
    have hwR : w ∈ rad.Rstar :=
      ⟨hw₀, fun h ↦ disjoint_left.mp hdis hw (image_mono Γ.V_subset h)⟩
    have hsetG : closure e ∩ rad.G.V = {cap.emb v₀, w} := by
      apply Subset.antisymm
      · rintro y ⟨hy, hyG⟩
        rw [← hset]
        exact ⟨hy, hsub.1 hyG⟩
      · intro y hy
        have hy' : y ∈ closure e ∩ G₃.V := by rw [hset]; exact hy
        refine ⟨hy'.1, ?_⟩
        rcases hy with rfl | rfl
        · exact hG2 (mem_image_of_mem _ hv₀)
        · exact hw₀
    have hvcl : cap.emb v₀ ∈ closure e := by
      have : cap.emb v₀ ∈ closure e ∩ G₃.V := by rw [hset]; exact Or.inl rfl
      exact this.1
    have htil : ∀ {g : Set S} {s₀ : Set Shat}, s₀ ∈ G₃.R → g ∈ arcComponentsIn (Γ.skU \ Γ.V) →
        cap.emb '' g ⊆ s₀ → e ⊆ closure s₀ → v₀ ∈ tilde g := by
      intro g s₀ hs₀ hgm hgs he₀
      have hcl : cap.emb v₀ ∈ closure s₀ := by
        have : closure e ⊆ closure s₀ := closure_minimal he₀ isClosed_closure
        exact this hvcl
      have := hF.2.2 s₀ hs₀ _ ((hD.edge_iff hS).mpr ⟨g, hgm, rfl⟩) hgs _ hv hcl
      rw [(cap.isClosedEmbedding hS).closure_image_eq] at this
      obtain ⟨x, hx, hxe⟩ := this
      obtain rfl := cap.isEmbedding.injective hxe
      exact ⟨hx, fun hxg ↦ (hgm.2.1 hxg).2 hv₀⟩
    have hregion : rad.regionOf w = r := by
      obtain ⟨y, hy, hyr⟩ := hhr
      change connectedComponentIn (Γ.hatU cap)ᶜ w = r
      rw [← hyr] at hw ⊢
      exact (connectedComponentIn_eq hw).symm
    have hfr : ∀ {g : Set S}, g ∈ arcComponentsIn (Γ.skU \ Γ.V) → cap.emb '' g ⊆ closure r →
        cap.emb '' g ⊆ frontier (rad.regionOf w) := by
      intro g hgm hg
      rw [hregion, (region_isOpen hr).frontier_eq]
      intro x hx
      refine ⟨hg hx, fun hxr ↦ region_subset hr hxr ?_⟩
      rw [hD.hU]
      obtain ⟨z, hz, rfl⟩ := hx
      exact mem_image_of_mem _ (hgm.2.1 hz).1
    have hff : f ≠ f' := fun h ↦ hcc (hc.unique (h ▸ hc'))
    refine ⟨heR, v₀, w, hv₀, hwR, hset, f, f', c, c', ⟨v₀, w, hv₀, hwR, hsetG, f, f', hff, hc, hc',
      htil hsZ.1 hc.mem hfs hes, htil hs'.1 hc'.mem hfs' hes', hfr hc.mem h₁, hfr hc'.mem h₂⟩, hc,
        hc',
      htil hsZ.1 hc.mem hfs hes, htil hs'.1 hc'.mem hfs' hes', fun h ↦ ht' (h.mp ht)⟩
  · have hcl : closure r ⊆ cap.emb '' closure c₀ := closure_minimal hrsub
      ((cap.isClosedEmbedding hS).isClosedMap _ isClosed_closure)
    exact absurd ((hc.eq_of_subset hc₀ (h₁.trans hcl)).trans
      (hc'.eq_of_subset hc₀ (h₂.trans hcl)).symm) hcc

end Colour

section Counting

/-- A walk that alternates between `P` and its complement has at most about twice as many edges as
vertices in `P`. -/
theorem walk_bound {α β : Type*} {G : Graph α β} (P : α → Prop) [DecidablePred P]
    (halt : ∀ e x y, G.IsLink e x y → (P x ↔ ¬ P y)) {a b : α} (W : GraphWalk G a b) :
    W.length + (if P a then 1 else 0) + (if P b then 1 else 0) ≤ 2 * W.support.countP P := by
  induction W with
  | @nil v h =>
    by_cases hp : P v <;> simp [hp, GraphWalk.support_nil]
  | @cons u v w e h r ih =>
    have hx := halt _ _ _ h
    rw [GraphWalk.length_cons, GraphWalk.support_cons, List.countP_cons]
    by_cases hu : P u <;> by_cases hv : P v
    · exact absurd hv (hx.mp hu)
    · simp only [hu, hv, ite_true, ite_false, decide_true] at ih ⊢
      omega
    · simp only [hu, hv, ite_true, ite_false, decide_false] at ih ⊢
      omega
    · exact absurd (hx.mpr hv) hu

/-- A circuit in a bipartite drawing has at most twice as many edges as vertices on one side. -/
theorem IsCircuit.ncard_le {T : Type} [TopologicalSpace T] {C : Drawing T}
  (hC : C.IsCircuit)
    {P : Set T} (halt : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ P ↔ y ∉ P)) :
    C.E.ncard ≤ 2 * (C.V ∩ P).ncard := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := hC
  have hl : C.E.ncard = W.length := by
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set T)) := by
      ext x
      simp
    rw [hE, h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have hb := walk_bound (· ∈ P) halt W
  have hsupp := W.support_eq_cons
  have hcount : W.support.countP (· ∈ P) = (if u ∈ P then 1 else 0) +
      W.support.tail.countP (· ∈ P) := by
    conv_lhs => rw [hsupp, List.countP_cons]
    by_cases hu : u ∈ P <;> simp [hu, add_comm]
  have hsub : (((W.support.tail.filter (· ∈ P)).toFinset : Finset T) : Set T) ⊆ C.V ∩ P := by
    intro x hx
    have hx' : x ∈ W.support.tail ∧ x ∈ P := by simpa using hx
    exact ⟨by rw [hV]; exact List.mem_of_mem_tail hx'.1, hx'.2⟩
  have hle := ncard_le_ncard hsub (C.finite_V.subset inter_subset_left)
  rw [ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _), ← List.countP_eq_length_filter]
    at hle
  rw [hl]
  by_cases hu : u ∈ P <;> simp only [hu, ite_true, ite_false] at hb hcount <;> omega

end Counting

section Mono

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T] {G : Drawing T}

/-- **A colour change inside a connected open set.** -/
theorem exists_boundary_edge (hT : IsClosedSurface T) {Z : Set (Set T)} {X : Set T}
    (hX : IsOpen X) (hXc : IsPreconnected X) {s₁ s₂ : Set T} (h₁ : s₁ ∈ Z) (hZ : Z ⊆ G.R)
    (h₂ : s₂ ∈ G.R \ Z) (hm₁ : (s₁ ∩ X).Nonempty) (hm₂ : (s₂ ∩ X).Nonempty) :
    ∃ e ∈ (boundaryDrawing G Z).E, (e ∩ X).Nonempty := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have hRfin : G.R.Finite := finite_R hT G
  have hconn := isPreconnected_sdiff_finite hT hX hXc G.finite_V
  let A : Set T := closure (⋃₀ Z)
  let B : Set T := closure (⋃₀ (G.R \ Z))
  have hcov : X \ G.V ⊆ A ∪ B := by
    intro y hy
    have hdense : y ∈ closure (⋃₀ G.R) := by
      rw [mem_closure_iff]
      intro O hO hyO
      obtain ⟨z, hzO, hzU⟩ := exists_notMem_U (Γ := G) hT hO ⟨y, hyO⟩
      obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
      exact ⟨z, hzO, r, hr, hzr⟩
    have hsplit : ⋃₀ G.R = ⋃₀ Z ∪ ⋃₀ (G.R \ Z) := by
      rw [← sUnion_union, union_sdiff_cancel hZ]
    rw [hsplit, closure_union] at hdense
    exact hdense
  have hne₁ : ((X \ G.V) ∩ A).Nonempty := by
    obtain ⟨z, hzs, hzX⟩ := hm₁
    exact ⟨z, ⟨hzX, fun hc ↦ region_subset (hZ h₁) hzs (G.V_subset_U hc)⟩,
      subset_closure ⟨s₁, h₁, hzs⟩⟩
  have hne₂ : ((X \ G.V) ∩ B).Nonempty := by
    obtain ⟨z, hzs, hzX⟩ := hm₂
    exact ⟨z, ⟨hzX, fun hc ↦ region_subset h₂.1 hzs (G.V_subset_U hc)⟩,
      subset_closure ⟨s₂, h₂, hzs⟩⟩
  obtain ⟨y, hyX, hyA, hyB⟩ := isPreconnected_closed_iff.mp hconn A B isClosed_closure
    isClosed_closure hcov hne₁ hne₂
  have hAe : y ∈ ⋃ s ∈ Z, closure s := by
    have hf : Z.Finite := hRfin.subset hZ
    change y ∈ closure (⋃₀ Z) at hyA
    rwa [sUnion_eq_biUnion, hf.closure_biUnion] at hyA
  have hBe : y ∈ ⋃ s ∈ G.R \ Z, closure s := by
    have hf : (G.R \ Z).Finite := hRfin.subset sdiff_subset
    change y ∈ closure (⋃₀ (G.R \ Z)) at hyB
    rwa [sUnion_eq_biUnion, hf.closure_biUnion] at hyB
  obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hAe
  obtain ⟨s', hs', hys'⟩ := mem_iUnion₂.mp hBe
  have hne : s ≠ s' := fun h ↦ hs'.2 (h ▸ hs)
  by_cases hyU : y ∈ G.U
  · obtain ⟨e, he, hye⟩ := G.exists_edge_of_mem hyU hyX.2
    refine ⟨e, mem_boundaryDrawing_E.mpr ⟨⟨s, hs, he, hZ hs, y, hye, hys⟩,
      ⟨s', hs', he, hs'.1, y, hye, hys'⟩⟩, y, hye, hyX.1⟩
  · exfalso
    obtain ⟨q, hq, hyq⟩ := exists_region_of_notMem hyU
    obtain ⟨z, hzq, hzs⟩ := mem_closure_iff.mp hys q (region_isOpen hq) hyq
    obtain ⟨z', hzq', hzs'⟩ := mem_closure_iff.mp hys' q (region_isOpen hq) hyq
    have e₁ := region_eq_of_mem hq (hZ hs) hzq hzs
    have e₂ := region_eq_of_mem hq hs'.1 hzq' hzs'
    exact hne (e₁.symm.trans e₂)

omit [ConnectedSpace T] in
/-- A region with a point of the inside of a disc in its closure lies inside the disc, when the
boundary of the disc lies in `U(G)`. -/
theorem region_in (hT : IsClosedSurface T) {Δ : Set T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ ⊆ G.U) {s : Set T} (hs : s ∈ G.R) {p : T} (hp : p ∈ closure s)
    (hpi : p ∈ discInt Δ) : s ⊆ discInt Δ := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hopen := hΔ.isOpen_discInt hman
  obtain ⟨z, hzΔ, hzs⟩ := mem_closure_iff.mp hp _ hopen hpi
  obtain ⟨x, hx, rfl⟩ := id hs
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hopen
    hΔ.isClosed.isOpen_compl (disjoint_left.mpr fun w hw hn ↦ hn hw.1) (fun w hw ↦ ?_)
    ⟨z, hzs, hzΔ⟩
  by_cases hwΔ : w ∈ Δ
  · exact Or.inl ⟨hwΔ, fun hb ↦ region_subset hs hw (hbd hb)⟩
  · exact Or.inr hwΔ

/-- A disc whose boundary is a circuit of `N(Z)`, with an edge of `N(Z)` inside, contains a smaller
such disc. The regions of `Z` in the disc give an `N(Z'')` with an edge inside, and that edge is in
a circuit because the valencies are even. -/
theorem exists_smaller (hT : IsClosedSurface T) {Z : Set (Set T)} (hZ : Z ⊆ G.R) {F : Drawing T}
    (_hF : F.IsCircuit) (hFs : F.IsSubdrawing (boundaryDrawing G Z)) {Δ : Set T}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) {e : Set T} (he : e ∈ (boundaryDrawing G Z).E)
    (hmeet : (e ∩ discInt Δ).Nonempty) :
    ∃ (C : Drawing T) (Δ' : Set T), C.IsCircuit ∧ C.IsSubdrawing (boundaryDrawing G Z) ∧
      IsClosedDisc Δ' ∧ discBd Δ' = C.U ∧
      {s ∈ G.R | s ⊆ Δ'}.ncard < {s ∈ G.R | s ⊆ Δ}.ncard := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hRfin : G.R.Finite := finite_R hT G
  have hNs : (boundaryDrawing G Z).IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hFG := hFs.trans hNs
  have hbdU : discBd Δ ⊆ G.U := hbd ▸ hFG.U_subset
  let Z' : Set (Set T) := {s | s ∈ Z ∧ s ⊆ Δ}
  let N' : Drawing T := boundaryDrawing G Z'
  have hN's : N'.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hedgeN := hNs.2
  have heG : e ∈ G.E := hedgeN he
  have hinc : ∀ {a}, G.EdgeRegionIncident e a → e ⊆ closure a := fun h ↦
    edge_subset_closure_of_incident hT h.1 h.2.1 h.2.2
  obtain ⟨y, hye, hyΔ⟩ := hmeet
  obtain ⟨⟨s, hsZ, hsi⟩, ⟨s', hs', hsi'⟩⟩ := mem_boundaryDrawing_E.mp he
  have heN' : e ∈ N'.E := by
    refine mem_boundaryDrawing_E.mpr ⟨⟨s, ⟨hsZ, ?_⟩, hsi⟩, ⟨s', ⟨hs'.1, fun h ↦ hs'.2 h.1⟩, hsi'⟩⟩
    exact (region_in hT hΔ hbdU (hZ hsZ) (hinc hsi hye) hyΔ).trans (discInt_subset Δ)
  have : Nonempty T := ⟨y⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar G
  obtain ⟨C, hC, hCs, heC⟩ := exists_circuit_of_even hγ hN's
    (fun v hv ↦ even_nHalf hT G hγ hv Z') heN'
  have hCG := hCs.trans hN's
  have hedge : ∀ g ∈ C.E, g ∈ (boundaryDrawing G Z).E ∧ g ⊆ Δ := by
    intro g hg
    obtain ⟨⟨a, haZ, hai⟩, ⟨b, hb, hbi⟩⟩ := mem_boundaryDrawing_E.mp (hCs.2 hg)
    have hgG := hCG.2 hg
    have hga : g ⊆ closure a := edge_subset_closure_of_incident hT hgG
      hai.2.1 hai.2.2
    have hgb : g ⊆ closure b := edge_subset_closure_of_incident hT hgG
      hbi.2.1 hbi.2.2
    have hgΔ : g ⊆ Δ := hga.trans (closure_minimal haZ.2 hΔ.isClosed)
    refine ⟨?_, hgΔ⟩
    by_cases hbZ : b ∈ Z
    · have hbn : ¬ b ⊆ Δ := fun h ↦ hb.2 ⟨hbZ, h⟩
      have hno : ∀ x ∈ g, x ∉ discInt Δ := fun x hx hxi ↦
        hbn ((region_in hT hΔ hbdU hb.1 (hgb hx) hxi).trans (discInt_subset Δ))
      by_cases hgF : g ∈ F.E
      · exact hFs.2 hgF
      · exfalso
        obtain ⟨x, hx⟩ := hgG.1
        have hd := edge_disjoint_U hFG hgG hgF
        refine hno x hx ⟨hgΔ hx, fun hxb ↦ disjoint_left.mp hd hx ?_⟩
        rwa [hbd] at hxb
    · exact mem_boundaryDrawing_E.mpr ⟨⟨a, haZ.1, hai⟩, ⟨b, ⟨hb.1, hbZ⟩, hbi⟩⟩
  have hCN : C.IsSubdrawing (boundaryDrawing G Z) :=
    circuit_isSubdrawing_of_E hC hCG hNs fun g hg ↦ (hedge g hg).1
  have hCU : C.U ⊆ Δ := by
    have hclo : ∀ g ∈ C.E, closure g ⊆ Δ := fun g hg ↦
      closure_minimal (hedge g hg).2 hΔ.isClosed
    intro x hx
    by_cases hxV : x ∈ C.V
    · obtain ⟨g, hg, hxg⟩ := exists_edge_at_vertex hC hxV
      exact hclo g hg hxg
    · obtain ⟨g, hg, hxg⟩ := C.exists_edge_of_mem hx hxV
      exact (hedge g hg).2 hxg
  obtain ⟨Δ', ⟨hΔ'Δ, hΔ', hbd', -⟩, -⟩ := disc_oArc.{0} Δ C.U hΔ hCU (GM14.isOArc_of_isCircuit hC)
  refine ⟨C, Δ', hC, hCN, hΔ', hbd', ?_⟩
  have hne : Δ' ≠ Δ := by
    rintro rfl
    obtain ⟨x, hx⟩ := heG.1
    have hmem : x ∈ F.U := hbd ▸ hbd' ▸ (show x ∈ C.U from (heC.2.1 hx).1)
    have heF : e ∉ F.E := fun hc ↦ by
      have : y ∈ F.U := (hc.2.1 hye).1
      exact hyΔ.2 (hbd ▸ this)
    exact disjoint_left.mp (edge_disjoint_U hFG heG heF) hx hmem
  obtain ⟨z, hzΔ, hzn⟩ : ∃ z ∈ Δ, z ∉ Δ' := by
    by_contra hall
    push Not at hall
    exact hne (Subset.antisymm hΔ'Δ hall)
  have hO : IsOpen (Δ'ᶜ ∩ discInt Δ) := hΔ'.isClosed.isOpen_compl.inter (hΔ.isOpen_discInt hman)
  have hOne : (Δ'ᶜ ∩ discInt Δ).Nonempty := by
    obtain ⟨w, hw, hwi⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt hzΔ) _
      hΔ'.isClosed.isOpen_compl hzn
    exact ⟨w, hw, hwi⟩
  obtain ⟨w, hwO, hwU⟩ := exists_notMem_U (Γ := G) hT hO hOne
  obtain ⟨q, hq, hwq⟩ := exists_region_of_notMem hwU
  have hsubs : {s ∈ G.R | s ⊆ Δ'} ⊂ {s ∈ G.R | s ⊆ Δ} := by
    refine ⟨fun s hs ↦ ⟨hs.1, hs.2.trans hΔ'Δ⟩, fun hc ↦ ?_⟩
    have hqΔ : q ⊆ Δ := (region_in hT hΔ hbdU hq (subset_closure hwq) hwO.2).trans
      (discInt_subset Δ)
    exact hwO.1 ((hc ⟨hq, hqΔ⟩).2 hwq)
  exact ncard_lt_ncard hsubs (hRfin.subset fun _ h ↦ h.1)

/-- A disc bounded by a circuit of `N(Z)` contains one with no edge of `N(Z)` inside. -/
theorem exists_clean (hT : IsClosedSurface T) {Z : Set (Set T)} (hZ : Z ⊆ G.R) {F₀ : Drawing T}
    (hF₀ : F₀.IsCircuit) (hFs₀ : F₀.IsSubdrawing (boundaryDrawing G Z)) {Δ₀ : Set T}
    (hΔ₀ : IsClosedDisc Δ₀) (hbd₀ : discBd Δ₀ = F₀.U) :
    ∃ (F : Drawing T) (Δ : Set T), F.IsCircuit ∧ F.IsSubdrawing (boundaryDrawing G Z) ∧
      IsClosedDisc Δ ∧ discBd Δ = F.U ∧ ∀ e ∈ (boundaryDrawing G Z).E, Disjoint e (discInt Δ) := by
  induction hn : {s ∈ G.R | s ⊆ Δ₀}.ncard using Nat.strong_induction_on generalizing F₀ Δ₀ with
  | _ n ih =>
    by_cases hall : ∀ e ∈ (boundaryDrawing G Z).E, Disjoint e (discInt Δ₀)
    · exact ⟨F₀, Δ₀, hF₀, hFs₀, hΔ₀, hbd₀, hall⟩
    · push Not at hall
      obtain ⟨e, he, hne⟩ := hall
      obtain ⟨C, Δ', hC, hCs, hΔ', hbd', hlt⟩ :=
        exists_smaller hT hZ hF₀ hFs₀ hΔ₀ hbd₀ he (not_disjoint_iff_nonempty_inter.mp hne)
      exact ih _ (hn ▸ hlt) hC hCs hΔ' hbd' rfl

end Mono

/-- Each edge of `Γ` contains an edge of `sk(Γ)`. -/
theorem Painting.exists_sk_in {c : Set S} (hc : c ∈ Γ.E) : ∃ f, Γ.IsSkEdgeIn f c := by
  rcases Γ.size_cases hc with h2' | h3'
  · exact ⟨c, hc, Or.inl ⟨h2', rfl⟩⟩
  · obtain ⟨a, b, z, hab, -, -, hset⟩ := Set.ncard_eq_three.mp h3'
    obtain ⟨f, hf, -⟩ := Γ.exists_sk_at hc (show a ∈ tilde c from hset ▸ Or.inl rfl)
    exact ⟨f, hf⟩

private theorem edges_on_one_side_of_internal_disc
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    {Γ : Painting S}
    {A : Hypergraph S (Set S)}
    {B : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B)
    (G₃ : Drawing Shat)
    (Z : Set (Set Shat))
    (hreg : ∀ f ∈ arcComponentsIn (Γ.skU \ Γ.V), ∃ s ∈ Drawing.R G₃, cap.emb '' f ⊆ s)
    (hcol : ∀ {f c : Set S} {s : Set Shat}, Γ.IsSkEdgeIn f c → s ∈ Drawing.R G₃ → cap.emb '' f ⊆ s
      → (s ∈ Z ↔ c ∈ A.edgeSet))
    (Δ : Set Shat)
    (hno : ∀ s₁ ∈ Z, ∀ s₂ ∈ Drawing.R G₃ \ Z, (s₁ ∩ discInt Δ).Nonempty → (s₂ ∩ discInt
      Δ).Nonempty → False) :
    (∀ (f c : Set S), Γ.IsSkEdgeIn f c → (cap.emb '' f ∩ discInt Δ).Nonempty → c ∈ A.edgeSet) ∨ ∀
      (f c : Set S), Γ.IsSkEdgeIn f c → (cap.emb '' f ∩ discInt Δ).Nonempty → c ∈ B.edgeSet := by
  by_cases hcase : ∃ s ∈ Z, (s ∩ discInt Δ).Nonempty
  · obtain ⟨s₁, h₁, m₁⟩ := hcase
    left
    intro f c hfc hm
    obtain ⟨s, hs, hfs⟩ := hreg f hfc.mem
    by_contra hc
    have : s ∈ G₃.R \ Z := ⟨hs, fun h ↦ hc ((hcol hfc hs hfs).mp h)⟩
    exact hno s₁ h₁ s this m₁ (hm.mono (inter_subset_inter_left _ hfs))
  · right
    intro f c hfc hm
    obtain ⟨s, hs, hfs⟩ := hreg f hfc.mem
    have hsn : s ∉ Z := fun h ↦ hcase ⟨s, h, hm.mono (inter_subset_inter_left _ hfs)⟩
    have hc : c ∉ A.edgeSet := fun h ↦ hsn ((hcol hfc hs hfs).mpr h)
    rcases edge_cases hAB hfc.1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hc
    · exact h

/-- (8.1), with what the proof gives about `F`: all vertices of `Γ` on `F` are in `V(A ∩ B)`. -/
theorem theorem_8_1' (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (rad : RadialDrawing cap Γ) {A B : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B)
    [T2Space Shat] (hlt : (Hypergraph.separationOrder A B : ℕ∞) < Painting.rep rad)
    (hA : A.edgeSet.Nonempty) (hB : B.edgeSet.Nonempty) :
    ∃ (F : Drawing Shat) (Δ : Set Shat), F.IsCircuitOf rad.G ∧ (∀ e ∈ F.E, rad.Splits A B e) ∧
      IsClosedDisc Δ ∧ discBd Δ = F.U ∧
      (Γ.restrict (cap.emb ⁻¹' Δ) ≤ A ∨ Γ.restrict (cap.emb ⁻¹' Δ) ≤ B) ∧
      F.E.ncard / 2 ≤ Hypergraph.separationOrder A B ∧
      (∀ v, cap.emb v ∈ F.U → v ∈ Γ.V → v ∈ (A ∩ B).vertexSet) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ := rad.exists_full hS h2 h3.1
  have hDE := hD.E_nonempty hS h3.1
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := id rad.isPreRadial
  let t : Set S → Prop := (· ∈ A.edgeSet)
  let Z : Set (Set Shat) := colourSet cap Γ G₃ t
  have hZ : Z ⊆ G₃.R := fun _ h ↦ h.1
  let N : Drawing Shat := boundaryDrawing G₃ Z
  have hNs : N.IsSubdrawing G₃ := Drawing.span_isSubdrawing G₃ _ _
  have hreg : ∀ f, f ∈ arcComponentsIn (Γ.skU \ Γ.V) → ∃ s ∈ G₃.R, cap.emb '' f ⊆ s := by
    intro f hf
    have hg := (hD.edge_iff hS).mpr ⟨f, hf, rfl⟩
    have hdis : Disjoint (cap.emb '' f) G₃.U := by
      refine disjoint_left.mpr fun y hy hyU ↦ ?_
      have hyD := hg.2.1 hy
      have : y ∈ D.U ∩ G₃.U := ⟨hyD.1, hyU⟩
      rw [show D.U ∩ G₃.U = D.V from hrad.2.1] at this
      exact hyD.2 this
    obtain ⟨y, hy⟩ := hg.1
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem (disjoint_left.mp hdis hy)
    exact ⟨s, hs, subset_region hs hg.2.2.1.isConnected.isPreconnected hdis hy hys⟩
  have hcol : ∀ {f c s}, Γ.IsSkEdgeIn f c → s ∈ G₃.R → cap.emb '' f ⊆ s → (s ∈ Z ↔ c ∈ A.edgeSet)
    := by
    intro f c s hfc hs hfs
    constructor
    · rintro ⟨-, f', c', h', hf', ht⟩
      rw [(colour_unique hS hD hrad hmax hDE hs hfc h' hfs hf').2]
      exact ht
    · exact fun h ↦ ⟨hs, f, c, hfc, hfs, h⟩
  obtain ⟨ca, hca⟩ := hA
  obtain ⟨cb, hcb⟩ := hB
  have hcaE : ca ∈ Γ.E := hAB.left_le.edgeSet_subset hca
  have hcbE : cb ∈ Γ.E := hAB.right_le.edgeSet_subset hcb
  have hcbA : cb ∉ A.edgeSet := fun h ↦ by
    rcases edge_cases hAB hcbE with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h' hcb
    · exact h' h
  obtain ⟨e₀, he₀⟩ : ∃ e, e ∈ N.E := by
    obtain ⟨fa, hfa⟩ := Γ.exists_sk_in hcaE
    obtain ⟨fb, hfb⟩ := Γ.exists_sk_in hcbE
    obtain ⟨sa, hsa, hfsa⟩ := hreg fa hfa.mem
    obtain ⟨sb, hsb, hfsb⟩ := hreg fb hfb.mem
    have h₁ : sa ∈ Z := (hcol hfa hsa hfsa).mpr hca
    have h₂ : sb ∈ G₃.R \ Z := ⟨hsb, fun h ↦ hcbA ((hcol hfb hsb hfsb).mp h)⟩
    obtain ⟨xa, hxa⟩ : sa.Nonempty := region_nonempty hsa
    obtain ⟨xb, hxb⟩ : sb.Nonempty := region_nonempty hsb
    obtain ⟨e, he, -⟩ := exists_boundary_edge hT isOpen_univ isPreconnected_univ h₁ hZ h₂
      ⟨xa, hxa, mem_univ _⟩ ⟨xb, hxb, mem_univ _⟩
    exact ⟨e, he⟩
  have hbs : ∀ {e}, e ∈ N.E → _ := fun {e} he ↦
    boundary_split hS hDE rad hD hrad hmax hsub hhat (t := t) (e := e) he
  have hincX : ∀ {X : Hypergraph S (Set S)}, X ≤ Γ.toHypergraph → ∀ {c v}, c ∈ X.edgeSet →
      v ∈ Γ.V → v ∈ tilde c → v ∈ X.vertexSet := by
    intro X hX c v hc hv hvc
    have h₁ : v ∈ Γ.toHypergraph.ends c := ⟨hX.edgeSet_subset hc, hv, hvc⟩
    rw [hX.ends_eq c hc] at h₁
    exact X.vertex_mem_of_inc h₁
  have hcirc : ∀ C : Drawing Shat, C.IsCircuit → C.IsSubdrawing N →
      C.IsSubdrawing rad.G ∧ (∀ e ∈ C.E, rad.Splits A B e) ∧ C.E.ncard / 2 ≤
        Hypergraph.separationOrder A B ∧
      ∀ x ∈ C.V, x ∈ D.V → ∃ v₀, x = cap.emb v₀ ∧ v₀ ∈ (A ∩ B).vertexSet := by
    intro C hC hCs
    have hCG := hCs.trans hNs
    have hat : ∀ x ∈ C.V, ∃ g ∈ C.E, x ∈ closure g ∩ G₃.V := fun x hx ↦ by
      obtain ⟨g, hg, hxg⟩ := exists_edge_at_vertex hC hx
      exact ⟨g, hg, hxg, hCG.1 hx⟩
    have hmid : ∀ x ∈ C.V, x ∈ D.V → ∃ v₀, x = cap.emb v₀ ∧ v₀ ∈ (A ∩ B).vertexSet := by
      intro x hx hxD
      obtain ⟨g, hg, hxg⟩ := hat x hx
      obtain ⟨-, v₀, w, hv₀, hw, hset, f₁, f₂, c₁, c₂, hp, h₁, h₂, ht₁, ht₂, hnt⟩ := hbs (hCs.2 hg)
      rw [hset] at hxg
      have hxv : x = cap.emb v₀ := by
        rcases hxg with h | h
        · exact h
        · exact absurd (by rw [hD.hV] at hxD; exact h ▸ hxD) hw.2
      have hc₁ : v₀ ∈ tilde c₁ :=
        ⟨closure_mono h₁.subset ht₁.1, fun h ↦ Γ.disjoint_V h₁.1 h hv₀⟩
      have hc₂ : v₀ ∈ tilde c₂ :=
        ⟨closure_mono h₂.subset ht₂.1, fun h ↦ Γ.disjoint_V h₂.1 h hv₀⟩
      refine ⟨v₀, hxv, ?_⟩
      have e₁ := edge_cases hAB h₁.1
      have e₂ := edge_cases hAB h₂.1
      have hnt' : ¬ (c₁ ∈ A.edgeSet ↔ c₂ ∈ A.edgeSet) := hnt
      by_cases ha₁ : c₁ ∈ A.edgeSet
      · have hb₂ : c₂ ∈ B.edgeSet := by tauto
        exact ⟨hincX hAB.left_le ha₁ hv₀ hc₁, hincX hAB.right_le hb₂ hv₀ hc₂⟩
      · have hb₁ : c₁ ∈ B.edgeSet := by tauto
        have ha₂ : c₂ ∈ A.edgeSet := by tauto
        exact ⟨hincX hAB.left_le ha₂ hv₀ hc₂, hincX hAB.right_le hb₁ hv₀ hc₁⟩
    refine ⟨⟨fun x hx ↦ ?_, fun e he ↦ (hbs (hCs.2 he)).1⟩, fun e he ↦ ?_, ?_, hmid⟩
    · obtain ⟨g, hg, hxg⟩ := hat x hx
      obtain ⟨-, v₀, w, hv₀, hw, hset, -⟩ := hbs (hCs.2 hg)
      rw [hset] at hxg
      rcases hxg with rfl | rfl
      · exact hG2 (mem_image_of_mem _ hv₀)
      · exact hw.1
    · obtain ⟨-, v₀, w, hv₀, hw, hset, f₁, f₂, c₁, c₂, hp, h₁, h₂, ht₁, ht₂, hnt⟩ := hbs (hCs.2 he)
      exact (splits_of_pair hS h3 hp hAB).mpr hnt
    · have hb := IsCircuit.ncard_le hC (P := D.V) fun e x y hl ↦
        bipartite_of_preRadial hrad.2 e x y ((hCG.isLink_iff hl.1).mp hl)
      have hsubs : C.V ∩ D.V ⊆ cap.emb '' (A ∩ B).vertexSet := by
        rintro x ⟨hx, hxD⟩
        obtain ⟨v₀, rfl, hv₀⟩ := hmid x hx hxD
        exact mem_image_of_mem _ hv₀
      have hle₁ := ncard_le_ncard hsubs ((A ∩ B).vertexSet_finite.image _)
      have hle₂ := ncard_image_le (f := cap.emb) (A ∩ B).vertexSet_finite
      have : (C.V ∩ D.V).ncard ≤ Hypergraph.separationOrder A B := hle₁.trans hle₂
      omega
  have : Nonempty Shat := ⟨cap.emb (Classical.choose (show (tilde ca).Nonempty from by
    obtain ⟨f, hf⟩ := Γ.exists_sk_in hcaE
    rcases Γ.size_cases hcaE with h | h <;>
      exact Set.nonempty_of_ncard_ne_zero (by omega)))⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar G₃
  obtain ⟨C₀, hC₀, hC₀s, -⟩ := exists_circuit_of_even hγ hNs
    (fun v hv ↦ even_nHalf hT G₃ hγ hv Z) he₀
  obtain ⟨hC₀G, -, hcount, -⟩ := hcirc C₀ hC₀ hC₀s
  have hnull : IsNullHomotopicOArc C₀.U := by
    by_contra hn
    have hle : Painting.rep rad ≤ ((C₀.E.ncard / 2 : ℕ) : ℕ∞) :=
      sInf_le ⟨C₀, ⟨hC₀G, hC₀⟩, hn, rfl⟩
    have h₁ : ((C₀.E.ncard / 2 : ℕ) : ℕ∞) ≤ (Hypergraph.separationOrder A B : ℕ∞) := by
      exact_mod_cast hcount
    exact absurd (hlt.trans_le (hle.trans h₁)) (lt_irrefl _)
  have hbdS : Disjoint C₀.U (bd Shat) :=
    disjoint_left.mpr fun x _ hx ↦ hx (hT.2.2 x)
  obtain ⟨Δ₀, -, hΔ₀, hbd₀⟩ := (epstein Shat univ C₀.U (Surface.IsClosedSurface.isSurface hT)
    inferInstance
    (GM14.isOArc_of_isCircuit hC₀) (subset_univ _) hbdS).1 hnull
  obtain ⟨F, Δ, hFc, hFs, hΔ, hbd, hclean⟩ := exists_clean hT hZ hC₀ hC₀s hΔ₀ hbd₀
  obtain ⟨hFG, hFsplit, hFcount, hmid⟩ := hcirc F hFc hFs
  have hopen := hΔ.isOpen_discInt hman
  have hno : ∀ s₁ ∈ Z, ∀ s₂ ∈ G₃.R \ Z, (s₁ ∩ discInt Δ).Nonempty →
      (s₂ ∩ discInt Δ).Nonempty → False := by
    intro s₁ h₁ s₂ h₂ m₁ m₂
    obtain ⟨e, he, y, hye, hyi⟩ :=
      exists_boundary_edge hT hopen hΔ.isPreconnected_discInt h₁ hZ h₂ m₁ m₂
    exact disjoint_left.mp (hclean e he) hye hyi
  have hside : (∀ f c, Γ.IsSkEdgeIn f c → (cap.emb '' f ∩ discInt Δ).Nonempty → c ∈ A.edgeSet) ∨
      (∀ f c, Γ.IsSkEdgeIn f c → (cap.emb '' f ∩ discInt Δ).Nonempty → c ∈ B.edgeSet) := by
    exact edges_on_one_side_of_internal_disc (S := S) (Shat := Shat) (cap := cap) (Γ := Γ) (A :=
      A) (B := B) hAB G₃ Z hreg hcol Δ hno
  have hFU : ∀ {x}, x ∈ F.U → x ∈ rad.G.U := fun h ↦ hFG.U_subset h
  have hfinal : ∀ X : Hypergraph S (Set S), X ≤ Γ.toHypergraph →
      (∀ v, cap.emb v ∈ F.U → v ∈ Γ.V → v ∈ X.vertexSet) →
      (∀ f c, Γ.IsSkEdgeIn f c → (cap.emb '' f ∩ discInt Δ).Nonempty → c ∈ X.edgeSet) →
      Γ.restrict (cap.emb ⁻¹' Δ) ≤ X := by
    intro X hX hXm hXc
    have hedge : ∀ e ∈ (Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet, e ∈ X.edgeSet := by
      rintro c ⟨hc, hsubc, -⟩
      obtain ⟨f, hf⟩ := Γ.exists_sk_in hc
      obtain ⟨x, hx⟩ := hf.mem.1
      refine hXc f c hf ⟨_, mem_image_of_mem _ hx, hsubc (hf.subset hx), fun hb ↦ ?_⟩
      rw [hbd] at hb
      have : cap.emb x ∈ Γ.hatU cap ∩ rad.G.U :=
        ⟨mem_image_of_mem _ (Γ.skU_subset (hf.mem.2.1 hx).1), hFU hb⟩
      rw [hG1] at this
      obtain ⟨z, hz, hzx⟩ := this
      obtain rfl := cap.isEmbedding.injective hzx
      exact (hf.mem.2.1 hx).2 hz
    refine ⟨?_, hedge, ?_⟩
    · rintro v ⟨hv, hvΔ⟩
      by_cases hvF : cap.emb v ∈ F.U
      · exact hXm v hvF hv
      · have hvi : cap.emb v ∈ discInt Δ := ⟨hvΔ, fun hb ↦ hvF (hbd ▸ hb)⟩
        obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 rad hv
        have hvt : v ∈ tilde c := ⟨hvc, fun h ↦ Γ.disjoint_V hc h hv⟩
        obtain ⟨f, hf, hvf⟩ := Γ.exists_sk_at hc hvt
        have hcl : cap.emb v ∈ closure (cap.emb '' f) :=
          image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hvf.1)
        obtain ⟨w, hwi, hwf⟩ := mem_closure_iff.mp hcl _ hopen hvi
        exact hincX hX (hXc f c hf ⟨w, hwf, hwi⟩) hv hvt
    · intro e he
      rw [← hX.ends_eq e (hedge e he), (Γ.restrict_le _).ends_eq e he]
  have hmidF : ∀ v, cap.emb v ∈ F.U → v ∈ Γ.V → v ∈ (A ∩ B).vertexSet := by
    intro v hvF hv
    have hvG : cap.emb v ∈ rad.G.V := hG2 (mem_image_of_mem _ hv)
    have hvFV : cap.emb v ∈ F.V := by
      by_contra hn
      obtain ⟨e, he, hve⟩ := F.exists_edge_of_mem hvF hn
      exact ((hFG.2 he).2.1 hve).2 hvG
    obtain ⟨v₀, hv₀, hm⟩ := hmid _ hvFV (by rw [hD.hV]; exact mem_image_of_mem _ hv)
    obtain rfl := cap.isEmbedding.injective hv₀
    exact hm
  refine ⟨F, Δ, ⟨hFG, hFc⟩, hFsplit, hΔ, hbd, ?_, hFcount, hmidF⟩
  rcases hside with h | h
  · exact Or.inl (hfinal A hAB.left_le (fun v h₁ h₂ ↦ (hmidF v h₁ h₂).1) h)
  · exact Or.inr (hfinal B hAB.right_le (fun v h₁ h₂ ↦ (hmidF v h₁ h₂).2) h)

/-- **Graph Minors XIX, (8.1).** "**8.1.** *Let $(A, B)$ be a separation of $\Gamma$ of order
$< rep(\Gamma)$, with $E(A), E(B) \ne \emptyset$. Then there is a circuit $F$ of $\Gamma^*$ such
that $(A, B)$ splits every edge of $F$ and there is a disc $\Delta \subseteq \hat{\Sigma}$ bounded
by $U(F)$ such that either $\Gamma \cap \Delta \subseteq A$ or $\Gamma \cap \Delta \subseteq B$.*"

The paper counts valencies in the drawing of split edges. We use `N(Z)` of Graph Minors XI for the
regions `Z` of the colouring of this file, which has the same edges. Epstein's theorem gives the
first disc, from `rep(Γ)`. -/
theorem theorem_8_1_proof (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (rad : RadialDrawing cap Γ) {A B : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B)
    [T2Space Shat] (hlt : (Hypergraph.separationOrder A B : ℕ∞) < Painting.rep rad)
    (hA : A.edgeSet.Nonempty) (hB : B.edgeSet.Nonempty) :
    ∃ (F : Drawing Shat) (Δ : Set Shat), F.IsCircuitOf rad.G ∧ (∀ e ∈ F.E, rad.Splits A B e) ∧
      IsClosedDisc Δ ∧ discBd Δ = F.U ∧
      (Γ.restrict (cap.emb ⁻¹' Δ) ≤ A ∨ Γ.restrict (cap.emb ⁻¹' Δ) ≤ B) := by
  obtain ⟨F, Δ, h₁, h₂, h₃, h₄, h₅, -⟩ := theorem_8_1' hS h3 rad hAB hlt hA hB
  exact ⟨F, Δ, h₁, h₂, h₃, h₄, h₅⟩

end GraphMinor.GM19
