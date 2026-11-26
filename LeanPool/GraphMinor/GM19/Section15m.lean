/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15l
public import LeanPool.GraphMinor.GM19.Spokes

/-!
# Graph Minors XIX, (15.2): a radial drawing of the skeleton

The proof of (15.2) compares the metric of `Γ` with the metric of `sk(Γ)` in the sense of Graph
Minors XI. For this we need a radial drawing `G₃` of `sk(Γ)` that contains the radial drawing of
`Γ`, and we need that `G₃` has no more spokes than `Γ*` in the
regions of `Γ`. The paper does not say this. The reason is that a spoke of `G₃` in a region of `Γ`
could be added to `Γ*`, and `Γ*` is maximal (`RadialDrawing.mem_of_extension`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

/-- A spoke that bounds no disc with another spoke can be added to a maximal pre-radial drawing, so
it is already there. The proof follows `exists_spoke_of_line`. -/
theorem mem_of_spoke_line {T : Type} [TopologicalSpace T] [T2Space T] {U V : Set T} {G : Drawing T}
    (hpre : IsPreRadial U V G)
    (hmax : ∀ G' : Drawing T, IsPreRadial U V G' → G.IsSubdrawing G' → G'.IsSubdrawing G)
    {r : Set T} {c x : T} (hcr : c ∈ r) (hc : c ∈ G.V) (hx : x ∈ V)
    {K : Set T} (hK : IsLineWithEnds K c x) (hcx : c ≠ x) (hKr : K \ {c, x} ⊆ r)
    (hKU : Disjoint (K \ {c, x}) G.U) (hrU : Disjoint r U) (hVU : V ⊆ U)
    (hiv : ∀ f ∈ G.E, K \ {c, x} ≠ f → ∀ v ∈ V, ∀ r' ∈ componentsIn Uᶜ, ∀ w ∈ r' ∩ G.V,
      K ∩ G.V = {v, w} → closure f ∩ G.V = {v, w} →
      ¬ ∃ Δ : Set T, IsClosedDisc Δ ∧ Δ ⊆ r' ∪ {v} ∧ subBd Δ = K ∪ closure f) :
    K \ {c, x} ∈ G.E := by
  exact mem_spoke_line_of_no_bounded_disc hpre hmax hcr hc hx hK hcx hKr hKU hrU hVU hiv

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]

omit [T2Space S] in
/-- **A spoke of a radial drawing of `sk(Γ)` in a region of `Γ` is already a spoke of `Γ*`.** -/
theorem RadialDrawing.mem_of_extension {cap : IsCappedSurface S Shat} {Γ : Painting S}
  (rad : RadialDrawing cap Γ) {H G₃ : Drawing Shat} (hH : IsSkHat cap Γ H)
    (hpre : PreRad (PaintingOrDrawing.drawing H) G₃) (hsub : rad.G.IsSubdrawing G₃) {e r : Set
      Shat} (he : e ∈ G₃.E) (hr : r ∈ Γ.hatRegions cap) (her : e ⊆ r) : e ∈ rad.G.E := by
  classical
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  by_contra heG
  have hhat : ∀ x ∈ Γ.hatRegions cap, Disjoint x (Γ.hatU cap) := by
    rintro _ ⟨y, hy, rfl⟩
    exact disjoint_left.mpr fun z hz hzU ↦ connectedComponentIn_subset _ _ hz hzU
  have hrH := hH.hatRegion_mem_R hr
  obtain ⟨v, hv, r', hr', w, hw, hwV, hset, hsubr⟩ := GM11.spoke_ends hpre hT he
  have hrr : r' = r := by
    obtain ⟨y, hy⟩ := he.1
    exact GM11.region_eq_of_mem hr' hrH (hsubr hy) (her hy)
  subst hrr
  obtain ⟨w₀, ⟨hw₀r, hw₀⟩, -⟩ := rad.isPreRadial.2.2.1 r' hr
  have hww : w = w₀ := (hpre.2.2.2.1 r' hrH).unique ⟨hw, hwV⟩ ⟨hw₀r, hsub.1 hw₀⟩
  subst hww
  have hvhat : v ∈ Γ.hatV cap := by
    rw [hH.hV] at hv
    exact hv
  have hwv : w ≠ v := fun h => GM11.region_subset hr' hw (H.V_subset_U (h ▸ hv))
  have hK : IsLineWithEnds (closure e) w v :=
    GM11.isLine_closure he hwv (by rwa [pair_comm])
  have heV : ∀ y ∈ e, y ∉ G₃.V := fun y hy => (he.2.1 hy).2
  have hKsd : closure e \ {w, v} = e := by
    apply Subset.antisymm
    · rintro y ⟨hy, hyn⟩
      rcases closure_edge_subset he hy with h₁ | h₁
      · exact h₁
      · have h₂ : y ∈ closure e ∩ G₃.V := ⟨hy, h₁⟩
        rw [hset] at h₂
        exact absurd (show y ∈ ({w, v} : Set Shat) by rw [pair_comm]; exact h₂) hyn
    · intro y hy
      refine ⟨subset_closure hy, fun hyn => heV y hy ?_⟩
      rcases hyn with rfl | hyn
      · exact hwV
      · rw [mem_singleton_iff.mp hyn]
        exact hpre.2.2.1 hv
  have hKU : Disjoint (closure e \ {w, v}) rad.G.U := by
    rw [hKsd]
    refine disjoint_left.mpr fun y hy hyG ↦ ?_
    have hyV : y ∉ rad.G.V := fun hc ↦ heV y hy (hsub.1 hc)
    obtain ⟨f, hf, hyf⟩ := exists_arcComp_superset (F := rad.G.U \ rad.G.V)
      (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hyG, hyV⟩)
    exact heG (arcComp_eq_of_mem he (hsub.2 hf) hy (hyf rfl) ▸ hf)
  have hKV : closure e ∩ rad.G.V = closure e ∩ G₃.V := by
    apply Subset.antisymm (inter_subset_inter_right _ hsub.1)
    rw [hset]
    rintro y (rfl | hyn)
    · exact ⟨(hset ▸ (.inl rfl : y ∈ ({y, w} : Set Shat)) : y ∈ closure e ∩ G₃.V).1,
        rad.isPreRadial.2.1 hvhat⟩
    · rw [mem_singleton_iff.mp hyn]
      exact ⟨(hset ▸ (.inr rfl : w ∈ ({v, w} : Set Shat)) : w ∈ closure e ∩ G₃.V).1, hw₀⟩
  have hmem := mem_of_spoke_line rad.isPreRadial rad.maximal hw hw₀ hvhat hK hwv
    (by rwa [hKsd]) hKU (hhat _ hr) (image_mono Γ.V_subset) ?_
  · rw [hKsd] at hmem
    exact heG hmem
  rw [hKsd]
  intro f hf hef v' hv' r₂ hr₂ w' hw' hee hfe hΔ
  have hv'H : v' ∈ H.V := by
    rw [hH.hV]
    exact hv'
  have hr₂H := hH.hatRegion_mem_R hr₂
  have hee' : closure e ∩ G₃.V = {v', w'} := hKV ▸ hee
  have hfe' : closure f ∩ G₃.V = {v', w'} := by
    obtain ⟨v₂, hv₂, w₂, ⟨hw₂V, hw₂n⟩, hc⟩ := hpre.2.2.2.2.2.1 f (hsub.2 hf)
    have h₁ : v' ∈ closure f ∩ G₃.V := by
      have : v' ∈ closure f ∩ rad.G.V := hfe ▸ .inl rfl
      exact ⟨this.1, hsub.1 this.2⟩
    have h₂ : w' ∈ closure f ∩ G₃.V := by
      have : w' ∈ closure f ∩ rad.G.V := hfe ▸ .inr rfl
      exact ⟨this.1, hsub.1 this.2⟩
    have hw'H : w' ∉ H.V := fun h => GM11.region_subset hr₂H hw'.1 (H.V_subset_U h)
    rw [hc] at h₁ h₂ ⊢
    have e₁ : v' = v₂ := h₁.resolve_right fun h => hw₂n (mem_singleton_iff.mp h ▸ hv'H)
    have e₂ : w' = w₂ := h₂.resolve_left fun h => hw'H (h ▸ hv₂)
    rw [e₁, e₂]
  exact hpre.2.2.2.2.2.2 e he f (hsub.2 hf) hef v' hv'H r₂ hr₂H w' ⟨hw'.1,
    hsub.1 hw'.2⟩ hee' hfe' hΔ

omit [T2Space S] in
/-- **A radial drawing of `sk(Γ)` that extends `Γ*`.** -/
theorem TangleDatum.exists_skData {α : Type w} {χ : ColourScheme S α} {cap : IsCappedSurface S
  Shat} (D : TangleDatum cap χ) (h2 : ∀ r ∈ D.P.Γ.hatRegions cap, IsOpenDisc r) :
    ∃ H G₃, D.SkData H G₃ := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨H, W, hDU, hDV, hD2, -, hG'⟩ := D.P.Γ.exists_hubDrawing hS cap h2
  have hD : IsSkHat cap D.P.Γ H := ⟨hDU, hDV⟩
  obtain ⟨G', hpre, hU', hV', hE'⟩ := hG' D.rad.G D.rad.isPreRadial
  have hGsub : D.rad.G.IsSubdrawing G' := ⟨by rw [hV']; exact subset_union_left, by rw [hE']⟩
  let A : Set ℕ := {n | ∃ G₄ : Drawing Shat, (GM11.PaintingOrDrawing.drawing H).IsPreRadialDrawing
    G₄ ∧ G'.IsSubdrawing G₄ ∧ G₄.E.ncard = n}
  have hAne : A.Nonempty := ⟨_, G', hpre, ⟨subset_rfl, subset_rfl⟩, rfl⟩
  have hAb : BddAbove A := ⟨H.V.ncard + 2 * H.E.ncard, by
    rintro _ ⟨G₄, h₄, -, rfl⟩
    exact GM11.ncard_spokes_le (Γ := H) (Γ' := G₄) ⟨hD2, h₄⟩ hT⟩
  obtain ⟨G₃, hpre₃, hsub₃, hc₃⟩ := Nat.sSup_mem hAne hAb
  have hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing H) G₃ := ⟨hD2, hpre₃⟩
  have hmax : GM11.RadMax (GM11.PaintingOrDrawing.drawing H) G₃ := by
    intro G₄ h₄ hs
    refine ⟨fun y hy ↦ ?_, ?_⟩
    · by_cases hyV : y ∈ H.V
      · exact hpre₃.2.1 hyV
      obtain ⟨p, hp, hyp⟩ := h₄.2.2.2.1 y ⟨hy, hyV⟩
      obtain ⟨y', ⟨hy'p, hy'⟩, -⟩ := hpre₃.2.2.1 p hp
      rw [(h₄.2.2.1 p hp).unique ⟨hyp, hy⟩ ⟨hy'p, hs.1 hy'⟩]
      exact hy'
    · have hle : G₄.E.ncard ≤ G₃.E.ncard := by
        rw [hc₃]
        exact le_csSup hAb ⟨G₄, h₄, ⟨hsub₃.1.trans hs.1, hsub₃.2.trans hs.2⟩, rfl⟩
      exact (eq_of_subset_of_ncard_le hs.2 hle G₄.finite_edges).ge
  have hsub : D.rad.G.IsSubdrawing G₃ := ⟨hGsub.1.trans hsub₃.1, hGsub.2.trans hsub₃.2⟩
  exact ⟨H, G₃, hD, hrad, hmax, hsub, fun e he r hr her => D.rad.mem_of_extension hD hrad hsub
    he hr her⟩

end GraphMinor.GM19
