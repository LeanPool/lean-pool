/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Feasibility
public import LeanPool.GraphMinor.GM19.Section15e

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Graph Minors XIX, (15.2)

We apply (3.2) of Graph Minors XII to `sk(Γ)` and the discs of `exists_discFamily`. The connected
subdrawings it gives, with the edges `β(e)`, are an inflation of `(Γ₀, φ₀)` in `(Γ, φ)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- All the ends of the edges `β(e)`. -/
def allEnds (cap : IsCappedSurface S Shat) (P₀ : ColouredPainting χ) (b : Set S → Set S) : Set Shat
  :=
  cap.emb '' ⋃ e ∈ P₀.Γ.E, tilde (b e)

variable (hM : D.IsMatchSetting P₀ n b)
include hM

omit [T2Space S] in
theorem IsMatchSetting.ncard_allEnds_le : (allEnds cap P₀ b).ncard ≤ 3 * P₀.Γ.E.ncard := by
  classical
  have hfin := P₀.Γ.finite_edges
  let t : Set S → Finset S := fun e => ((D.P.Γ.finite_V.inter_of_right (tilde (b e)))).toFinset
  have ht : ∀ e ∈ hfin.toFinset, (t e).card ≤ 3 := fun e he => by
    have he' : e ∈ P₀.Γ.E := hfin.mem_toFinset.mp he
    have hbm := hM.edge.mem e he'
    have h₁ : (tilde (b e) ∩ D.P.Γ.V).ncard ≤ (tilde (b e)).ncard := ncard_le_ncard
      inter_subset_left (D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V hbm))
    have h₂ : (tilde (b e)).ncard ≤ 3 := by
      rcases D.P.Γ.size_cases hbm with h | h <;> omega
    have h₃ : (t e).card = (tilde (b e) ∩ D.P.Γ.V).ncard := (Set.ncard_eq_toFinset_card _ _).symm
    omega
  have hcard := Finset.card_biUnion_le_card_mul hfin.toFinset t 3 ht
  have hsub : (⋃ e ∈ P₀.Γ.E, tilde (b e)) ⊆ ↑(hfin.toFinset.biUnion t) := fun y hy => by
    obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨e, hfin.mem_toFinset.mpr he,
      (Set.Finite.mem_toFinset _).mpr ⟨hy, D.P.Γ.tilde_subset_V (hM.edge.mem e he) hy⟩⟩)
  have h₁ : (allEnds cap P₀ b).ncard ≤ (⋃ e ∈ P₀.Γ.E, tilde (b e)).ncard := ncard_image_le
    ((Finset.finite_toSet _).subset hsub)
  have h₂ := ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h₂
  have h₃ : hfin.toFinset.card = P₀.Γ.E.ncard := (Set.ncard_eq_toFinset_card _ _).symm
  rw [h₃] at hcard
  omega

theorem IsMatchSetting.iUnion_discEnds (hS : IsSurface S) : ⋃ i, discEnds cap b P₀ i
  = allEnds cap P₀ b := by
  apply Subset.antisymm
  · refine iUnion_subset ?_
    rintro (Θ | e)
    · rintro _ ⟨y, ⟨e, he, -, hy⟩, rfl⟩
      exact mem_image_of_mem _ (mem_biUnion he hy)
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_image_of_mem _ (mem_biUnion e.2.1 hy)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
    by_cases hi : Painting.IsInternal e
    · exact mem_iUnion.mpr ⟨.inr ⟨e, he, hi⟩, mem_image_of_mem _ hy⟩
    · obtain ⟨s, -, Θ, hΘ, hsΘ, hes, -, -⟩ := hM.exists_cuff_of_border hS he
        (not_disjoint_iff_nonempty_inter.mp hi)
      exact mem_iUnion.mpr ⟨.inl ⟨Θ, hΘ⟩, mem_image_of_mem _ ⟨e, he, hes.trans hsΘ, hy⟩⟩

omit [T2Space S] [T2Space Shat] hM in
theorem IsMatchSetting.endClass_of_getElem {e : Set S} (he : e ∈ P₀.Γ.E) {i : ℕ} (hi : i <
  (P₀.Γ.γ e).length) (hi' : i < (D.P.Γ.γ (b e)).length) :
    cap.emb (D.P.Γ.γ (b e))[i] ∈ endClass cap P₀ D.P b (P₀.Γ.γ e)[i] :=
  mem_image_of_mem _ ⟨e, he, i, hi, hi', rfl, rfl⟩

omit [T2Space S] in
theorem IsMatchSetting.length_eq {e : Set S} (he : e ∈ P₀.Γ.E) : (P₀.Γ.γ e).length = (D.P.Γ.γ
  (b e)).length := by
  rw [P₀.Γ.length_γ_eq he, D.P.Γ.length_γ_eq (hM.edge.mem e he), hM.edge.size e he]

omit [T2Space S] [TopologicalSpace Shat] [T2Space Shat] hM in
theorem IsMatchSetting.getElem_mem_V {e : Set S} (he : e ∈ P₀.Γ.E) {i : ℕ} (hi : i <
  (P₀.Γ.γ e).length) : (P₀.Γ.γ e)[i] ∈ P₀.Γ.V := by
  have : (P₀.Γ.γ e)[i] ∈ {v | v ∈ P₀.Γ.γ e} := List.getElem_mem hi
  rw [P₀.Γ.γ_set e he] at this
  exact P₀.Γ.tilde_subset_V he this

omit [T2Space S] in
theorem IsMatchSetting.iUnion_endClass : ⋃ v ∈ P₀.Γ.V, endClass cap P₀ D.P b v = allEnds cap P₀ b
  := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun v _ => ?_
    rintro _ ⟨y, ⟨e, he, i, hi, hi', -, rfl⟩, rfl⟩
    have hm : (D.P.Γ.γ (b e))[i] ∈ {v | v ∈ D.P.Γ.γ (b e)} := List.getElem_mem hi'
    rw [D.P.Γ.γ_set _ (hM.edge.mem e he)] at hm
    exact mem_image_of_mem _ (mem_biUnion he hm)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
    have hm : y ∈ {v | v ∈ D.P.Γ.γ (b e)} := by rwa [D.P.Γ.γ_set _ (hM.edge.mem e he)]
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hm
    have hi : i < (P₀.Γ.γ e).length := by rw [hM.length_eq he]; exact hi'
    exact mem_iUnion₂.mpr ⟨_, TangleDatum.IsMatchSetting.getElem_mem_V he hi,
      TangleDatum.IsMatchSetting.endClass_of_getElem he hi hi'⟩

theorem IsMatchSetting.endClass_nonempty (hS : IsSurface S) {v : S} (hv : v ∈ P₀.Γ.V) :
  (endClass cap P₀ D.P b v).Nonempty := by
  have h3 := P₀.fits.internally_three_connected
  obtain ⟨rad⟩ := h3.nonempty_radialDrawing hS cap
  obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 rad hv
  have hvt : v ∈ tilde c := ⟨hvc, fun h => P₀.Γ.disjoint_V hc h hv⟩
  have hm : v ∈ {x | x ∈ P₀.Γ.γ c} := by rwa [P₀.Γ.γ_set _ hc]
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  have hi' : i < (D.P.Γ.γ (b c)).length := by rw [← hM.length_eq hc]; exact hi
  exact ⟨_, TangleDatum.IsMatchSetting.endClass_of_getElem hc hi hi'⟩

end TangleDatum

/-- **Graph Minors XIX, (15.2)**, from (3.2) of Graph Minors XII. -/
theorem theorem_15_2_proof : Theorem152Statement.{w} := by
  classical
  intro S Shat _ _ _ _ β cap χ P₀
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have hconn : ConnectedSpace Shat := cap.connected
  have hfinI := TangleDatum.finite_discIndex hS P₀
  let eI := Finite.equivFin (TangleDatum.DiscIndex S P₀)
  obtain ⟨θ, hθ, hmain⟩ := GraphMinor.GM12.gm19_theorem32.{0} Shat hT hconn (Nat.card
    (TangleDatum.DiscIndex S P₀)) (3 * P₀.Γ.E.ncard)
  set z := 3 * P₀.Γ.E.ncard with hz
  let m := θ + z
  let n := 2 * (2 * m + 16 * θ + 20)
  have hlab : ∀ side, ∃ ω, side ∈ χ.Φ.longSides → IsBorderLabels P₀ side ω := fun side => by
    by_cases h : side ∈ χ.Φ.longSides
    · obtain ⟨ω, hω⟩ := exists_isBorderLabels hS P₀ h
      exact ⟨ω, fun _ => hω⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose ω hω using hlab
  refine ⟨n, by omega, ⟨2 * m + 16 * θ + 20, by omega⟩, ω, hω, fun D horient hno hrep => ?_⟩
  by_contra hall
  simp only [not_or] at hall
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hall
  have hfar : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → n < D.vDist r₁ r₂
    := fun r₁ hr₁ r₂ hr₂ hne => by
    by_contra hle
    exact h₁ ⟨r₁, hr₁, r₂, hr₂, hne, not_lt.mp hle⟩
  have hfree : ∀ C, ¬ D.IsFreeCircuit n C := fun C hC => h₂ ⟨C, hC⟩
  have hnr : n < D.rep := by omega
  have hrep4 : 4 ≤ D.rep := by omega
  have hmr : m ≤ D.rep := by omega
  have hro : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
  have h3m : 3 * m < 2 * D.ord + 3 := by omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨b, hb⟩ :=
    TangleDatum.exists_edgeMap ⟨2 * m + 16 * θ + 20, by omega⟩ hrep4 hω
      (fun side hs hc => h₃ ⟨side, hs, hc⟩) (fun f hf hi hc => h₄ ⟨f, hf, hi, hc⟩)
  have hM : D.IsMatchSetting P₀ n b := ⟨hb, by omega, hnr, hfree, hfar⟩
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨H, G₃, hd⟩ := D.exists_skData (h3.hatRegions_isOpenDisc hS cap)
  have hresp := D.isRespectful_skTangle hd hm1 hmr h3m
  obtain ⟨ins, hins⟩ := GM11.exists_derivedSlope hT hresp hd.pre.2
  have hσ : ∀ Θ, ∃ s, Θ ∈ cuffs S → s ∈ χ.Φ.shortSides ∧ s ⊆ Θ := fun Θ => by
    by_cases h : Θ ∈ cuffs S
    · obtain ⟨s, h₁, h₂⟩ := TangleDatum.exists_short_on_cuff (χ := χ) hS h
      exact ⟨s, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  obtain ⟨Δ, hA, hdisj, hsub, hsub₃⟩ := hM.exists_discFamily hS hd.sk (σ := σ) hσ
  have hUbd : ∀ i, H.V ∩ subBd (Δ i) = TangleDatum.discEnds cap b P₀ i := fun i =>
    (hA i).vertex_inter_subBd
  let Δ' : Fin (Nat.card (TangleDatum.DiscIndex S P₀)) → Set Shat := fun i => Δ (eI.symm i)
  have hVf : Finite P₀.Γ.V := P₀.Γ.finite_V
  let eV := Finite.equivFin P₀.Γ.V
  let Zs : Fin (Nat.card P₀.Γ.V) → Set Shat := fun j => TangleDatum.endClass cap P₀ D.P b
    (eV.symm j).1
  have hU₁ : (⋃ i, H.V ∩ subBd (Δ' i)) = TangleDatum.allEnds cap P₀ b := by
    rw [← hM.iUnion_discEnds hS, ← iUnion_congr hUbd]
    exact eI.symm.surjective.iUnion_comp fun i => H.V ∩ subBd (Δ i)
  have hU₂ : (⋃ j, Zs j) = TangleDatum.allEnds cap P₀ b := by
    rw [← hM.iUnion_endClass, biUnion_eq_iUnion]
    exact eV.symm.surjective.iUnion_comp fun v : P₀.Γ.V => TangleDatum.endClass cap P₀ D.P b v.1
  have hUΔ : (⋃ i, Δ' i) = ⋃ i, Δ i := eI.symm.surjective.iUnion_comp Δ
  have hallF : (TangleDatum.allEnds cap P₀ b).Finite :=
    (P₀.Γ.finite_edges.biUnion fun e he => D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V
      (hM.edge.mem e he))).image _
  obtain ⟨Dv, hD₁, hD₂, hD₃⟩ := theorem152Feasibility S Shat β cap χ P₀ D n b horient hM Δ (fun i
    => (hA i).disc) (fun i => (hA i).sub_bd) hdisj hsub hsub₃
  have hfe : GM12.IsTopologicallyFeasible Δ' Zs := by
    refine ⟨fun j => Dv (eV.symm j).1, fun j => hD₁ _ (eV.symm j).2, ?_, ?_⟩
    · intro i j hij
      exact hD₂ _ (eV.symm i).2 _ (eV.symm j).2 (fun h => hij (eV.symm.injective (Subtype.ext h)))
    · intro j
      rw [hUΔ]
      exact hD₃ _ (eV.symm j).2
  have hhalf : n / 2 = 2 * m + 16 * θ + 20 := by omega
  obtain ⟨H', hs', hc', hd', hV'⟩ := hmain Δ' H m (D.skTangle H m) (GM14.tangleMetric H G₃ ins m)
    (Nat.card P₀.Γ.V) Zs
    (fun i => ⟨(hA _).disc, by rw [hUbd]; exact (hA _).inter⟩)
    (fun i j hij => hdisj _ _ fun h => hij (eI.symm.injective h))
    (by rw [hU₁]; exact hM.ncard_allEnds_le)
    (hU₂.trans hU₁.symm)
    (fun j₁ j₂ h => hM.disjoint_endClass hS fun h' => h (eV.symm.injective (Subtype.ext h')))
    hfe (by omega)
    ⟨⟨hd.pre.1, D.isTangle_skTangle hd.sk hm1 h3m, hresp⟩, G₃, ins, ⟨hd.pre.1, hd.pre.2, hd.max⟩,
      hins, fun _ _ _ _ => rfl⟩
    (fun i j hij ri hri hmi rj hrj hmj => by
      have hl := hM.lt_dist_discAnchor hS hσ (eI.symm i) (eI.symm j) (fun h => hij
        (eI.symm.injective h))
      exact hd.le_skMetric hrep4 hmr hm1 h3m hins (by omega) (hA _) (hA _)
        (by omega) hri hmi hrj hmj)
    (fun i => by
      rw [hUbd]
      have hsubA : TangleDatum.discEnds cap b P₀ (eI.symm i) ⊆ TangleDatum.allEnds cap P₀ b := by
        rw [← hM.iUnion_discEnds hS]
        exact subset_iUnion _ _
      have hle := ncard_le_ncard hsubA hallF
      have := hM.ncard_allEnds_le
      exact hM.isFreeSet_discEnds hd hmr hm1 h3m hins (by omega) _ (hA _) (by omega))
  let Hv : S → Drawing Shat := fun v => if hv : v ∈ P₀.Γ.V then H' (eV ⟨v, hv⟩) else H
  have hHv : ∀ v (hv : v ∈ P₀.Γ.V), Hv v = H' (eV ⟨v, hv⟩) := fun v hv => dite_eq_left hv
  have hZ : ∀ v (hv : v ∈ P₀.Γ.V), TangleDatum.endClass cap P₀ D.P b v ⊆ (Hv v).V := fun v hv x hx
    => by
    rw [hHv v hv]
    have h := hV' (eV ⟨v, hv⟩)
    have hzs : Zs (eV ⟨v, hv⟩) = TangleDatum.endClass cap P₀ D.P b v := by
      change TangleDatum.endClass cap P₀ D.P b (eV.symm (eV ⟨v, hv⟩)).1 = _
      rw [Equiv.symm_apply_apply]
    rw [hzs] at h
    exact (h ▸ hx : x ∈ (H' (eV ⟨v, hv⟩)).V ∩ _).1
  refine hno ⟨_, _, isColouredInflation_of_subdrawings hS hd.sk hb Hv
    (fun v hv => ?_) (fun v hv => ?_) (fun v hv v' hv' hne => ?_) (fun v hv => ?_)
    (fun e he i hi hi' => ?_)⟩
  · rw [hHv v hv]
    exact hs' _
  · rw [hHv v hv]
    exact hc' _
  · rw [hHv v hv, hHv v' hv']
    exact hd' _ _ fun h => hne (congrArg Subtype.val (eV.injective h))
  · exact (hM.endClass_nonempty hS hv).mono (hZ v hv)
  · exact hZ _ (TangleDatum.IsMatchSetting.getElem_mem_V he hi)
      (TangleDatum.IsMatchSetting.endClass_of_getElem he hi hi')

end GraphMinor.GM19
