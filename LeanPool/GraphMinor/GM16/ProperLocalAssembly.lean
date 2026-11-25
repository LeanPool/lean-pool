/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement
import LeanPool.GraphMinor.GM16.ProperDiscIntersection
import LeanPool.GraphMinor.GM16.ProperDiscTransport
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.ProperBridgeIntersections
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

import LeanPool.GraphMinor.GM09.Bridge

/-!
# The proper arrangement in the proof of XVI (7.2)

We retain the arrangement constructed in XV (7.7), pages 139–142.
A large society belongs to one of its local segregations, each of which
has at most one large society. Distinct local pieces have disjoint vertex
sets by XV (7.6), so their large societies have disjoint boundary sets.
This proves the properness asserted in XVI, page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

/-- The construction of XV (7.7), pages 139–142, gives a proper arrangement,
as observed in XVI (7.2), page 62. Its claims (1)–(9) build the segregation
and arrangement. Properness then follows from XV (7.6) and the fact that
each local segregation has at most one society with more than three ends. -/
theorem exists_proper_arrangement_of_no_crooked_transactions
     :
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 100 * beta ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    (∀ i : Fin k, ∀ P_set : Set (Graph α β),
      (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    ∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
      IsCentralSegregation G T_star 𝒮 ∧
      GM15.IsSegregationOfType G (3 * π + 9) k 𝒮 ∧ IsProperArrangement 𝒮 disc pt := by
  classical
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hθ_bound : 2 * (θ' + 12 * μ + 14) + μ ≤ θ := by omega
  have hDisj_star : Pairwise (fun i j : Fin k => Disjoint V((D i).localSociety.G) V((D
    j).localSociety.G))
    :=
    theorem_7_6_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
      hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist hη₀_v hThree hArr₀ hCompat₀ hDisj_Δ
  let G₀ := section7G0 G H η d θ' μ r
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hJi_le : ∀ i : Fin k, eyeBridgeUnion G H η d θ' μ (r i) ≤ G :=
    fun _ => subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPi_le : ∀ i : Fin k, arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G :=
    fun _ => (restrict_le.trans (G₀.induce_le inter_subset_right)).trans hG₀_le
  have hstar_le : ∀ i : Fin k, (D i).localSociety.G ≤ G := by
    intro i
    rw [(D i).soc_star_G]
    exact subgraphUnion_le (hJi_le i) (hPi_le i)
  -- For each `i : Fin k`, apply (6.1) (`theorem_6_1_proof`) and transport to `(D i).Δ`.
  have hex_i : ∀ i : Fin k,
      ∃ (S_seg_i : Set (Society α β)) (α_disc_i : Society α β → Set S) (α_pt_i : α → S),
        GM15.IsSegregationOfType (D i).localSociety.G (3 * π + 9) 1 S_seg_i ∧
        (D i).localSociety.Ω.bar ⊆ segregationVertices S_seg_i ∧
        (∀ v ∈ (D i).localSociety.Ω.bar, α_pt_i v = α₀_pt v) ∧
        (∀ v ∈ segregationVertices S_seg_i, α_pt_i v ∈ (D i).Δ) ∧
        (∀ v ∈ segregationVertices S_seg_i, v ∉ (D i).localSociety.Ω.bar →
          α_pt_i v ∈ (D i).Δ \ subBd (D i).Δ) ∧
        InjOn α_pt_i (segregationVertices S_seg_i) ∧
        (∀ B ∈ S_seg_i, IsClosedDisc (α_disc_i B) ∧ α_disc_i B ⊆ (D i).Δ ∧
          ∀ x ∈ B.Ω.bar, α_pt_i x ∈ subBd (α_disc_i B)) ∧
        (∀ B ∈ S_seg_i, IsNaturalOrderFrom α_pt_i B.Ω (subBd (α_disc_i B))) ∧
        (∀ B ∈ S_seg_i, α_disc_i B ∩ subBd (D i).Δ ⊆ α_pt_i '' (B.Ω.bar ∩
          (D i).localSociety.Ω.bar)) ∧
        (∀ B₁ ∈ S_seg_i, ∀ B₂ ∈ S_seg_i, B₁ ≠ B₂ →
          α_disc_i B₁ ∩ α_disc_i B₂ ⊆ α_pt_i '' (B₁.Ω.bar ∩ B₂.Ω.bar)) := by
    intro i
    obtain ⟨S_seg_i, m, A₀_i, A_i, Δ_E, α₀_E, α_disc_E, α_pt_E,
        hS_eq, hType_i, hBar_i, hDiscArr_i⟩ :=
      GM15.theorem_6_1_proof (D i).localSociety π hπ2 hπ3 (hno_crooked i)
    subst hS_eq
    have hinj_bar_i : InjOn α₀_pt (D i).localSociety.Ω.bar :=
      hArr₀.injOn_pts.mono (fun v hv => ((D i).soc_star_Ω.1 ▸ hv).1)
    obtain ⟨α_disc_S, α_pt_S, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_surface_disc_arrangement_of_isDiscArrangement hS (D i).localSociety A₀_i A_i
        Δ_E α₀_E α_disc_E α_pt_E hBar_i hDiscArr_i (D i).Δ (D i).isClosedDisc_Δ
        α₀_pt hinj_bar_i (D i).soc_star_Ω.2
    exact ⟨insert A₀_i (range A_i), α_disc_S, α_pt_S, hType_i, hBar_i,
      h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose S_seg α_disc_i α_pt_i hType_i hBar_i hpt_i_eq_0 hpt_i_mem_Δ hpt_i_mem_int
    hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i using hex_i
  have hseg_i_sub_V : ∀ i : Fin k, segregationVertices (S_seg i) ⊆ V((D i).localSociety.G) := by
    intro i v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    exact ((hType_i i).1.le B hB).vertexSet_mono (B.bar_subset hvB)
  -- Define `S'`, `S_seg' i`, and `S_final`.
  let S' : Set (Society α β) := {A ∈ S₀ | ∀ i : Fin k, ¬ α₀_disc A ⊆ (D i).Δ}
  let S_seg' : Fin k → Set (Society α β) := fun i =>
    {B ∈ S_seg i | V(B.G).Nonempty ∧ B ∉ S'}
  let S_final : Set (Society α β) := S' ∪ ⋃ i : Fin k, S_seg' i
  have hDisj_S'_seg' : ∀ i : Fin k, Disjoint S' (S_seg' i) :=
    fun i => Set.disjoint_left.mpr fun _ hS' hseg' => hseg'.2.2 hS'
  have hDisj_seg' : Pairwise (fun i j : Fin k => Disjoint (S_seg' i) (S_seg' j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun B hBi hBj => ?_
    obtain ⟨v, hv⟩ := hBi.2.1
    exact Set.disjoint_left.mp (hDisj_star hij)
      (((hType_i i).1.le B hBi.1).vertexSet_mono hv)
      (((hType_i j).1.le B hBj.1).vertexSet_mono hv)
  -- Claim (2): `S_final` is a graph segregation of `G`.
  have hFin₀ : S'.Finite := hThree.1.finite.subset fun _ h => h.1
  have hFin_eye (i : Fin k) : (S_seg' i).Finite := (hType_i i).1.finite.subset fun _ h => h.1
  have hFin_final : S_final.Finite := hFin₀.union (finite_iUnion hFin_eye)
  have hLe_final : ∀ B ∈ S_final, B.G ≤ G := by
    rintro B (hB_S' | hB_i)
    · exact (hThree.1.le B hB_S'.1).trans hG₀_le
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      exact ((hType_i i).1.le B hBi.1).trans (hstar_le i)
  have hCover_star_V : ∀ (i : Fin k) {v : α}, v ∈ V((D i).localSociety.G) →
      ∃ B ∈ S_final, v ∈ V(B.G) := by
    intro i v hv
    have hv_u : v ∈ V(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact hv
    rw [vertexSet_subgraphSUnion] at hv_u
    obtain ⟨_, ⟨B, hB, rfl⟩, hvB⟩ := mem_iUnion₂.mp hv_u
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', hvB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨v, hvB⟩, hB_S'⟩), hvB⟩
  have hCover_star_E : ∀ (i : Fin k) {e : β}, e ∈ E((D i).localSociety.G) →
      ∃ B ∈ S_final, e ∈ E(B.G) := by
    intro i e he
    have he_u : e ∈ E(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact he
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact (hType_i i).1.le B hB)] at he_u
    obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp he_u
    obtain ⟨x, _, hxy⟩ := B.G.exists_isLink_of_mem_edgeSet heB
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', heB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨x, hxy.left_mem⟩, hB_S'⟩), heB⟩
  have hClaim2 : IsGraphSegregation G S_final := by
    exact assemble_eye_segregation (S := S) (α := α) (β := β) G H η θ_star θ θ' π beta μ k T_star
      T d r η₀ S₀ α₀_disc α₀_pt D hη₀_v hThree hArr₀ hCompat₀ hS hDisj_star hPair_le hJi_le
      hPi_le hstar_le S_seg hType_i hBar_i hFin_final hLe_final hCover_star_V
      hCover_star_E
  -- Claim (3): `S_final` is of type `(3 * π + 9, k)`.
  have hClaim3 : GM15.IsSegregationOfType G (3 * π + 9) k S_final := by
    refine ⟨hClaim2, ?_, ?_⟩
    · let F : Fin k → Set (Society α β) := fun i => {B ∈ S_seg i | 3 < B.Ω.bar.ncard}
      have hsub : {B ∈ S_final | 3 < B.Ω.bar.ncard} ⊆ ⋃ i : Fin k, F i := by
        rintro B ⟨hB_S' | hB_i, hgt⟩
        · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
        · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
          exact mem_iUnion.mpr ⟨i, hBi.1, hgt⟩
      have hfin_u : (⋃ i : Fin k, F i).Finite :=
        finite_iUnion fun i => (hType_i i).1.finite.subset fun _ h => h.1
      exact (ncard_le_ncard hsub hfin_u).trans
        (ncard_iUnion_le_of_ncard_le_one k F (fun i => (hType_i i).vortex_count_le))
    · rintro B (hB_S' | hB_i) hgt
      · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        exact (hType_i i).is_p_vortex hBi.1 hgt
  -- Claim (4): `S_final` is `T_star`-central.
  have hClaim4 : IsCentralSegregation G T_star S_final := by
    exact assembled_eye_segregation_is_central (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π
      beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D hFlat hMetric hμ1 hπ2 hbeta_eq hθ_ge hr_eye
      hη₀_v hη₀_e hThree hLocal hCompat₀ hS hθ_bound hJi_le hPi_le S_seg hType_i
       hClaim3
  -- Define `α_disc` and `α_pt` and prove Claims (5)–(9).
  let α_disc : Society α β → Set S := fun B =>
    if h : ∃ i : Fin k, B ∈ S_seg' i then α_disc_i (Classical.choose h) B else α₀_disc B
  let α_pt : α → S := fun v =>
    if h : ∃ i : Fin k, v ∈ segregationVertices (S_seg i) then α_pt_i (Classical.choose h) v
    else α₀_pt v
  have hα_disc_S' : ∀ {B : Society α β}, B ∈ S' → α_disc B = α₀_disc B := by
    intro B hB
    have hnot : ¬ ∃ i : Fin k, B ∈ S_seg' i := by
      rintro ⟨i, hBi⟩
      exact Set.disjoint_left.mp (hDisj_S'_seg' i) hB hBi
    simp [α_disc, hnot]
  have hα_disc_seg' : ∀ (i : Fin k) {B : Society α β}, B ∈ S_seg' i → α_disc B = α_disc_i i B := by
    intro i B hBi
    have hex : ∃ j : Fin k, B ∈ S_seg' j := ⟨i, hBi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_seg' hne) (Classical.choose_spec hex) hBi
    simp [α_disc, hex, hij]
  -- Claim (5): For `i : Fin k`, if `v ∈ segregationVertices (S_seg i)` then `α_pt v = α_pt_i i v`.
  have hClaim5 : ∀ (i : Fin k) {v : α}, v ∈ segregationVertices (S_seg i) →
      α_pt v = α_pt_i i v := by
    intro i v hvi
    have hex : ∃ j : Fin k, v ∈ segregationVertices (S_seg j) := ⟨i, hvi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_star hne)
        (hseg_i_sub_V _ (Classical.choose_spec hex)) (hseg_i_sub_V i hvi)
    simp [α_pt, hex, hij]
  have hα_pt_S' : ∀ {v : α}, v ∈ segregationVertices S' → α_pt v = α₀_pt v := by
    intro v hv_S'
    by_cases hex : ∃ i : Fin k, v ∈ segregationVertices (S_seg i)
    · obtain ⟨i, hvi⟩ := hex
      rw [hClaim5 i hvi]
      obtain ⟨A, hA_S', hvA⟩ := mem_iUnion₂.mp hv_S'
      have hv_bar_star : v ∈ (D i).localSociety.Ω.bar :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
          ⟨hseg_i_sub_V i hvi, A.bar_subset hvA⟩
      exact hpt_i_eq_0 i v hv_bar_star
    · simp [α_pt, hex]
  -- Claims (6)–(9): `(S_final, α_disc, α_pt)` is a surface arrangement in `S`.
  have hArr_final : IsSurfaceArrangement S_final α_disc α_pt := by
    exact arrange_replacement_societies (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π beta μ
      k T_star T d r S₀ α₀_disc α₀_pt D hFlat hArr₀ hDisj_Δ hS S_seg α_disc_i α_pt_i hBar_i
      hpt_i_eq_0 hpt_i_mem_Δ hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i
       α_disc α_pt hα_disc_S' hα_disc_seg' hClaim5 hα_pt_S'
  refine ⟨S_final, α_disc, α_pt, hClaim4, hClaim3,
    IsSurfaceArrangement.isProper_of_disjoint_boundaries hArr_final ?_⟩
  intro A hA B hB hne hlargeA hlargeB
  have hLargeLocal : ∀ C ∈ S_final, 3 < C.Ω.bar.ncard → ∃ i, C ∈ S_seg' i := by
    intro C hC hlarge
    rcases hC with hC | hC
    · exact (not_lt_of_ge (hThree.2 C hC.1) hlarge).elim
    · exact mem_iUnion.mp hC
  obtain ⟨i, hAi⟩ := hLargeLocal A hA hlargeA
  obtain ⟨j, hBj⟩ := hLargeLocal B hB hlargeB
  have hij : i ≠ j := by
    intro hij
    subst j
    have hfin : {C ∈ S_seg i | 3 < C.Ω.bar.ncard}.Finite :=
      (hType_i i).1.finite.subset fun _ h => h.1
    exact hne ((Set.ncard_le_one hfin).mp (hType_i i).vortex_count_le A
      ⟨hAi.1, hlargeA⟩ B ⟨hBj.1, hlargeB⟩)
  exact (hDisj_star hij).mono
    (fun _ hv => ((hType_i i).1.le A hAi.1).vertexSet_mono (A.bar_subset hv))
    (fun _ hv => ((hType_i j).1.le B hBj.1).vertexSet_mono (B.bar_subset hv))

end GraphMinor.GM16
