/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section9Parameters
import LeanPool.GraphMinor.GM16.SpanCongr
import LeanPool.GraphMinor.GM16.Section9Rigidity
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9ClearFamily
import LeanPool.GraphMinor.GM16.Section9SpanClearing
import LeanPool.GraphMinor.GM16.Section9Claim4
import LeanPool.GraphMinor.GM16.Section9GlobalCut
import LeanPool.GraphMinor.GM16.Section9BoundaryVertices
import LeanPool.GraphMinor.GM16.Section9SeparatorPaths
import LeanPool.GraphMinor.GM11.CitedResults
import Mathlib.Data.Fintype.EquivFin

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Section9a

import LeanPool.GraphMinor.GM14.Section9b

import LeanPool.GraphMinor.GM16.Theorem35Bridge

/-!
# Graph Minors XVI, (8.1)

Follow Section 9. Choose the paper's constants and separated
battlefields. Clear them successively, preserving rigidity, the
span, and the chosen free boundary sets. A large boundary linkage
adds a handle. Otherwise Menger gives the global separator, and
the clean-annulus argument proves that it meets every long path
in the cleared drawing. All numbered claims of Section 9 are
proved in the preceding modules.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, (8.1), pages 64 and 71–75, by the complete
battlefield, clearing, linkage, and clean-annulus proof of Section 9.
Only statements of other papers are assumed. The separation constant
is increased by `4 * φ + 8` from the printed choice on page 71 to
supply the line condition missing from the printed XV (3.5). -/
theorem theorem_8_1_with_radius
     :
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ δ φ ψ : ℕ, 3 ≤ φ → 3 ≤ ψ →
      ∃ γ θ : ℕ, 2 ≤ γ ∧ (4 * γ + 2) * δ < θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ) (Y : Set S),
          θ ≤ θ_span →
          IsSigmaSpan G H η θ_star θ_span T_star T →
          HasTangleMetric H θ_span T d →
          Y ⊆ H.V → Y.ncard = δ →
          (∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂}) →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsObtainedByAddingHandle S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          (∃ (P : Graph α β) (s t : S),
            s ∈ H.V ∧ t ∈ H.V ∧
            IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) ∧
            ψ ≤ d {s} {t} ∧ ∀ y ∈ Y, ψ ≤ d {s} {y}) ∨
          (∃ (Λ : S → Set S) (Z : Set α)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsEnvelope H d Y γ Λ ∧
            Z ⊆ V(G) \ V((restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph) ∧
            Z.ncard ≤ (δ ^ 2 * φ ^ 2) / 2 ∧
            IsSigmaSpan G (clearEnvelopeDrawing H Y Λ)
              (restrictCleared η (⋃ y ∈ Y, Λ y)) θ_star (θ_span - (4 * γ + 2) * δ) T_star T' ∧
            IsLambdaCompression H (clearEnvelopeDrawing H Y Λ)
              θ_span ((4 * γ + 2) * δ) T T' d d' ∧
            ∀ (P : Graph α β) (s t : S),
              s ∈ (clearEnvelopeDrawing H Y Λ).V →
              t ∈ (clearEnvelopeDrawing H Y Λ).V →
              IsHPathWithEnds G (restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph P
                (η.vMap s) (η.vMap t) →
              2 * ψ ≤ d' {s} {t} →
              (Z ∩ V(P)).Nonempty) := by
  classical
  intro S _ _ hS hConn δ φ ψ hφ hψ
  let : ConnectedSpace S := hConn
  obtain ⟨κ, β, γ, τ₀, hκEq, hκpos, hEven, hLow, _, hγ, hτ₀, hβ4, hClear₀, hBig₀, _, hMax⟩ :=
    section9_parameters δ φ ψ hφ hψ
  -- The corrected XV (3.5) needs room for a normal line with fewer than φ vertices.
  let τ := τ₀ + 4 * φ + 8
  have hClear : (4 * γ + 2) * δ < τ := by dsimp [τ]; omega
  have hBig : 16 * β + 17 ≤ τ := by dsimp [τ]; omega
  subst γ
  refine ⟨3 * β + 3, τ, by omega, hClear, ?_⟩
  intro α βe G θ_star θ_span T_star H η T d Y hτSpan hSpan hMet hY hYCard hSep
  obtain ⟨hψβ, hκβ, hβθ, hκθ, hSepBudget⟩ := section9_path_bounds hκpos hLow hψ hBig hτSpan
  by_cases hOld : ∃ (P : Graph α βe) (s t : S), s ∈ H.V ∧ t ∈ H.V ∧
      IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) ∧
      ψ ≤ d {s} {t} ∧ ∀ y ∈ Y, ψ ≤ d {s} {y}
  · exact Or.inr (Or.inl hOld)
  have hNoPath : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph Q (η.vMap s) (η.vMap t) →
      ψ ≤ d {s} {t} → (∀ y ∈ Y, ψ ≤ d {s} {y}) → False := by
    intro Q s t hs ht hQ hst hsy
    exact hOld ⟨Q, s, t, hs, ht, hQ, hst, hsy⟩
  have hBExists : ∀ y : S, ∃ (Λ : Set S) (C : Drawing S) (X : Set S),
      y ∈ Y → IsBattlefield H T d θ_span β {y} Λ C X := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨Λ, C, X, hB⟩ := GraphMinor.GM14.theorem_9_5_proof.{w} H θ_span β T d {y} hS hConn
        hSpan.isRigid hMet
        (Or.inl (Or.inl ⟨y, hY hy, rfl⟩)) hβ4 hEven (hBig.trans hτSpan)
      obtain ⟨X', _, hB'⟩ := hB.normalize
      exact ⟨Λ, C, X', fun _ => hB'⟩
    · exact ⟨∅, H, ∅, fun h => False.elim (hy h)⟩
  choose Λ C X hBattle using hBExists
  have hZone := fun y hy => (hBattle y hy).isZone
  obtain ⟨_, _, _, hSymm, hTri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ_span T d hS hConn
    hMet
  have hDis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)) := by
    intro y hy z hz hyz
    exact section9_disjoint_zones (hZone y hy) (hZone z hz) hSymm hTri
      (hSep y hy z hz hyz) (by omega)
  have hEnv := envelope_of_battlefields hSpan.isRigid hY hBattle hDis
  have hYFin : Y.Finite := H.finite_V.subset hY
  let ys := hYFin.toFinset
  have hys : (ys : Set S) = Y := hYFin.coe_toFinset
  have hysCard : ys.card = δ := (ncard_eq_toFinset_card _ hYFin).symm.trans hYCard
  have hYys : ∀ y ∈ ys, y ∈ H.V := fun y hy => hY (hYFin.mem_toFinset.mp hy)
  have hBattleYs : ∀ y ∈ ys, IsBattlefield H T d θ_span β {y} (Λ y) (C y) (X y) :=
    fun y hy => hBattle y (hYFin.mem_toFinset.mp hy)
  have hZoneYs := fun y hy => (hBattleYs y hy).isZone
  have hDisYs : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)) :=
    fun y hy z hz => hDis y (hYFin.mem_toFinset.mp hy) z (hYFin.mem_toFinset.mp hz)
  have hClearSpan : (4 * (3 * β + 3) + 2) * ys.card < θ_span := by
    rw [hysCard]
    exact lt_of_lt_of_le hClear hτSpan
  obtain ⟨T', d', hComp, hLe⟩ := exists_compression_clearFamily hS ys Λ
    (3 * β + 3) hMet hYys hZoneYs hDisYs hClearSpan
  have hEnvYs : IsEnvelope H d (ys : Set S) (3 * β + 3) Λ := hys.symm ▸ hEnv
  have hSpanClear := span_after_clearFamily hS ys Λ (3 * β + 3) η hSpan hEnvYs hComp
  let η' := restrictCleared η (⋃ y ∈ Y, Λ y)
  have hMap : η'.vMap = η.vMap := rfl
  have hCompY : IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ_span
      ((4 * (3 * β + 3) + 2) * δ) T T' d d' := by simpa only [hys, hysCard] using hComp
  have hSpanY : IsSigmaSpan G (clearEnvelopeDrawing H Y Λ) η' θ_star
      (θ_span - (4 * (3 * β + 3) + 2) * δ) T_star T' := by
    have hDrawingEq : clearEnvelopeDrawing H (ys : Set S) Λ = clearEnvelopeDrawing H Y Λ :=
      congrArg (fun A => clearEnvelopeDrawing H A Λ) hys
    have hSpanY' := span_congr_drawing_embedding hDrawingEq _ η' rfl rfl hSpanClear
    simpa only [hysCard] using hSpanY'
  have hLeY : ∀ x y : S, pointDist (clearEnvelopeDrawing H Y Λ) d' x y ≤ pointDist H d x y := by
    simpa only [hys] using hLe
  have hδκ : δ ≤ κ := by rw [hκEq]; exact section9_hairs_le_kappa δ φ hφ
  have hδβ : δ ≤ β := hδκ.trans (by omega)
  have hParam : 2 * β + 6 * (3 * β + 3) + 2 +
      (4 * (3 * β + 3) + 2) * ys.card < τ := by
    rw [hysCard]
    have hfree := section9_free_bound δ β hδβ
    dsimp [τ]
    rw [hτ₀]
    omega
  have hLineBudget : 4 * φ + (4 * (3 * β + 3) + 2) * ys.card ≤ τ := by
    rw [hysCard]
    dsimp [τ]
    omega
  have hBudget : (4 * (3 * β + 3) + 2) * ys.card + 8 < τ := by omega
  let : Fintype Y := hYFin.fintype
  have hCardY : Fintype.card Y = δ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hYCard]
  let e : Fin δ ≃ Y := (finCongr hCardY.symm).trans (Fintype.equivFin Y).symm
  let B : Fin δ → Set α := fun i => η.vMap '' X (e i).val
  have hBsub : ∀ i, B i ⊆ V(η'.imageGraph) := by
    intro i x hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [← hMap]
    exact η'.bijOn_v.mapsTo (boundary_vertex_mem_clearFamily hZone hDis (e i).prop
      ((hBattle (e i).val (e i).prop).isFree_X.1 hv))
  have hBdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    have hNe : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
    exact battlefield_image_sets_disjoint η (hBattle (e i).val (e i).prop)
      (hBattle (e j).val (e j).prop) (hDis _ (e i).prop _ (e j).prop hNe)
  rcases boundary_linkages_or_global_separator G η'.imageGraph
      hSpan.isControlling.isTangle_star.finite_V hSpan.isControlling.isTangle_star.finite_E
      η'.imageGraph_le δ φ B hBsub hBdis with hPack | hCut
  · obtain ⟨i, j, hij, P, hP, hPDis⟩ := hPack
    have hNe : (e i).val ≠ (e j).val := fun h => (ne_of_lt hij) (e.injective (Subtype.ext h))
    have hLink : ∀ k, ∃ a ∈ X (e i).val, ∃ b ∈ X (e j).val,
        IsHPathWithEnds G η'.imageGraph (P k) (η.vMap a) (η.vMap b) := by
      intro k
      obtain ⟨a', ha', b', hb', hPk⟩ := hP k
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact ⟨a, ha, b, hb, hPk⟩
    have hSepYs : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → τ ≤ d {y} {z} :=
      fun y hy z hz => hSep y (hYFin.mem_toFinset.mp hy) z (hYFin.mem_toFinset.mp hz)
    have hLinkYs : ∀ k, ∃ a ∈ X (e i).val, ∃ b ∈ X (e j).val,
        IsHPathWithEnds G (restrictCleared η (⋃ q ∈ (ys : Set S), Λ q)).imageGraph
          (P k) (η.vMap a) (η.vMap b) := by
      have hUnion : (⋃ q ∈ (ys : Set S), Λ q) = ⋃ q ∈ Y, Λ q := by rw [hys]
      have hImage : (restrictCleared η (⋃ q ∈ (ys : Set S), Λ q)).imageGraph = η'.imageGraph :=
        congrArg (fun A => (restrictCleared η A).imageGraph) hUnion
      simpa only [hImage] using hLink
    obtain ⟨S', instS', instT2', hHandle, H', ηH', T'', hSpan'⟩ := theorem_8_1_claim_4 hS η hSpan
      hYys hBattleYs hDisYs hSepYs hParam hBudget hLineBudget hφ hComp
      (hYFin.mem_toFinset.mpr (e i).prop) (hYFin.mem_toFinset.mpr (e j).prop) hNe P hLinkYs hPDis
    exact Or.inl ⟨S', instS', instT2', H', ηH', φ, T'', hHandle, Nat.le_refl _, hSpan'⟩
  · obtain ⟨Z₀, hZ₀G, hZ₀Card, _, hZ₀Cut⟩ := hCut
    have hZ₀Fin := hSpan.isControlling.isTangle_star.finite_V.subset hZ₀G
    have hCardκ : Z₀.ncard < κ := by rwa [← hκEq] at hZ₀Card
    have hCutY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ∀ Q a b,
        IsHPathWithEnds G η'.imageGraph Q a b →
        a ∈ η.vMap '' X y → b ∈ η.vMap '' X z → (V(Q) ∩ Z₀).Nonempty := by
      intro y hy z hz hyz Q a b hQ ha hb
      let i := e.symm ⟨y, hy⟩
      let j := e.symm ⟨z, hz⟩
      have hi : (e i).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      have hj : (e j).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
      have hij : i ≠ j := fun h => hyz (hi.symm.trans ((congrArg (fun k => (e k).val) h).trans hj))
      apply hZ₀Cut i j hij Q a b hQ
      · simpa only [B, hi] using ha
      · simpa only [B, hj] using hb
    refine Or.inr (Or.inr ⟨Λ, Z₀ \ V(η'.imageGraph), T', d', hEnv, ?_, ?_, hSpanY, hCompY, ?_⟩)
    · exact fun x hx => ⟨hZ₀G hx.1, hx.2⟩
    · have hc := ncard_le_ncard (show Z₀ \ V(η'.imageGraph) ⊆ Z₀ from sdiff_subset) hZ₀Fin
      omega
    · intro P s t hs ht hP hLong
      exact section9_long_new_path_meets_separator hS η η' hMap hMet hCompY.hasMetric'
        hY hBattle hSep hLeY hNoPath (by rw [hYCard]; exact hκEq) hφ hψ hψβ hκβ hβθ hκθ
        hSepBudget hMax hZ₀Fin hCardκ hCutY hs ht hP hLong

/-- Graph Minors XVI, (8.1), with the printed statement. The proof
above also records that its chosen zone radius is at least two. -/
theorem theorem_8_1_proof
     : GM16Theorem81Statement.{u, v, w} := by
  intro S _ _ hS hConn δ φ ψ hφ hψ
  obtain ⟨γ, θ, _, hClear, hRest⟩ := theorem_8_1_with_radius hS hConn δ φ ψ hφ hψ
  exact ⟨γ, θ, hClear, hRest⟩

end GraphMinor.GM16
