/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Section4
public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section9Rigidity
import LeanPool.GraphMinor.GM16.Section9SpanClearing
import LeanPool.GraphMinor.GM16.Section9BattlefieldFree
import LeanPool.GraphMinor.GM16.Section9SeparatedBoundaries
import LeanPool.GraphMinor.GM16.Section9HandleLinkage
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9Regions
import LeanPool.GraphMinor.GM11.Section810

import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM16.Theorem35Bridge

/-!
# Claim (4) in the proof of XVI (8.1)

All the clearings give a controlled rigid span, and each battlefield
boundary set remains free. Distant centres rule out a region incident
with both boundaries. The ordered linkage selection and XV (3.5)
therefore give the required span with a handle added.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (4), page 72, with the
clearing, freeness, boundary circuits, and incidence conditions proved. -/
theorem theorem_8_1_claim_4
    (hS : IsClosedSurface S)
    {α : Type u} {βe : Type v} {G : Graph α βe} {H : Drawing S} (η : SpanEmbedding H G)
    {θ_star θ β sep φ : ℕ} {ys : Finset S}
    {T_star : Set (Hypergraph α βe × Hypergraph α βe)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T) (hY : ∀ y ∈ ys, y ∈ H.V)
    (hBattle : ∀ y ∈ ys, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hdis : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hsep : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → sep ≤ d {y} {z})
    (hparam : 2 * β + 6 * (3 * β + 3) + 2 + (4 * (3 * β + 3) + 2) * ys.card < sep)
    (hbudget : (4 * (3 * β + 3) + 2) * ys.card + 8 < sep)
    (hLineBudget : 4 * φ + (4 * (3 * β + 3) + 2) * ys.card ≤ sep)
    (hφ : 3 ≤ φ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
      θ ((4 * (3 * β + 3) + 2) * ys.card) T T' d d')
    {y z : S} (hy : y ∈ ys) (hz : z ∈ ys) (hyz : y ≠ z)
    (P : Fin (φ ^ 2) → Graph α βe)
    (hLink : ∀ i, ∃ a ∈ X y, ∃ b ∈ X z,
      IsHPathWithEnds G (restrictCleared η (⋃ q ∈ (ys : Set S), Λ q)).imageGraph
        (P i) (η.vMap a) (η.vMap b))
    (hDis : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingHandle S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T' := by
  let K := clearEnvelopeDrawing H (ys : Set S) Λ
  let η' := restrictCleared η (⋃ q ∈ (ys : Set S), Λ q)
  have hZone := fun q hq => (hBattle q hq).isZone
  have hEnv := envelope_of_battlefields hSpan.isRigid (fun q hq => hY q hq) hBattle hdis
  have hSpan' := span_after_clearFamily hS ys Λ (3 * β + 3) η hSpan hEnv hComp
  have hFree := battlefield_free_after_clearFamily hS hY hBattle hdis hsep hparam hComp
  have hClosed : IsClosed (univ \ ⋃ q ∈ (ys : Set S), Λ q) :=
    isClosed_univ.sdiff (isOpen_iUnion fun q => isOpen_iUnion fun hq => (hZone q hq).isOpenDisc.1)
  have hX : ∀ q ∈ ys, X q ⊆ (K.interSet (subBd (Λ q))).V := by
    intro q hq x hx
    have hxb := (hBattle q hq).isFree_X.1 hx
    have hxK := zone_boundary_subset_clearFamily hZone hdis hq hxb.2
    have hxOut := ((clearFamily_U hZone) ▸ hxK).2
    have hxKV : x ∈ K.V := (mem_interSet_V_iff hClosed).mpr ⟨hxb.1, mem_univ _, hxOut⟩
    exact (mem_interSet_V_iff (show IsClosed (subBd (Λ q)) by
      rw [subBd_eq_frontier]; exact isClosed_frontier)).mpr ⟨hxKV, hxb.2⟩
  have hne : Λ y ≠ Λ z := by
    intro heq
    have hyΛ := (hZone y hy).z_subset (mem_singleton y)
    exact (hdis y hy z hz hyz).notMem_of_mem_left (subset_closure hyΛ) (subset_closure (heq ▸ hyΛ))
  have hex : ∀ i, ∃ a b, a ∈ X y ∧ b ∈ X z ∧
      IsHPathWithEnds G η'.imageGraph (P i) (η'.vMap a) (η'.vMap b) := by
    intro i
    obtain ⟨a, ha, b, hb, hp⟩ := hLink i
    exact ⟨a, b, ha, hb, hp⟩
  choose a b hEnds using hex
  exact handle_span_of_boundary_linkage η' hSpan' hComp.hasMetric'
    (zone_mem_R_clearFamily hZone hdis hy) (zone_mem_R_clearFamily hZone hdis hz) hne
    (hZone y hy).isOArc_bd (hZone z hz).isOArc_bd
    (zone_boundary_isCircuit_clearFamily hZone hdis hy) (zone_boundary_isCircuit_clearFamily hZone
      hdis hz)
    (no_region_incident_two_cleared_boundaries hS (fun q hq => hY q hq)
      hZone hdis hComp hy hz (hsep y hy z hz hyz) hbudget)
    (normal_line_between_cleared_boundaries hS (fun q hq => hY q hq)
      hZone hdis hComp hy hz hyz (hsep y hy z hz hyz) hLineBudget)
    hφ (hX y hy) (hX z hz) (hFree y hy) (hFree z hz) P a b
    (fun i => ⟨(hEnds i).1, (hEnds i).2.1⟩) (fun i => (hEnds i).2.2) hDis

end GraphMinor.GM16
