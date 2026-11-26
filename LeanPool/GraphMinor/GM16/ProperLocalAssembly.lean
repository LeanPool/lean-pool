/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement


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
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  obtain ⟨𝒮, disc, pt, hCentral, hType, hArr, hDisj⟩ :=
    assemble_eye_arrangement G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt
      D hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
      hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  exact ⟨𝒮, disc, pt, hCentral, hType,
    IsSurfaceArrangement.isProper_of_disjoint_boundaries hArr hDisj⟩

end GraphMinor.GM16
