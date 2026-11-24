/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8Animal
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM09.Basic

import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Non-level spans give another hair

This proves XVI (8.3) by its proof on pages 65–68. Truncate the animal, rule
out long paths avoiding the deleted set, and apply the definition of level.
A non-level rearrangement yields the extra hair by Claims (3)–(12).

The threshold is increased from the paper's constant term `11` to `31`.
This allows the two-unit larger cutoff for retained hairs used in Claim (12).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, (8.3), pages 65–68. The proof uses the metric laws of
XI (9.1) and the proved truncation, vertex-deletion, and rearrangement lemmas.
The larger constant term `31` provides the buffer in Claim (12). -/
theorem theorem_8_3_with_bound :
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ lower τ χ δ lam ζ ψ : ℕ, 3 ≤ ψ →
      ∃ θ : ℕ, lower ≤ θ ∧ ζ < θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ) (X : Set α) (Y : Set S) (Z : Set α)
          (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ (ζ + τ))
          (_ : Z ⊆ V(G)) (hZ_disj : Disjoint V(η.imageGraph) Z)
          (_ : X ⊆ Z) (_ : Z.ncard ≤ ζ),
          HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
          (∃ (P : Graph α β) (s₁ s₂ y₁ y₂ : S),
            s₁ ∈ H.V ∧ s₂ ∈ H.V ∧ y₁ ∈ Y ∧ y₂ ∈ Y ∧ y₁ ≠ y₂ ∧
            IsHPathWithEnds (GM09.deleteVertices G Z) η.imageGraph P
              (η.vMap s₁) (η.vMap s₂) ∧
            d {s₁} {y₁} < ψ ∧ d {s₂} {y₂} < ψ) ∨
          (∃ d₀ : Set S → Set S → ℕ,
            IsLevelSpan (GM09.deleteVertices G Z) H (restrictDeleteVertices η Z hZ_disj)
              (θ_star - Z.ncard) (θ - Z.ncard) lam (2 * ψ)
              (deleteGraphVerticesTangle G hAnim.2.2.1.isControlling.isTangle_star.finite_V
                hAnim.2.2.1.isControlling.isTangle_star.finite_E Z T_star θ_star)
              (GM10.truncation T (θ - Z.ncard)) d₀) := by
  classical
  intro S _ _ hS hConn lower τ χ δ lam ζ ψ hψ
  let θ := lower + 4 * ψ + 10 * lam + 3 * ζ + 31
  refine ⟨θ, by dsimp [θ]; omega, by dsimp [θ]; omega, ?_⟩
  intro α β G θ_star θ_span T_star H η T d X Y Z hAnim hZsub hZdisj hXZ hZcard
  let T₀ := GM10.truncation T θ
  let d₀ : Set S → Set S → ℕ := fun a b => min (d a b) θ
  have hNorm : IsAnimal G T_star θ_star H η θ T₀ d₀ X Y χ δ θ (ζ + τ) :=
    theorem_8_3_claim_1 hAnim
  have hSpan := hNorm.2.2.1
  have hMet := hNorm.2.2.2.1
  have hT := hSpan.isControlling.isTangle_star
  have hZfin : Z.Finite := hT.finite_V.subset hZsub
  have hZlt : Z.ncard < θ := by dsimp [θ]; omega
  have hZltStar : Z.ncard < θ_star := hZlt.trans_le hSpan.isControlling.theta_le
  obtain ⟨_, hself, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T₀ d₀ hS hConn
    hMet
  have hψθ : ψ ≤ θ := by dsimp [θ]; omega
  have hOldDel : η.imageGraph ≤ GM09.deleteVertices G Z :=
    le_deleteVertices_of_disjoint η.imageGraph_le hZdisj
  by_cases hshort : ∀ (P : Graph α β) (s t : S), s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) →
      Disjoint V(P) Z → d₀ {s} {t} < 2 * ψ
  · let η₀ := restrictDeleteVertices η Z hZdisj
    let T_del := GM10.truncation T₀ (θ - Z.ncard)
    let d_del : Set S → Set S → ℕ := fun a b => min (d₀ a b) (θ - Z.ncard)
    let T_star_del := deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star
    have hDel : IsSigmaSpan (GM09.deleteVertices G Z) H η₀ (θ_star - Z.ncard)
        (θ - Z.ncard) T_star_del T_del :=
      theorem_8_2_proof G θ_star θ (θ - Z.ncard) T_star H η T₀ Z hSpan hZsub hZdisj hZlt
        (by omega) le_rfl
    have hDelMet : HasTangleMetric H (θ - Z.ncard) T_del d_del :=
      HasTangleMetric.truncation hMet (by omega) (Nat.sub_le _ _)
    by_cases hlevel : IsLevelSpan (GM09.deleteVertices G Z) H η₀ (θ_star - Z.ncard)
        (θ - Z.ncard) lam (2 * ψ) T_star_del T_del d_del
    · right; right
      refine ⟨d_del, ?_⟩
      have hEq : T_del = GM10.truncation T (θ - Z.ncard) :=
        truncation_truncation_eq T (Nat.sub_le _ _)
      rwa [hEq] at hlevel
    · have hnotstep : ¬ IsMuSteppedSpan (GM09.deleteVertices G Z) H η₀ d_del (2 * ψ) := by
        rintro ⟨P, s, t, hs, ht, hP, hlong⟩
        have hPG : IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) :=
          ⟨η.imageGraph_le, hP.2.1.mono (G.induce_le sdiff_subset), hP.2.2⟩
        have hPZ : Disjoint V(P) Z := disjoint_left.mpr fun v hv hvZ =>
          (hP.2.1.1.vertexSet_mono hv).2 hvZ
        have hb := hshort P s t hs ht hPG hPZ
        change 2 * ψ ≤ min (d₀ {s} {t}) (θ - Z.ncard) at hlong
        omega
      obtain ⟨H', η', T'', d'', z, P, s, t, hRearr, hStep, hsnear, htnear⟩ :=
        theorem_8_3_claim_3 hDel hDelMet (by dsimp [θ]; omega) hnotstep hlevel
      let lam' := lam + (Z.ncard + 3) / 4
      have hbudget : Z.ncard + (4 * lam + 2) ≤ 4 * lam' + 2 := by dsimp [lam']; omega
      have hlam : lam ≤ lam' := Nat.le_add_right _ _
      have hgap : lam' < θ - Z.ncard := by dsimp [lam', θ]; omega
      have hnewpos : 4 * lam' + 2 < θ := by dsimp [lam', θ]; omega
      have hLift := theorem_8_3_claim_4 hSpan hMet hZsub hZdisj η' hRearr hlam hgap hbudget hnewpos
      let η_new := liftSpanEmbedding η' (G.induce_le sdiff_subset)
      let T_new := GM10.truncation T'' (θ - (4 * lam' + 2))
      let d_new : Set S → Set S → ℕ := fun a b => min (d'' a b) (θ - (4 * lam' + 2))
      have hNew : IsRearrangedWithin G H H' η η_new θ_star θ lam' T_star T₀ T_new d₀ d_new z
        := hLift
      have hnewZ : Disjoint V(η_new.imageGraph) Z := disjoint_left.mpr fun v hv hvZ =>
        (η'.imageGraph_le.vertexSet_mono hv).2 hvZ
      have hPZ : Disjoint V(P) Z := disjoint_left.mpr fun v hv hvZ =>
        (hStep.2.2.1.2.1.1.vertexSet_mono hv).2 hvZ
      have hPG : IsHPathWithEnds G η_new.imageGraph P (η_new.vMap s) (η_new.vMap t) :=
        ⟨η_new.imageGraph_le, hStep.2.2.1.2.1.mono (G.induce_le sdiff_subset), hStep.2.2.1.2.2⟩
      have hlong : 2 * ψ ≤ d_new {s} {t} := by
        have hb := hStep.2.2.2
        change 2 * ψ ≤ min (d'' {s} {t}) (θ - (4 * lam' + 2))
        have hcut : 2 * ψ ≤ θ - (4 * lam' + 2) := by dsimp [θ, lam']; omega
        exact le_min hb hcut
      have hsnear' : pointAtomDist H d₀ s z ≤ lam' := by
        change pointAtomDist H (fun a b => min (d₀ a b) (θ - Z.ncard)) s z ≤ lam at hsnear
        rw [pointAtomDist_min] at hsnear
        omega
      have htnear' : pointAtomDist H d₀ t z ≤ lam' := by
        change pointAtomDist H (fun a b => min (d₀ a b) (θ - Z.ncard)) t z ≤ lam at htnear
        rw [pointAtomDist_min] at htnear
        omega
      left
      exact animal_of_rearrangement hS hNorm hNew hZfin hXZ hZcard hnewZ hshort
        hStep.1 hStep.2.1 hPG hPZ hlong hsnear' htnear' hψ
        (by dsimp [θ, lam']; omega) (by dsimp [θ, lam']; omega) (by dsimp [θ, lam']; omega)
  · push Not at hshort
    obtain ⟨P, s, t, hs, ht, hP, hPZ, hlong⟩ := hshort
    rcases theorem_8_3_claim_2 hNorm (by omega) hψθ (show τ ≤ ζ + τ by omega) hsymm hself htri
      hs ht hP (hPZ.symm.mono_left hXZ) hlong with hnew | hnear
    · exact Or.inl hnew
    · obtain ⟨y₁, hy₁, y₂, hy₂, hne, hnear₁, hnear₂⟩ := hnear
      right; left
      refine ⟨P, s, t, y₁, y₂, hs, ht, hy₁, hy₂, hne, ?_, ?_, ?_⟩
      · exact ⟨hOldDel, hP.2.1.in_deleteVertices hPZ.symm, hP.2.2⟩
      · change min (d {s} {y₁}) θ < ψ at hnear₁
        omega
      · change min (d {t} {y₂}) θ < ψ at hnear₂
        omega

/-- Graph Minors XVI, (8.3), with its printed statement. The strengthened
proof also permits any prescribed lower bound on the chosen threshold,
as used in the proof of (7.1) on page 69. -/
theorem theorem_8_3_proof : GM16Theorem83Statement.{u, v, w} := by
  intro S _ _ hS hConn τ χ δ lam ζ ψ hψ
  obtain ⟨θ, _, hζ, hRest⟩ := theorem_8_3_with_bound hS hConn 0 τ χ δ lam ζ ψ hψ
  exact ⟨θ, hζ, hRest⟩

end GraphMinor.GM16
