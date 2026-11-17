/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

public import LeanPool.SteinerSpanners.Defs
public import LeanPool.SteinerSpanners.Glue
public import LeanPool.SteinerSpanners.Projection
public import LeanPool.SteinerSpanners.Combinatorics
public import LeanPool.SteinerSpanners.CSP
public import LeanPool.SteinerSpanners.Bucketing
public import LeanPool.SteinerSpanners.Hamming
public import LeanPool.SteinerSpanners.Dvoretzky

/-!
# Polynomial lower bounds for high-dimensional Steiner spanners

Source: url:https://github.com/goranzuzic/high-dimensional-steiner-spanners/tree/e75290d4a81dc898469a71414edf5bee43dc1b02
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
Status: verified
Main declarations: `HighDimSteinerSpanners.thm_1_3_non_metric_steiner_spanner_lower_bound`,
  `HighDimSteinerSpanners.thm_1_2_geometric_spanner_lower_bound`,
  `HighDimSteinerSpanners.cor_1_4_lp_dvoretzky_lower_bound`,
  `HighDimSteinerSpanners.thm_2_3_locally_list_bounded_csp_codes`,
  `HighDimSteinerSpanners.prop_3_4_three_hop_hypercube_collapse`
Tags: steiner-spanners, metric-embeddings, coding-theory, concentration
MSC: 68R10, 05C12, 46B07
-/

/-! # High-dimensional Steiner spanner lower bounds

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners

theorem lpDist_eq_toLp_dist :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) :=
  HighDimSteinerSpanners.Proofs.Glue.lpDist_eq_toLp_dist_proof

theorem thm_2_1a_metric_nearest_terminal_projection :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_2_1a_proof

theorem thm_2_1b_hypercube_lp_reduction :
    ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_2_1b_proof

theorem thm_2_2a_last_hit_edge_charging :
    ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet :=
  HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2a_proof

theorem thm_2_2b_biclique_bottleneck :
    ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ) :=
  HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2b_proof

lemma lem_5_1_interval_crossing :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t :=
  HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof

lemma lem_6_3_biclique_list_hit :
    ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X :=
  HighDimSteinerSpanners.Proofs.Glue.lem_6_3_from_2_2b thm_2_2b_biclique_bottleneck

theorem thm_2_3_locally_list_bounded_csp_codes :
    ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X :=
  HighDimSteinerSpanners.Proofs.CSP.thm_2_3_from_6_3 lem_6_3_biclique_list_hit

theorem thm_1_3_non_metric_steiner_spanner_lower_bound :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) :=
  HighDimSteinerSpanners.Proofs.Glue.thm_1_3_from_modules
    thm_2_1b_hypercube_lp_reduction
    thm_2_2a_last_hit_edge_charging
    thm_2_3_locally_list_bounded_csp_codes

theorem thm_1_2_geometric_spanner_lower_bound :
    ∃ M : ℝ, 0 < M ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (c c₀ A β₁ β₂ : ℝ),
            (2 : ℝ) ^ (-M * C ^ (4 * p)) ≤ (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
            (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c ∧
            0 < c₀ ∧ 0 < A ∧ 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * Real.logb 2 (nSeq j : ℝ) ∧
                  (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A ∧
                  ∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_1_2_from_1_3
    lpDist_eq_toLp_dist
    thm_1_3_non_metric_steiner_spanner_lower_bound

theorem cor_1_4_lp_dvoretzky_lower_bound :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) :=
  HighDimSteinerSpanners.Proofs.Dvoretzky.cor_1_4_from_1_3
    lpDist_eq_toLp_dist
    thm_1_3_non_metric_steiner_spanner_lower_bound

theorem prop_3_1_diameter_bounded_bucketing :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C : ℝ), 1 ≤ C →
        ∀ (I : Type) [Fintype I] (B : I → Finset P),
          (∀ i : I, 2 ≤ (B i).card) →
          (Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card ∧
            ∀ x y : P,
              ENNReal.ofReal (dist x y) ≤
                graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y)) ∧
          ((∀ x y : P, x ≠ y → ∃ i : I, x ∈ B i ∧ y ∈ B i ∧ bucketDiam (B i) ≤ C * dist x y) →
            IsGeneralNonMetricSteinerSpanner C (bucketingGraph B) (bucketingWeight B) ∧
            ∀ x y : P, x ≠ y →
              ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
                q.IsPath ∧ q.length ≤ 2 ∧
                walkWeight (bucketingWeight B) q ≤ C * dist x y) :=
  HighDimSteinerSpanners.Proofs.Bucketing.prop_3_1_proof

theorem prop_3_2_simplex_separation :
    ∀ (p : ℝ), 1 ≤ p →
      (∀ n : ℕ, 3 ≤ n →
        (∀ (C : ℝ), 1 ≤ C → C < 2 →
          ∀ G : SimpleGraph (Fin n),
            IsGeometricSpanner p (stdBasis n) C G →
            Nat.card G.edgeSet = Nat.choose n 2) ∧
        (∃ (S : Type) (_ : Fintype S)
            (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ),
          IsNonMetricSteinerSpanner p (stdBasis n) 1 H w ∧
          Nat.card H.edgeSet = n ∧
          ∀ i j : Fin n, i ≠ j →
            ∃ q : H.Walk (.inl i) (.inl j),
              q.IsPath ∧ q.length ≤ 2 ∧
              walkWeight w q ≤ 1 * lpDist p (stdBasis n i) (stdBasis n j))) ∧
      (∀ (N q r₀ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ r₀ →
        ∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → r₀ ≤ hammingDist x y) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            let stretch : ℝ := ((N : ℝ) / (r₀ : ℝ)) ^ (1 / p)
            ∃ (S : Type) (_ : Fintype S)
              (H : SimpleGraph (Fin X.card ⊕ S)) (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P stretch H w ∧
              Nat.card H.edgeSet = X.card ∧
              ∀ i j : Fin X.card, i ≠ j →
                ∃ q : H.Walk (.inl i) (.inl j),
                  q.IsPath ∧ q.length ≤ 2 ∧
                  walkWeight w q ≤ stretch * lpDist p (P i) (P j)) :=
  HighDimSteinerSpanners.Proofs.Bucketing.prop_3_2_proof

lemma lem_3_3_blockwise_hamming_hubs :
    ∀ (r d : ℕ), 4 ≤ r → 1 ≤ d →
      ∀ (p : ℝ), 1 ≤ p →
        let b_r : ℝ := (2 : ℝ) ^ r - 1
        let ρ_r : ℝ := 1 / (64 * b_r)
        ∀ (P : Finset (Fin d → Bool)),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
          ∃ (S_r : Finset (Fin d → Bool)),
            Disjoint P S_r ∧
            ∃ (H_r : SimpleGraph ↥(P ∪ S_r)),
              let w := cubeSubgraphWeight p (P ∪ S_r)
              Nat.card H_r.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H_r w ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ_r * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * ρ_r * (d : ℝ) →
                ∃ q : H_r.Walk ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 387 * cubeLpDist p x y) :=
  HighDimSteinerSpanners.Proofs.Hamming.lem_3_3_proof

theorem prop_3_4_three_hop_hypercube_collapse :
    ∀ (p : ℝ), 1 ≤ p →
      ((∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ d : ℕ, 1 ≤ d →
            ∀ P : Finset (Fin d → Bool),
              2 ≤ P.card →
              (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
              (∃ (S : Finset (Fin d → Bool)),
                Disjoint P S ∧
                ∃ H : SimpleGraph ↥(P ∪ S),
                  let w := cubeSubgraphWeight p (P ∪ S)
                  Nat.card H.edgeSet ≤ 2 * P.card ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    ENNReal.ofReal (cubeLpDist p x y) ≤
                      graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩) ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                    (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                    ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩,
                      q.IsPath ∧ q.length ≤ 3 ∧
                      walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
              ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                  (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
                ∃ (S : Finset (Fin d → Bool)),
                  Disjoint P S ∧
                  ∃ H : SimpleGraph ↥(P ∪ S),
                    let w := cubeSubgraphWeight p (P ∪ S)
                    (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                      ENNReal.ofReal (cubeLpDist p x y) ≤
                        graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                      ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩,
                        q.IsPath ∧ q.length ≤ 3 ∧
                        walkWeight w q ≤ 5760 * cubeLpDist p x y))) ∧
      (∀ d : ℕ, 2 ≤ d →
        ∃ H : SimpleGraph (Fin d → Bool),
          let w : Sym2 (Fin d → Bool) → ℝ :=
            Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
              simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
          (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
          (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w x y) ∧
          (∀ x y : Fin d → Bool, x ≠ y →
            ∃ q : H.Walk x y,
              q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 5760 * cubeLpDist p x y))) :=
  HighDimSteinerSpanners.Proofs.Hamming.prop_3_4_proof

end HighDimSteinerSpanners
