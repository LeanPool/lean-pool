/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6HairFamily
public import LeanPool.GraphMinor.GM16.Section6CliquePaths
import LeanPool.GraphMinor.GM16.Section6ActiveBound
import LeanPool.GraphMinor.GM16.Section6Clustering
import LeanPool.GraphMinor.GM16.Section6CliqueLinkage

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Producing the cluster in XVI (6.3)

The active hair bound leaves many hairs in separate components. Apply
the maximal-pair selection argument. Its separated-pair alternative gives
a clique minor, so failure of both desired outcomes yields a large set
of far hair ends close to one drawing vertex.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

private theorem hair_cluster_count_arithmetic {μ τ' : ℕ} (hμ : 1 ≤ μ) (hτ : 2 ≤ τ') :
    2 * (μ - 1) * (μ * τ') + (μ - 1) * τ' < 2 * μ ^ 2 * τ' ^ 2 := by
  have hμsq : μ ≤ μ ^ 2 := by nlinarith
  have hτsq : 2 * τ' ≤ τ' ^ 2 := by nlinarith
  have hB := Nat.mul_le_mul_right τ' ((Nat.sub_le μ 1).trans hμsq)
  have hA := Nat.mul_le_mul_right (μ * τ') (Nat.sub_le μ 1)
  have hδ := Nat.mul_le_mul_left (2 * μ ^ 2) hτsq
  have hpos : 0 < μ ^ 2 * τ' := Nat.mul_pos (pow_pos (by omega) _) (by omega)
  nlinarith

/-- Graph Minors XVI, proof of (6.3), page 60: if neither conclusion
holds, many far hair ends lie within distance less than `r` of one vertex.
This includes the construction of the maximal separated family, not a
hypothesis asserting its consequence. -/
theorem theorem_6_3_far_end_cluster
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {p τ τ' χ δ θ_star θ_span θ σ ψ r : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ)
    (F : HairFamily G H η d X Y θ)
    (hμ : 1 ≤ p * (p - 1) / 2)
    (hδ : δ = 2 * (p * (p - 1) / 2) ^ 2 * τ' ^ 2)
    (hr₀ : cliquePathThreshold.{u, v, w} hS hConn p ≤ r) (hr : 1
      ≤ r) (hθ : 2 * r < θ)
    (hψ : 1 ≤ ψ) (hψθ : ψ ≤ θ) (hτσ : τ ≤ σ) (hττ' : τ ≤ τ') (hτ' : 2 ≤ τ')
    (hself : ∀ a ∈ H.V, d {a} {a} = 0)
    (hsymm : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a})
    (htri : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c})
    (hNoClique : ¬ ControlsMinor G (completeGraph p) T_star)
    (hNoHorn : ¬ HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ) :
    ∃ w ∈ H.V, ∃ Y₄ ⊆ Y, (p * (p - 1) / 2) * τ' ≤ Y₄.ncard ∧
      ∀ y ∈ Y₄, d {F.far y} {w} < r := by
  classical
  let μ := p * (p - 1) / 2
  have hSaved := hAnim
  obtain ⟨_, horder, hSpan, hMet, _, _, hYsub, hYcard, _, _, hsep⟩ := hAnim
  have hrθ : r ≤ θ := by omega
  have hYfin : Y.Finite := H.finite_V.subset hYsub
  have hsmall := theorem_6_3_active_bound hS hConn hSaved F (hr₀.trans hrθ)
    hψ hψθ hτσ hττ' hτ' hNoClique hNoHorn
  have hnum : 2 * (μ - 1) * (μ * τ') < (Y \ F.active).ncard := by
    have ha := hair_cluster_count_arithmetic hμ hτ'
    have hc := ncard_le_ncard_sdiff_add_ncard Y F.active
      (hYfin.subset (fun _ h => h.1))
    rw [hδ] at hYcard
    change F.active.ncard ≤ (μ - 1) * τ' at hsmall
    change 2 * (μ - 1) * (μ * τ') + (μ - 1) * τ' < 2 * μ ^ 2 * τ' ^ 2 at ha
    change Y.ncard = 2 * μ ^ 2 * τ' ^ 2 at hYcard
    omega
  rcases separated_pairs_or_far_end_cluster (hYfin.sdiff) (fun _ h => hYsub h.1)
      (fun y hy => F.far_mem y hy.1) hr hself hsymm htri
      (fun y hy z hz hyz => lt_of_lt_of_le hθ (hsep y hy.1 z hz.1 hyz)) hnum with
    ⟨f, hf, hcross⟩ | ⟨w, hw, Y₄, hY₄, hY₄card, hnear⟩
  · have hpairH : ∀ i, ∀ a ∈ ({f i, F.far (f i)} : Set S), a ∈ H.V := by
      intro i a ha
      rcases ha with rfl | ha
      · exact hYsub (hf i).1
      · exact (mem_singleton_iff.mp ha) ▸ F.far_mem (f i) (hf i).1
    have hcross_ne : ∀ i j, i ≠ j → ∀ a ∈ ({f i, F.far (f i)} : Set S),
        ∀ b ∈ ({f j, F.far (f j)} : Set S), a ≠ b := by
      intro i j hij a ha b hb heq
      have hd := hcross i j hij a ha b hb
      rw [heq, hself b (hpairH j b hb)] at hd
      omega
    have hPP : Pairwise (fun i j => Disjoint V(F.path (f i)) V(F.path (f j))) := by
      intro i j hij
      exact F.full_hairs_disjoint hYsub (hf i).1 (hf j).1 (f.injective.ne hij) (hf i).2
        (hcross_ne i j hij _ (mem_insert_of_mem _ (mem_singleton _)) _ (mem_insert _ _))
        (hcross_ne i j hij _ (mem_insert_of_mem _ (mem_singleton _)) _
          (mem_insert_of_mem _ (mem_singleton _)))
        (hcross_ne i j hij _ (mem_insert _ _) _ (mem_insert_of_mem _ (mem_singleton _)))
    have hsepR : ∀ a ∈ range f ∪ range (fun i => F.far (f i)),
        ∀ b ∈ range f ∪ range (fun i => F.far (f i)), a ≠ b → r ≤ d {a} {b} := by
      rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩) b (⟨j, rfl⟩ | ⟨j, rfl⟩) hab
      · have hij : i ≠ j := fun h => hab (congrArg f h)
        exact hcross i j hij _ (mem_insert _ _) _ (mem_insert _ _)
      · by_cases hij : i = j
        · subst j
          exact hrθ.trans (F.dist (f i) (hf i).1)
        · exact hcross i j hij _ (mem_insert _ _) _ (mem_insert_of_mem _ (mem_singleton _))
      · by_cases hij : i = j
        · subst j
          rw [hsymm (F.far (f i)) (F.far_mem (f i) (hf i).1) (f i) (hYsub (hf i).1)]
          exact hrθ.trans (F.dist (f i) (hf i).1)
        · exact hcross i j hij _ (mem_insert_of_mem _ (mem_singleton _)) _ (mem_insert _ _)
      · have hij : i ≠ j := fun h => hab (congrArg (fun i => F.far (f i)) h)
        exact hcross i j hij _ (mem_insert_of_mem _ (mem_singleton _)) _
          (mem_insert_of_mem _ (mem_singleton _))
    apply False.elim
    apply hNoClique
    exact controlsMinor_of_separated_hPaths hS hConn p hSpan hMet
      (hr₀.trans (hrθ.trans horder))
      (fun i => ⟨hYsub (hf i).1, F.far_mem (f i) (hf i).1⟩)
      (fun i => F.is_hPath (f i) (hf i).1) hPP
      (fun a ha b hb hab => hr₀.trans (hsepR a ha b hb hab))
  · exact ⟨w, hw, Y₄, fun y hy => (hY₄ hy).1, hY₄card, hnear⟩

end GraphMinor.GM16
