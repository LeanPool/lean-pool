/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8Paths
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.MetricPoints

/-!
# Keeping hairs after rearrangement

This proves Claim (12) in XVI (8.3). Follow an old hair until it first meets
the new span again. If it never does, extend it through the old drawing until
it does. The two distance bounds proved in `Section8Paths` ensure that the
result is a long path of the new span. We use a two-unit larger cutoff for
retained hairs to cover the last-edge estimate.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Graph Minors XVI, proof of (8.3), Claim (12), page 68.
A retained hair gives a long path of the rearranged span avoiding the horns.
The cutoff `ψ + 5λ + 4` is two larger than the paper's cutoff, to allow the
last-edge bound in `rearranged_exit_path_dist`. -/
theorem theorem_8_3_claim_12 (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hprox : ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2)
    (hself' : ∀ a ∈ H'.A, d' a a = 0)
    {X : Set α} (hXold : Disjoint X V(η.imageGraph))
    {Q : Graph α β} {y x : S} (hy : y ∈ H.V) (hx : x ∈ H.V)
    (hQ : IsHPathWithEnds G η.imageGraph Q (η.vMap y) (η.vMap x))
    (hQX : Disjoint X V(Q)) (hfar : ψ + 5 * lam + 4 ≤ d z {y})
    (hψ : 3 ≤ ψ) (hθ : ψ + (4 * lam + 2) ≤ θ) (hdist : θ ≤ d {y} {x}) :
    ∃ (v : S) (P : Graph α β), v ∈ H'.V ∧ y ≠ v ∧
      IsHPathWithEnds G η'.imageGraph P (η'.vMap y) (η'.vMap v) ∧
      Disjoint X V(P) ∧ ψ ≤ d' {y} {v} := by
  classical
  have hkeep := h.vMap_eq y hy (by omega)
  have hy' := hkeep.1
  have hynew : η.vMap y ∈ V(η'.imageGraph) := by
    rw [← hkeep.2]
    exact η'.bijOn_v.mapsTo hy'
  by_cases hhit : ∃ w ∈ V(Q), w ∈ V(η'.imageGraph) ∧ w ≠ η.vMap y
  · obtain ⟨w, hwQ, hwNew, hwne⟩ := hhit
    obtain ⟨Q₀, hQ₀Q, _, hQ₀⟩ := hQ.2.1.exists_subpath hQ.2.1.left_mem hwQ
    obtain ⟨w₀, hw₀, w₁, hw₁, P, hPQ₀, hP, _, hPnew⟩ :=
      hQ₀.exists_isFromToPathWithEnds (mem_singleton (η.vMap y))
        (show w ∈ V(η'.imageGraph) \ {η.vMap y} from ⟨hwNew, hwne⟩)
    have hPQ : P ≤ Q := hPQ₀.trans hQ₀Q
    rw [mem_singleton_iff] at hw₀
    subst w₀
    obtain ⟨v, hv, hmap⟩ := η'.bijOn_v.surjOn hw₁.1
    have hvQ : η'.vMap v ∈ V(Q) := by rw [hmap]; exact hPQ.vertexSet_mono hP.right_mem
    have hvne : η'.vMap v ≠ η.vMap y := by simpa only [hmap, mem_singleton_iff] using hw₁.2
    have hd := rearranged_hair_hit_dist hS h hsymm htri hy hx hy' hv hQ hvQ hvne
      (by omega) hθ hdist
    have hPmap : IsGraphPathWithEnds G P (η'.vMap y) (η'.vMap v) := by
      rw [hkeep.2, hmap]
      exact hP
    have hinter : V(P) ∩ V(η'.imageGraph) = {η'.vMap y, η'.vMap v} := by
      rw [hkeep.2, hmap]
      apply subset_antisymm
      · rintro a ⟨haP, haNew⟩
        by_cases hay : a = η.vMap y
        · exact mem_insert_iff.mpr (Or.inl hay)
        · have haBoth : a ∈ V(P) ∩ (V(η'.imageGraph) \ {η.vMap y}) := ⟨haP, haNew, hay⟩
          rw [hPnew] at haBoth
          exact mem_insert_of_mem _ haBoth
      · rintro a (rfl | ha)
        · exact ⟨hP.left_mem, hynew⟩
        · rw [mem_singleton_iff] at ha
          subst a
          exact ⟨hP.right_mem, hw₁.1⟩
    have hne : η'.vMap y ≠ η'.vMap v := by rw [hkeep.2]; exact hvne.symm
    refine ⟨v, P, hv, fun heq => hne (congrArg η'.vMap heq), ?_, hQX.mono_right hPQ.vertexSet_mono,
      hd⟩
    exact isHPath_of_far_ends hS η' h.isCompression.hasMetric' hy' hv hPmap hne hinter (hψ.trans hd)
  · have hQnew : V(Q) ∩ V(η'.imageGraph) = {η.vMap y} := by
      apply subset_antisymm
      · rintro w ⟨hwQ, hwNew⟩
        apply mem_singleton_iff.mpr
        by_contra hwne
        exact hhit ⟨w, hwQ, hwNew, hwne⟩
      · rintro w rfl
        exact ⟨hQ.2.1.left_mem, hynew⟩
    have hxnot : η.vMap x ∉ V(η'.imageGraph) := by
      intro hxNew
      have heq : η.vMap x = η.vMap y :=
        mem_singleton_iff.mp (hQnew ▸ ⟨hQ.2.1.right_mem, hxNew⟩)
      exact hQ.2.2.1 heq.symm
    obtain ⟨W⟩ := drawing_walk_of_twoCell hS h.isSpan.isRespectful.1 hx hy
    obtain ⟨a, ha, b, hb, R, _, _, hR, _, hRnew⟩ :=
      exists_isFromToPathWithEnds_of_walk (mapSpanWalk η W)
        (mem_singleton (η.vMap x)) hynew
    rw [mem_singleton_iff] at ha
    subst a
    obtain ⟨v, hv, hmap⟩ := η'.bijOn_v.surjOn hb
    have hRold : R ≤ η.imageGraph := hR.1
    have hRG : IsGraphPathWithEnds G R (η.vMap x) (η'.vMap v) := by
      rw [hmap]
      exact hR.mono η.imageGraph_le
    have hRnew' : V(R) ∩ V(η'.imageGraph) = {η'.vMap v} := by rwa [hmap]
    have hd := rearranged_exit_path_dist hS h hsymm htri
      hprox hy hy' hv hRG hRold hRnew' hxnot hfar
    have hne : y ≠ v := by
      intro heq
      subst v
      rw [hself' {y} (singleton_mem_A_of_mem_V hy')] at hd
      omega
    have hmapne : η'.vMap y ≠ η'.vMap v := fun heq => hne (η'.bijOn_v.injOn hy' hv heq)
    have hQmap : IsGraphPathWithEnds G Q (η'.vMap y) (η.vMap x) := by
      rw [hkeep.2]
      exact hQ.2.1
    obtain ⟨P, hPsub, hP⟩ := exists_hPath_of_two_paths η'.imageGraph_le hQmap hRG
      (η'.bijOn_v.mapsTo hy') (η'.bijOn_v.mapsTo hv) hmapne (by rw [hkeep.2, hQnew])
        (by rw [hRnew'])
    have hRX : Disjoint X V(R) := hXold.mono_right hRold.vertexSet_mono
    have hPX : Disjoint X V(P) := by
      apply disjoint_left.mpr
      intro a haX haP
      have haUnion := hPsub.vertexSet_mono haP
      change a ∈ V(Q) ∪ V(R) at haUnion
      exact haUnion.elim (fun haQ => hQX.notMem_of_mem_left haX haQ)
        (fun haR => hRX.notMem_of_mem_left haX haR)
    exact ⟨v, P, hv, hne, hP, hPX, hd⟩

end GraphMinor.GM16
