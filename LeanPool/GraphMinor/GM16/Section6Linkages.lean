/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section5Reroute
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2c

/-!
# Paths and fans in the hair graphs of XVI (6.3)

Shorten paths at their first meeting with the embedded drawing. A disjoint
family between drawing vertices becomes a family of old-graph paths.
A fan whose centre is outside the drawing becomes a horn. The ends stay
in the prescribed marked set, so their metric separation is retained.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Disjoint paths between vertices of the embedded drawing can be
shortened to old-graph paths, as used twice in XVI (6.3), pages 60–61.
The subgraph has no old-graph edge, and all its old-graph vertices have
labels in `Y`. -/
theorem hPaths_of_disjoint_paths_in_subgraph
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G K : Graph α β} {H : Drawing S} {η : SpanEmbedding H G} {Y : Set S}
    {n : ℕ} {P : Fin n → Graph α β} {a b : Fin n → α}
    (hKG : K ≤ G) (hKH : Disjoint E(K) E(η.imageGraph))
    (hKY : V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y)
    (hP : ∀ i, a i ∈ V(η.imageGraph) ∧ b i ∈ V(η.imageGraph) ∧ a i ≠ b i ∧
      IsGraphPathWithEnds K (P i) (a i) (b i))
    (hPP : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    ∃ (R : Fin n → Graph α β) (s t : Fin n → S),
      (∀ i, s i ∈ Y ∧ t i ∈ Y ∧ s i ≠ t i) ∧
      (∀ i, IsHPathWithEnds G η.imageGraph (R i) (η.vMap (s i)) (η.vMap (t i))) ∧
      Pairwise (fun i j => Disjoint V(R i) V(R j)) := by
  classical
  have htrim : ∀ i, ∃ (c : α) (R : Graph α β), c ∈ V(η.imageGraph) ∧ a i ≠ c ∧ R ≤ P i ∧
      IsGraphPathWithEnds K R (a i) c ∧ V(R) ∩ V(η.imageGraph) = {a i, c} := by
    intro i
    exact path_trim_marked (hP i).2.2.2 (hP i).1 (hP i).2.1 (hP i).2.2.1
  choose c R hc hac hRP hR hinter using htrim
  have hsa : ∀ i, ∃ y ∈ Y, η.vMap y = a i := by
    intro i
    exact hKY ⟨(hR i).le.vertexSet_mono (hR i).left_mem, (hP i).1⟩
  have htc : ∀ i, ∃ y ∈ Y, η.vMap y = c i := by
    intro i
    exact hKY ⟨(hR i).le.vertexSet_mono (hR i).right_mem, hc i⟩
  choose s hs hsa using hsa
  choose t ht htc using htc
  refine ⟨R, s, t, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hs i, ht i, ?_⟩
    intro heq
    apply hac i
    rw [← hsa i, ← htc i, heq]
  · intro i
    rw [hsa i, htc i]
    exact ⟨η.imageGraph_le, (hR i).mono hKG, hac i, (hP i).1, hc i, hinter i,
      hKH.mono_left (hR i).le.edgeSet_mono⟩
  · intro i j hij
    exact (hPP hij).mono (hRP i).vertexSet_mono (hRP j).vertexSet_mono

/-- A fan with centre outside the embedded drawing can be shortened to
a horn. This is the fan-to-horn step in XVI (6.3), pages 60–61. -/
theorem horn_of_fan_in_subgraph
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G K : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {Y : Set S} {d : Set S → Set S → ℕ} {x : α} {n r : ℕ}
    {P : Fin n → Graph α β} {b : Fin n → α}
    (hKG : K ≤ G) (hxK : x ∈ V(K)) (hxH : x ∉ V(η.imageGraph))
    (hKY : V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y) (hY : Y ⊆ H.V)
    (hsep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → r ≤ d {y} {z})
    (hP : ∀ i, b i ∈ V(η.imageGraph) ∧ IsGraphPathWithEnds K (P i) x (b i))
    (hPP : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {x} ∧ Disjoint E(P i) E(P j)) :
    ∃ (R : Fin n → Graph α β) (ends : Fin n → S), IsHorn G H η d x r n R ends := by
  classical
  have htrim : ∀ i, ∃ c ∈ V(η.imageGraph), ∃ R : Graph α β,
      R ≤ P i ∧ IsGraphPathWithEnds K R x c ∧ V(R) ∩ V(η.imageGraph) = {c} := by
    intro i
    obtain ⟨c, ⟨_, hc⟩, R, hRP, hR, hhit, _⟩ := (hP i).2.exists_first_hit
      (S := V(η.imageGraph)) ⟨b i, (hP i).2.right_mem, (hP i).1⟩
    exact ⟨c, hc, R, hRP, hR.mono (hP i).2.le, hhit⟩
  choose c hc R hRP hR hinter using htrim
  have hlabels : ∀ i, ∃ y ∈ Y, η.vMap y = c i := by
    intro i
    exact hKY ⟨(hR i).le.vertexSet_mono (hR i).right_mem, hc i⟩
  choose ends hends heq using hlabels
  have hRR : ∀ i j, i ≠ j → V(R i) ∩ V(R j) = {x} ∧ Disjoint E(R i) E(R j) := by
    intro i j hij
    constructor
    · apply Set.Subset.antisymm
      · exact (inter_subset_inter (hRP i).vertexSet_mono (hRP j).vertexSet_mono).trans
          (hPP i j hij).1.subset
      · rintro z rfl
        exact ⟨(hR i).left_mem, (hR j).left_mem⟩
    · exact ((hPP i j hij).2).mono (hRP i).edgeSet_mono (hRP j).edgeSet_mono
  refine ⟨R, ends, ⟨hKG.vertexSet_mono hxK, hxH⟩, fun i => hY (hends i), ?_, ?_, hRR, ?_⟩
  · intro i
    rw [heq i]
    exact (hR i).mono hKG
  · intro i
    rw [heq i]
    exact hinter i
  · intro i j hij
    apply hsep (ends i) (hends i) (ends j) (hends j)
    intro hendsij
    have hcij : c i = c j := by rw [← heq i, ← heq j, hendsij]
    have hci : c i ∈ V(R i) ∩ V(R j) :=
      ⟨(hR i).right_mem, hcij ▸ (hR j).right_mem⟩
    rw [(hRR i j hij).1, mem_singleton_iff] at hci
    exact hxH (hci ▸ hc i)

/-- Disjoint old-graph paths have distinct labels at all their ends.
This supplies the endpoint hypotheses of XVI (5.2). -/
theorem hPath_end_labels_injective
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {n : ℕ} {P : Fin n → Graph α β} {s t : Fin n → S}
    (hP : ∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (t i)))
    (hPP : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    Function.Injective s ∧ Function.Injective t ∧ Disjoint (range s) (range t) := by
  constructor
  · intro i j hij
    by_contra hne
    have hsi := IsGraphPathWithEnds.left_mem (hP i).2.1
    have hsj := IsGraphPathWithEnds.left_mem (hP j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hPP hne)) hsi (heq ▸ hsj)
  constructor
  · intro i j hij
    by_contra hne
    have hti := IsGraphPathWithEnds.right_mem (hP i).2.1
    have htj := IsGraphPathWithEnds.right_mem (hP j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hPP hne)) hti (heq ▸ htj)
  · apply Set.disjoint_left.mpr
    rintro z ⟨i, rfl⟩ ⟨j, htj⟩
    by_cases hij : i = j
    · subst j
      exact (hP i).2.2.1 (congrArg η.vMap htj.symm)
    · have hsi := IsGraphPathWithEnds.left_mem (hP i).2.1
      have htj' := IsGraphPathWithEnds.right_mem (hP j).2.1
      have heq := congrArg η.vMap htj
      exact (Set.disjoint_left.mp (hPP hij)) hsi (heq ▸ htj')

end GraphMinor.GM16
