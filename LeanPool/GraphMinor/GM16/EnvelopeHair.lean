/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8
import LeanPool.GraphMinor.GM16.EnvelopeExitPaths
import LeanPool.GraphMinor.GM16.EnvelopeHairMetric
import LeanPool.GraphMinor.GM16.HairBetweenExits
import LeanPool.GraphMinor.GM16.SpanSubdrawing
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9Attachments
import LeanPool.GraphMinor.GM16.ClearedPathVertices
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Section88
import LeanPool.GraphMinor.GM09.Basic

/-!
# Extending one hair to the cleared drawing

Use the chosen exit path at the near end and a first exit path at
the far end. Their union with the old hair contains a path relative
to the cleared drawing. Work in the graph with the horn centres
deleted so the new hair still avoids them. The compression estimate
makes the two new ends far apart. This is XVI (7.1), Claim (6), page 70.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- An old hair and the exit path chosen at its near end yield a
hair of the cleared drawing with the required new breadth. -/
theorem exists_hair_after_envelope (hS : IsClosedSurface S)
    {H P : Drawing S} {G Q : Graph α β} (η : SpanEmbedding H G)
    {θ γ loss θ₂ : ℕ} {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S} {Λ : S → Set S} {X : Set α}
    (hEnv : IsEnvelope H d Y γ Λ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ loss T T' d d')
    (hX : X ⊆ V(G) \ V(η.imageGraph)) (hθ₂ : 1 ≤ θ₂)
    (hBudget : θ₂ + 3 * γ + loss ≤ θ)
    {y r p : S} (hy : y ∈ Y) (hr : r ∈ H.V)
    (hp : p ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hP : P.IsSubdrawing H) (hPath : P.IsPathBetween y p)
    (hPClear : P.V ∩ (clearEnvelopeDrawing H Y Λ).V = {p})
    (hyp : d {y} {p} ≤ γ)
    (hQ : IsHPathWithEnds G η.imageGraph Q (η.vMap y) (η.vMap r))
    (hQX : Disjoint X V(Q)) (hFar : θ ≤ d {y} {r}) :
    ∃ q ∈ (clearEnvelopeDrawing H Y Λ).V, ∃ R : Graph α β,
      p ≠ q ∧ IsHPathWithEnds G (restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph R
        (η.vMap p) (η.vMap q) ∧ Disjoint X V(R) ∧ θ₂ ≤ d' {p} {q} := by
  classical
  let K := clearEnvelopeDrawing H Y Λ
  let ηK := restrictCleared η (⋃ y ∈ Y, Λ y)
  have hKH : K.IsSubdrawing H := interSet_isSub
  have hyH := hEnv.1 hy
  obtain ⟨q, hq, B, hBPath, hBH, hBClear, hrq⟩ :=
    exists_envelope_vertex_exit hS hComp.hasMetric hEnv hr
  have hDist : θ₂ ≤ d' {p} {q} := envelope_hair_end_distance hS hKH hComp
    hyH hr hp hq hFar hyp hrq hBudget
  obtain ⟨_, hSelf, _, _, _, _⟩ := GM11.gm15_theorem_9_1 K (θ - loss) T' d' hS inferInstance
    hComp.hasMetric'
  have hpq : p ≠ q := by
    intro heq
    rw [heq, hSelf {q} (Or.inl (Or.inl ⟨q, hq, rfl⟩))] at hDist
    omega
  have hOldDis : Disjoint V(η.imageGraph) X := by
    apply disjoint_left.mpr
    exact fun x hx hxX => (hX hxX).2 hx
  have hOldDel : η.imageGraph ≤ deleteVertices G X := le_deleteVertices_of_disjoint η.imageGraph_le
    hOldDis
  obtain ⟨A, hA, hAV, hAOld⟩ := exists_span_image_path η hP hPath
  obtain ⟨B', hB', hBV, hBOld⟩ := exists_span_image_path η hBH hBPath
  have hAKV : V(ηK.imageGraph) = η.vMap '' K.V := by rw [← ηK.bijOn_v.image_eq]; rfl
  have hAClear : V(A) ∩ V(ηK.imageGraph) = {η.vMap p} := by
    rw [hAV, hAKV, ← η.bijOn_v.injOn.image_inter hP.1 hKH.1, hPClear, image_singleton]
  have hBClear' : V(B') ∩ V(ηK.imageGraph) = {η.vMap q} := by
    rw [hBV, hAKV, ← η.bijOn_v.injOn.image_inter hBH.1 hKH.1, hBClear, image_singleton]
  have hyNot : η.vMap y ∉ V(ηK.imageGraph) := by
    rw [hAKV]
    rintro ⟨z, hz, hzy⟩
    have hzy' := η.bijOn_v.injOn (hKH.1 hz) hyH hzy
    have hyK : y ∈ K.V := hzy' ▸ hz
    have hOut := (clearFamily_U hEnv.2.1 ▸ K.V_subset_U hyK).2
    exact hOut (mem_iUnion₂.mpr ⟨y, hy, (hEnv.2.1 y hy).z_subset (mem_singleton y)⟩)
  have hpK : η.vMap p ∈ V(ηK.imageGraph) := hAKV.symm ▸ mem_image_of_mem η.vMap hp
  have hqK : η.vMap q ∈ V(ηK.imageGraph) := hAKV.symm ▸ mem_image_of_mem η.vMap hq
  have hpqIm : η.vMap p ≠ η.vMap q := fun h => hpq (η.bijOn_v.injOn (hKH.1 hp) (hKH.1 hq) h)
  have hQDel : IsHPathWithEnds (deleteVertices G X) η.imageGraph Q (η.vMap y) (η.vMap r) :=
    ⟨hOldDel, hQ.2.1.in_deleteVertices hQX, hQ.2.2⟩
  obtain ⟨R, hR⟩ := exists_hPath_between_exits (restrictCleared_imageGraph_le η (⋃ y ∈ Y, Λ y))
    hQDel (hA.of_le (hAOld.trans hOldDel)) (hB'.of_le (hBOld.trans hOldDel))
    hAClear hBClear' hyNot hpK hqK hpqIm
  have hRX : Disjoint X V(R) := by
    apply disjoint_left.mpr
    intro x hxX hxR
    exact (hR.2.1.1.vertexSet_mono hxR).2 hxX
  have hRG : IsHPathWithEnds G ηK.imageGraph R (η.vMap p) (η.vMap q) :=
    ⟨ηK.imageGraph_le, hR.2.1.mono (deleteVertices_le G X), hR.2.2⟩
  exact ⟨q, hq, R, hpq, hRG, hRX, hDist⟩

end GraphMinor.GM16
