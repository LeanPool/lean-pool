/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.SpanCongr

/-!
# Transporting a horn along equal drawings and metrics

The paths and the vertex map of a horn do not change when the drawing
and its embedding are identified. Only the endpoint distances need
comparison. This transports the horns after the successive clearings
in XVI (7.1), Claim (4), page 69.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v}

omit [T2Space S] in
/-- Reindex the paths of a horn by an equivalence of their finite
index sets. -/
theorem horn_reindex {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {a : α} {θ σ σ' : ℕ}
    {P : Fin σ → Graph α β} {u : Fin σ → S}
    (e : Fin σ' ≃ Fin σ) (h : IsHorn G H η d a θ σ P u) :
    IsHorn G H η d a θ σ' (fun i => P (e i)) (fun i => u (e i)) := by
  obtain ⟨ha, hu, hP, hInter, hDis, hDist⟩ := h
  refine ⟨ha, fun i => hu (e i), fun i => hP (e i), fun i => hInter (e i), ?_, ?_⟩
  · intro i j hij
    exact hDis (e i) (e j) (fun h => hij (e.injective h))
  · intro i j hij
    exact hDist (e i) (e j) (fun h => hij (e.injective h))

omit [T2Space S] in
/-- Identify the drawing and embedding of a horn and replace its
metric by one agreeing on the drawing vertices. -/
theorem horn_congr_drawing_embedding {G : Graph α β} {H K : Drawing S}
    (hHK : H = K) (η : SpanEmbedding H G) (η' : SpanEmbedding K G)
    (hv : η.vMap = η'.vMap) (he : η.eMap = η'.eMap)
    {d d' : Set S → Set S → ℕ} {a : α} {θ σ : ℕ}
    {P : Fin σ → Graph α β} {u : Fin σ → S}
    (hEq : ∀ x ∈ H.V, ∀ y ∈ H.V, d {x} {y} = d' {x} {y})
    (hHorn : IsHorn G H η d a θ σ P u) : IsHorn G K η' d' a θ σ P u := by
  subst K
  have hη := spanEmbedding_eq_of_maps η η' hv he
  subst η'
  obtain ⟨ha, hu, hP, hInter, hDis, hDist⟩ := hHorn
  refine ⟨ha, hu, hP, hInter, hDis, ?_⟩
  intro i j hij
  rw [← hEq (u i) (hu i) (u j) (hu j)]
  exact hDist i j hij

end GraphMinor.GM16
