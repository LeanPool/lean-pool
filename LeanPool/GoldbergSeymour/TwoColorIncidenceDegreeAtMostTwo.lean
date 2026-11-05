/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Basic.Finite.Sum

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Two Color Incidence Degree At Most Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorIncidenceDegreeAtMostTwo {V E : Type*}
    [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z : Sum V E) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) z (Fintype.ofFinite _) ≤
      2 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  cases z with
  | inl v =>
    let neighbors := {x : E // Sum.inr x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl v)}
    let : Fintype neighbors := Fintype.ofFinite neighbors
    let chooseColor : neighbors → Fin 2 := fun x =>
      if phi x.1 = some alpha then 0 else 1
    have chooseColor_injective : Function.Injective chooseColor := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hx := x.2
      have hy := y.2
      have hxraw := x.2
      have hyraw := y.2
      simp only [TwoColorIncidenceGraph, SimpleGraph.mem_neighborSet] at hx hy
      rcases hx with ⟨hxinc, hxcol⟩
      rcases hy with ⟨hyinc, hycol⟩
      by_cases hxa : phi x.1 = some alpha
      · have hya : phi y.1 = some alpha := by simpa [chooseColor, hxa] using hxy
        exact (hproper hne (⟨v, hxinc, hyinc⟩) hxa) hya
      · have hxb : phi x.1 = some beta := hxcol.resolve_left hxa
        have hyb : phi y.1 = some beta := hycol.resolve_left (by
          intro hya
          have hzero : chooseColor ⟨y.1, hyraw⟩ = 0 := by simp [chooseColor, hya]
          have hone : chooseColor ⟨x.1, hxraw⟩ = 1 := by simp [chooseColor, hxa]
          have : (1 : Fin 2) = 0 := hone.symm.trans (hxy.trans hzero)
          exact Fin.zero_ne_one this.symm)
        exact (hproper hne (⟨v, hxinc, hyinc⟩) hxb) hyb
    have hc : Fintype.card neighbors ≤ Fintype.card (Fin 2) :=
      Fintype.card_le_of_injective chooseColor chooseColor_injective
    have existsEdge (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inl v)}) :
        ∃ e, x.1 = Sum.inr e := by
      cases hx : x.1 with
      | inl w =>
          have hp := x.2; rw [hx] at hp; simp [SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] at hp
      | inr e => simp []
    let edgeOf (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl v)}) : E :=
      Classical.choose (existsEdge x)
    have edgeOf_spec (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inl v)}) :
        x.1 = Sum.inr (edgeOf x) := Classical.choose_spec (existsEdge x)
    have fullInjective : Function.Injective (fun x => chooseColor ⟨edgeOf x, by
      rw [← edgeOf_spec x] at *
      exact x.2⟩) := by
      intro x y h
      apply Subtype.ext
      rw [edgeOf_spec x, edgeOf_spec y]
      have hx := x.2
      have hy := y.2
      rw [edgeOf_spec x] at hx
      rw [edgeOf_spec y] at hy
      simp only [TwoColorIncidenceGraph, SimpleGraph.mem_neighborSet] at hx hy
      by_cases heq : edgeOf x = edgeOf y
      · exact congrArg Sum.inr heq
      exfalso
      by_cases ha : phi (edgeOf x) = some alpha
      · have hb : phi (edgeOf y) = some alpha := by simpa [chooseColor, ha] using h
        exact (hproper heq (⟨v, hx.1, hy.1⟩) ha) hb
      · have hb : phi (edgeOf x) = some beta := by
          exact hx.2.resolve_left ha
        have hc : phi (edgeOf y) = some beta := by
          have : ¬ phi (edgeOf y) = some alpha := by
            intro hy
            have : (0 : Fin 2) = 1 := by simpa [chooseColor, ha, hy] using h.symm
            exact Fin.zero_ne_one this
          exact hy.2.resolve_left this
        exact (hproper heq (⟨v, hx.1, hy.1⟩) hb) hc
    let : Fintype {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl v)} := Fintype.ofFinite _
    have fullBound : Fintype.card {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inl v)} ≤ 2 := by
      simpa using Fintype.card_le_of_injective _ fullInjective
    exact fullBound
  | inr e =>
    let neighbors := {x : V // Sum.inl x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inr e)}
    let endpoints := (G.ends e).toFinset
    let : Fintype neighbors := Fintype.ofFinite neighbors
    have map_injective : Function.Injective (fun x : neighbors => (⟨x.1, Sym2.mem_toFinset.mpr
        x.2.1⟩ : endpoints)) := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun q => q.1) h
    have hc : Fintype.card neighbors ≤ Fintype.card endpoints :=
      Fintype.card_le_of_injective _ map_injective
    have he : Fintype.card endpoints ≤ 2 := by
      rw [Fintype.card_coe, Sym2.card_toFinset]
      split <;> omega
    have existsVertex (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inr e)}) :
        ∃ v, x.1 = Sum.inl v := by
      cases hx : x.1 with
      | inl v => simp []
      | inr f =>
          have hp := x.2; rw [hx] at hp; simp [SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] at hp
    let vertexOf (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inr e)}) : V :=
      Classical.choose (existsVertex x)
    have vertexOf_spec (x : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inr e)}) :
        x.1 = Sum.inl (vertexOf x) := Classical.choose_spec (existsVertex x)
    let : Fintype {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inr e)} := Fintype.ofFinite _
    let map : {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha beta).neighborSet (Sum.inr
        e)} → endpoints := fun x => ⟨vertexOf x, by
      have hp := x.2
      rw [vertexOf_spec x] at hp
      simp only [TwoColorIncidenceGraph, SimpleGraph.mem_neighborSet] at hp
      exact Sym2.mem_toFinset.mpr hp.1⟩
    have fullBound : Fintype.card {x : Sum V E // x ∈ (TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inr e)} ≤ Fintype.card endpoints := by
      apply Fintype.card_le_of_injective map
      intro x y h
      apply Subtype.ext
      rw [vertexOf_spec x, vertexOf_spec y]
      exact congrArg Sum.inl (congrArg Subtype.val h)
    exact fullBound.trans he

end GoldbergSeymour

end
