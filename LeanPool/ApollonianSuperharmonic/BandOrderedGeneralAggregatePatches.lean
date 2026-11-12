/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.FiniteInducedTilePatch
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.P3161T1AggregateInducedConnectivity
public import LeanPool.ApollonianSuperharmonic.P3161T1AggregateComplementConnectivity
public import Mathlib.Data.List.Chain

-- [TABLET NODE: BandOrderedGeneralAggregatePatches]

/-!
# BandOrderedGeneralAggregatePatches

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralAggregatePatches
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
      {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
        ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
    let triangles : Finset (Finset (Int × Int)) :=
      {
        {(0, 0), (1, 0), (0, -1)},
        {(0, 0), (0, 1), (1, 1)},
        {(0, 0), (-1, -1), (-1, 0)}
      }
    ∀ τ ∈ triangles, ∀ σ ∈ τ.powerset, σ.Nonempty →
      ∃ patch : FiniteInducedTilePatch
          cert.modified.plane cert.modified.tile,
        patch.indices = σ.biUnion (fun mn ↦ K mn.1 mn.2) ∧
        ∀ x, x ∈ patch.unionTile.cells ↔
          ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2,
            x ∈ (cert.modified.tile a).cells := by
-- BODY
  classical
  dsimp only
  intro τ hτ σ hσ hnonempty
  have hsubset : σ ⊆ τ := Finset.mem_powerset.mp hσ
  let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
    {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
      ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
  let I := σ.biUnion (fun mn ↦ K mn.1 mn.2)
  have memI (a : PeriodicSubtileIndex) :
      a ∈ I ↔ (a.first, a.second) ∈ σ := by
    constructor
    · intro ha
      obtain ⟨z, hz, ha⟩ := Finset.mem_biUnion.mp ha
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hz
    · intro ha
      refine Finset.mem_biUnion.mpr ⟨(a.first, a.second), ha, ?_⟩
      cases a with | mk label m n => cases label <;> simp [K]
  have hI : I.Nonempty := by
    obtain ⟨z, hz⟩ := hnonempty
    exact ⟨⟨.A, z.1, z.2⟩, (memI _).mpr hz⟩
  let U : ProtoTile := ⟨I.biUnion (fun a ↦ (cert.modified.tile a).cells), 0⟩
  have exactU (x : LatticeCell) :
      x ∈ U.cells ↔ ∃ a ∈ I, x ∈ (cert.modified.tile a).cells :=
    Finset.mem_biUnion
  have injective : Set.InjOn cert.modified.tile (I : Set PeriodicSubtileIndex) := by
    intro a _ b _ hab
    obtain ⟨homeo⟩ := cert.modified.tiles_are_disks a
    have hp := (homeo ⟨0, by simp⟩).property
    change (homeo ⟨0, by simp⟩ : Real × Real) ∈
      TileRealization (cert.modified.tile a) at hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    obtain ⟨x, hxa, _⟩ := hp
    have hxb : x ∈ (cert.modified.tile b).cells := by rw [← hab]; exact hxa
    have ha : x ∈ (ModifiedSubtileOccurrenceInterpretation
        cert.P cert.O cert.u cert.v a).cells := by
      simpa only [cert.modified_tile a] using hxa
    have hb : x ∈ (ModifiedSubtileOccurrenceInterpretation
        cert.P cert.O cert.u cert.v b).cells := by
      simpa only [cert.modified_tile b] using hxb
    obtain ⟨o, _, unique⟩ := cert.partition x
    exact (unique a ha).trans (unique b hb).symm
  have walk (S : PeriodicSubtileIndex → Prop) (a b : PeriodicSubtileIndex)
      (ha : S a)
      (h : Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ S x ∧ S y) a b) :
      ∃ p : List PeriodicSubtileIndex,
        p.head? = some a ∧ p.getLast? = some b ∧
        (∀ x ∈ p, S x) ∧
        ∀ x y : PeriodicSubtileIndex, ∀ l₁ l₂ : List PeriodicSubtileIndex,
          p = l₁ ++ x :: y :: l₂ → cert.modified.plane.adjacent x y := by
    obtain ⟨l, hc, hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    refine ⟨a :: l, rfl, ?_, ?_, ?_⟩
    · simpa only [List.getLast?_eq_some_getLast (List.cons_ne_nil a l)]
        using congrArg some hl
    · have go : ∀ (u : PeriodicSubtileIndex) (p : List PeriodicSubtileIndex), S u →
          (u :: p).IsChain (fun x y ↦ AllowedSubtileIncidence x y ∧ S x ∧ S y) →
          ∀ x ∈ u :: p, S x := by
        intro u p
        induction p generalizing u with
        | nil => simp_all
        | cons v p ih =>
          intro hu hc x hx
          simp only [List.mem_cons] at hx
          rcases hx with hx | hx
          · exact hx.symm ▸ hu
          · exact ih v hc.rel.2.2 hc.tail x (by simpa only [List.mem_cons] using hx)
      exact go a l ha hc
    · intro x y l₁ l₂ he
      exact (cert.modified_adjacency x y).mpr
        ((List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he).1)
  let patch : FiniteInducedTilePatch cert.modified.plane cert.modified.tile := {
    indices := I
    unionTile := U
    nonempty := hI
    tile_injective := injective
    exact_union := exactU
    induced_connected := by
      intro a ha b hb
      apply walk (fun x ↦ x ∈ I) a b ha
      exact Relation.ReflTransGen.mono
        (fun x y e ↦ ⟨e.1, (memI x).mpr e.2.1, (memI y).mpr e.2.2⟩) a b
        (P3161T1AggregateInducedConnectivity τ σ hτ hsubset a b
          ((memI a).mp ha) ((memI b).mp hb))
    complement_connected := by
      intro a ha b hb
      apply walk (fun x ↦ x ∉ I) a b ha
      exact Relation.ReflTransGen.mono
        (fun x y e ↦ ⟨e.1, fun hx ↦ e.2.1 ((memI x).mp hx),
          fun hy ↦ e.2.2 ((memI y).mp hy)⟩) a b
        (P3161T1AggregateComplementConnectivity τ σ hτ hsubset a b
          (fun hx ↦ ha ((memI a).mpr hx)) (fun hy ↦ hb ((memI b).mpr hy)))
  }
  refine ⟨patch, rfl, ?_⟩
  intro x
  change x ∈ U.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2,
    x ∈ (cert.modified.tile a).cells
  rw [exactU]
  simp only [I, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ⟨mn, hmn, ha⟩, hx⟩
    exact ⟨mn, hmn, a, ha, hx⟩
  · rintro ⟨mn, hmn, a, ha, hx⟩
    exact ⟨a, ⟨mn, hmn, ha⟩, hx⟩

end ApollonianSuperharmonic

end
