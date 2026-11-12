/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.ConsecutivePatchInterface
public import LeanPool.ApollonianSuperharmonic.P4623T1ZeroBlockPaths
public import LeanPool.ApollonianSuperharmonic.P4623T1ZeroBlockExterior
public import LeanPool.ApollonianSuperharmonic.P4623T1ZeroBlockLinks

-- [TABLET NODE: BandOrderedGeneralFinitePatches]

/-!
# BandOrderedGeneralFinitePatches

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralFinitePatches
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    ∃ whole : FiniteInducedTilePatch
        cert.modified.plane cert.modified.tile,
      whole.indices =
        ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
          ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} :
          Finset PeriodicSubtileIndex) ∧
      whole.unionTile = T ∧
      cert.modified.tile ⟨.A, 0, 0⟩ =
        TileCellComplement (cert.P 0 true) cert.O ∧
      ∀ d ∈ whole.indices,
        ∃ rest : FiniteInducedTilePatch
            cert.modified.plane cert.modified.tile,
          rest.indices = whole.indices.erase d ∧
          rest.unionTile = TileCellComplement T (cert.modified.tile d) ∧
          Nonempty (ConsecutivePatchInterface
            cert.modified.plane cert.modified.tile rest d) := by
-- BODY
  classical
  let K : Finset PeriodicSubtileIndex :=
    {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
  have zero (l : SixSubtileLabel) : cert.modified.tile ⟨l, 0, 0⟩ =
      match l with
      | .A => TileCellComplement (cert.P 0 true) cert.O
      | .B => cert.P 0 false
      | .C => cert.P 1 true
      | .D => cert.P 1 false
      | .E => cert.P 2 true
      | .F => cert.P 2 false := by
    rw [cert.modified_tile]
    have ht : GaussianTranslation 0 = id := by
      funext z
      simp [GaussianTranslation]
    simp [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
      ht, GaussianTranslation]
    cases l <;> rfl
  have unique (x : LatticeCell) (a b : PeriodicSubtileIndex)
      (ha : x ∈ (cert.modified.tile a).cells)
      (hb : x ∈ (cert.modified.tile b).cells) : a = b := by
    obtain ⟨o, _, ho⟩ := cert.partition x
    have ha' : x ∈ (ModifiedSubtileOccurrenceInterpretation
        cert.P cert.O cert.u cert.v a).cells := by
      simpa only [cert.modified_tile a] using ha
    have hb' : x ∈ (ModifiedSubtileOccurrenceInterpretation
        cert.P cert.O cert.u cert.v b).cells := by
      simpa only [cert.modified_tile b] using hb
    exact (ho a ha').trans (ho b hb').symm
  have injective : Function.Injective cert.modified.tile := by
    intro a b hab
    obtain ⟨homeo⟩ := cert.modified.tiles_are_disks a
    have hp := (homeo ⟨0, by simp⟩).property
    change (homeo ⟨0, by simp⟩ : Real × Real) ∈
      TileRealization (cert.modified.tile a) at hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    obtain ⟨x, hxa, _⟩ := hp
    exact unique x a b hxa (by rw [← hab]; exact hxa)
  have precursor_in_minus (x : LatticeCell) (hx : x ∈ cert.O.cells) :
      x ∈ (cert.P 0 false).cells := by
    apply (cert.minus_union x).mpr
    exact ⟨0, true, by simpa only [← cert.precursor_cells] using hx⟩
  have whole_union (x : LatticeCell) : x ∈ T.cells ↔
      ∃ a ∈ K, x ∈ (cert.modified.tile a).cells := by
    constructor
    · intro hx
      obtain ⟨i, s, hx⟩ := (cert.outer_union x).mp hx
      fin_cases i <;> cases s
      · exact ⟨⟨.B, 0, 0⟩, by decide, by simpa [zero] using hx⟩
      · by_cases hO : x ∈ cert.O.cells
        · exact ⟨⟨.B, 0, 0⟩, by decide, by
            simpa [zero] using precursor_in_minus x hO⟩
        · exact ⟨⟨.A, 0, 0⟩, by decide, by
            simpa [zero, TileCellComplement, Finset.mem_sdiff] using
              And.intro hx hO⟩
      · exact ⟨⟨.D, 0, 0⟩, by decide, by simpa [zero] using hx⟩
      · exact ⟨⟨.C, 0, 0⟩, by decide, by simpa [zero] using hx⟩
      · exact ⟨⟨.F, 0, 0⟩, by decide, by simpa [zero] using hx⟩
      · exact ⟨⟨.E, 0, 0⟩, by decide, by simpa [zero] using hx⟩
    · rintro ⟨a, ha, hx⟩
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · apply (cert.outer_union x).mpr
        exact ⟨0, true, (Finset.mem_sdiff.mp (by
          simpa only [zero, TileCellComplement] using hx)).1⟩
      · exact (cert.outer_union x).mpr ⟨0, false, by simpa [zero] using hx⟩
      · exact (cert.outer_union x).mpr ⟨1, true, by simpa [zero] using hx⟩
      · exact (cert.outer_union x).mpr ⟨1, false, by simpa [zero] using hx⟩
      · exact (cert.outer_union x).mpr ⟨2, true, by simpa [zero] using hx⟩
      · exact (cert.outer_union x).mpr ⟨2, false, by simpa [zero] using hx⟩
  have rest_union (d : PeriodicSubtileIndex) (x : LatticeCell) :
      x ∈ (TileCellComplement T (cert.modified.tile d)).cells ↔
        ∃ a ∈ K.erase d, x ∈ (cert.modified.tile a).cells := by
    change x ∈ T.cells \ (cert.modified.tile d).cells ↔ _
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxT, hxd⟩
      obtain ⟨a, ha, hxa⟩ := (whole_union x).mp hxT
      refine ⟨a, Finset.mem_erase.mpr ⟨?_, ha⟩, hxa⟩
      intro had
      exact hxd (had ▸ hxa)
    · rintro ⟨a, ha, hxa⟩
      refine ⟨(whole_union x).mpr ⟨a, Finset.mem_of_mem_erase ha, hxa⟩, ?_⟩
      intro hxd
      exact (Finset.mem_erase.mp ha).1 (unique x a d hxa hxd)
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
        (List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he).1
  let makePatch (S : Finset PeriodicSubtileIndex) (U : ProtoTile)
      (hS : S = K ∨ ∃ d ∈ K, S = K.erase d) (hne : S.Nonempty)
      (hU : ∀ x, x ∈ U.cells ↔ ∃ a ∈ S, x ∈ (cert.modified.tile a).cells) :
      FiniteInducedTilePatch cert.modified.plane cert.modified.tile := {
    indices := S
    unionTile := U
    nonempty := hne
    tile_injective := injective.injOn
    exact_union := hU
    induced_connected := by
      intro a ha b hb
      exact walk (fun x ↦ x ∈ S) a b ha
        (P4623T1ZeroBlockPaths S hS a ha b hb)
    complement_connected := by
      intro a ha b hb
      exact walk (fun x ↦ x ∉ S) a b ha
        (P4623T1ZeroBlockExterior S hS a ha b hb)
  }
  let whole := makePatch K T (Or.inl rfl) (by decide) whole_union
  refine ⟨whole, rfl, rfl, zero .A, ?_⟩
  intro d hd
  change d ∈ K at hd
  have hne : (K.erase d).Nonempty := by
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let rest := makePatch (K.erase d) (TileCellComplement T (cert.modified.tile d))
    (Or.inr ⟨d, hd, rfl⟩) hne (rest_union d)
  obtain ⟨n, N, F, hn, hN, hF, hneighbors, hfaces⟩ := P4623T1ZeroBlockLinks d hd
  refine ⟨rest, rfl, rfl, ⟨{
    exterior := by change d ∉ K.erase d; exact Finset.notMem_erase d K
    length := n
    positive := hn
    neighbor := N
    face := cert.modifiedFaceEquivalence.symm ∘ F
    neighbor_injective := hN
    face_injective := cert.modifiedFaceEquivalence.symm.injective.comp hF
    neighbors_exact := ?_
    consecutive_faces := ?_
  }⟩⟩
  · intro b
    change b ∈ K.erase d ∧ cert.modified.plane.adjacent d b ↔ ∃ k, N k = b
    rw [cert.modified_adjacency]
    exact hneighbors b
  · intro k
    simpa only [Function.comp_apply, cert.modified_face_vertices,
      Equiv.apply_symm_apply] using hfaces k

end ApollonianSuperharmonic

end
