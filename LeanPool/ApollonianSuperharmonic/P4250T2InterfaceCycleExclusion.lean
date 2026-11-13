/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity

-- [TABLET NODE: P4250T2InterfaceCycleExclusion]

/-!
# P4250T2InterfaceCycleExclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InterfaceCycleGeometry

private theorem path_omits_boundary :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (LatticeTile U) → (∀ (Q : Set GaussianInt), ∀ (R : Set (Finset
            GaussianInt)), (SimpleGridPath Q R) → (∃ e ∈ BoundaryFootprintEdges U, e ∉ R)) ) := by
  classical
  intro U hU Q R hR
  as_aux_lemma =>
  have hUne : U.cells.Nonempty := (LatticeTileGridStructure U hU).1.1
  obtain ⟨r, hr, hrl, hrv, hra, hre⟩ := hR
  obtain ⟨p, x, y, hp, hpl, hph, hpt, hpv, hpc, hpa, hpe⟩ :=
    (LatticeTileGridStructure U hU).2.2
  have hpne : p.toFinset.Nonempty := by
    obtain ⟨p', hp'⟩ := List.head?_eq_some_iff.mp hph
    exact ⟨x, by simp [hp']⟩
  obtain ⟨v, hv, hmin⟩ := p.toFinset.exists_min_image (fun a => r.idxOf a) hpne
  have hvU : v ∈ BoundaryFootprintVertices U := by
    rw [hpv]; exact hv
  have hminU : ∀ w ∈ BoundaryFootprintVertices U, r.idxOf v ≤ r.idxOf w := by
    intro w hw
    apply hmin w
    simpa [hpv] using hw
  have degree := BoundaryFootprintVertexDegreeTwo U hUne
    (LatticeTileGridStructure U hU).2.1 v hvU
  obtain ⟨e, f, hef, heq⟩ := Set.ncard_eq_two.mp degree
  have he : e ∈ BoundaryFootprintEdges U ∧ v ∈ e := by
    change e ∈ {e | e ∈ BoundaryFootprintEdges U ∧ v ∈ e}
    rw [heq]; simp
  have hf : f ∈ BoundaryFootprintEdges U ∧ v ∈ f := by
    change f ∈ {e | e ∈ BoundaryFootprintEdges U ∧ v ∈ e}
    rw [heq]; simp
  by_contra hn
  have hall : ∀ e ∈ BoundaryFootprintEdges U, e ∈ R := by
    simpa only [not_exists, not_and, not_not] using hn
  have outgoing : ∀ e ∈ BoundaryFootprintEdges U, v ∈ e →
      ∃ w, e = {v, w} ∧ r.idxOf w = r.idxOf v + 1 := by
    intro e he hve
    obtain ⟨a, b, l₁, l₂, hd, rfl⟩ := (hre e).mp (hall e he)
    have haU : a ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hUne]
      exact ⟨{a, b}, he, by simp⟩
    have hbU : b ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hUne]
      exact ⟨{a, b}, he, by simp⟩
    have hai : r.idxOf a = l₁.length := by
      have hi : l₁.length < r.length := by simp [hd]
      have hh := hr.idxOf_getElem l₁.length hi
      simpa [hd] using hh
    have hbi : r.idxOf b = l₁.length + 1 := by
      have hi : l₁.length + 1 < r.length := by simp [hd]
      have hh := hr.idxOf_getElem (l₁.length + 1) hi
      simpa [hd] using hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl
    · exact ⟨b, rfl, by omega⟩
    · have := hminU a haU
      omega
  obtain ⟨a, hea, hai⟩ := outgoing e he.1 he.2
  obtain ⟨b, hfb, hbi⟩ := outgoing f hf.1 hf.2
  have ha : a ∈ r := by
    obtain ⟨c, d, l₁, l₂, hd, hecd⟩ := (hre e).mp (hall e he.1)
    have ha : a ∈ ({c, d} : Finset GaussianInt) := by rw [← hecd, hea]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> rw [hd] <;> simp
  have hab : a = b := (List.idxOf_inj ha).mp (by omega)
  exact hef (by rw [hea, hfb, hab])

private theorem attachment :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (BandPrototile (q (0 : Fin (4 : ℕ)))
            T) → ((∀ (U : ProtoTile), (LatticeTile U) → (∀ (Q : Set GaussianInt), ∀ (R : Set
            (Finset GaussianInt)), (SimpleGridPath Q R) → (∃ e ∈ BoundaryFootprintEdges U, e ∉
            R))) → (∀ i, ∀ s, ∃ e : Finset GaussianInt, e ∈ BoundaryFootprintEdges (cert.P i s) ∧
            e ∈ BoundaryFootprintEdges T)) ) := by
  classical
  intro C q cfg T cert hT path_omits_boundary
  as_aux_lemma =>
  intro i s
  let U := cert.P i s
  let K := TileCellComplement T U
  have hcomp := (BandTileSimultaneousInduction q cfg.proper T hT).2.2.1
    cert.P cert.outer_occurrence cert.outer_union i s
  rcases hcomp with ⟨hKlat, htouch⟩
  have hUne : U.cells.Nonempty :=
    (LatticeTileGridStructure U (cert.parent_lattice i s)).1.1
  have hKne : K.cells.Nonempty := (LatticeTileGridStructure K hKlat).1.1
  have hsub : ∀ z ∈ U.cells, z ∈ T.cells := by
    intro z hz
    exact (cert.outer_union z).mpr ⟨i, s, hz⟩
  have hKmem : ∀ z, z ∈ K.cells ↔ z ∈ T.cells ∧ z ∉ U.cells := by
    intro z
    exact Finset.mem_sdiff
  rcases htouch with hpath | hempty | hempty
  · obtain ⟨e, he, hnot⟩ := path_omits_boundary U (cert.parent_lattice i s)
      _ _ hpath.2.2.2
    have heK : e ∉ BoundaryFootprintEdges K := fun h => hnot ⟨h, he⟩
    refine ⟨e, he, ?_⟩
    have lift_cells : ∀ a b,
        ((a ∈ U.cells ∧ b ∉ U.cells) ∨ (a ∉ U.cells ∧ b ∈ U.cells)) →
        ¬ ((a ∈ K.cells ∧ b ∉ K.cells) ∨ (a ∉ K.cells ∧ b ∈ K.cells)) →
        ((a ∈ T.cells ∧ b ∉ T.cells) ∨ (a ∉ T.cells ∧ b ∈ T.cells)) := by
      intro a b hu hk
      simp only [hKmem] at hk
      rcases hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := hsub a ha
        clear * - ha hb hk this
        tauto
      · have := hsub b hb
        clear * - ha hb hk this
        tauto
    rcases he with ⟨z, (⟨hez, hz⟩ | ⟨hez, hz⟩)⟩
    · refine ⟨z, Or.inl ⟨hez, lift_cells z (z - ⟨0, 1⟩) hz ?_⟩⟩
      intro hk
      exact heK ⟨z, Or.inl ⟨hez, hk⟩⟩
    · refine ⟨z, Or.inr ⟨hez, lift_cells z (z - 1) hz ?_⟩⟩
      intro hk
      exact heK ⟨z, Or.inr ⟨hez, hk⟩⟩
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hKne) hempty.1)
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hUne) hempty.1)

private theorem hpInDifference :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), ∀ (V : Set GaussianInt), (V ⊆
            (↑(D \ P) : Set GaussianInt)) → (∀ (p : List GaussianInt), (V = (↑p.toFinset : Set
            GaussianInt)) → (∀ z, z ∈ p → z ∈ ((D \ P : Finset GaussianInt) : Set GaussianInt)))
            ) := by
  classical
  intro D P V hsub p hV z hz
  have hzV : z ∈ V := by
    rw [hV]
    exact List.mem_toFinset.mpr hz
  exact hsub hzV

private theorem hpInD :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), ∀ (p : List GaussianInt), (∀ z, z
            ∈ p → z ∈ ((D \ P : Finset GaussianInt) : Set GaussianInt)) → (∀ z, z ∈ p → z ∈ D) )
            := by
  classical
  intro D P p hpInDifference z hz
  exact (Finset.mem_sdiff.mp (hpInDifference z hz)).1

private theorem hpNotP :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), ∀ (p : List GaussianInt), (∀ z, z
            ∈ p → z ∈ ((D \ P : Finset GaussianInt) : Set GaussianInt)) → (∀ z, z ∈ p → z ∉ P) )
            := by
  classical
  intro D P p hpInDifference z hz
  exact (Finset.mem_sdiff.mp (hpInDifference z hz)).2

private theorem hpInteriorT :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (x : GaussianInt), x ∈ D ↔ x ∈
            FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T) → (∀ (p : List GaussianInt),
            (∀ z, z ∈ p → z ∈ D) → (∀ z, z ∈ p → z ∈ FootprintVertices T ∧ z ∉
            BoundaryFootprintVertices T)) ) := by
  classical
  intro T D hD p hpInD z hz
  exact (hD z).mp (hpInD z hz)

private theorem hpParentBoundary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → (∀ (p : List GaussianInt), (∀ z, z ∈ p → z ∈ D) → ((∀ z, z ∈ p → z ∉ P) → (∀ z,
            z ∈ p → ∀ i, ∀ s, z ∈ FootprintVertices (cert.P i s) → z ∈ BoundaryFootprintVertices
            (cert.P i s)))) ) := by
  classical
  intro C q cfg T cert D P hP p hpInD hpNotP z hz i s hzFoot
  by_contra hzNotBoundary
  apply hpNotP z hz
  exact (hP z).mpr ⟨hpInD z hz, i, s, hzFoot, hzNotBoundary⟩

private theorem vertex_cells :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (v : GaussianInt), (v ∈ FootprintVertices U) →
            ((v ∉ BoundaryFootprintVertices U) → (v ∈ U.cells ∧ v - 1 ∈ U.cells ∧ v - ⟨0, 1⟩ ∈
            U.cells ∧ v - 1 - ⟨0, 1⟩ ∈ U.cells))) ) := by
  classical
  intro U hne v hv hnb
  as_aux_lemma =>
  have horizontal (z : GaussianInt) (hz : v ∈ ({z, z + 1} : Finset GaussianInt)) :
      z ∈ U.cells ↔ z - ⟨0, 1⟩ ∈ U.cells := by
    by_contra hh
    apply hnb
    rw [BoundaryFootprintVertices, ite_eq_left hne]
    refine ⟨{z, z + 1}, ⟨z, Or.inl ⟨rfl, ?_⟩⟩, hz⟩
    clear * - hh
    tauto
  have vertical (z : GaussianInt)
      (hz : v ∈ ({z, z + ⟨0, 1⟩} : Finset GaussianInt)) :
      z ∈ U.cells ↔ z - 1 ∈ U.cells := by
    by_contra hh
    have hxor : (z ∈ U.cells ∧ z - 1 ∉ U.cells) ∨
        (z ∉ U.cells ∧ z - 1 ∈ U.cells) := by
      by_cases ha : z ∈ U.cells
      · exact Or.inl ⟨ha, fun hb => hh ⟨fun _ => hb, fun _ => ha⟩⟩
      · refine Or.inr ⟨ha, ?_⟩
        by_contra hb
        exact hh ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩
    have he : ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U := by
      refine ⟨z, ?_⟩
      exact Or.inr ⟨rfl, hxor⟩
    apply hnb
    rw [BoundaryFootprintVertices, ite_eq_left hne]
    exact ⟨{z, z + ⟨0, 1⟩}, he, hz⟩
  have h₁ := horizontal v (by simp)
  have h₂ := vertical v (by simp)
  have h₃ := horizontal (v - 1) (by simp)
  have hany : v ∈ U.cells ∨ v - 1 ∈ U.cells ∨ v - ⟨0, 1⟩ ∈ U.cells ∨
      v - 1 - ⟨0, 1⟩ ∈ U.cells := by
    rw [FootprintVertices, ite_eq_left hne] at hv
    obtain ⟨a, ha, hv⟩ := hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by simpa using ha))
    · exact Or.inr (Or.inr (Or.inl (by simpa using ha)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [sub_sub] using ha)))
  have hvc : v ∈ U.cells := by
    rcases hany with hh | hh | hh | hh
    · exact hh
    · exact h₂.mpr hh
    · exact h₁.mpr hh
    · exact h₂.mpr (h₃.mpr hh)
  exact ⟨hvc, h₂.mp hvc, h₁.mp hvc, h₃.mp (h₂.mp hvc)⟩

private theorem hpCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (p : List GaussianInt), (∀ z, z ∈ p → z ∈ FootprintVertices T ∧ z ∉
            BoundaryFootprintVertices T) → ((T.cells.Nonempty) → ((∀ (U : ProtoTile),
            (U.cells.Nonempty) → (∀ (v : GaussianInt), (v ∈ FootprintVertices U) → ((v ∉
            BoundaryFootprintVertices U) → (v ∈ U.cells ∧ v - 1 ∈ U.cells ∧ v - ⟨0, 1⟩ ∈ U.cells
            ∧ v - 1 - ⟨0, 1⟩ ∈ U.cells)))) → (∀ z ∈ p, z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - ⟨0, 1⟩
            ∈ T.cells ∧ z - 1 - ⟨0, 1⟩ ∈ T.cells))) ) := by
  classical
  intro T p hpInteriorT hTne vertex_cells z hz
  exact vertex_cells T hTne z (hpInteriorT z hz).1 (hpInteriorT z hz).2

private theorem horizontal_interior :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ((z - ⟨0, 1⟩ ∈ U.cells) →
            (OpenLatticeEdge z (z + 1) ⊆ interior (TileRealization U))) ) := by
  classical
  intro U z hz hzs
  as_aux_lemma =>
  let R : Set (Real × Real) :=
    Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
      Set.Ioo ((z.im : Real) - 1) ((z.im : Real) + 1)
  have hRopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRU : R ⊆ TileRealization U := by
    intro a ha
    rcases ha with ⟨ha₁, ha₂⟩
    by_cases hs : a.2 ≤ (z.im : Real)
    · apply Set.mem_iUnion.mpr
      refine ⟨z - ⟨0, 1⟩, Set.mem_iUnion.mpr ⟨hzs, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Int.cast_sub, Int.cast_one, sub_zero]
      constructor <;> constructor <;> linarith [ha₁.1, ha₁.2, ha₂.1, ha₂.2]
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith [ha₁.1, ha₁.2, ha₂.1, ha₂.2]
  intro a ha
  apply interior_maximal hRU hRopen
  obtain ⟨t, ht₀, ht₁, rfl⟩ := ha
  simp [R, GaussianRealPoint]
  constructor <;> constructor <;> nlinarith

private theorem vertical_interior :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ((z - 1 ∈ U.cells) →
            (OpenLatticeEdge z (z + ⟨0, 1⟩) ⊆ interior (TileRealization U))) ) := by
  classical
  intro U z hz hzw
  as_aux_lemma =>
  let R : Set (Real × Real) :=
    Set.Ioo ((z.re : Real) - 1) ((z.re : Real) + 1) ×ˢ
      Set.Ioo (z.im : Real) ((z.im : Real) + 1)
  have hRopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRU : R ⊆ TileRealization U := by
    intro a ha
    rcases ha with ⟨ha₁, ha₂⟩
    by_cases hw : a.1 ≤ (z.re : Real)
    · apply Set.mem_iUnion.mpr
      refine ⟨z - 1, Set.mem_iUnion.mpr ⟨hzw, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
        Int.cast_sub, Int.cast_one, sub_zero]
      constructor <;> constructor <;> linarith [ha₁.1, ha₁.2, ha₂.1, ha₂.2]
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith [ha₁.1, ha₁.2, ha₂.1, ha₂.2]
  intro a ha
  apply interior_maximal hRU hRopen
  obtain ⟨t, ht₀, ht₁, rfl⟩ := ha
  simp [R, GaussianRealPoint]
  constructor <;> constructor <;> nlinarith

private theorem edge_vertices :
    (by
      classical
      exact
        ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (p.head? = some x) → ((p.getLast? = some y) → ((FourNeighborAdjacent y
            x) → ((∀ (e : Finset GaussianInt), e ∈ E ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b :
            GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂
            ∧ e = {a, b}) → (∀ e ∈ E, ∀ z ∈ e, z ∈ p)))) ) := by
  classical
  intro E p x y hpHead hpLast hclose hpEdges e he z hz
  rcases (hpEdges e).mp he with rfl | ⟨a, b, l₁, l₂, hd, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact List.mem_of_getLast? hpLast
    · exact List.mem_of_head? hpHead
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> rw [hd] <;> simp

private theorem parent_regular :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (q : Fin 4 → CircleCoordinates),
            ∀ (cfg : BandOrderedGeneralConfiguration q),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ i,
                    ∀ s,
                      ∀ a,
                        ∀ b,
                          FourNeighborAdjacent a b →
                            a ∈ BoundaryFootprintVertices (cert.P i s) →
                              b ∈ BoundaryFootprintVertices (cert.P i s) →
                                ¬OpenLatticeEdge a b ⊆
                                interior (TileRealization (cert.P i s))
    ) := by
  classical
  intro C q cfg T cert
  as_aux_lemma =>
  intro i s
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 i
  have hne : (q i.succ).1 ≠ 0 := cfg.noLine i.succ
  have hpos : 0 < (q i.succ).1 := by omega
  let B : BandCircle :=
    ⟨⟨q i.succ, ⟨Or.inl hpos,
      ⟨q, cfg.proper.1, ⟨i.succ, rfl⟩⟩⟩⟩, hpos⟩
  exact (LatticeEdgeRegularity B (cert.P i s)
    (cert.outer_occurrence i s).1 (cert.parent_lattice i s)).1

private theorem no_horizontal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (E : Set (Finset GaussianInt)), ∀
            (p : List GaussianInt), (∀ z, z ∈ p → ∀ i, ∀ s, z ∈ FootprintVertices (cert.P i s) →
            z ∈ BoundaryFootprintVertices (cert.P i s)) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ U.cells) → ((z - ⟨0, 1⟩ ∈ U.cells) → (OpenLatticeEdge z (z + 1) ⊆
            interior (TileRealization U)))) → ((∀ e ∈ E, ∀ z ∈ e, z ∈ p) → ((∀ i, ∀ s, (∀ a, ∀ b,
            FourNeighborAdjacent a b → a ∈ BoundaryFootprintVertices (cert.P i s) → b ∈
            BoundaryFootprintVertices (cert.P i s) → ¬ OpenLatticeEdge a b ⊆ interior
            (TileRealization (cert.P i s)))) → (∀ (i s) (z : GaussianInt)
          (hz : z ∈ (cert.P i s).cells) (hzs : z - ⟨0, 1⟩ ∈ (cert.P i s).cells),
        ({z, z + 1} : Finset GaussianInt) ∉ E)))) ) := by
  classical
  intro C q cfg T cert E p hpParentBoundary horizontal_interior edge_vertices parent_regular i s
      z hz hzs
  as_aux_lemma =>
  intro he
  have hne : (cert.P i s).cells.Nonempty := ⟨z, hz⟩
  have ha : z ∈ BoundaryFootprintVertices (cert.P i s) := by
    apply hpParentBoundary z (edge_vertices _ he z (by simp)) i s
    rw [FootprintVertices, ite_eq_left hne]
    exact ⟨z, hz, Or.inl rfl⟩
  have hb : z + 1 ∈ BoundaryFootprintVertices (cert.P i s) := by
    apply hpParentBoundary (z + 1) (edge_vertices _ he (z + 1) (by simp)) i s
    rw [FootprintVertices, ite_eq_left hne]
    exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
  exact parent_regular i s z (z + 1) (Or.inl rfl) ha hb
    (horizontal_interior (cert.P i s) z hz hzs)

private theorem no_vertical :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (E : Set (Finset GaussianInt)), ∀
            (p : List GaussianInt), (∀ z, z ∈ p → ∀ i, ∀ s, z ∈ FootprintVertices (cert.P i s) →
            z ∈ BoundaryFootprintVertices (cert.P i s)) → ((∀ (U : ProtoTile), ∀ (z :
                GaussianInt), (z ∈ U.cells) → ((z - 1 ∈ U.cells) → (OpenLatticeEdge z (z + ⟨0, 1⟩) ⊆
            interior (TileRealization U)))) → ((∀ e ∈ E, ∀ z ∈ e, z ∈ p) → ((∀ i, ∀ s, (∀ a, ∀ b,
                FourNeighborAdjacent a b → a ∈ BoundaryFootprintVertices (cert.P i s) → b ∈
            BoundaryFootprintVertices (cert.P i s) → ¬ OpenLatticeEdge a b ⊆ interior
            (TileRealization (cert.P i s)))) → (∀ i, ∀ s, ∀ (z : GaussianInt), (z ∈ (cert.P i
                s).cells) → ((z - 1 ∈ (cert.P i s).cells) → (({z, z + ⟨0, 1⟩} : Finset
                GaussianInt) ∉ E))))))) := by
  classical
  intro C q cfg T cert E p hpParentBoundary vertical_interior edge_vertices parent_regular i s z
      hz hzw
  as_aux_lemma =>
  intro he
  have hne : (cert.P i s).cells.Nonempty := ⟨z, hz⟩
  have ha : z ∈ BoundaryFootprintVertices (cert.P i s) := by
    apply hpParentBoundary z (edge_vertices _ he z (by simp)) i s
    rw [FootprintVertices, ite_eq_left hne]
    exact ⟨z, hz, Or.inl rfl⟩
  have hb : z + ⟨0, 1⟩ ∈ BoundaryFootprintVertices (cert.P i s) := by
    apply hpParentBoundary (z + ⟨0, 1⟩)
      (edge_vertices _ he (z + ⟨0, 1⟩) (by simp)) i s
    rw [FootprintVertices, ite_eq_left hne]
    exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
  have hadj : FourNeighborAdjacent z (z + ⟨0, 1⟩) :=
    Or.inr (Or.inr (Or.inl rfl))
  have hnot := parent_regular i s z (z + ⟨0, 1⟩) hadj ha hb
  apply hnot
  exact vertical_interior (cert.P i s) z hz hzw

private theorem zip_decomp :
    (by
      classical
      exact
        ∀ (r : List GaussianInt), ∀ a, ∀ b, (a, b) ∈ r.zip r.tail → ∃ l₁ l₂, r = l₁ ++ a :: b ::
            l₂ ) := by
  classical
  intro r
  induction r with
  | nil => simp
  | cons c r ih =>
    cases r with
    | nil => simp
    | cons d r =>
      intro a b hab
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons,
        Prod.mk.injEq] at hab
      rcases hab with ⟨rfl, rfl⟩ | hab
      · exact ⟨[], r, rfl⟩
      · obtain ⟨l₁, l₂, hd⟩ := ih a b hab
        exact ⟨c :: l₁, l₂, congrArg (c :: ·) hd⟩

private theorem es_edge :
    (by
      classical
      exact
        ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (p.head? = some x) → ((p.getLast? = some y) → ((FourNeighborAdjacent y
            x) → ((∀ (e : Finset GaussianInt), e ∈ E ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b :
            GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂
            ∧ e = {a, b}) → ((∀ (r : List GaussianInt), ∀ a, ∀ b, (a, b) ∈ r.zip r.tail → ∃ l₁
            l₂, r = l₁ ++ a :: b :: l₂) → (
        let es := (p.zip p.tail) ++ [(y, x)]
        ∀ a, ∀ b, (a, b) ∈ es → ({a, b} : Finset GaussianInt) ∈ E))))) ) := by
  classical
  intro E p x y hpHead hpLast hclose hpEdges zip_decomp es a b hab
  simp only [es, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hab
  apply (hpEdges _).mpr
  rcases hab with hab | ⟨rfl, rfl⟩
  · obtain ⟨l₁, l₂, hd⟩ := zip_decomp p a b hab
    exact Or.inr ⟨a, b, l₁, l₂, hd, rfl⟩
  · exact Or.inl rfl

private theorem hzipAdjacent :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List
            GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ →
            FourNeighborAdjacent a b) → ((∀ (r : List GaussianInt), ∀ a, ∀ b, (a, b) ∈ r.zip
            r.tail → ∃ l₁ l₂, r = l₁ ++ a :: b :: l₂) → (∀ a, ∀ b, (a, b) ∈ p.zip p.tail →
            FourNeighborAdjacent a b)) ) := by
  classical
  intro p hpAdjacent zip_decomp a b hab
  obtain ⟨l₁, l₂, hd⟩ := zip_decomp p a b hab
  exact hpAdjacent a b l₁ l₂ hd

private theorem index_horizontal :
    (by
      classical
      exact
        ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt),
        let es := (p.zip p.tail) ++ [(y, x)]
        (∀ a, ∀ b, (a, b) ∈ es → ({a, b} : Finset GaussianInt) ∈ E) → ((
        let cyclicEdges := p.zip p.tail ++ [(y, x)]; ∀ (q : LatticeCell), ((q + (1 :
            LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉
            cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q +
            (1 : LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges →
            GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (∀ (z : GaussianInt), (({z, z + 1} :
            Finset GaussianInt) ∉ E) → (GridRayCrossingIndex z p = GridRayCrossingIndex (z - ⟨0,
            1⟩) p))) ) := by
  classical
  intro E p x y es es_edge index_control z he
  have hn : z - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ = z + 1 := by abel
  have hc := (index_control (z - ⟨0, 1⟩)).2.2.1
  apply (show GridRayCrossingIndex (z - ⟨0, 1⟩ + ⟨0, 1⟩) p =
    GridRayCrossingIndex (z - ⟨0, 1⟩) p → _ by simp only [sub_add_cancel]; exact id)
  apply hc
  constructor <;> intro h
  · apply he
    simpa only [hn, sub_add_cancel, Finset.pair_comm] using es_edge _ _ h
  · apply he
    simpa only [hn, sub_add_cancel] using es_edge _ _ h

private theorem index_vertical :
    (by
      classical
      exact
        ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt),
        let es := (p.zip p.tail) ++ [(y, x)]
        (∀ a, ∀ b, (a, b) ∈ es → ({a, b} : Finset GaussianInt) ∈ E) → ((
        let cyclicEdges := p.zip p.tail ++ [(y, x)]; ∀ (q : LatticeCell), ((q + (1 :
            LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉
            cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q +
            (1 : LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges →
            GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (∀ (z : GaussianInt), (({z, z + ⟨0,
            1⟩} : Finset GaussianInt) ∉ E) → (GridRayCrossingIndex z p = GridRayCrossingIndex (z
            - 1) p))) ) := by
  classical
  intro E p x y es es_edge index_control z he
  have hc := (index_control (z - 1)).1
  apply (show GridRayCrossingIndex (z - 1 + 1) p =
    GridRayCrossingIndex (z - 1) p → _ by simp only [sub_add_cancel]; exact id)
  apply hc
  constructor <;> intro h
  · apply he
    simpa only [sub_add_cancel] using es_edge _ _ h
  · apply he
    simpa only [sub_add_cancel, Finset.pair_comm] using es_edge _ _ h

private theorem parent_step :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (E : Set (Finset GaussianInt)), ∀
            (p : List GaussianInt), (∀ i, ∀ s, ∀ (z : GaussianInt), ∀ (hz : z ∈ (cert.P i
            s).cells), ∀ (hzs : z - ⟨0, 1⟩ ∈ (cert.P i s).cells), ({z, z + 1} : Finset
            GaussianInt) ∉ E) → ((∀ i, ∀ s, ∀ (z : GaussianInt), (z ∈ (cert.P i s).cells) → ((z -
            1 ∈ (cert.P i
            s).cells) → (({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∉ E))) → ((∀ (z : GaussianInt),
                (({z,
            z + 1} : Finset GaussianInt) ∉ E) → (GridRayCrossingIndex z p = GridRayCrossingIndex
            (z - ⟨0, 1⟩) p)) → ((∀ (z : GaussianInt), (({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∉
            E) → (GridRayCrossingIndex z p = GridRayCrossingIndex (z - 1) p)) → (∀ i, ∀ s, ∀ (a :
                GaussianInt), ∀ (b : GaussianInt), (a ∈ (cert.P i s).cells) → ((b ∈ (cert.P i
                s).cells) → ((FourNeighborAdjacent a b) → (GridRayCrossingIndex a p =
                GridRayCrossingIndex b p)))))))) := by
  classical
  intro C q cfg T cert E p no_horizontal no_vertical index_horizontal index_vertical i s a b ha
      hb hab
  rcases hab with rfl | rfl | rfl | rfl
  · have he := no_vertical i s (a + 1) hb (by simpa using ha)
    simpa using (index_vertical (a + 1) he).symm
  · exact index_vertical a (no_vertical i s a ha hb)
  · have he := no_horizontal i s (a + ⟨0, 1⟩) hb (by simpa using ha)
    simpa using (index_horizontal (a + ⟨0, 1⟩) he).symm
  · exact index_horizontal a (no_horizontal i s a ha hb)

private theorem list_end_eq :
    (by
      classical
      exact
        ∀ (r : List GaussianInt), ∀ (f : GaussianInt → Int), (∀ a, ∀ b, ∀ l₁, ∀ l₂, r = l₁ ++ a
            :: b :: l₂ → f a = f b) → ∀ a, ∀ b, r.head? = some a → r.getLast? = some b → f a = f
            b ) := by
  classical
  intro r f
  induction r with
  | nil => simp
  | cons c r ih =>
    cases r with
    | nil =>
      intro heq a b hh ht
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at ht
      rw [← hh, ← ht]
    | cons d r =>
      intro heq a b hh ht
      have hca : c = a := Option.some.inj hh
      subst a
      have hcd := heq c d [] r rfl
      apply hcd.trans
      apply ih _ d b rfl (by simpa using ht)
      intro u v l₁ l₂ hd
      exact heq u v (c :: l₁) l₂ (congrArg (c :: ·) hd)

private theorem parent_index_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (p : List GaussianInt), (∀ i, ∀ s,
            ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (cert.P i s).cells) → ((b ∈ (cert.P i
            s).cells) → ((FourNeighborAdjacent a b) → (GridRayCrossingIndex a p =
            GridRayCrossingIndex b p)))) → ((∀ (r : List GaussianInt), ∀ (f : GaussianInt → Int),
            (∀ a, ∀ b, ∀ l₁, ∀ l₂, r = l₁
                ++ a
            :: b :: l₂ → f a = f b) → ∀ a, ∀ b, r.head? = some a → r.getLast? = some b → f a = f
            b) → (∀ i, ∀ s, ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (cert.P i s).cells) →
                ((b ∈ (cert.P i s).cells) → (GridRayCrossingIndex a p = GridRayCrossingIndex b
                p))))) := by
  classical
  intro C q cfg T cert p parent_step list_end_eq i s a b ha hb
  obtain ⟨r, hh, ht, hr, hadj⟩ :=
    (LatticeTileGridStructure (cert.P i s) (cert.parent_lattice i s)).1.2 a ha b hb
  apply list_end_eq r (fun c => GridRayCrossingIndex c p) _ a b hh ht
  intro u v l₁ l₂ hd
  apply parent_step i s u v
  · apply hr u
    rw [hd]; simp
  · apply hr v
    rw [hd]; simp
  · exact hadj u v l₁ l₂ hd

private theorem unit_segment :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ U.cells) → ((b ∈
            U.cells) → ((FourNeighborAdjacent a b) → (∀ t : Set.Icc (0 : Real) 1, ((1 - (t :
            Real)) * (a.re : Real) + (t : Real) * (b.re : Real), (1 - (t : Real)) * (a.im : Real)
            + (t : Real) * (b.im : Real)) ∈ TileRealization U))) ) := by
  classical
  intro U a b ha hb hab
  as_aux_lemma =>
  intro t
  rcases hab with rfl | rfl | rfl | rfl
  · apply Set.mem_iUnion.mpr
    refine ⟨a, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
    simp [ClosedSquareRealization]
    constructor <;> constructor <;> nlinarith [t.property.1, t.property.2]
  · apply Set.mem_iUnion.mpr
    refine ⟨a - 1, Set.mem_iUnion.mpr ⟨hb, ?_⟩⟩
    simp [ClosedSquareRealization]
    constructor <;> constructor <;> nlinarith [t.property.1, t.property.2]
  · apply Set.mem_iUnion.mpr
    refine ⟨a, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
    simp [ClosedSquareRealization]
    constructor <;> constructor <;> nlinarith [t.property.1, t.property.2]
  · apply Set.mem_iUnion.mpr
    refine ⟨a - ⟨0, 1⟩, Set.mem_iUnion.mpr ⟨hb, ?_⟩⟩
    simp [ClosedSquareRealization]
    constructor <;> constructor <;> nlinarith [t.property.1, t.property.2]

private theorem cycle_segments :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), (p.head? = some x) → ((p.getLast? = some y) →
            ((FourNeighborAdjacent y x) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ :
            List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ →
            FourNeighborAdjacent a b) → ((∀ (e : Finset GaussianInt), e ∈ E ↔ e = {y, x} ∨ ∃ (a :
            GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p =
            l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ z ∈ p, z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - ⟨0,
            1⟩ ∈ T.cells ∧ z - 1 - ⟨0, 1⟩ ∈ T.cells) → (
        let es := (p.zip p.tail) ++ [(y, x)]
        (∀ a, ∀ b, (a, b) ∈ es → ({a, b} : Finset GaussianInt) ∈ E) → ((
        let cyclicEdges := p.zip p.tail ++ [(y, x)]; ∀ (q : LatticeCell), ((q + (1 :
            LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉
            cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q +
            (1 : LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges →
            GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → ((∀ (U : ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (a ∈ U.cells) → ((b ∈ U.cells) →
            ((FourNeighborAdjacent a b) → (∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * (a.re
            : Real) + (t : Real) * (b.re : Real), (1 - (t : Real)) * (a.im : Real) + (t : Real) *
            (b.im : Real)) ∈ TileRealization U)))) → (∀ a b : GaussianInt, ((∃ l₁ l₂ : List
            GaussianInt, p = l₁ ++ a :: b :: l₂) ∨ (a = y ∧ b = x)) → ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re : Real), (1 - (t : Real)) *
            (a.im : Real) + (t : Real) * (b.im : Real)) ∈ TileRealization T))))))))) ) := by
  classical
  intro T E p x y hpHead hpLast hclose hpAdjacent hpEdges hpCells es es_edge index_control
      unit_segment a b hab
  rcases hab with ⟨l₁, l₂, hd⟩ | ⟨rfl, rfl⟩
  · have ha : a ∈ p := by rw [hd]; simp
    have hb : b ∈ p := by rw [hd]; simp
    exact unit_segment T a b (hpCells a ha).1 (hpCells b hb).1
      (hpAdjacent a b l₁ l₂ hd)
  · exact unit_segment T a b (hpCells a (List.mem_of_getLast? hpLast)).1
      (hpCells b (List.mem_of_head? hpHead)).1 hclose

private theorem unoccupied_center_outside :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (c : LatticeCell), (c ∉ T.cells) → ((((c.re : Real) + (1 / 2 :
            Real)), ((c.im : Real) + (1 / 2 : Real))) ∉ TileRealization T) ) := by
  classical
  intro T c hc
  as_aux_lemma =>
  intro hcenter
  simp only [TileRealization, Set.mem_iUnion] at hcenter
  obtain ⟨w, hw, hcw⟩ := hcenter
  simp only [ClosedSquareRealization, Set.mem_Icc] at hcw
  have hre_lt : w.re < c.re + 1 := by
    exact_mod_cast (show (w.re : Real) < (c.re : Real) + 1 by linarith [hcw.1.1])
  have hre_gt : c.re < w.re + 1 := by
    exact_mod_cast (show (c.re : Real) < (w.re : Real) + 1 by linarith [hcw.2.1])
  have him_lt : w.im < c.im + 1 := by
    exact_mod_cast (show (w.im : Real) < (c.im : Real) + 1 by linarith [hcw.1.2])
  have him_gt : c.im < w.im + 1 := by
    exact_mod_cast (show (c.im : Real) < (w.im : Real) + 1 by linarith [hcw.2.2])
  have hwc : w = c := by apply Zsqrtd.ext <;> omega
  exact hc (hwc ▸ hw)

private theorem outside_zero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (LatticeTile T) → (∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y
            : GaussianInt), (p.head? = some x) → ((p.getLast? = some y) → ((FourNeighborAdjacent
            y x) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ :
            List GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) → ((∀ a b :
            GaussianInt, ((∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨ (a = y ∧ b = x))
            → ∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re
            : Real), (1 - (t : Real)) * (a.im : Real) + (t : Real) * (b.im : Real)) ∈
            TileRealization T) → ((∀ (c : LatticeCell), (c ∉ T.cells) → ((((c.re : Real) + (1 / 2
            : Real)), ((c.im : Real) + (1 / 2 : Real))) ∉ TileRealization T)) → (∀ (c :
            LatticeCell), (c ∉ T.cells) → (GridRayCrossingIndex c p = 0)))))))) ) := by
  classical
  intro T hlat p x y hpHead hpLast hclose hpAdjacent cycle_segments unoccupied_center_outside c hc
  apply TopologicalDiskGridRayCrossingIndexZero (TileRealization T) hlat c
    (unoccupied_center_outside c hc) p x y hpHead hpLast hpAdjacent hclose
  exact cycle_segments

private theorem boundary_not_cycle :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (E : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), (∀ z, z ∈
            p → z ∈ FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → ((T.cells.Nonempty)
            → ((∀ e ∈ E, ∀ z ∈ e, z ∈ p) → (∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges T) → (e ∉ E)))) ) := by
  classical
  intro T E p hpInteriorT hTne edge_vertices e he heE
  have hene : e.Nonempty := by
    rcases he with ⟨z, (⟨rfl, _⟩ | ⟨rfl, _⟩)⟩ <;> simp
  obtain ⟨z, hz⟩ := hene
  apply (hpInteriorT z (edge_vertices e heE z hz)).2
  rw [BoundaryFootprintVertices, ite_eq_left hTne]
  exact ⟨e, he, hz⟩

private theorem horizontal_unique :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, a + 1} : Finset GaussianInt) = {b,
            b + 1}) → (a = b) ) := by
  classical
  intro a b h
  as_aux_lemma =>
  have ha : a ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
  have ha1 : a + 1 ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
  rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
  · exact hab
  · exact hab
  · exfalso
    apply_fun Zsqrtd.re at hab ha1b
    simp at hab ha1b
    omega
  · exfalso
    apply_fun Zsqrtd.re at hab ha1b
    simp at hab ha1b
    omega

private theorem vertical_unique :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, a + ⟨0, 1⟩} : Finset GaussianInt) = {b,
            b + ⟨0, 1⟩}) → (a = b) ) := by
  classical
  intro a b h
  as_aux_lemma =>
  have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
  have ha1 : a + ⟨0, 1⟩ ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
  rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
  · exact hab
  · exact hab
  · exfalso
    apply_fun Zsqrtd.im at hab ha1b
    simp at hab ha1b
    omega
  · exfalso
    apply_fun Zsqrtd.im at hab ha1b
    simp at hab ha1b
    omega

private theorem horizontal_vertical_ne :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), ({a, a + 1} : Finset GaussianInt) ≠ {b, b + ⟨0,
            1⟩} ) := by
  classical
  intro a b
  as_aux_lemma =>
  intro h
  have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
  have ha1 : a + 1 ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
  rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
  all_goals apply_fun Zsqrtd.re at hab ha1b; simp at hab ha1b; omega

private theorem horizontal_boundary_cells :
    (by
      classical
      exact
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, a + 1} : Finset GaussianInt) = {b,
            b + 1}) → (a = b)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ({a, a + 1} : Finset
            GaussianInt) ≠ {b, b + ⟨0, 1⟩}) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), (({z,
            z + 1} : Finset GaussianInt) ∈ BoundaryFootprintEdges U) → ((z ∈ U.cells ∧ z - ⟨0, 1⟩
            ∉ U.cells) ∨ (z ∉ U.cells ∧ z - ⟨0, 1⟩ ∈ U.cells)))) ) := by
  classical
  intro horizontal_unique horizontal_vertical_ne U z he
  rcases he with ⟨a, (⟨ha, hocc⟩ | ⟨ha, hocc⟩)⟩
  · have haz := horizontal_unique a z ha.symm
    simpa [haz] using hocc
  · exact False.elim (horizontal_vertical_ne z a ha)

private theorem vertical_boundary_cells :
    (by
      classical
      exact
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, a + ⟨0, 1⟩} : Finset GaussianInt) = {b,
            b + ⟨0, 1⟩}) → (a = b)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ({a, a + 1} :
            Finset GaussianInt) ≠ {b, b + ⟨0, 1⟩}) → (∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U) → ((z ∈ U.cells ∧
            z - 1 ∉ U.cells) ∨ (z ∉ U.cells ∧ z - 1 ∈ U.cells)))) ) := by
  classical
  intro vertical_unique horizontal_vertical_ne U z he
  rcases he with ⟨a, (⟨ha, hocc⟩ | ⟨ha, hocc⟩)⟩
  · exact False.elim (horizontal_vertical_ne a z ha.symm)
  · have haz := vertical_unique a z ha.symm
    simpa [haz] using hocc

private theorem parent_cell_in_outer :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ i, ∀ s, ∀ z, z ∈ (cert.P i s).cells
            → z ∈ T.cells ) := by
  classical
  intro C q cfg T cert i s z hz
  exact (cert.outer_union z).mpr ⟨i, s, hz⟩

private theorem parent_anchor :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ i, ∀ s, ∃ e : Finset GaussianInt,
            e ∈ BoundaryFootprintEdges (cert.P i s) ∧ e ∈ BoundaryFootprintEdges T) → (∀ (E : Set
            (Finset GaussianInt)), ∀ (p : List GaussianInt), (∀ (z : GaussianInt), (({z, z + 1} :
            Finset GaussianInt) ∉ E) → (GridRayCrossingIndex z p = GridRayCrossingIndex (z - ⟨0,
            1⟩) p)) → ((∀ (z : GaussianInt), (({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∉ E) →
            (GridRayCrossingIndex z p = GridRayCrossingIndex (z - 1) p)) → ((∀ (c : LatticeCell),
            (c ∉ T.cells) → (GridRayCrossingIndex c p = 0)) → ((∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges T) → (e ∉ E)) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (({z, z + 1} : Finset GaussianInt) ∈ BoundaryFootprintEdges U) → ((z ∈ U.cells ∧ z -
            ⟨0, 1⟩ ∉ U.cells) ∨ (z ∉ U.cells ∧ z - ⟨0, 1⟩ ∈ U.cells))) → ((∀ (U : ProtoTile), ∀
            (z : GaussianInt), (({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges
            U) → ((z ∈ U.cells ∧ z - 1 ∉ U.cells) ∨ (z ∉ U.cells ∧ z - 1 ∈ U.cells))) → ((∀ i, ∀
            s, ∀ z, z ∈ (cert.P i s).cells → z ∈ T.cells) → (∀ (i s),
        ∃ c ∈ (cert.P i s).cells, GridRayCrossingIndex c p = 0)))))))) ) := by
  classical
  intro C q cfg T cert attachment E p index_horizontal index_vertical outside_zero
      boundary_not_cycle horizontal_boundary_cells vertical_boundary_cells parent_cell_in_outer i s
  obtain ⟨e, heU, heT⟩ := attachment i s
  have heE := boundary_not_cycle e heT
  rcases heU with ⟨z, (⟨rfl, hu⟩ | ⟨rfl, hu⟩)⟩
  · have ht := horizontal_boundary_cells T z heT
    have hi := index_horizontal z heE
    rcases hu with ⟨hzu, hzsnu⟩ | ⟨hznu, hzsu⟩
    · have hzt := parent_cell_in_outer i s z hzu
      have hzsout : z - ⟨0, 1⟩ ∉ T.cells := by
        rcases ht with hh | hh
        · exact hh.2
        · exact (hh.1 hzt).elim
      exact ⟨z, hzu, hi.trans (outside_zero _ hzsout)⟩
    · have hzst := parent_cell_in_outer i s (z - ⟨0, 1⟩) hzsu
      have hzout : z ∉ T.cells := by
        rcases ht with hh | hh
        · exact (hh.2 hzst).elim
        · exact hh.1
      exact ⟨z - ⟨0, 1⟩, hzsu, hi.symm.trans (outside_zero _ hzout)⟩
  · have ht := vertical_boundary_cells T z heT
    have hi := index_vertical z heE
    rcases hu with ⟨hzu, hzwnu⟩ | ⟨hznu, hzwu⟩
    · have hzt := parent_cell_in_outer i s z hzu
      have hzwout : z - 1 ∉ T.cells := by
        rcases ht with hh | hh
        · exact hh.2
        · exact (hh.1 hzt).elim
      exact ⟨z, hzu, hi.trans (outside_zero _ hzwout)⟩
    · have hzwt := parent_cell_in_outer i s (z - 1) hzwu
      have hzout : z ∉ T.cells := by
        rcases ht with hh | hh
        · exact (hh.2 hzwt).elim
        · exact hh.1
      exact ⟨z - 1, hzwu, hi.symm.trans (outside_zero _ hzout)⟩

private theorem parent_zero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (p : List GaussianInt), (∀ i, ∀ s,
            ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (cert.P i s).cells) → ((b ∈ (cert.P i
            s).cells) → (GridRayCrossingIndex a p = GridRayCrossingIndex b p))) → ((∀ i, ∀ s, ∃ c
            ∈ (cert.P i
            s).cells, GridRayCrossingIndex c p = 0) → (∀ i, ∀ s, ∀ (c : LatticeCell), (c ∈
            (cert.P i s).cells) → (GridRayCrossingIndex c p = 0)))) := by
  classical
  intro C q cfg T cert p parent_index_eq parent_anchor i s c hc
  obtain ⟨a, ha, hazero⟩ := parent_anchor i s
  exact (parent_index_eq i s c a hc ha).trans hazero

private theorem outer_zero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (p : List GaussianInt), (∀ i, ∀ s,
            ∀ (c : LatticeCell), (c ∈ (cert.P i s).cells) → (GridRayCrossingIndex c p = 0)) → (∀
            (c : LatticeCell), (c ∈ T.cells) → (GridRayCrossingIndex c p = 0))) := by
  classical
  intro C q cfg T cert p parent_zero c hc
  obtain ⟨i, s, hc⟩ := (cert.outer_union c).mp hc
  exact parent_zero i s c hc

private theorem all_zero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (p : List GaussianInt), (∀ (c : LatticeCell), (c ∉ T.cells) →
            (GridRayCrossingIndex c p = 0)) → ((∀ (c : LatticeCell), (c ∈ T.cells) →
            (GridRayCrossingIndex c p = 0)) → (∀ (c : LatticeCell), GridRayCrossingIndex c p =
            0)) ) := by
  classical
  intro T p outside_zero outer_zero c
  by_cases hc : c ∈ T.cells
  · exact outer_zero c hc
  · exact outside_zero c hc

private theorem heqAt735 :
    (by
      classical
      exact
        ∀ (y : GaussianInt), (y - ⟨0, 1⟩ + ⟨0, 1⟩, y - ⟨0, 1⟩ + 1 + ⟨0, 1⟩) = (y, y + 1) ) := by
  classical
  intro y
  apply Prod.ext <;> dsimp <;> abel

private theorem hjumpAt738 :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (y : GaussianInt),
        let es := (p.zip p.tail) ++ [(y, y + 1)]
        (
        let cyclicEdges := p.zip p.tail ++ [(y, y + (1 : LatticeCell))]; ∀ (q : LatticeCell), ((q
            + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉
            cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q +
            (1 : LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges →
            GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (((y, y + (1 : LatticeCell)) ∈ es) →
            (((y - ⟨0, 1⟩ + ⟨0, 1⟩, y - ⟨0, 1⟩ + 1 + ⟨0, 1⟩) = (y, y + 1)) → (Int.natAbs
            (GridRayCrossingIndex (y - ⟨0, 1⟩ + ⟨0, 1⟩) p - GridRayCrossingIndex (y - ⟨0, 1⟩) p)
            = 1))) ) := by
  classical
  intro p y es index_control hmem heq
  apply (index_control (y - ⟨0, 1⟩)).2.2.2
  right
  rw [heq]
  exact hmem

private theorem heqAt748 :
    (by
      classical
      exact
        ∀ (y : GaussianInt), (y - 1 - ⟨0, 1⟩ + 1 + ⟨0, 1⟩, y - 1 - ⟨0, 1⟩ + ⟨0, 1⟩) = (y, y - 1)
            ) := by
  classical
  intro y
  apply Prod.ext <;> dsimp <;> abel

private theorem hjumpAt751 :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (y : GaussianInt),
        let es := (p.zip p.tail) ++ [(y, y - 1)]
        (
        let cyclicEdges := p.zip p.tail ++ [(y, y - (1 : LatticeCell))]; ∀ (q : LatticeCell), ((q
            + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉
            cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q +
            (1 : LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges →
            GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (((y, y - (1 : LatticeCell)) ∈ es) →
            (((y - 1 - ⟨0, 1⟩ + 1 + ⟨0, 1⟩, y - 1 - ⟨0, 1⟩ + ⟨0, 1⟩) = (y, y - 1)) → (Int.natAbs
            (GridRayCrossingIndex (y - 1 - ⟨0, 1⟩ + ⟨0, 1⟩) p - GridRayCrossingIndex (y - 1 - ⟨0,
            1⟩) p) = 1))) ) := by
  classical
  intro p y es index_control hmem heq
  apply (index_control (y - 1 - ⟨0, 1⟩)).2.2.2
  left
  rw [heq]
  exact hmem

private theorem hjumpAt763 :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (y : GaussianInt),
        let es := (p.zip p.tail) ++ [(y, y + ⟨0, 1⟩)]
        (
        let cyclicEdges := p.zip p.tail ++ [(y, y + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))]; ∀ (q :
            LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (1 : LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 :
            LatticeCell)) p = GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈
            cyclicEdges → (GridRayCrossingIndex (q + (1 : LatticeCell)) p - GridRayCrossingIndex
            q p).natAbs = (1 : ℕ)) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∉ cyclicEdges → GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (((y, y + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∈ es) → (((y - 1 + 1, y - 1 + 1 + ⟨0, 1⟩) = (y, y + ⟨0, 1⟩)) →
            (Int.natAbs (GridRayCrossingIndex (y - 1 + 1) p - GridRayCrossingIndex (y - 1) p) =
            1))) ) := by
  classical
  intro p y es index_control hmem heq
  apply (index_control (y - 1)).2.1
  left
  rw [heq]
  exact hmem

private theorem heqAt772 :
    (by
      classical
      exact
        ∀ (y : GaussianInt), (y - ⟨0, 1⟩ - 1 + 1 + ⟨0, 1⟩, y - ⟨0, 1⟩ - 1 + 1) = (y, y - ⟨0, 1⟩)
            ) := by
  classical
  intro y
  apply Prod.ext <;> dsimp <;> abel

private theorem hjumpAt775 :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (y : GaussianInt),
        let es := (p.zip p.tail) ++ [(y, y - ⟨0, 1⟩)]
        (
        let cyclicEdges := p.zip p.tail ++ [(y, y - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))]; ∀ (q :
            LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∉ cyclicEdges ∧ (q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (1 : LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 :
            LatticeCell)) p = GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (1 :
            LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell)) ∈
            cyclicEdges → (GridRayCrossingIndex (q + (1 : LatticeCell)) p - GridRayCrossingIndex
            q p).natAbs = (1 : ℕ)) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∉ cyclicEdges ∧ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∉ cyclicEdges → GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p =
            GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt), q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∈ cyclicEdges ∨ (q + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), q + (1 : LatticeCell) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∈ cyclicEdges → (GridRayCrossingIndex (q + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p -
            GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → (((y, y - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ∈ es) → (((y - ⟨0, 1⟩ - 1 + 1 + ⟨0, 1⟩, y - ⟨0, 1⟩ - 1 + 1) = (y, y -
            ⟨0, 1⟩)) → (Int.natAbs (GridRayCrossingIndex (y - ⟨0, 1⟩ - 1 + 1) p -
            GridRayCrossingIndex (y - ⟨0, 1⟩ - 1) p) = 1))) ) := by
  classical
  intro p y es index_control hmem heq
  apply (index_control (y - ⟨0, 1⟩ - 1)).2.1
  right
  rw [heq]
  exact hmem

end InterfaceCycleGeometry

theorem P4250T2InterfaceCycleExclusion
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : BandPrototile (q 0) T) (hlat : LatticeTile T)
    (D P : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)) :
    (∀ i s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (cert.P i s) ∧
        e ∈ BoundaryFootprintEdges T) ∧
    ∀ V E, SimpleGridCycle V E → ¬ V ⊆ ((D \ P : Finset GaussianInt) : Set GaussianInt) := by
-- BODY
  classical
  -- A simple touching path omits an edge of the complete parent boundary.
  have attachment := InterfaceCycleGeometry.attachment C q cfg T cert hT
      (InterfaceCycleGeometry.path_omits_boundary)
  refine ⟨attachment, ?_⟩
  intro V E hcyc hsub
  obtain ⟨p, x, y, hpNodup, hpLength, hpHead, hpLast, hV,
    hclose, hpAdjacent, hpEdges⟩ := hcyc
  have hpInDifference := InterfaceCycleGeometry.hpInDifference D P V hsub p hV
  have hpInD := InterfaceCycleGeometry.hpInD D P p hpInDifference
  have hpInteriorT := InterfaceCycleGeometry.hpInteriorT T D hD p hpInD
  have hpParentBoundary := InterfaceCycleGeometry.hpParentBoundary C q cfg T cert D P hP p hpInD
      (InterfaceCycleGeometry.hpNotP D P p hpInDifference)
  have hTne : T.cells.Nonempty := (LatticeTileGridStructure T hlat).1.1
  -- Absence of a boundary edge forces all four incident cells to be present.
  have edge_vertices := InterfaceCycleGeometry.edge_vertices E p x y hpHead hpLast hclose hpEdges
  have parent_regular := InterfaceCycleGeometry.parent_regular C q cfg T cert
  -- A cycle side cannot lie between two cells of one parent.
  have zip_decomp := InterfaceCycleGeometry.zip_decomp
  let es := (p.zip p.tail) ++ [(y, x)]
  have es_edge := InterfaceCycleGeometry.es_edge E p x y hpHead hpLast hclose hpEdges zip_decomp
  have index_control := GridRayCrossingIndexAdjacentCell p x y hpHead hpLast
    hpNodup (by omega) (InterfaceCycleGeometry.hzipAdjacent p hpAdjacent zip_decomp) hclose
  have index_horizontal := InterfaceCycleGeometry.index_horizontal E p x y es_edge index_control
  have index_vertical := InterfaceCycleGeometry.index_vertical E p x y es_edge index_control
  have outside_zero := InterfaceCycleGeometry.outside_zero T hlat p x y hpHead hpLast hclose
      hpAdjacent (InterfaceCycleGeometry.cycle_segments T E p x y hpHead hpLast hclose hpAdjacent
      hpEdges (InterfaceCycleGeometry.hpCells T p hpInteriorT hTne
      (InterfaceCycleGeometry.vertex_cells)) es_edge index_control
      (InterfaceCycleGeometry.unit_segment)) (InterfaceCycleGeometry.unoccupied_center_outside T)
  have horizontal_vertical_ne := InterfaceCycleGeometry.horizontal_vertical_ne
  -- The common outer side anchors the index throughout each parent.
  -- Exact cell coverage transfers these zero values to the entire outer tile.
  have all_zero (c : LatticeCell) : GridRayCrossingIndex c p = 0 :=
      InterfaceCycleGeometry.all_zero T p outside_zero (InterfaceCycleGeometry.outer_zero C q cfg
      T cert p (InterfaceCycleGeometry.parent_zero C q cfg T cert p
      (InterfaceCycleGeometry.parent_index_eq C q cfg T cert p
      (InterfaceCycleGeometry.parent_step C q cfg T cert E p
      (InterfaceCycleGeometry.no_horizontal C q cfg T cert E p hpParentBoundary
      (InterfaceCycleGeometry.horizontal_interior) edge_vertices parent_regular)
      (InterfaceCycleGeometry.no_vertical C q cfg T cert E p hpParentBoundary
      (InterfaceCycleGeometry.vertical_interior) edge_vertices parent_regular) index_horizontal
      index_vertical) (InterfaceCycleGeometry.list_end_eq)) (InterfaceCycleGeometry.parent_anchor
      C q cfg T cert attachment E p index_horizontal index_vertical outside_zero
      (InterfaceCycleGeometry.boundary_not_cycle T E p hpInteriorT hTne edge_vertices)
      (InterfaceCycleGeometry.horizontal_boundary_cells
      (InterfaceCycleGeometry.horizontal_unique) horizontal_vertical_ne)
      (InterfaceCycleGeometry.vertical_boundary_cells (InterfaceCycleGeometry.vertical_unique)
      horizontal_vertical_ne) (InterfaceCycleGeometry.parent_cell_in_outer C q cfg T cert)))) c
  have hmem : (y, x) ∈ es := by simp [es]
  clear * - p x y es index_control all_zero hmem hclose
  rcases hclose with hclose | hclose | hclose | hclose
  · subst x
    have heq := InterfaceCycleGeometry.heqAt735 y
    have hjump : Int.natAbs
        (GridRayCrossingIndex (y - ⟨0, 1⟩ + ⟨0, 1⟩) p -
          GridRayCrossingIndex (y - ⟨0, 1⟩) p) = 1 := InterfaceCycleGeometry.hjumpAt738 p y
              index_control hmem heq
    simp only [all_zero, sub_self, Int.natAbs_zero] at hjump
    norm_num at hjump
  · subst x
    have heq := InterfaceCycleGeometry.heqAt748 y
    have hjump : Int.natAbs
        (GridRayCrossingIndex (y - 1 - ⟨0, 1⟩ + ⟨0, 1⟩) p -
          GridRayCrossingIndex (y - 1 - ⟨0, 1⟩) p) = 1 := InterfaceCycleGeometry.hjumpAt751 p y
              index_control hmem heq
    simp only [all_zero, sub_self, Int.natAbs_zero] at hjump
    norm_num at hjump
  · subst x
    have heq : (y - 1 + 1, y - 1 + 1 + ⟨0, 1⟩) = (y, y + ⟨0, 1⟩) := by
      apply Prod.ext <;> dsimp <;> abel
    have hjump : Int.natAbs
        (GridRayCrossingIndex (y - 1 + 1) p - GridRayCrossingIndex (y - 1) p) = 1 :=
            InterfaceCycleGeometry.hjumpAt763 p y index_control hmem heq
    simp only [all_zero, sub_self, Int.natAbs_zero] at hjump
    norm_num at hjump
  · subst x
    have heq := InterfaceCycleGeometry.heqAt772 y
    have hjump : Int.natAbs
        (GridRayCrossingIndex (y - ⟨0, 1⟩ - 1 + 1) p -
          GridRayCrossingIndex (y - ⟨0, 1⟩ - 1) p) = 1 := InterfaceCycleGeometry.hjumpAt775 p y
              index_control hmem heq
    simp only [all_zero, sub_self, Int.natAbs_zero] at hjump
    norm_num at hjump

end ApollonianSuperharmonic

end
