/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4366T1PrecursorRemainderFamily
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.P4397T1PathAvoidsPrecursorEdges
public import LeanPool.ApollonianSuperharmonic.P4397T1SimplePathSplicing

-- [TABLET NODE: P4366T1PrecursorPathLoop]

/-!
# P4366T1PrecursorPathLoop

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PrecursorLoopGeometry

private theorem hOA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P (0 : Fin (3 : ℕ))
            true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells = cert.O.cells) → (cert.O.cells
            ⊆ (cert.P 0 true).cells) ) := by
  classical
  intro C q cfg T cert hpair z hz
  exact (Finset.mem_inter.mp (hpair.symm ▸ hz)).1

private theorem hOB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P (0 : Fin (3 : ℕ))
            true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells = cert.O.cells) → (cert.O.cells
            ⊆ (cert.P 0 false).cells) ) := by
  classical
  intro C q cfg T cert hpair z hz
  exact (Finset.mem_inter.mp (hpair.symm ▸ hz)).2

private theorem footprint_mono :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (U' : ProtoTile), (U.cells.Nonempty) → ((U.cells ⊆ U'.cells) →
            (FootprintVertices U ⊆ FootprintVertices U')) ) := by
  classical
  intro U U' hn hsub
  rw [FootprintVertices, ite_eq_left hn, FootprintVertices, ite_eq_left (hn.mono hsub)]
  rintro x ⟨z, hz, hc⟩
  exact ⟨z, hsub hz, hc⟩

private theorem realization_mono :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (U' : ProtoTile), (U.cells ⊆ U'.cells) → (TileRealization U ⊆
            TileRealization U') ) := by
  classical
  intro U U' hsub x hx
  simp only [TileRealization, Set.mem_iUnion] at hx ⊢
  obtain ⟨z, hz, hx⟩ := hx
  exact ⟨z, hsub hz, hx⟩

private theorem hno :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → (∀ (u : GaussianInt), (u ∈ D \ P) → (∀ (v : GaussianInt), (v ∈ D \ P) →
            ((FourNeighborAdjacent u v) → (∀ (i : Fin 3), ∀ (s : Bool), (u ∈ FootprintVertices
            (cert.P i s)) → ((v ∈ FootprintVertices (cert.P i s)) → (¬ OpenLatticeEdge u v ⊆
            interior (TileRealization (cert.P i s)))))))) ) := by
  classical
  intro C q cfg T cert D P hP u hu v hv hadj i s huf hvf
  have boundary (x : GaussianInt) (hx : x ∈ D \ P)
      (hf : x ∈ FootprintVertices (cert.P i s)) :
      x ∈ BoundaryFootprintVertices (cert.P i s) := by
    by_contra hnb
    exact (Finset.mem_sdiff.mp hx).2 ((hP x).mpr
      ⟨(Finset.mem_sdiff.mp hx).1, i, s, hf, hnb⟩)
  have hpos : 0 < (q i.succ).1 := by
    have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 i
    have hz := cfg.noLine i.succ
    exact lt_of_le_of_ne hn (Ne.symm hz)
  let B : BandCircle :=
    ⟨⟨q i.succ, Or.inl hpos, q, cfg.proper.1, i.succ, rfl⟩, hpos⟩
  exact (LatticeEdgeRegularity B (cert.P i s)
    (cert.outer_occurrence i s).1 (cert.parent_lattice i s)).1
      u v hadj (boundary u hu huf) (boundary v hv hvf)

private theorem Fsub :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        ∀ (i : Fin 3), ∀ (s : Bool), (F i s).cells ⊆ (cert.P i s).cells ) := by
  classical
  intro C q cfg T cert F i s
  dsimp [F, P4366T1PrecursorRemainderFamily]
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.refl _

private theorem FnotO :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), (i, s) ≠ (j, t) →
            ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) → Disjoint (cert.P i s).cells
            (cert.P j t).cells) → ((cert.O.cells ⊆ (cert.P 0 true).cells) → ((∀ (i : Fin 3), ∀ (s
            : Bool), (F i s).cells ⊆ (cert.P i s).cells) → (∀ (i : Fin 3), ∀ (s : Bool), ∀ (z :
            GaussianInt), (z ∈ (F i s).cells) → (z ∉ cert.O.cells)))) ) := by
  classical
  intro C q cfg T cert F hdisjoint hOA Fsub i s z hz
  by_cases hi : i = 0
  · simpa [F, P4366T1PrecursorRemainderFamily, hi, TileCellComplement]
      using (Finset.mem_sdiff.mp (show z ∈ (cert.P i s).cells \ cert.O.cells by
        simpa [F, P4366T1PrecursorRemainderFamily, hi, TileCellComplement] using hz)).2
  · intro ho
    exact Finset.disjoint_left.mp
      (hdisjoint i s 0 true (fun he => hi (congrArg Prod.fst he))
        (fun he => hi he.1)) (Fsub i s hz) (hOA ho)

private theorem boundary_raw :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (BoundaryFootprintVertices U ⊆ FootprintVertices
            U) ) := by
  classical
  intro U hn x hx
  rw [BoundaryFootprintVertices, ite_eq_left hn] at hx
  rw [FootprintVertices, ite_eq_left hn]
  obtain ⟨e, ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩, hxe⟩ := hx
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hz with hz | hz
    · refine ⟨z, hz.1, ?_⟩
      rcases hxe with rfl | rfl <;> simp
    · refine ⟨_, hz.2, ?_⟩
      rcases hxe with rfl | rfl <;>
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem edge_split :
    (by
      classical
      exact
        ∀ (l : List GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ l.zip
            l.tail) → (∃ l1 l2, l = l1 ++ u :: v :: l2) ) := by
  classical
  intro l u v he
  induction l with
  | nil => simp at he
  | cons c l ih =>
    cases l with
    | nil => simp at he
    | cons d ds =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
      rcases he with he | he
      · cases he
        exact ⟨[], ds, rfl⟩
      · obtain ⟨l1, l2, hl⟩ := ih he
        exact ⟨c :: l1, l2, congrArg (List.cons c) hl⟩

private theorem boundary_step :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (({u, v} : Finset
            GaussianInt) ∈ BoundaryFootprintEdges U) → (FourNeighborAdjacent u v) ) := by
  classical
  intro U u v he
  obtain ⟨z, ⟨he, _⟩ | ⟨he, _⟩⟩ := he
  all_goals
    have hs := congrArg (fun e : Finset GaussianInt => (e : Set GaussianInt)) he
    simp only [Finset.coe_pair] at hs
    rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem gW :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), ∀ (V : Set GaussianInt), (V ⊆
            (↑(D \ P) : Set GaussianInt)) → (∀ (g : List GaussianInt), (V = (↑g.toFinset : Set
            GaussianInt)) → (∀ (z : GaussianInt), (z ∈ g) → (z ∈ D \ P))) ) := by
  classical
  intro D P V hV g hgv z hz
  apply hV
  rw [hgv]
  simpa using hz

private theorem gsteps :
    (by
      classical
      exact
        (∀ (l : List GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ l.zip
            l.tail) → (∃ l1 l2, l = l1 ++ u :: v :: l2)) → (∀ (g : List GaussianInt), (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), g = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 :
            GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ g.zip
            g.tail) → (FourNeighborAdjacent u v))) ) := by
  classical
  intro edge_split g hgs u v he
  obtain ⟨l1, l2, hl⟩ := edge_split g u v he
  exact hgs u v l1 l2 hl

private theorem gstar :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), (∀ (x :
            GaussianInt), x ∈ D ↔ x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T) →
            ((T.cells.Nonempty) → (∀ (g : List GaussianInt), (∀ (z : GaussianInt), (z ∈ g) → (z ∈
            D \ P)) → (∀ (u : GaussianInt), (u ∈ g) → (∀ j : Fin 4, LatticeVertexIncidentCell u j
            ∈ T.cells)))) ) := by
  classical
  intro T D P hD hT g gW u hu
  obtain ⟨hx, hnb⟩ := (hD u).mp (Finset.mem_sdiff.mp (gW u hu)).1
  have hs : ∃ k : Fin 4, LatticeVertexIncidentCell u k ∈ T.cells := by
    rw [FootprintVertices, ite_eq_left hT] at hx
    obtain ⟨z, hz, rfl | rfl | rfl | rfl⟩ := hx
    · exact ⟨0, hz⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hz⟩
    · refine ⟨2, ?_⟩
      convert hz using 1; simp [LatticeVertexIncidentCell,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  intro j
  by_contra hj
  exact hnb (P3161T2IncidentBoundary T u hs ⟨j, hj⟩)

private theorem ordered :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
                GaussianInt)) → ((b ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((a
                ≠ b) → ((a =
            cert.precursorBoundary.a ∧ b = cert.precursorBoundary.b) ∨ (a =
            cert.precursorBoundary.b ∧ b = cert.precursorBoundary.a)))) ) := by
  classical
  intro C q cfg T cert a b ha hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (hab (ha.trans hb.symm)).elim

private theorem hreflectab :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
                GaussianInt)) → ((b ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((a
                ≠ b) → (∀ (g : List
            GaussianInt), (g.head? = some a) → ((g.getLast? = some b) → (((a =
            cert.precursorBoundary.a ∧ b = cert.precursorBoundary.b) ∨ (a =
            cert.precursorBoundary.b ∧ b = cert.precursorBoundary.a)) → ((GaussianRealPoint
            cert.precursorBoundary.b = ((2 : ℝ) * (TileCentroid cert.O).1 - (GaussianRealPoint
            cert.precursorBoundary.a).1, (2 : ℝ) * (TileCentroid cert.O).2 - (GaussianRealPoint
            cert.precursorBoundary.a).2)) → (GaussianRealPoint b = (2 * (TileCentroid cert.O).1
            - (GaussianRealPoint a).1, 2 * (TileCentroid cert.O).2 - (GaussianRealPoint
            a).2)))))))) ) := by
  classical
  intro C q cfg T cert a b ha hb hab g hga hgb ordered hreflect
  rcases ordered with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hreflect
  · apply Prod.ext
    · have h := congrArg Prod.fst hreflect
      dsimp at h ⊢
      linarith
    · have h := congrArg Prod.snd hreflect
      dsimp at h ⊢
      linarith

private theorem roots_ab :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
                GaussianInt)) → ((b ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((a
                ≠ b) → (∀ (g : List
            GaussianInt), (g.head? = some a) → ((g.getLast? = some b) → (((a =
            cert.precursorBoundary.a ∧ b = cert.precursorBoundary.b) ∨ (a =
            cert.precursorBoundary.b ∧ b = cert.precursorBoundary.a)) → ((GaussianRealPoint b =
            (2 * (TileCentroid cert.O).1 - (GaussianRealPoint a).1, 2 * (TileCentroid cert.O).2 -
            (GaussianRealPoint a).2)) → (∀ (z : GaussianInt), (z ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} :
            Finset GaussianInt)) → (z = a ∨ z = b)))))))) ) := by
  classical
  intro C q cfg T cert a b ha hb hab g hga hgb ordered hreflectab z hz
  rcases ordered with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  · simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm] using hz

private theorem arc_props :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (Finset.Nonempty cert.O.cells) → (∀
            (a : GaussianInt), ∀ (b : GaussianInt), (∀ (U : ProtoTile), (U.cells.Nonempty) →
            (BoundaryFootprintVertices U ⊆ FootprintVertices U)) → ((∀ (l : List GaussianInt), ∀
            (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ l.zip l.tail) → (∃ l1 l2, l = l1 ++
            u :: v :: l2)) → (∀ (l : List GaussianInt), (l.Nodup) → ((l.head? = some b) →
            ((l.getLast? = some a) → (((l.toFinset : Set GaussianInt) ⊆ BoundaryFootprintVertices
            cert.O) → ((∀ u, ∀ v, ∀ l1, ∀ l2, l = l1 ++ u :: v :: l2 →
            ({u, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges cert.O) → (∃ k : List
                GaussianInt, k.Nodup ∧ k.head? = some b ∧ k.getLast? = some a ∧ (∀ u, ∀ v, (u, v)
                ∈ k.zip k.tail → ({u, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges cert.O) ∧
                (∀ z ∈ k, z ∈ FootprintVertices cert.O))))))))) ) := by
  classical
  intro C q cfg T cert hO a b boundary_raw edge_split l hn hhead hlast hfoot hedge
  refine ⟨l, hn, hhead, hlast, ?_, ?_⟩
  · intro u v he
    obtain ⟨l1, l2, hl⟩ := edge_split l u v he
    exact hedge u v l1 l2 hl
  · intro z hz
    exact boundary_raw cert.O hO (hfoot (by simpa using hz))

private theorem hkl :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a ≠ b) → (∀ (k : List GaussianInt), (k.Nodup) → ((k.head? = some b) →
            ((k.getLast? = some a) → ((∀ (u : GaussianInt), ∀ (v : GaussianInt), (u, v) ∈ k.zip
            k.tail → {u, v} ∈ BoundaryFootprintEdges cert.O) → ((∀ z ∈ k, z ∈ FootprintVertices
            cert.O) → (2 ≤ k.length)))))) ) := by
  classical
  intro C q cfg T cert a b hab k hkn hkb hka hkboundary hkraw
  cases k with
  | nil => simp at hkb
  | cons c l =>
    cases l with
    | nil => simp only [List.head?_cons, List.getLast?_singleton,
        Option.some.injEq] at hkb hka
             exact (hab (hka.symm.trans hkb)).elim
    | cons d ds => simp

private theorem kedge_raw :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (k : List GaussianInt), (∀ (u :
            GaussianInt), ∀ (v : GaussianInt), (u, v) ∈ k.zip k.tail → {u, v} ∈
            BoundaryFootprintEdges cert.O) → ((∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v)
            ∈ k.zip k.tail) → (FourNeighborAdjacent u v)) → (∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ((u, v) ∈ k.zip k.tail) → (({u, v} : Finset GaussianInt) ∈
            FootprintEdges cert.O))) ) := by
  classical
  intro C q cfg T cert k hkboundary ksteps u v he
  obtain ⟨z, w, hs⟩ := P4397T1UnitEdgeCells.1 u v (ksteps u v he)
  have hg := P4397T1UnitEdgeCells.2 u v z w hs cert.O
  apply hg.1.mpr
  rcases hg.2.1.mp (hkboundary u v he) with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

private theorem trans_zero :
    (by
      classical
      exact
        ∀ (U : ProtoTile), TileTranslation U 0 = U ) := by
  classical
  intro U
  cases U
  simp [TileTranslation, GaussianTranslation, show GaussianTranslation 0 = id from
    funext (fun z => add_zero z)]

private theorem kstar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (i : Fin 3), ∀ (s : Bool), (cert.P
            i s).cells ⊆ T.cells) → (∀ (k : List GaussianInt), (∀ z ∈ k, z ∈ FootprintVertices
            cert.O) → ((∀ (U : ProtoTile), TileTranslation U 0 = U) → (∀ (x : GaussianInt), (x ∈
            k) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells)))) ) := by
  classical
  intro C q cfg T cert parent_sub k hkraw trans_zero x hx j
  have hcorner : x ∈ FootprintVertices
      (⟨{LatticeVertexIncidentCell x j}, LatticeVertexIncidentCell x j⟩ : ProtoTile) := by
    rw [FootprintVertices, ite_eq_left (Finset.singleton_nonempty _)]
    refine ⟨LatticeVertexIncidentCell x j, by simp, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  have hiso := cert.precursor_isolated 0 0 x
    (by simpa only [Int.cast_zero, zero_mul, zero_add, trans_zero] using hkraw x hx)
    (LatticeVertexIncidentCell x j) hcorner
  simp only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul,
    zero_add, trans_zero] at hiso
  exact hiso.elim (fun hz => parent_sub 0 true hz) (fun hz => parent_sub 0 false hz)

private theorem hcycles :
    (by
      classical
      exact
        ∀ (g : List GaussianInt), ∀ (k : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), ((g.dropLast ++ k.dropLast).zip (g.dropLast ++ k.dropLast).tail ++ [(y,
            x)] = g.zip g.tail ++ k.zip k.tail) → (
        let p := g.dropLast ++ k.dropLast
        let edges := (p.zip p.tail) ++ [(y, x)]
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), (u, v) ∈ edges ↔ (u, v) ∈ g.zip g.tail ∨ (u, v)
            ∈ k.zip k.tail) ) := by
  classical
  intro g k x y hedges p edges u v
  dsimp [edges]
  rw [hedges]
  exact List.mem_append

private theorem gsegments :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (l : List GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt),
            ((u, v) ∈ l.zip l.tail) → (u ∈ l ∧ v ∈ l)) → (∀ (g : List GaussianInt), (∀ (u :
            GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ g.zip g.tail) → (FourNeighborAdjacent u
            v)) → ((∀ (u : GaussianInt), (u ∈ g) → (∀ j : Fin 4, LatticeVertexIncidentCell u j ∈
            T.cells)) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ g.zip g.tail) → (∀ t
            : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * (u.re : Real) + (t : Real) * (v.re :
            Real), (1 - (t : Real)) * (u.im : Real) + (t : Real) * (v.im : Real)) ∈
            TileRealization T)))) ) := by
  classical
  intro T edge_vertices g gsteps gstar u v he
  obtain ⟨z, w, hs⟩ := P4397T1UnitEdgeCells.1 u v (gsteps u v he)
  have hg := P4397T1UnitEdgeCells.2 u v z w hs T
  exact (hg.2.2.1 (Or.inl (hg.2.2.2.2
    (gstar u (edge_vertices g u v he).1)).1)).2.2

private theorem ksegments :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (cert.O.cells ⊆ T.cells) → ((∀ (U :
            ProtoTile), ∀ (U' : ProtoTile), (U.cells ⊆ U'.cells) → (TileRealization U ⊆
            TileRealization U')) → (∀ (k : List GaussianInt), (∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ((u, v) ∈ k.zip k.tail) → (FourNeighborAdjacent u v)) → ((∀ (u :
            GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ k.zip k.tail) → (({u, v} : Finset
            GaussianInt) ∈ FootprintEdges cert.O)) → (∀ (u : GaussianInt), ∀ (v : GaussianInt),
            ((u, v) ∈ k.zip k.tail) → (∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * (u.re :
            Real) + (t : Real) * (v.re : Real), (1 - (t : Real)) * (u.im : Real) + (t : Real) *
            (v.im : Real)) ∈ TileRealization T))))) ) := by
  classical
  intro C q cfg T cert hOT realization_mono k ksteps kedge_raw u v he
  obtain ⟨z, w, hs⟩ := P4397T1UnitEdgeCells.1 u v (ksteps u v he)
  have hg := P4397T1UnitEdgeCells.2 u v z w hs cert.O
  exact fun t => realization_mono _ _ hOT
    ((hg.2.2.1 (hg.1.mp (kedge_raw u v he))).2.2 t)

private theorem exclude_pair :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        (∀ (u : GaussianInt), (u ∈ D \ P) → (∀ (v : GaussianInt), (v ∈ D \ P) →
            ((FourNeighborAdjacent u v) → (∀ (i : Fin 3), ∀ (s : Bool), (u ∈ FootprintVertices
            (cert.P i s)) → ((v ∈ FootprintVertices (cert.P i s)) → (¬ OpenLatticeEdge u v ⊆
            interior (TileRealization (cert.P i s)))))))) → ((∀ (i : Fin 3), ∀ (s : Bool), (F i
            s).cells ⊆ (cert.P i s).cells) → ((∀ (i : Fin 3), ∀ (s : Bool), ∀ (z : GaussianInt),
            (z ∈ (F i s).cells) → (z ∉ cert.O.cells)) → ((∀ (l : List GaussianInt), ∀ (u :
            GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ l.zip l.tail) → (u ∈ l ∧ v ∈ l)) → (∀ (g
            : List GaussianInt), (∀ (z : GaussianInt), (z ∈ g) → (z ∈ D \ P)) → ((∀ (u :
            GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ g.zip g.tail) → (FourNeighborAdjacent u
            v)) → (∀ (k : List GaussianInt), (∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈
            k.zip k.tail) → (({u, v} : Finset GaussianInt) ∈ FootprintEdges cert.O)) → (∀ (x :
            GaussianInt), ∀ (y : GaussianInt),
        let p := g.dropLast ++ k.dropLast
        let edges := (p.zip p.tail) ++ [(y, x)]
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), (u, v) ∈ edges ↔ (u, v) ∈ g.zip g.tail ∨ (u,
            v) ∈ k.zip k.tail) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (z : GaussianInt),
            ∀ (w : GaussianInt), ((((u = z + 1 ∧ v = z + 1 + ⟨0, 1⟩) ∨
              (v = z + 1 ∧ u = z + 1 + ⟨0, 1⟩)) ∧ w = z + 1 ∨
            ((u = z + 1 + ⟨0, 1⟩ ∧ v = z + ⟨0, 1⟩) ∨
              (v = z + 1 + ⟨0, 1⟩ ∧ u = z + ⟨0, 1⟩)) ∧ w = z + ⟨0, 1⟩)) → (∀ (i : Fin 3), ∀ (s :
                  Bool), (z ∈ (F i s).cells) → ((w ∈ (F i s).cells) → ((u, v) ∉ edges)))))))))))
                  ) := by
  classical
  intro C q cfg T cert D P F hno Fsub FnotO edge_vertices g gW gsteps k kedge_raw x y p edges
      hcycles u v z w hs i s hz hw he
  have hgeom := P4397T1UnitEdgeCells.2 u v z w hs
  rcases (hcycles u v).mp he with hg | hk
  · have hp := hgeom (cert.P i s)
    have hboth := And.intro (Fsub i s hz) (Fsub i s hw)
    have hraw := hp.2.2.1 (Or.inl hboth.1)
    have huv := edge_vertices g u v hg
    exact hno u (gW u huv.1) v (gW v huv.2) (gsteps u v hg)
      i s hraw.1 hraw.2.1 (hp.2.2.2.1 hboth)
  · rcases (hgeom cert.O).1.mp (kedge_raw u v hk) with ho | ho
    · exact FnotO i s z hz ho
    · exact FnotO i s w hw ho

private theorem he'At460 :
    (by
      classical
      exact
        ∀ (g k : List GaussianInt) (x y : GaussianInt),
          let p := g.dropLast ++ k.dropLast;
          let edges := p.zip p.tail ++ [(y, x)];
          ∀ (u v : GaussianInt), (u, v) ∈ p.zip p.tail ∨ u = y ∧ v = x → (u, v) ∈ edges) := by
  classical
  intro g k x y p edges u v he
  rcases he with he | ⟨rfl, rfl⟩
  · simp only [edges, List.mem_append]; exact Or.inl he
  · simp [edges]

private theorem hnone :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (g : List GaussianInt), (∀ (u :
            GaussianInt), ∀ (v : GaussianInt), (u, v) ∈ g.zip g.tail → {u, v} ∉ FootprintEdges
            cert.O) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ((u, v) ∈ g.zip g.tail) → (∀ (z
            : GaussianInt), ∀ (w : GaussianInt), (∀ (U : ProtoTile), ({u, v} ∈ FootprintEdges U ↔
            z ∈ U.cells ∨ w ∈ U.cells) ∧ ({u, v} ∈ BoundaryFootprintEdges U ↔ z ∈ U.cells ∧ w ∉
            U.cells ∨ z ∉ U.cells ∧ w ∈ U.cells) ∧ (z ∈ U.cells ∨ w ∈ U.cells → u ∈
            FootprintVertices U ∧ v ∈ FootprintVertices U ∧ ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) :
            Type)), (((1 : ℝ) - (↑t : ℝ)) * (↑u.re : ℝ) + (↑t : ℝ) * (↑v.re : ℝ), ((1 : ℝ) - (↑t
            : ℝ)) * (↑u.im : ℝ) + (↑t : ℝ) * (↑v.im : ℝ)) ∈ TileRealization U) ∧ (z ∈ U.cells ∧ w
            ∈ U.cells → OpenLatticeEdge u v ⊆ interior (TileRealization U)) ∧ ((∀ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell u j ∈ U.cells) → z ∈ U.cells ∧ w ∈ U.cells)) → (z ∉
            cert.O.cells ∧ w ∉ cert.O.cells))) ) := by
  classical
  intro C q cfg T cert g gnoO u v he z w hg
  have hn : ¬ (z ∈ cert.O.cells ∨ w ∈ cert.O.cells) :=
    fun h => gnoO u v he ((hg cert.O).1.mpr h)
  exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩

end PrecursorLoopGeometry

theorem P4366T1PrecursorPathLoop
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (D P : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s))
    (hO : cert.O.cells.Nonempty)
    (hOband : BandPrototile (cfg.firstPredecessor 1) cert.O)
    (hroots : ∀ x ∈ D \ P,
      x ∈ FootprintVertices cert.O ↔
        x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
          Finset GaussianInt))
    (a b : GaussianInt)
    (ha : a ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
      Finset GaussianInt))
    (hb : b ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
      Finset GaussianInt))
    (hab : a ≠ b) (V : Set GaussianInt) (E : Set (Finset GaussianInt))
    (hpath : SimpleGridPathBetween V E a b)
    (hV : V ⊆ (D \ P : Finset GaussianInt)) :
    let F := P4366T1PrecursorRemainderFamily cert.P cert.O
    ∃ (p : List GaussianInt) (x y : GaussianInt),
      p.Nodup ∧ 3 ≤ p.length ∧ p.head? = some x ∧ p.getLast? = some y ∧
      (∀ u v, (u, v) ∈ p.zip p.tail → FourNeighborAdjacent u v) ∧
      FourNeighborAdjacent y x ∧
      (∀ u v, ((u, v) ∈ p.zip p.tail ∨ (u = y ∧ v = x)) →
        ∀ t : Set.Icc (0 : Real) 1,
          ((1 - (t : Real)) * (u.re : Real) + (t : Real) * (v.re : Real),
            (1 - (t : Real)) * (u.im : Real) + (t : Real) * (v.im : Real)) ∈
            TileRealization T) ∧
      (∀ z ∈ p, z ∉ BoundaryFootprintVertices T) ∧
      (let edges := (p.zip p.tail) ++ [(y, x)]
       (∀ i s z,
         ((z ∈ (F i s).cells ∧ z + 1 ∈ (F i s).cells) →
           (z + 1, z + 1 + ⟨0, 1⟩) ∉ edges ∧
             (z + 1 + ⟨0, 1⟩, z + 1) ∉ edges) ∧
         ((z ∈ (F i s).cells ∧ z + ⟨0, 1⟩ ∈ (F i s).cells) →
           (z + 1 + ⟨0, 1⟩, z + ⟨0, 1⟩) ∉ edges ∧
             (z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩) ∉ edges)) ∧
       (∃ z : GaussianInt,
         ((z ∈ T.cells ∧ z ∉ cert.O.cells) ∧
           (z + 1 ∈ T.cells ∧ z + 1 ∉ cert.O.cells) ∧
           ((z + 1, z + 1 + ⟨0, 1⟩) ∈ edges ∨
             (z + 1 + ⟨0, 1⟩, z + 1) ∈ edges)) ∨
         ((z ∈ T.cells ∧ z ∉ cert.O.cells) ∧
           (z + ⟨0, 1⟩ ∈ T.cells ∧ z + ⟨0, 1⟩ ∉ cert.O.cells) ∧
           ((z + 1 + ⟨0, 1⟩, z + ⟨0, 1⟩) ∈ edges ∨
             (z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩) ∈ edges)))) := by
-- BODY
  classical
  dsimp only
  let F := P4366T1PrecursorRemainderFamily cert.P cert.O
  obtain ⟨_, _, _, _, _, _, hpair, hdisjoint⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have hOA := PrecursorLoopGeometry.hOA C q cfg T cert hpair
  have hOB := PrecursorLoopGeometry.hOB C q cfg T cert hpair
  have parent_sub (i : Fin 3) (s : Bool) : (cert.P i s).cells ⊆ T.cells :=
    fun z hz => (cert.outer_union z).mpr ⟨i, s, hz⟩
  have hOT : cert.O.cells ⊆ T.cells := fun z hz => parent_sub 0 true (hOA hz)
  have hT : T.cells.Nonempty := hO.mono hOT
  have realization_mono := PrecursorLoopGeometry.realization_mono
  have hOfootA := (PrecursorLoopGeometry.footprint_mono) cert.O (cert.P 0 true) hO hOA
  have hno := PrecursorLoopGeometry.hno C q cfg T cert D P hP
  have Fsub := PrecursorLoopGeometry.Fsub C q cfg T cert
  have FnotO := PrecursorLoopGeometry.FnotO C q cfg T cert hdisjoint hOA Fsub
  have boundary_raw := PrecursorLoopGeometry.boundary_raw
  have edge_split := PrecursorLoopGeometry.edge_split
  have edge_vertices (l : List GaussianInt) (u v : GaussianInt)
      (he : (u, v) ∈ l.zip l.tail) : u ∈ l ∧ v ∈ l :=
    ⟨(List.of_mem_zip he).1, List.mem_of_mem_tail (List.of_mem_zip he).2⟩
  have boundary_step := PrecursorLoopGeometry.boundary_step
  obtain ⟨g, hgn, hgl, hga, hgb, hgv, hgs, _⟩ := hpath
  have gW := PrecursorLoopGeometry.gW D P V hV g hgv
  have gsteps := PrecursorLoopGeometry.gsteps edge_split g hgs
  have gstar := PrecursorLoopGeometry.gstar T D P hD hT g gW
  have ordered := PrecursorLoopGeometry.ordered C q cfg T cert a b ha hb hab
  obtain ⟨plusArc, minusArc, hpn, hmn, hph, hpl, hmh, hml,
      hpf, hmf, hpe, hme, _, _, hreflect, _⟩ :=
    (show ∃ plusArc minusArc : List GaussianInt, _ from by
      rcases cert.precursorBoundary.branch with hp | hn
      · exact hp.2
      · exact ((Finset.nonempty_iff_ne_empty.mp hO) hn.1).elim)
  have hreflectab := PrecursorLoopGeometry.hreflectab C q cfg T cert a b ha hb hab g hga hgb
      ordered hreflect
  have roots_ab := PrecursorLoopGeometry.roots_ab C q cfg T cert a b ha hb hab g hga hgb ordered
      hreflectab
  have gnoO := P4397T1PathAvoidsPrecursorEdges cert.O (TileCentroid cert.O)
    (BandPrototileCentralSymmetry _ _ hOband) a b hab hreflectab
    g hgn hga hgb gsteps
    (fun z hz hf => roots_ab z ((hroots z (gW z hz)).mp hf))
    (by
      intro u v he hu hv hchord
      have huv := edge_vertices g u v he
      exact hno u (gW u huv.1) v (gW v huv.2) (gsteps u v he)
        0 true (hOfootA hu) (hOfootA hv)
        (fun x hx => interior_mono (realization_mono _ _ hOA) (hchord hx)))
  obtain ⟨k, hkn, hkb, hka, hkboundary, hkraw⟩ :
      ∃ k : List GaussianInt, k.Nodup ∧ k.head? = some b ∧
        k.getLast? = some a ∧
        (∀ u v, (u, v) ∈ k.zip k.tail →
          ({u, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges cert.O) ∧
        (∀ z ∈ k, z ∈ FootprintVertices cert.O) := by
    have arc_props := PrecursorLoopGeometry.arc_props C q cfg T cert hO a b boundary_raw edge_split
    rcases ordered with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact arc_props minusArc hmn hmh hml
        (fun z hz => (hmf ▸ hz).2) (fun u v l1 l2 hl => (hme u v l1 l2 hl).2)
    · exact arc_props plusArc hpn hph hpl
        (fun z hz => (hpf ▸ hz).2) (fun u v l1 l2 hl => (hpe u v l1 l2 hl).2)
  have hkl := PrecursorLoopGeometry.hkl C q cfg T cert a b hab k hkn hkb hka hkboundary hkraw
  have ksteps (u v : GaussianInt) (he : (u, v) ∈ k.zip k.tail) :
      FourNeighborAdjacent u v := boundary_step cert.O u v (hkboundary u v he)
  have kedge_raw (u v : GaussianInt) (he : (u, v) ∈ k.zip k.tail) :
      ({u, v} : Finset GaussianInt) ∈ FootprintEdges cert.O := PrecursorLoopGeometry.kedge_raw C
          q cfg T cert k hkboundary ksteps u v he
  have kstar := PrecursorLoopGeometry.kstar C q cfg T cert parent_sub k hkraw
      (PrecursorLoopGeometry.trans_zero)
  obtain ⟨hnd, hlen, x, y, hhead, hlast, hedges, hmem⟩ :=
    P4397T1SimplePathSplicing g k a b hgn hkn hgl hkl hga hgb hkb hka
      (fun z hzg hzk => roots_ab z ((hroots z (gW z hzg)).mp (hkraw z hzk)))
      (by
        intro u v he
        exact ⟨fun hk => gnoO u v he (kedge_raw u v hk),
          fun hk => gnoO u v he (by simpa [Finset.pair_comm] using kedge_raw v u hk)⟩)
  let p := g.dropLast ++ k.dropLast
  let edges := (p.zip p.tail) ++ [(y, x)]
  have hcycles := PrecursorLoopGeometry.hcycles g k x y hedges
  have allsteps (u v : GaussianInt) (he : (u, v) ∈ edges) : FourNeighborAdjacent u v :=
    ((hcycles u v).mp he).elim (gsteps u v) (ksteps u v)
  have exclude_pair := PrecursorLoopGeometry.exclude_pair C q cfg T cert D P hno Fsub FnotO
      edge_vertices g gW gsteps k kedge_raw x y hcycles
  refine ⟨p, x, y, hnd, hlen, hhead, hlast, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v he
    exact allsteps u v (by simp only [edges, List.mem_append]; exact Or.inl he)
  · exact allsteps y x (by simp [edges])
  · intro u v he
    have he' := PrecursorLoopGeometry.he'At460 g k x y u v he
    exact ((hcycles u v).mp he').elim ((PrecursorLoopGeometry.gsegments T edge_vertices g gsteps
        gstar) u v) ((PrecursorLoopGeometry.ksegments C q cfg T cert hOT realization_mono k
        ksteps kedge_raw) u v)
  · intro z hz
    rcases hmem z hz with hg | hk
    · exact ((hD z).mp (Finset.mem_sdiff.mp (gW z hg)).1).2
    · intro hz
      rw [BoundaryFootprintVertices, ite_eq_left hT] at hz
      obtain ⟨e, ⟨w, ⟨rfl, hw⟩ | ⟨rfl, hw⟩⟩, hze⟩ := hz
      all_goals
        have h0 := kstar z hk 0
        have h1 := kstar z hk 1
        have h2 := kstar z hk 2
        have h3 := kstar z hk 3
        simp only [Finset.mem_insert, Finset.mem_singleton] at hze
        rcases hze with rfl | rfl
        all_goals
          simp [LatticeVertexIncidentCell, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc] at h0 h1 h2 h3 hw
          tauto
  · intro i s z
    constructor
    · rintro ⟨hz, hw⟩
      exact ⟨exclude_pair _ _ z (z + 1) (Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩) i s hz hw,
        exclude_pair _ _ z (z + 1) (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩) i s hz hw⟩
    · rintro ⟨hz, hw⟩
      exact ⟨exclude_pair _ _ z (z + ⟨0, 1⟩) (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩) i s hz hw,
        exclude_pair _ _ z (z + ⟨0, 1⟩) (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩) i s hz hw⟩
  · obtain ⟨u, v, he⟩ : ∃ u v, (u, v) ∈ g.zip g.tail := by
      cases g with
      | nil => simp at hgl
      | cons u l =>
        cases l with
        | nil => simp at hgl
        | cons v ds => exact ⟨u, v, by simp⟩
    obtain ⟨z, w, hs⟩ := P4397T1UnitEdgeCells.1 u v (gsteps u v he)
    have hg := P4397T1UnitEdgeCells.2 u v z w hs
    have hboth := (hg T).2.2.2.2 (gstar u (edge_vertices g u v he).1)
    have hnone := PrecursorLoopGeometry.hnone C q cfg T cert g gnoO u v he z w hg
    have he' : (u, v) ∈ edges := (hcycles u v).mpr (Or.inl he)
    refine ⟨z, ?_⟩
    rcases hs with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
    · refine Or.inl ⟨⟨hboth.1, hnone.1⟩, ⟨hboth.2, hnone.2⟩, ?_⟩
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl he'
      · exact Or.inr he'
    · refine Or.inr ⟨⟨hboth.1, hnone.1⟩, ⟨hboth.2, hnone.2⟩, ?_⟩
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl he'
      · exact Or.inr he'

end ApollonianSuperharmonic

end
