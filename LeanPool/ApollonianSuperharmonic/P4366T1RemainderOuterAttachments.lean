/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.P4366T1PrecursorRemainderFamily

-- [TABLET NODE: P4366T1RemainderOuterAttachments]

/-!
# P4366T1RemainderOuterAttachments

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RemainderAttachmentGeometry

private abbrev zero_translation := ApollonianSuperharmonic.TileTranslationProperties.zero

private theorem isolated :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (U : ProtoTile), TileTranslation U
            0 = U) → (∀ {x : GaussianInt}, ∀ {a : GaussianInt}, (x ∈ FootprintVertices cert.O) →
            ((x = a ∨ x = a + 1 ∨ x = a + ⟨0, 1⟩ ∨
            x = a + 1 + ⟨0, 1⟩) → (a ∈ T.cells))) ) := by
  classical
  intro C q cfg T cert zero_translation x a hx hxa
  have hx' : x ∈ FootprintVertices
      (TileTranslation cert.O ((0 : GaussianInt) * cert.u +
        (0 : GaussianInt) * cert.v)) := by
    simpa only [zero_mul, zero_add, zero_translation] using hx
  have hs : x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) := by
    simpa only [FootprintVertices, Finset.singleton_nonempty, ite_true,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left] using hxa
  have hi := cert.precursor_isolated 0 0 x hx' a hs
  simp only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul,
    zero_add, zero_translation] at hi
  rcases hi with h | h
  · exact (cert.outer_union a).mpr ⟨0, true, h⟩
  · exact (cert.outer_union a).mpr ⟨0, false, h⟩

private theorem corner :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (z : GaussianInt), (z ∈
            cert.O.cells) → (∀ (x : GaussianInt), (x = z ∨ x = z + 1 ∨ x = z + ⟨0, 1⟩ ∨
            x = z + 1 + ⟨0, 1⟩) → (x ∈ FootprintVertices cert.O)) ) := by
  classical
  intro C q cfg T cert z hx x hxa
  simpa only [FootprintVertices, ite_eq_left (show cert.O.cells.Nonempty from ⟨z, hx⟩),
    Set.mem_ofPred_eq] using (show ∃ a ∈ cert.O.cells,
      x = a ∨ x = a + 1 ∨ x = a + ⟨0, 1⟩ ∨
        x = a + 1 + ⟨0, 1⟩ from ⟨z, hx, hxa⟩)

private theorem hneighbors :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ {x : GaussianInt}, ∀
            {a : GaussianInt}, (x ∈ FootprintVertices cert.O) → ((x = a ∨ x = a + 1 ∨ x = a + ⟨0,
            1⟩ ∨ x = a + 1 + ⟨0, 1⟩) → (a ∈ T.cells))) → ((∀ (z : GaussianInt), (z ∈
            cert.O.cells) → (∀ (x : GaussianInt), (x = z ∨ x = z + 1 ∨ x = z + ⟨0, 1⟩ ∨ x = z + 1
            + ⟨0, 1⟩) → (x ∈ FootprintVertices cert.O))) → (∀ (z : GaussianInt), (z ∈
            cert.O.cells) → (z - ⟨0, 1⟩ ∈ T.cells ∧ z + ⟨0, 1⟩ ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z +
            1 ∈ T.cells))) ) := by
  classical
  intro C q cfg T cert isolated corner z hz
  refine ⟨isolated (corner z hz z (Or.inl rfl)) ?_,
    isolated (corner z hz (z + ⟨0, 1⟩)
      (Or.inr (Or.inr (Or.inl rfl)))) (Or.inl rfl),
    isolated (corner z hz z (Or.inl rfl)) ?_,
    isolated (corner z hz (z + 1) (Or.inr (Or.inl rfl))) (Or.inl rfl)⟩
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp))

private theorem hOsubA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 true).cells
            ) := by
  classical
  intro C q cfg T cert z hz
  exact (cert.plus_union z).mpr ⟨0, false,
    by simpa only [← cert.precursor_eq] using hz⟩

private theorem hOsubB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 false).cells
            ) := by
  classical
  intro C q cfg T cert z hz
  exact (cert.minus_union z).mpr ⟨0, true, by
    rw [← cert.precursor_cells]
    exact hz⟩

private theorem hcover :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        (cert.O.cells ⊆ (cert.P 0 true).cells) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin
            (3 : ℕ)), ∀ (t : Bool), (i, s) ≠ (j, t) → ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 :
            ℕ))) → Disjoint (cert.P i s).cells (cert.P j t).cells) → (∀ z, z ∈ T.cells ∧ z ∉
            cert.O.cells ↔ ∃ i s, z ∈ (F i s).cells)) ) := by
  classical
  intro C q cfg T cert F hOsubA hdisjoint z
  constructor
  · rintro ⟨hzT, hzO⟩
    obtain ⟨i, s, hzi⟩ := (cert.outer_union z).mp hzT
    refine ⟨i, s, ?_⟩
    dsimp [F, P4366T1PrecursorRemainderFamily]
    split_ifs with hi
    · simp only [TileCellComplement, Finset.mem_sdiff]
      exact ⟨hzi, hzO⟩
    · exact hzi
  · rintro ⟨i, s, hz⟩
    constructor
    · have : z ∈ (cert.P i s).cells := by
        change z ∈ (P4366T1PrecursorRemainderFamily cert.P cert.O i s).cells at hz
        simp only [P4366T1PrecursorRemainderFamily] at hz
        split_ifs at hz with hi
        · change z ∈ (cert.P i s).cells \ cert.O.cells at hz
          exact (Finset.mem_sdiff.mp hz).1
        · exact hz
      exact (cert.outer_union z).mpr ⟨i, s, this⟩
    · intro hzO
      have hzP : z ∈ (cert.P i s).cells := by
        change z ∈ (P4366T1PrecursorRemainderFamily cert.P cert.O i s).cells at hz
        simp only [P4366T1PrecursorRemainderFamily] at hz
        split_ifs at hz with hi
        · change z ∈ (cert.P i s).cells \ cert.O.cells at hz
          exact (Finset.mem_sdiff.mp hz).1
        · exact hz
      by_cases hi : i = 0
      · subst i
        cases s
        · have hz' : z ∈ (cert.P 0 false).cells \ cert.O.cells := by
            change z ∈ (P4366T1PrecursorRemainderFamily cert.P cert.O 0 false).cells at hz
            exact hz
          exact (Finset.mem_sdiff.mp hz').2 hzO
        · have hz' : z ∈ (cert.P 0 true).cells \ cert.O.cells := by
            change z ∈ (P4366T1PrecursorRemainderFamily cert.P cert.O 0 true).cells at hz
            exact hz
          exact (Finset.mem_sdiff.mp hz').2 hzO
      · have hne : (i, s) ≠ (0, true) := by
          intro he
          exact hi (congrArg Prod.fst he)
        have hdis := hdisjoint i s 0 true hne (by simp [hi])
        exact Finset.disjoint_left.mp hdis hzP (hOsubA hzO)

private theorem hLattice :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        ∀ i, ∀ s, LatticeTile (F i s) ) := by
  classical
  intro C q cfg T cert F i s
  by_cases hi : i = 0
  · subst i
    cases s
    · exact cert.precursor_complement_lattice.2
    · exact cert.precursor_complement_lattice.1
  · simpa [F, P4366T1PrecursorRemainderFamily, hi] using cert.parent_lattice i s

private theorem horiz_unique :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (({x, x + 1} : Finset GaussianInt) = {y,
            y + 1}) → (x = y) ) := by
  classical
  intro x y h
  have hx : x = y ∨ x = y + 1 := by
    have : x ∈ ({y, y + 1} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + 1 := by
    have : y ∈ ({x, x + 1} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have hre := congrArg Zsqrtd.re hxy
    have hre' := congrArg Zsqrtd.re hyx
    norm_num at hre hre'
    omega

private theorem vert_unique :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset
            GaussianInt) =
            {y, y + ⟨0, 1⟩}) → (x = y) ) := by
  classical
  intro x y h
  have hx : x = y ∨ x = y + ⟨0, 1⟩ := by
    have : x ∈ ({y, y + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + ⟨0, 1⟩ := by
    have : y ∈ ({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have him := congrArg Zsqrtd.im hxy
    have him' := congrArg Zsqrtd.im hyx
    simp at him him'
    omega

private theorem horiz_ne_vert :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ({x, x + 1} : Finset GaussianInt) ≠ {y,
            y + (⟨0, 1⟩ : GaussianInt)} ) := by
  classical
  intro x y h
  have hx : x = y ∨ x = y + ⟨0, 1⟩ := by
    have : x ∈ ({y, y + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hx1 : x + 1 = y ∨ x + 1 = y + ⟨0, 1⟩ := by
    have : x + 1 ∈ ({y, y + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  rcases hx with h1 | h1 <;> rcases hx1 with h2 | h2
  all_goals
    have hre := congrArg Zsqrtd.re h1
    have him := congrArg Zsqrtd.im h1
    have hre1 := congrArg Zsqrtd.re h2
    have him1 := congrArg Zsqrtd.im h2
    simp at hre him hre1 him1
    omega

private theorem sharedEdge :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (x : GaussianInt), ∀ (y : GaussianInt), (({x, x + 1} : Finset
            GaussianInt) = {y, y + 1}) → (x = y)) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt),
            (({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) = {y, y + ⟨0, 1⟩}) → (x = y))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), ({x, x + 1} : Finset GaussianInt) ≠ {y,
            y + (⟨0, 1⟩ : GaussianInt)}) → (∀ (A : ProtoTile), (A.cells ⊆ T.cells) → (∀ (e :
            Finset GaussianInt), (e ∈ BoundaryFootprintEdges A) → ((e ∈ BoundaryFootprintEdges T)
            → ((∃ z, e = {z, z + 1} ∧ ((z ∈ A.cells ∧ z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨ (z ∉
            A.cells ∧ z - ⟨0, 1⟩ ∈ A.cells ∧ z - ⟨0, 1⟩ ∈ T.cells ∧ z ∉ T.cells))) ∨ (∃ z, e =
            {z, z + ⟨0, 1⟩} ∧ ((z ∈ A.cells ∧ z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨ (z ∉ A.cells ∧ z -
            1 ∈ A.cells ∧ z - 1 ∈ T.cells ∧ z ∉ T.cells))))))))) ) := by
  classical
  intro T horiz_unique vert_unique horiz_ne_vert A hsub e heA heT
  rcases heA with ⟨x, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩
  · rcases heT with ⟨y, ⟨he, ht⟩ | ⟨he, ht⟩⟩
    · have hxy := horiz_unique x y he
      subst y
      rcases ha with ⟨hax, haxout⟩ | ⟨haxout, hax⟩
      · rcases ht with ⟨htx, htxout⟩ | ⟨htxout, htx⟩
        · exact Or.inl ⟨x, rfl, Or.inl ⟨hax, hsub hax, htxout⟩⟩
        · exact (htxout (hsub hax)).elim
      · rcases ht with ⟨htx, htxout⟩ | ⟨htxout, htx⟩
        · exact (htxout (hsub hax)).elim
        · exact Or.inl ⟨x, rfl, Or.inr ⟨(by
            intro hxA
            exact htxout (hsub hxA)), hax, hsub hax, htxout⟩⟩
    · exact (horiz_ne_vert x y he).elim
  · rcases heT with ⟨y, ⟨he, ht⟩ | ⟨he, ht⟩⟩
    · exact (horiz_ne_vert y x he.symm).elim
    · have hxy := vert_unique x y he
      subst y
      rcases ha with ⟨hax, haxout⟩ | ⟨haxout, hax⟩
      · rcases ht with ⟨htx, htxout⟩ | ⟨htxout, htx⟩
        · exact Or.inr ⟨x, rfl, Or.inl ⟨hax, hsub hax, htxout⟩⟩
        · exact (htxout (hsub hax)).elim
      · rcases ht with ⟨htx, htxout⟩ | ⟨htxout, htx⟩
        · exact (htxout (hsub hax)).elim
        · exact Or.inr ⟨x, rfl, Or.inr ⟨(by
            intro hxA
            exact htxout (hsub hxA)), hax, hsub hax, htxout⟩⟩

private theorem outerAttach :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let F := P4366T1PrecursorRemainderFamily cert.P cert.O
        (∀ (z : GaussianInt), (z ∈ cert.O.cells) → (z - ⟨0, 1⟩ ∈ T.cells ∧ z + ⟨0, 1⟩ ∈ T.cells ∧
            z - 1 ∈ T.cells ∧ z + 1 ∈ T.cells)) → ((∀ (A : ProtoTile), (A.cells ⊆ T.cells) → (∀
            (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges A) → ((e ∈
            BoundaryFootprintEdges T) → ((∃ z, e = {z, z + 1} ∧ ((z ∈ A.cells ∧ z ∈ T.cells ∧ z -
            ⟨0, 1⟩ ∉ T.cells) ∨ (z ∉ A.cells ∧ z - ⟨0, 1⟩ ∈ A.cells ∧ z - ⟨0, 1⟩ ∈ T.cells ∧ z ∉
            T.cells))) ∨ (∃ z, e = {z, z + ⟨0, 1⟩} ∧ ((z ∈ A.cells ∧ z ∈ T.cells ∧ z - 1 ∉
            T.cells) ∨ (z ∉ A.cells ∧ z - 1 ∈ A.cells ∧ z - 1 ∈ T.cells ∧ z ∉ T.cells))))))) → (∀
            (i : Fin 3), ∀ (s : Bool), ((cert.P i s).cells ⊆ T.cells) → ((∃ e : Finset GaussianInt,
            e ∈ BoundaryFootprintEdges (cert.P i s) ∧ e ∈ BoundaryFootprintEdges T) → (∃ e :
                Finset GaussianInt, e ∈ BoundaryFootprintEdges (F i s) ∧ e ∈
                BoundaryFootprintEdges T)))) ) := by
  classical
  intro C q cfg T cert F hneighbors sharedEdge i s hsub hcommon
  by_cases hdel : i = 0
  · subst i
    cases s
    · obtain ⟨e, heA, heT⟩ := hcommon
      have hshared := sharedEdge (cert.P 0 false) hsub e heA heT
      rcases hshared with ⟨z, he, hs⟩ | ⟨z, he, hs⟩
      · rcases hs with ⟨hzA, hzT, hout⟩ | ⟨hznotA, hzinA, hzinT, houtT⟩
        · have hznotO : z ∉ cert.O.cells := by
            intro hzO
            exact hout (hneighbors z hzO).1
          have heF : e ∈ BoundaryFootprintEdges (F 0 false) := by
            refine ⟨z, ?_⟩
            refine Or.inl ⟨he, Or.inl ⟨?_, ?_⟩⟩
            · change z ∈ (cert.P 0 false).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzA, hznotO⟩
            · intro hzbad
              exact hout (hsub (Finset.mem_sdiff.mp hzbad).1)
          exact ⟨e, heF, heT⟩
        · have hznotO : z - ⟨0, 1⟩ ∉ cert.O.cells := by
            intro hzO
            have hn := (hneighbors (z - ⟨0, 1⟩) hzO).2.1
            exact houtT (by simpa using hn)
          have heF : e ∈ BoundaryFootprintEdges (F 0 false) := by
            refine ⟨z, ?_⟩
            refine Or.inl ⟨he, Or.inr ⟨?_, ?_⟩⟩
            · intro hzbad
              exact hznotA (Finset.mem_sdiff.mp hzbad).1
            · change z - ⟨0, 1⟩ ∈ (cert.P 0 false).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzinA, hznotO⟩
          exact ⟨e, heF, heT⟩
      · rcases hs with ⟨hzA, hzT, hout⟩ | ⟨hznotA, hzinA, hzinT, houtT⟩
        · have hznotO : z ∉ cert.O.cells := by
            intro hzO
            exact hout (hneighbors z hzO).2.2.1
          have heF : e ∈ BoundaryFootprintEdges (F 0 false) := by
            refine ⟨z, ?_⟩
            refine Or.inr ⟨he, Or.inl ⟨?_, ?_⟩⟩
            · change z ∈ (cert.P 0 false).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzA, hznotO⟩
            · intro hzbad
              exact hout (hsub (Finset.mem_sdiff.mp hzbad).1)
          exact ⟨e, heF, heT⟩
        · have hznotO : z - 1 ∉ cert.O.cells := by
            intro hzO
            have hn := (hneighbors (z - 1) hzO).2.2.2
            exact houtT (by simpa using hn)
          have heF : e ∈ BoundaryFootprintEdges (F 0 false) := by
            refine ⟨z, ?_⟩
            refine Or.inr ⟨he, Or.inr ⟨?_, ?_⟩⟩
            · intro hzbad
              exact hznotA (Finset.mem_sdiff.mp hzbad).1
            · change z - 1 ∈ (cert.P 0 false).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzinA, hznotO⟩
          exact ⟨e, heF, heT⟩
    · obtain ⟨e, heA, heT⟩ := hcommon
      have hshared := sharedEdge (cert.P 0 true) hsub e heA heT
      rcases hshared with ⟨z, he, hs⟩ | ⟨z, he, hs⟩
      · rcases hs with ⟨hzA, hzT, hout⟩ | ⟨hznotA, hzinA, hzinT, houtT⟩
        · have hznotO : z ∉ cert.O.cells := by
            intro hzO
            exact hout (hneighbors z hzO).1
          have heF : e ∈ BoundaryFootprintEdges (F 0 true) := by
            refine ⟨z, ?_⟩
            refine Or.inl ⟨he, Or.inl ⟨?_, ?_⟩⟩
            · change z ∈ (cert.P 0 true).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzA, hznotO⟩
            · intro hzbad
              exact hout (hsub (Finset.mem_sdiff.mp hzbad).1)
          exact ⟨e, heF, heT⟩
        · have hznotO : z - ⟨0, 1⟩ ∉ cert.O.cells := by
            intro hzO
            have hn := (hneighbors (z - ⟨0, 1⟩) hzO).2.1
            exact houtT (by simpa using hn)
          have heF : e ∈ BoundaryFootprintEdges (F 0 true) := by
            refine ⟨z, ?_⟩
            refine Or.inl ⟨he, Or.inr ⟨?_, ?_⟩⟩
            · intro hzbad
              exact hznotA (Finset.mem_sdiff.mp hzbad).1
            · change z - ⟨0, 1⟩ ∈ (cert.P 0 true).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzinA, hznotO⟩
          exact ⟨e, heF, heT⟩
      · rcases hs with ⟨hzA, hzT, hout⟩ | ⟨hznotA, hzinA, hzinT, houtT⟩
        · have hznotO : z ∉ cert.O.cells := by
            intro hzO
            exact hout (hneighbors z hzO).2.2.1
          have heF : e ∈ BoundaryFootprintEdges (F 0 true) := by
            refine ⟨z, ?_⟩
            refine Or.inr ⟨he, Or.inl ⟨?_, ?_⟩⟩
            · change z ∈ (cert.P 0 true).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzA, hznotO⟩
            · intro hzbad
              exact hout (hsub (Finset.mem_sdiff.mp hzbad).1)
          exact ⟨e, heF, heT⟩
        · have hznotO : z - 1 ∉ cert.O.cells := by
            intro hzO
            have hn := (hneighbors (z - 1) hzO).2.2.2
            exact houtT (by simpa using hn)
          have heF : e ∈ BoundaryFootprintEdges (F 0 true) := by
            refine ⟨z, ?_⟩
            refine Or.inr ⟨he, Or.inr ⟨?_, ?_⟩⟩
            · intro hzbad
              exact hznotA (Finset.mem_sdiff.mp hzbad).1
            · change z - 1 ∈ (cert.P 0 true).cells \ cert.O.cells
              exact Finset.mem_sdiff.mpr ⟨hzinA, hznotO⟩
          exact ⟨e, heF, heT⟩
  · have h := hcommon
    simpa [F, P4366T1PrecursorRemainderFamily, hdel] using h

end RemainderAttachmentGeometry

theorem P4366T1RemainderOuterAttachments :
    ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
        BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
        BandOrderedGeneralLayoutCertificate q cfg C T), (cert.O.cells.Nonempty) → ((LatticeTile
        cert.O) → ((∀ i, ∀ s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (cert.P i s) ∧
        e ∈ BoundaryFootprintEdges T) → (
    let F := P4366T1PrecursorRemainderFamily cert.P cert.O
    (∀ i, ∀ s, LatticeTile (F i s)) ∧
    (∀ z, z ∈ T.cells ∧ z ∉ cert.O.cells ↔
      ∃ i s, z ∈ (F i s).cells) ∧
    (∀ i, ∀ s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (F i s) ∧
        e ∈ BoundaryFootprintEdges T)))) := by
  intro C q cfg T cert hO hOdisk hattach
-- BODY
  classical
  dsimp only
  let F := P4366T1PrecursorRemainderFamily cert.P cert.O
  have zero_translation (U : ProtoTile) : TileTranslation U 0 = U :=
      RemainderAttachmentGeometry.zero_translation U
  have isolated {x a : GaussianInt}
      (hx : x ∈ FootprintVertices cert.O)
      (hxa : x = a ∨ x = a + 1 ∨ x = a + ⟨0, 1⟩ ∨
        x = a + 1 + ⟨0, 1⟩) : a ∈ T.cells := RemainderAttachmentGeometry.isolated C q cfg T cert
            zero_translation (x := x) (a := a) hx hxa
  have corner (z : GaussianInt)
      (hx : z ∈ cert.O.cells) (x : GaussianInt)
      (hxa : x = z ∨ x = z + 1 ∨ x = z + ⟨0, 1⟩ ∨
        x = z + 1 + ⟨0, 1⟩) : x ∈ FootprintVertices cert.O := RemainderAttachmentGeometry.corner
            C q cfg T cert z hx x hxa
  have hneighbors (z : GaussianInt) (hz : z ∈ cert.O.cells) :
      z - ⟨0, 1⟩ ∈ T.cells ∧ z + ⟨0, 1⟩ ∈ T.cells ∧
        z - 1 ∈ T.cells ∧ z + 1 ∈ T.cells := RemainderAttachmentGeometry.hneighbors C q cfg T
            cert isolated corner z hz
  have hOsubA : cert.O.cells ⊆ (cert.P 0 true).cells := RemainderAttachmentGeometry.hOsubA C q
      cfg T cert
  have hOsubB : cert.O.cells ⊆ (cert.P 0 false).cells := RemainderAttachmentGeometry.hOsubB C q
      cfg T cert
  have hpair := (P4339T1PrecursorSupportGeometry C q cfg T cert).2.2.2.2.2.2.1
  have hdisjoint := (P4339T1PrecursorSupportGeometry C q cfg T cert).2.2.2.2.2.2.2
  have hcover : ∀ z, z ∈ T.cells ∧ z ∉ cert.O.cells ↔
      ∃ i s, z ∈ (F i s).cells := RemainderAttachmentGeometry.hcover C q cfg T cert hOsubA hdisjoint
  have hLattice : ∀ i s, LatticeTile (F i s) := RemainderAttachmentGeometry.hLattice C q cfg T cert
  have horiz_unique (x y : GaussianInt)
      (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y :=
          RemainderAttachmentGeometry.horiz_unique x y h
  have vert_unique (x y : GaussianInt)
      (h : ({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) =
        {y, y + ⟨0, 1⟩}) : x = y := RemainderAttachmentGeometry.vert_unique x y h
  have horiz_ne_vert (x y : GaussianInt) :
      ({x, x + 1} : Finset GaussianInt) ≠ {y, y + (⟨0, 1⟩ : GaussianInt)} :=
          RemainderAttachmentGeometry.horiz_ne_vert x y
  have sharedEdge (A : ProtoTile)
      (hsub : A.cells ⊆ T.cells) (e : Finset GaussianInt)
      (heA : e ∈ BoundaryFootprintEdges A) (heT : e ∈ BoundaryFootprintEdges T) :
      (∃ z, e = {z, z + 1} ∧
        ((z ∈ A.cells ∧ z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨
          (z ∉ A.cells ∧ z - ⟨0, 1⟩ ∈ A.cells ∧
            z - ⟨0, 1⟩ ∈ T.cells ∧ z ∉ T.cells))) ∨
      (∃ z, e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ A.cells ∧ z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ A.cells ∧ z - 1 ∈ A.cells ∧ z - 1 ∈ T.cells ∧ z ∉ T.cells))) :=
              RemainderAttachmentGeometry.sharedEdge T horiz_unique vert_unique horiz_ne_vert A
              hsub e heA heT
  have outerAttach (i : Fin 3) (s : Bool)
      (hsub : (cert.P i s).cells ⊆ T.cells)
      (hcommon : ∃ e : Finset GaussianInt,
        e ∈ BoundaryFootprintEdges (cert.P i s) ∧ e ∈ BoundaryFootprintEdges T) :
      ∃ e : Finset GaussianInt,
        e ∈ BoundaryFootprintEdges (F i s) ∧ e ∈ BoundaryFootprintEdges T :=
            RemainderAttachmentGeometry.outerAttach C q cfg T cert hneighbors sharedEdge i s hsub
            hcommon
  refine ⟨hLattice, hcover, ?_⟩
  intro i s
  by_cases hi : i = 0
  · subst i
    cases s
    · exact outerAttach 0 false (by
        intro z hz
        exact (cert.outer_union z).mpr ⟨0, false, hz⟩) (hattach 0 false)
    · exact outerAttach 0 true (by
        intro z hz
        exact (cert.outer_union z).mpr ⟨0, true, hz⟩) (hattach 0 true)
  · exact outerAttach i s (by
      intro z hz
      exact (cert.outer_union z).mpr ⟨i, s, hz⟩) (hattach i s)

end ApollonianSuperharmonic

end
