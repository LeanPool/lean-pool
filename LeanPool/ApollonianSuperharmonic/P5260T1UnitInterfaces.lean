/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage
public import LeanPool.ApollonianSuperharmonic.P5290T1RawBoundaryInterfaces
public import LeanPool.ApollonianSuperharmonic.P5290T1EqualDiamondPaths
public import LeanPool.ApollonianSuperharmonic.P5290T1UnitContactPaths
public import LeanPool.ApollonianSuperharmonic.P5290T1PredecessorPath
public import LeanPool.ApollonianSuperharmonic.P5290T1ColumnReflection

-- [TABLET NODE: P5260T1UnitInterfaces]

/-!
# P5260T1UnitInterfaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5260T1UnitInterfaces (k : Nat) (hk : 0 < k)
    (i : Fin 3) (b : Bool) (hi : i ≠ 2)
    (hreg : 1 < k ∨ (i = 1 ∧ b = false) ∨ (i = 0 ∧ b = true)) :
    let M := P5260T1PlacementLedger k i b
    let D := DiamondTile k
    ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
      ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
        ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
          R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
          A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
          I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
          M.2.2.1 ≠ M.2.2.2 := by
-- BODY
  have raw (T U : ProtoTile) (a c : GaussianInt)
      (h : T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
        SimpleGridPathBetween
          (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
          (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a c) :
      SimpleGridPathBetween (FootprintVertices T ∩ FootprintVertices U)
        (FootprintEdges T ∩ FootprintEdges U) a c := by as_aux_lemma =>
    have eqs := P5290T1RawBoundaryInterfaces T U h.1 h.2.1 h.2.2.1
    simpa only [eqs.1, eqs.2] using h.2.2.2
  have even (i : Fin 3) (hi : i ≠ 2) (hreg : 1 < k ∨ i = 1) :
      let M := P5260T1PlacementLedger k i false
      let D := DiamondTile k
      ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
        ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
          ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
            R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
            A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
            I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
            M.2.2.1 ≠ M.2.2.2 := by as_aux_lemma =>
    let M := P5260T1PlacementLedger k i false
    let D := DiamondTile k
    let W := M.1.1
    let Z := M.1.2
    let Dr := TileTranslation D M.2.1.1
    let Dl := TileTranslation D M.2.1.2
    let x := M.2.2.1
    let y := M.2.2.2
    let d : GaussianInt := if i = 0 then ⟨0, 1⟩ else -1
    let eR : GaussianInt := if i = 0 then ⟨-(k : Int), (k : Int) + 1⟩ else 0
    let eI : GaussianInt := if i = 0 then ⟨(k : Int), (k : Int)⟩ else ⟨-1, 2 * (k : Int)⟩
    obtain ⟨long, vR, vI⟩ := P5290T1EqualDiamondPaths k hk i hi
    obtain ⟨short, vDW, vWZ, unitZD⟩ := P5290T1UnitContactPaths k hk i hi hreg
    have rAB := long D Dr x eR (by simp only [List.mem_cons]; exact Or.inl rfl)
    have iAB := long D Dl y eI (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
    have dwXY := short D W x y (by simp only [List.mem_cons]; exact Or.inl rfl)
    have dwYX := short D W y x (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
    have rBC := short Dr W x (x + d) (by
      simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
    have iBC := short Dl W y (y + d) (by
      simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have aBC := short W Z y (y + d) (by
      simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have vR' := (P5290T1RawBoundaryInterfaces D Dr rAB.1 rAB.2.1 rAB.2.2.1).1.trans vR
    have vI' := (P5290T1RawBoundaryInterfaces D Dl iAB.1 iAB.2.1 iAB.2.2.1).1.trans vI
    have vDW' : FootprintVertices D ∩ FootprintVertices W = {x, y} :=
      (P5290T1RawBoundaryInterfaces D W dwXY.1 dwXY.2.1 dwXY.2.2.1).1.trans vDW
    have vWZ' : FootprintVertices W ∩ FootprintVertices Z = {y, y + d} :=
      (P5290T1RawBoundaryInterfaces W Z aBC.1 aBC.2.1 aBC.2.2.1).1.trans vWZ
    have rEnds : x ∈ FootprintVertices D ∩ FootprintVertices Dr ∧
        y ∉ FootprintVertices D ∩ FootprintVertices Dr := by as_aux_lemma =>
      rw [vR']
      fin_cases i <;>
        simp [x, y, M, P5260T1PlacementLedger] at hi ⊢ <;> omega
    have iEnds : y ∈ FootprintVertices D ∩ FootprintVertices Dl ∧
        x ∉ FootprintVertices D ∩ FootprintVertices Dl := by as_aux_lemma =>
      rw [vI']
      fin_cases i <;>
        simp [x, y, M, P5260T1PlacementLedger] at hi ⊢ <;> omega
    have sep : x ≠ y ∧ x ≠ y + d := by as_aux_lemma =>
      fin_cases i <;>
        simp [x, y, d, M, P5260T1PlacementLedger, Zsqrtd.ext_iff] at hi ⊢
    have xDW : x ∈ FootprintVertices D ∩ FootprintVertices W := by rw [vDW']; simp
    have yDW : y ∈ FootprintVertices D ∩ FootprintVertices W := by rw [vDW']; simp
    have yWZ : y ∈ FootprintVertices W ∩ FootprintVertices Z := by rw [vWZ']; simp
    have uniqueR (z : GaussianInt) :
        z ∈ FootprintVertices D ∩ FootprintVertices Dr ∩ FootprintVertices W ↔ z = x :=
            by as_aux_lemma =>
      constructor
      · intro hz
        have hzDW : z ∈ ({x, y} : Set GaussianInt) := by
          rw [← vDW']; exact ⟨hz.1.1, hz.2⟩
        rcases (show z = x ∨ z = y from by simpa using hzDW) with h | h
        · exact h
        · subst z; exact (rEnds.2 hz.1).elim
      · rintro rfl
        exact ⟨rEnds.1, xDW.2⟩
    have uniqueI (z : GaussianInt) :
        z ∈ FootprintVertices D ∩ FootprintVertices Dl ∩ FootprintVertices W ↔ z = y :=
            by as_aux_lemma =>
      constructor
      · intro hz
        have hzDW : z ∈ ({x, y} : Set GaussianInt) := by
          rw [← vDW']; exact ⟨hz.1.1, hz.2⟩
        rcases (show z = x ∨ z = y from by simpa using hzDW) with h | h
        · subst z; exact (iEnds.2 hz.1).elim
        · exact h
      · rintro rfl
        exact ⟨iEnds.1, yDW.2⟩
    have uniqueA (z : GaussianInt) :
        z ∈ FootprintVertices D ∩ FootprintVertices W ∩ FootprintVertices Z ↔ z = y :=
            by as_aux_lemma =>
      constructor
      · intro hz
        have hzDW := hz.1
        rw [vDW'] at hzDW
        rcases (show z = x ∨ z = y from by simpa using hzDW) with h | h
        · subst z
          have hxWZ : x ∈ ({y, y + d} : Set GaussianInt) := by
            rw [← vWZ']; exact ⟨hz.1.2, hz.2⟩
          rcases (show x = y ∨ x = y + d from by simpa using hxWZ) with h | h
          · exact (sep.1 h).elim
          · exact (sep.2 h).elim
        · exact h
      · rintro rfl
        exact ⟨yDW, yWZ.2⟩
    obtain ⟨eA, aCA⟩ : ∃ eA, SimpleGridPathBetween
        (FootprintVertices Z ∩ FootprintVertices D)
        (FootprintEdges Z ∩ FootprintEdges D) y eA := by
      by_cases hi0 : i = 0
      · subst i
        have hbig : 1 < k := hreg.resolve_right (by decide)
        have h := P5290T1PredecessorPath k hbig
        refine ⟨⟨(k : Int), (k : Int) + 1⟩, ?_⟩
        simpa [Z, D, y, M, P5260T1PlacementLedger] using raw _ _ _ _ h
      · have hi1 : i = 1 := by omega
        exact ⟨y + ⟨0, 1⟩, raw Z D y _ (unitZD hi1)⟩
    let R : ExactTileInterfaceTriple D Dr W :=
      ⟨x, eR, x + d, y, raw _ _ _ _ rAB, raw _ _ _ _ rBC,
        by simpa only [Set.inter_comm] using raw _ _ _ _ dwXY, uniqueR⟩
    let I : ExactTileInterfaceTriple D Dl W :=
      ⟨y, eI, y + d, x, raw _ _ _ _ iAB, raw _ _ _ _ iBC,
        by simpa only [Set.inter_comm] using raw _ _ _ _ dwYX, uniqueI⟩
    let A : ExactTileInterfaceTriple D W Z :=
      ⟨y, x, y + d, eA, raw _ _ _ _ dwYX, raw _ _ _ _ aBC, aCA, uniqueA⟩
    exact ⟨R, I, A, rfl, rfl, rfl, rfl, rfl, rfl, sep.1⟩
  cases b with
  | false =>
      apply even i hi
      rcases hreg with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · cases h
  | true =>
      let j : Fin 3 := if i = 0 then 1 else 0
      have hj : j ≠ 2 := by dsimp [j]; split <;> decide
      have reg : 1 < k ∨ j = 1 := by
        fin_cases i
        · exact Or.inr rfl
        · exact Or.inl (hreg.resolve_right (by simp))
        · exact (hi rfl).elim
      have hji : (if j = 0 then (1 : Fin 3) else 0) = i := by
        fin_cases i
        · rfl
        · rfl
        · exact (hi rfl).elim
      let S := P5260T1PlacementLedger k j false
      let T := P5260T1PlacementLedger k i true
      let D := DiamondTile k
      let J := fun z : GaussianInt => (⟨z.re, 2 * (k : Int) - z.im⟩ : GaussianInt)
      have hf : Function.Injective J := by
        intro a c h
        have hr := congrArg Zsqrtd.re h
        have hc := congrArg Zsqrtd.im h
        apply Zsqrtd.ext <;> simp only [J] at hr hc ⊢ <;> omega
      have hs (a c : GaussianInt)
          (h : c = a + 1 ∨ c = a - 1 ∨ c = a + ⟨0, 1⟩ ∨ c = a - ⟨0, 1⟩) :
          J c = J a + 1 ∨ J c = J a - 1 ∨
            J c = J a + ⟨0, 1⟩ ∨ J c = J a - ⟨0, 1⟩ := by
        rcases h with rfl | rfl | rfl | rfl
        · exact Or.inl (by ext <;> simp [J])
        · exact Or.inr (Or.inl (by ext <;> simp [J]))
        · exact Or.inr (Or.inr (Or.inr (by ext <;> simp [J]; ring)))
        · exact Or.inr (Or.inr (Or.inl (by ext <;> simp [J]; ring)))
      obtain ⟨R, I, A, hRp, hIp, hAp, hRc, hIc, hAa, hxy⟩ := even j hj reg
      have images := P5290T1ColumnReflection k hk j hj reg
      dsimp only at images
      rw [hji] at images
      obtain ⟨maps, hx, hy⟩ := images
      have mD := maps D D (by simp [D])
      have mR := maps (TileTranslation D S.2.1.1) (TileTranslation D T.2.1.1)
        (by simp [D, S, T])
      have mI := maps (TileTranslation D S.2.1.2) (TileTranslation D T.2.1.2)
        (by simp [D, S, T])
      have mW := maps S.1.1 T.1.1 (by simp [S, T])
      have mZ := maps S.1.2 T.1.2 (by simp [S, T])
      obtain ⟨R', hRp', hRab', hRbc', hRc'⟩ := P4055T1ExactTripleImage J hf hs
        D (TileTranslation D S.2.1.1) S.1.1
        D (TileTranslation D T.2.1.1) T.1.1
        mD.1 mR.1 mW.1 mD.2 mR.2 mW.2 R
      obtain ⟨I', hIp', hIab', hIbc', hIc'⟩ := P4055T1ExactTripleImage J hf hs
        D (TileTranslation D S.2.1.2) S.1.1
        D (TileTranslation D T.2.1.2) T.1.1
        mD.1 mI.1 mW.1 mD.2 mI.2 mW.2 I
      obtain ⟨A', hAp', hAa', hAbc', hAc'⟩ := P4055T1ExactTripleImage J hf hs
        D S.1.1 S.1.2 D T.1.1 T.1.2
        mD.1 mW.1 mZ.1 mD.2 mW.2 mZ.2 A
      refine ⟨R', I', A', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hRp'.trans ((congrArg J hRp).trans hx)
      · exact hIp'.trans ((congrArg J hIp).trans hy)
      · exact hAp'.trans ((congrArg J hAp).trans hy)
      · exact hRc'.trans ((congrArg J hRc).trans hy)
      · exact hIc'.trans ((congrArg J hIc).trans hx)
      · exact hAa'.trans ((congrArg J hAa).trans hx)
      · intro h
        apply hxy
        exact hf (hx.trans (h.trans hy.symm))

end ApollonianSuperharmonic

end
