/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer

-- [TABLET NODE: P4458T1RespectAppend]

/-!
# P4458T1RespectAppend

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RespectAppendProof

private theorem dropLastForall₂ :
    ∀ {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
        (List.Forall₂ Rel xs ys) → (List.Forall₂ Rel xs.dropLast ys.dropLast) := by
  classical
  intro α β Rel xs ys hall
  induction hall with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
    cases htail with
    | nil => simp
    | cons hnext hrest =>
      simpa only [List.dropLast_cons_cons] using List.Forall₂.cons hxy ih

private theorem zipDropLast :
    ∀ {α : Type}, ∀ {β : Type}, ∀ (xs : List α), ∀ (ys : List β), (xs.length = ys.length) →
        (xs.dropLast.zip ys.dropLast = (xs.zip ys).dropLast) := by
  classical
  intro α β xs ys hlen
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases xs with
      | nil => cases ys <;> simp
      | cons x' xs =>
        cases ys with
        | nil => simp at hlen
        | cons y' ys =>
          have ht : (x' :: xs).length = (y' :: ys).length := by simpa using hlen
          simp only [List.dropLast_cons_cons, List.zip_cons_cons]
          congr 1
          exact ih (y' :: ys) ht

private theorem hrightZipShape :
    ∀ (C : BandCircle), ∀ (C₀ : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R :
        ProtoTile), ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (hJ :
        PartialOdometer), ∀ (hS : PartialOdometer), ∀ (h₀ : PartialOdometer), ∀ (left : List
        ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr : List
        PartialOdometer), (hr.head? = some hJ) → ((hr.getLast? = some hS) → ((TileString C
        orientation base R S (left.dropLast ++ right)) → ((∀ U ∈ (List.drop (1 : ℕ)
        right).dropLast, ∃ (g : PartialOdometer), (U, g) ∈ right.zip hr ∧ AncestorOdometer C.1.1
            C₀.1.1 U T₀ g h₀) → ((List.Forall₂ (fun (T : ProtoTile) (h : PartialOdometer)
        => TileOdometer C.1.1 T h) right hr) →
        ((List.IsChain (fun (X Y : ProtoTile × PartialOdometer) => LeftLatticeAdjacent C X.1 Y.1
        X.2 Y.2) (right.zip hr)) → ((right.length = hr.length) → ((right.head? = some J) →
        ((right.getLast? = some S) → ((List.Pairwise (fun (T U : ProtoTile) => T ≠ U) right) →
        ((∀ T ∈ right, T ∈ RegularTileFamily base (TilingLattice C)) → ((List.IsChain (fun (T U :
        ProtoTile) => if C.1.1.1 = (1 : ℤ) then ∃ (v :
        GaussianInt), UnitTriangularStep orientation v ∧ TileCentroid U - TileCentroid T =
        GaussianRealPoint v else TileTouching T U) right) → ((∀ (pre : List ProtoTile), ∀ (T :
            ProtoTile), ∀ (post : List ProtoTile), right = pre ++ T :: post → pre ≠ [] → post ≠ [] →
        (0 : ℝ) ≤ (fun (T : ProtoTile) => ((TileCentroid T).2 - (TileCentroid J).2) *
        ((TileCentroid S).1 - (TileCentroid J).1) - ((TileCentroid T).1 - (TileCentroid J).1) *
        ((TileCentroid S).2 - (TileCentroid J).2)) T ∧ ∃ U ∈ RegularTileFamily base
        (TilingLattice C), (fun (T U : ProtoTile) => if C.1.1.1 = (1 : ℤ) then ∃ (v :
            GaussianInt), UnitTriangularStep orientation v
        ∧ TileCentroid U - TileCentroid T = GaussianRealPoint v else TileTouching T U) T U ∧ (fun
        (T : ProtoTile) => ((TileCentroid T).2 - (TileCentroid J).2) * ((TileCentroid S).1 -
        (TileCentroid J).1) - ((TileCentroid T).1 - (TileCentroid J).1) * ((TileCentroid S).2 -
        (TileCentroid J).2)) U < (0 : ℝ)) → ((List.Forall₂ (fun T h => TileOdometer C.1.1 T h)
        (left.dropLast ++ right) (hl.dropLast ++ hr)) → (((left.dropLast ++ right).zip
        (hl.dropLast ++ hr) = (left.zip hl).dropLast ++ right.zip hr) → (right.zip hr = [(J, hJ)]
        ++ right.tail.zip hr.tail))))))))))))))) := by
  classical
  intro C C₀ orientation base R J S T₀ hJ hS h₀ left right hl hr hrhead hrlast hjoined hrightAnc
      hrightOdo hrightChain hrightLen hrightTileHead hrightTileLast hrightNodup hrightMem
      hrightTileChain hrightHeight hrel hzip
  cases right with
  | nil => simp at hrightTileHead
  | cons t ts =>
    cases hr with
    | nil => simp at hrhead
    | cons g gs =>
      simp only [List.head?_cons] at hrightTileHead hrhead
      injection hrightTileHead with ht
      injection hrhead with hg
      subst t
      subst g
      rfl

private theorem hUdropLast :
    ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (U : ProtoTile), (U ∈ (List.drop (1
        : ℕ) (left.dropLast ++ right)).dropLast) → (U ∈ (left.dropLast ++ right).dropLast) := by
  classical
  intro left right U hU
  have hsub : List.Sublist ((left.dropLast ++ right).drop 1).dropLast
      (left.dropLast ++ right).dropLast := by
    cases left.dropLast ++ right with
    | nil => simp
    | cons a xs =>
      cases xs with
      | nil => simp
      | cons b xs =>
        simp only [List.drop_succ_cons, List.dropLast_cons_cons]
        exact List.Sublist.cons _ (List.Sublist.refl _)
  exact hsub.subset hU

end RespectAppendProof

namespace RespectAppendDetails

private theorem appendForall₂ :
    ∀ {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β}, ∀
        {us : List α}, ∀ {vs : List β}, (List.Forall₂ Rel xs ys) → ((List.Forall₂ Rel us vs) →
        (List.Forall₂ Rel (xs ++ us) (ys ++ vs))) := by
  classical
  intro α β Rel xs ys us vs hxy huv
  induction hxy with
  | nil => simpa using huv
  | cons hxy htail ih => exact List.Forall₂.cons hxy ih

private theorem hzip :
    ∀ (C : BandCircle), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List
        PartialOdometer), ∀ (hr : List PartialOdometer), (List.Forall₂ (fun (T : ProtoTile) (h :
        PartialOdometer) => TileOdometer C.1.1 T h)
        left hl) → ((∀ {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀
        {ys : List β}, (List.Forall₂ Rel xs ys) → (List.Forall₂ Rel xs.dropLast ys.dropLast)) →
        ((∀ {α : Type}, ∀ {β : Type}, ∀ (xs : List α), ∀ (ys : List β), (xs.length = ys.length) →
        (xs.dropLast.zip ys.dropLast = (xs.zip ys).dropLast)) → ((left.length = hl.length) →
        ((left.dropLast ++ right).zip (hl.dropLast ++ hr) =
      (left.zip hl).dropLast ++ right.zip hr)))) := by
  classical
  intro C left right hl hr hleftOdo dropLastForall₂ zipDropLast hleftLen
  rw [List.zip_append]
  · rw [zipDropLast left hl hleftLen]
  · exact List.Forall₂.length_eq (dropLastForall₂ hleftOdo)

private theorem hleftTailChain :
    ∀ (C : BandCircle), ∀ (left : List ProtoTile), ∀ (hl : List PartialOdometer), (List.IsChain
        (fun (X Y : ProtoTile × PartialOdometer) => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
        (left.zip hl)) → ((left.zip hl).dropLast.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)) := by
  classical
  intro C left hl hleftChain
  exact hleftChain.dropLast

private theorem hleftZipShape :
    ∀ (C : BandCircle), ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀
        (hl : List PartialOdometer), (List.Forall₂ (fun (T : ProtoTile) (h : PartialOdometer) =>
        TileOdometer C.1.1 T h) left hl) → ((∀
        {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
        (List.Forall₂ Rel xs ys) → (List.Forall₂ Rel xs.dropLast ys.dropLast)) → ((left.dropLast
        ++ [J] = left) → ((hl.dropLast ++ [hJ] = hl) → (left.zip hl = left.dropLast.zip
        hl.dropLast ++ [(J, hJ)])))) := by
  classical
  intro C J hJ left hl hleftOdo dropLastForall₂ hleftList hleftFunList
  rw [← hleftList, ← hleftFunList, List.zip_append]
  · simp
  · exact List.Forall₂.length_eq (dropLastForall₂ hleftOdo)

private theorem hleftChainShape :
    ∀ (C : BandCircle), ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀
        (hl : List PartialOdometer), (List.IsChain (fun (X Y : ProtoTile × PartialOdometer) =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (left.zip hl)) → ((left.zip hl = left.dropLast.zip
        hl.dropLast ++ [(J, hJ)]) → (List.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
      (left.dropLast.zip hl.dropLast ++ [(J, hJ)]))) := by
  classical
  intro C J hJ left hl hleftChain hleftZipShape
  rw [← hleftZipShape]
  exact hleftChain

private theorem hrightChainShape :
    ∀ (C : BandCircle), ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (right : List ProtoTile),
        ∀ (hr : List PartialOdometer), (List.IsChain (fun (X Y : ProtoTile × PartialOdometer) =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (right.zip hr)) → ((right.zip hr = [(J, hJ)] ++
        right.tail.zip hr.tail) → (List.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
      ([(J, hJ)] ++ right.tail.zip hr.tail))) := by
  classical
  intro C J hJ right hr hrightChain hrightZipShape
  rw [← hrightZipShape]
  exact hrightChain

private theorem hnewChain :
    ∀ (C : BandCircle), ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀
        (right : List ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr : List PartialOdometer),
        (left.zip hl = left.dropLast.zip hl.dropLast ++ [(J, hJ)]) → ((right.zip hr = [(J, hJ)]
        ++ right.tail.zip hr.tail) → ((List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2
        Y.2) (left.dropLast.zip hl.dropLast ++ [(J, hJ)])) → ((List.IsChain (fun X Y =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) ([(J, hJ)] ++ right.tail.zip hr.tail)) →
        (((left.zip hl).dropLast ++ right.zip hr).IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2))))) := by
  classical
  intro C J hJ left right hl hr hleftZipShape hrightZipShape hleftChainShape hrightChainShape
  rw [hleftZipShape, hrightZipShape, List.dropLast_append, List.dropLast_singleton]
  simpa [List.append_assoc] using
    hleftChainShape.append_overlap hrightChainShape
      (show [(J, hJ)] ≠ [] by simp)

private theorem hleftZipDrop :
    ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀ (hl : List
        PartialOdometer), (left.zip hl = left.dropLast.zip hl.dropLast ++ [(J, hJ)]) → ((left.zip
        hl).dropLast = left.dropLast.zip hl.dropLast) := by
  classical
  intro J hJ left hl hleftZipShape
  rw [hleftZipShape]
  simp

private theorem hJmem :
    ∀ (C : BandCircle), ∀ (C₀ : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R :
        ProtoTile), ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (hJ :
        PartialOdometer), ∀ (h₀ : PartialOdometer), ∀ (left : List ProtoTile), ∀ (right : List
        ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr : List PartialOdometer), (∀ U ∈
        (List.drop (1 : ℕ) right).dropLast, ∃ (g : PartialOdometer), (U, g) ∈ right.zip hr ∧
        AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀) → ((List.Forall₂ (fun (T : ProtoTile)
        (h : PartialOdometer) => TileOdometer C.1.1 T
        h) right hr) → ((List.IsChain (fun (X Y : ProtoTile × PartialOdometer) =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (right.zip hr)) → ((right.length = hr.length) →
        ((right.head? = some J) → ((right.getLast? = some S) → ((List.Pairwise (fun (T U :
        ProtoTile) => T ≠ U) right) → ((∀ T ∈ right, T ∈ RegularTileFamily base (TilingLattice
        C)) → ((List.IsChain (fun (T U : ProtoTile) => if C.1.1.1 = (1 : ℤ) then ∃ (v :
            GaussianInt), UnitTriangularStep orientation v
        ∧ TileCentroid U - TileCentroid T = GaussianRealPoint v else TileTouching T U) right) →
        ((∀ (pre : List ProtoTile), ∀ (T : ProtoTile), ∀ (post : List ProtoTile), right = pre ++
        T :: post → pre ≠ [] → post ≠ [] → (0 : ℝ) ≤ (fun (T : ProtoTile) => ((TileCentroid T).2
        - (TileCentroid J).2) * ((TileCentroid S).1 - (TileCentroid J).1) - ((TileCentroid T).1 -
        (TileCentroid J).1) * ((TileCentroid S).2 - (TileCentroid J).2)) T ∧ ∃ U ∈
        RegularTileFamily base (TilingLattice C), (fun (T U : ProtoTile) => if C.1.1.1 = (1 : ℤ)
            then ∃ (v : GaussianInt),
        UnitTriangularStep orientation v ∧ TileCentroid U - TileCentroid T = GaussianRealPoint v
        else TileTouching T U) T U ∧ (fun (T : ProtoTile) => ((TileCentroid T).2 - (TileCentroid
        J).2) * ((TileCentroid S).1 - (TileCentroid J).1) - ((TileCentroid T).1 - (TileCentroid
        J).1) * ((TileCentroid S).2 - (TileCentroid J).2)) U < (0 : ℝ)) → ((List.Forall₂ (fun T h
        => TileOdometer C.1.1 T h) (left.dropLast ++ right) (hl.dropLast ++ hr)) →
        (((left.dropLast ++ right).zip (hl.dropLast ++ hr) = (left.zip hl).dropLast ++ right.zip
        hr) → ((right.zip hr = [(J, hJ)] ++ right.tail.zip hr.tail) → ((List.IsChain (fun X Y =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) ([(J, hJ)] ++ right.tail.zip hr.tail)) →
        ((((left.zip hl).dropLast ++ right.zip hr).IsChain (fun X Y => LeftLatticeAdjacent C X.1
        Y.1 X.2 Y.2)) → ((TileString C orientation base R S (left.dropLast ++ right)) →
        (((left.dropLast ++ right).head? = some R) → (((left.dropLast ++ right).getLast? = some
        S) → ((List.Pairwise (fun (T U : ProtoTile) => T ≠ U) (left.dropLast ++ right)) →
        ((List.Nodup (left.dropLast ++ right)) → ((List.Disjoint left.dropLast right) → (J ∈
        right))))))))))))))))))))) := by
  classical
  intro C C₀ orientation base R J S T₀ hJ h₀ left right hl hr hrightAnc hrightOdo hrightChain
      hrightLen hrightTileHead hrightTileLast hrightNodup hrightMem hrightTileChain hrightHeight
      hrel hzip hrightZipShape hrightChainShape hnewChain hjoinedKeep hcatHead hcatLast
      hcatPairwise hcatNodup hdisj
  cases right with
  | nil => simp at hrightTileHead
  | cons t ts =>
    simp only [List.head?_cons] at hrightTileHead
    injection hrightTileHead with ht
    subst t
    simp

private theorem leftPairDrop :
    ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀ (hl : List
        PartialOdometer), (left.zip hl = left.dropLast.zip hl.dropLast ++ [(J, hJ)]) → (∀
        {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈ left.zip hl) → ((U ≠ J) → ((U, g) ∈
        left.dropLast.zip hl.dropLast))) := by
  classical
  intro J hJ left hl hleftZipShape U g hpair hUJ
  rw [hleftZipShape] at hpair
  simp only [List.mem_append, List.mem_singleton] at hpair
  rcases hpair with hpair | heq
  · exact hpair
  · have hEq : U = J := congrArg Prod.fst heq
    exact (hUJ hEq).elim

private theorem leftPairTransfer :
    ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr :
        List PartialOdometer), ((left.dropLast ++ right).zip (hl.dropLast ++ hr) = (left.zip
        hl).dropLast ++ right.zip hr) → (((left.zip hl).dropLast = left.dropLast.zip hl.dropLast)
        → (∀ {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈ left.dropLast.zip hl.dropLast) →
        ((U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr)))) := by
  classical
  intro left right hl hr hzip hleftZipDrop U g hpair
  rw [hzip, hleftZipDrop]
  exact List.mem_append.mpr (Or.inl hpair)

private theorem rightPairTransfer :
    ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr :
        List PartialOdometer), ((left.dropLast ++ right).zip (hl.dropLast ++ hr) = (left.zip
        hl).dropLast ++ right.zip hr) → (∀ {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈
        right.zip hr) → ((U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr))) := by
  classical
  intro left right hl hr hzip U g hpair
  rw [hzip]
  exact List.mem_append.mpr (Or.inr hpair)

private theorem hrespect :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
        ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List
        PartialOdometer), ∀ (hr : List PartialOdometer), (List.Forall₂ (fun T h => TileOdometer
        C.1.1 T h) (left.dropLast ++ right) (hl.dropLast ++ hr)) → (((left.dropLast ++ right).zip
        (hl.dropLast ++ hr) = (left.zip hl).dropLast ++ right.zip hr) → ((((left.zip hl).dropLast
        ++ right.zip hr).IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)) →
        ((TileString C orientation base R S (left.dropLast ++ right)) → (OdometerStringRespect C
        orientation base R S
      (left.dropLast ++ right) (hl.dropLast ++ hr))))) := by
  classical
  intro C orientation base R S left right hl hr hrel hzip hnewChain hjoinedKeep
  exact ⟨hjoinedKeep, hrel, by rw [hzip]; exact hnewChain⟩

private theorem hhead :
    ∀ (C : BandCircle), ∀ (C₀ : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R :
        ProtoTile), ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (hR :
        PartialOdometer), ∀ (hJ : PartialOdometer), ∀ (h₀ : PartialOdometer), ∀ (left : List
        ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr : List
        PartialOdometer), (hl.head? = some hR) → ((hl.getLast? = some hJ) → ((hr.head? = some hJ)
        → ((∀ U ∈ (List.drop (1 : ℕ) left).dropLast, ∃ (g : PartialOdometer), (U, g) ∈ left.zip
        hl ∧ AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀) → ((List.Forall₂ (fun (T : ProtoTile)
        (h : PartialOdometer) => TileOdometer C.1.1 T
        h) left hl) → ((List.IsChain (fun (X Y : ProtoTile × PartialOdometer) =>
        LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (left.zip hl)) → ((left.length = hl.length) →
        ((List.Forall₂ (fun T h => TileOdometer C.1.1 T h) (left.dropLast ++ right) (hl.dropLast
        ++ hr)) → (((left.dropLast ++ right).zip (hl.dropLast ++ hr) = (left.zip hl).dropLast ++
        right.zip hr) → (((left.zip hl).dropLast.IsChain (fun X Y => LeftLatticeAdjacent C X.1
        Y.1 X.2 Y.2)) → ((hl.dropLast ++ [hJ] = hl) → ((left.zip hl = left.dropLast.zip
        hl.dropLast ++ [(J, hJ)]) → ((List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2
        Y.2) (left.dropLast.zip hl.dropLast ++ [(J, hJ)])) → ((((left.zip hl).dropLast ++
        right.zip hr).IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)) → (((left.zip
        hl).dropLast = left.dropLast.zip hl.dropLast) → ((∀ {U : ProtoTile}, ∀
        {g : PartialOdometer}, ((U, g) ∈ left.zip hl) → ((U ≠ J) → ((U, g) ∈ left.dropLast.zip
        hl.dropLast))) → ((∀ {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈
        left.dropLast.zip hl.dropLast) → ((U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++
        hr))) → ((∀ {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈ right.zip hr) → ((U, g) ∈
        (left.dropLast ++ right).zip (hl.dropLast ++ hr))) → ((OdometerStringRespect C
        orientation base R S (left.dropLast ++ right) (hl.dropLast ++ hr)) → ((hl.dropLast ++
        hr).head? = some hR))))))))))))))))))) := by
  classical
  intro C C₀ orientation base R J S T₀ hR hJ h₀ left right hl hr hlhead hllast hrhead hleftAnc
      hleftOdo hleftChain hleftLen hrel hzip hleftTailChain hleftFunList hleftZipShape
      hleftChainShape hnewChain hleftZipDrop leftPairDrop leftPairTransfer rightPairTransfer
      hrespect
  cases hl with
  | nil => simp at hlhead
  | cons x xs => cases xs <;> simp_all

private theorem hlast :
    ∀ (C : BandCircle), ∀ (C₀ : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R :
        ProtoTile), ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (hR :
        PartialOdometer), ∀ (hJ : PartialOdometer), ∀ (hS : PartialOdometer), ∀ (h₀ :
        PartialOdometer), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (hl : List
        PartialOdometer), ∀ (hr : List PartialOdometer), (hr.head? = some hJ) → ((hr.getLast? =
        some hS) → ((∀ U ∈ (List.drop (1 : ℕ) right).dropLast, ∃ (g : PartialOdometer), (U, g) ∈
        right.zip hr ∧ AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀) → ((List.Forall₂ (fun (T :
        ProtoTile) (h : PartialOdometer) => TileOdometer C.1.1 T h) right hr) → ((List.IsChain
            (fun (X Y : ProtoTile ×
        PartialOdometer) => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (right.zip hr)) →
        ((right.length = hr.length) → ((List.Forall₂ (fun T h => TileOdometer C.1.1 T h)
        (left.dropLast ++ right) (hl.dropLast ++ hr)) → (((left.dropLast ++ right).zip
        (hl.dropLast ++ hr) = (left.zip hl).dropLast ++ right.zip hr) → ((right.zip hr = [(J,
        hJ)] ++ right.tail.zip hr.tail) → ((List.IsChain (fun X Y => LeftLatticeAdjacent C X.1
        Y.1 X.2 Y.2) ([(J, hJ)] ++ right.tail.zip hr.tail)) → ((((left.zip hl).dropLast ++
        right.zip hr).IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)) → ((∀
        {U : ProtoTile}, ∀ {g : PartialOdometer}, ((U, g) ∈ left.dropLast.zip hl.dropLast) → ((U,
        g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr))) → ((∀ {U : ProtoTile}, ∀
        {g : PartialOdometer}, ((U, g) ∈ right.zip hr) → ((U, g) ∈ (left.dropLast ++ right).zip
        (hl.dropLast ++ hr))) → ((OdometerStringRespect C orientation base R S (left.dropLast ++
        right) (hl.dropLast ++ hr)) → (((hl.dropLast ++ hr).head? = some hR) → ((hl.dropLast ++
        hr).getLast? = some hS))))))))))))))) := by
  classical
  intro C C₀ orientation base R J S T₀ hR hJ hS h₀ left right hl hr hrhead hrlast hrightAnc
      hrightOdo hrightChain hrightLen hrel hzip hrightZipShape hrightChainShape hnewChain
      leftPairTransfer rightPairTransfer hrespect hhead
  have hne : hr ≠ [] := by
    intro he; simp [he] at hrlast
  cases hr with
  | nil => contradiction
  | cons x xs => simpa using hrlast

private theorem hcatNe :
    ∀ (R : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ((left.dropLast ++
        right).head? = some R) → (left.dropLast ++ right ≠ []) := by
  classical
  intro R left right hcatHead he
  simp [he] at hcatHead

private theorem hcatGetLast :
    ∀ (S : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ((left.dropLast ++
        right).getLast? = some S) → (∀ (hcatNe : left.dropLast ++ right ≠ []), (left.dropLast ++
        right).getLast hcatNe = S) := by
  classical
  intro S left right hcatLast hcatNe
  have hopt := hcatLast
  rw [List.getLast?_eq_getLast_of_ne_nil hcatNe] at hopt
  exact Option.some.inj hopt

private theorem hUneS :
    ∀ (S : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), (List.Pairwise (fun
        (T U : ProtoTile) => T ≠ U) (left.dropLast ++ right)) → (∀ (U : ProtoTile), (U ∈
        (left.dropLast ++ right).dropLast) → (∀ (hcatNe : left.dropLast ++ right ≠ []),
        ((left.dropLast ++ right).getLast hcatNe = S) → (U ≠ S))) := by
  classical
  intro S left right hcatPairwise U hUdropLast hcatNe hcatGetLast
  have hne := hcatPairwise.rel_dropLast_getLast hUdropLast
  simpa [hcatGetLast] using hne

private theorem hshape :
    ∀ (R : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ((left.dropLast ++
        right).head? = some R) → (left.dropLast ++ right = R :: (left.dropLast ++ right).tail) := by
  classical
  intro R left right hcatHead
  cases hcat : left.dropLast ++ right with
  | nil => simp [hcat] at hcatHead
  | cons a xs =>
    have ha : a = R := by simpa [hcat] using hcatHead
    subst a
    simp []

private theorem hUtail :
    ∀ (R : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (U : ProtoTile),
        (U ∈ (left.dropLast ++ right).drop 1) → ((left.dropLast ++ right = R :: (left.dropLast ++
        right).tail) → (U ∈ (left.dropLast ++ right).tail)) := by
  classical
  intro R left right U hUstart hshape
  rw [hshape] at hUstart
  simpa using hUstart

private theorem hUneR :
    ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile),
        (List.Pairwise (fun (T U : ProtoTile) => T ≠ U) (left.dropLast ++ right)) → (∀ (U :
        ProtoTile), (U ∈ (List.drop (1 : ℕ) (left.dropLast ++ right)).dropLast) → ((U ∈
        (left.dropLast ++ right).drop 1) → ((U ∈ left.dropLast ++ right) → ((U ∈ (left.dropLast
        ++ right).dropLast) → ((U ≠ S) → ((left.dropLast ++ right = R :: (left.dropLast ++
        right).tail) → ((U ∈ (left.dropLast ++ right).tail) → (U ≠ R)))))))) := by
  classical
  intro R S left right hcatPairwise U hU hUstart hUall hUdropLast hUneS hshape hUtail he
  subst U
  have hnot : R ∉ (left.dropLast ++ right).tail := by
    rw [hshape] at hcatPairwise
    have hfirst := (List.pairwise_cons.mp hcatPairwise).1
    exact fun hm => (hfirst R hm) rfl
  exact hnot hUtail

private theorem hUneJ :
    ∀ (J : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), (List.Disjoint
        left.dropLast right) → ((J ∈ right) → (∀ (U : ProtoTile), (U ∈ left.dropLast) → (U ≠ J)))
        := by
  classical
  intro J left right hdisj hJmem U hUL he
  have hJleft : J ∈ left.dropLast := by simpa [he] using hUL
  exact (List.disjoint_left.mp hdisj) hJleft hJmem

private theorem hUintAt389 :
    ∀ (R : ProtoTile), ∀ (U : ProtoTile), (U ≠ R) → (∀ (b : ProtoTile), ∀ (bs : List ProtoTile),
        (U ∈ (R :: b :: bs).dropLast) → (U ∈ (b :: bs).dropLast)) := by
  classical
  intro R U hUneR b bs hUL
  simp only [List.dropLast_cons_cons, List.mem_cons] at hUL
  rcases hUL with hEq | hmem
  · exact (hUneR hEq).elim
  · exact hmem

private theorem hpairRight :
    ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (right : List ProtoTile), ∀ (hr : List
        PartialOdometer), (right.zip hr = [(J, hJ)] ++ right.tail.zip hr.tail) → ((J, hJ) ∈
        right.zip hr) := by
  classical
  intro J hJ right hr hrightZipShape
  rw [hrightZipShape]
  simp

private theorem hpairNewAt405 :
    ∀ (J : ProtoTile), ∀ (hJ : PartialOdometer), ∀ (left : List ProtoTile), ∀ (right : List
        ProtoTile), ∀ (hl : List PartialOdometer), ∀ (hr : List PartialOdometer), ((left.dropLast
        ++ right).zip (hl.dropLast ++ hr) = (left.zip hl).dropLast ++ right.zip hr) → (((J, hJ) ∈
        right.zip hr) → ((J, hJ) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr))) := by
  classical
  intro J hJ left right hl hr hzip hpairRight
  rw [hzip]
  exact List.mem_append.mpr (Or.inr hpairRight)

private theorem hUintAt414 :
    ∀ (J : ProtoTile), ∀ (U : ProtoTile), (¬U = J) → (∀ (as : List ProtoTile), (U ∈ J :: as) → (U
        ∈ as)) := by
  classical
  intro J U hUJ as hUR
  simpa using (List.mem_cons.mp hUR).resolve_left (by
    intro hEq
    exact hUJ hEq)

private theorem hrightGetLast :
    ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (as : List ProtoTile), ((J ::
        as).getLast? = some S) → ((J :: as).getLast (by simp) = S) := by
  classical
  intro J S as hrightTileLast
  have hopt := hrightTileLast
  rw [List.getLast?_eq_getLast_of_ne_nil (by simp)] at hopt
  exact Option.some.inj hopt

private theorem hrightDrop :
    ∀ (J : ProtoTile), ∀ (S : ProtoTile), ∀ (U : ProtoTile), (U ≠ S) → (∀ (as : List
        ProtoTile), (U ∈ J :: as) → (((J :: as).getLast (by simp) = S) → (U ∈ (J ::
        as).dropLast))) := by
  classical
  intro J S U hUneS as hUR hrightGetLast
  exact List.mem_dropLast_of_mem_of_ne_getLast hUR (by
    simpa [hrightGetLast] using hUneS)

private theorem hrightTailDrop :
    ∀ (J : ProtoTile), ∀ (U : ProtoTile), (¬U = J) → (∀ (b : ProtoTile), ∀ (bs : List ProtoTile),
        (U ∈ (J :: b :: bs).dropLast) → (U ∈ (b :: bs).dropLast)) := by
  classical
  intro J U hUJ b bs hrightDrop
  simp only [List.dropLast_cons_cons, List.mem_cons] at hrightDrop
  rcases hrightDrop with hEq | hmem
  · exact (hUJ hEq).elim
  · exact hmem

end RespectAppendDetails

theorem P4458T1RespectAppend
    (C C₀ : BandCircle) (orientation : Bool)
    (base R J S T₀ : ProtoTile) (hR hJ hS h₀ : PartialOdometer)
    (left right : List ProtoTile) (hl hr : List PartialOdometer)
    (hleft : OdometerStringRespect C orientation base R J left hl)
    (hright : OdometerStringRespect C orientation base J S right hr)
    (hlhead : hl.head? = some hR) (hllast : hl.getLast? = some hJ)
    (hrhead : hr.head? = some hJ) (hrlast : hr.getLast? = some hS)
    (hjoined : TileString C orientation base R S (left.dropLast ++ right))
    (hjoin : AncestorOdometer C.1.1 C₀.1.1 J T₀ hJ h₀)
    (hleftAnc : ∀ U ∈ (left.drop 1).dropLast,
      ∃ g, (U, g) ∈ left.zip hl ∧ AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀)
    (hrightAnc : ∀ U ∈ (right.drop 1).dropLast,
      ∃ g, (U, g) ∈ right.zip hr ∧ AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀) :
    (hl.dropLast ++ hr).head? = some hR ∧
    (hl.dropLast ++ hr).getLast? = some hS ∧
    OdometerStringRespect C orientation base R S
      (left.dropLast ++ right) (hl.dropLast ++ hr) ∧
    ∀ U ∈ ((left.dropLast ++ right).drop 1).dropLast,
      ∃ g, (U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr) ∧
        AncestorOdometer C.1.1 C₀.1.1 U T₀ g h₀ := by
-- BODY
  classical
  rcases hleft with ⟨hleftTiles, hleftOdo, hleftChain⟩
  rcases hright with ⟨hrightTiles, hrightOdo, hrightChain⟩
  have dropLastForall₂ {α β : Type} {Rel : α → β → Prop}
      {xs : List α} {ys : List β} (hall : List.Forall₂ Rel xs ys) :
      List.Forall₂ Rel xs.dropLast ys.dropLast := RespectAppendProof.dropLastForall₂ (α := α) (β
          := β) (Rel := Rel) (xs := xs) (ys := ys) hall
  have appendForall₂ {α β : Type} {Rel : α → β → Prop}
      {xs : List α} {ys : List β} {us : List α} {vs : List β}
      (hxy : List.Forall₂ Rel xs ys) (huv : List.Forall₂ Rel us vs) :
      List.Forall₂ Rel (xs ++ us) (ys ++ vs) := RespectAppendDetails.appendForall₂ (α := α) (β :=
          β) (Rel := Rel) (xs := xs) (ys := ys) (us := us) (vs := vs) hxy huv
  have zipDropLast {α β : Type} (xs : List α) (ys : List β)
      (hlen : xs.length = ys.length) :
      xs.dropLast.zip ys.dropLast = (xs.zip ys).dropLast := RespectAppendProof.zipDropLast (α :=
          α) (β := β) xs ys hlen
  have hleftLen : left.length = hl.length := List.Forall₂.length_eq hleftOdo
  have hrightLen : right.length = hr.length := List.Forall₂.length_eq hrightOdo
  rcases hleftTiles with ⟨_, hleftTileHead, hleftTileLast, hleftNodup, hleftMem,
    hleftTileChain, hleftHeight⟩
  rcases hrightTiles with ⟨_, hrightTileHead, hrightTileLast, hrightNodup, hrightMem,
    hrightTileChain, hrightHeight⟩
  have hrel : List.Forall₂ (fun T h => TileOdometer C.1.1 T h)
      (left.dropLast ++ right) (hl.dropLast ++ hr) :=
    appendForall₂ (dropLastForall₂ hleftOdo) hrightOdo
  have hzip : (left.dropLast ++ right).zip (hl.dropLast ++ hr) =
      (left.zip hl).dropLast ++ right.zip hr := RespectAppendDetails.hzip C left right hl hr
          hleftOdo dropLastForall₂ zipDropLast hleftLen
  have hleftTailChain : (left.zip hl).dropLast.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) := RespectAppendDetails.hleftTailChain C
          left hl hleftChain
  have hleftList : left.dropLast ++ [J] = left :=
    List.dropLast_append_getLast? J (by simp [hleftTileLast])
  have hleftFunList : hl.dropLast ++ [hJ] = hl :=
    List.dropLast_append_getLast? hJ (by simp [hllast])
  have hleftZipShape : left.zip hl = left.dropLast.zip hl.dropLast ++ [(J, hJ)] :=
      RespectAppendDetails.hleftZipShape C J hJ left hl hleftOdo dropLastForall₂ hleftList
      hleftFunList
  have hrightZipShape : right.zip hr = [(J, hJ)] ++ right.tail.zip hr.tail :=
      RespectAppendProof.hrightZipShape C C₀ orientation base R J S T₀ hJ hS h₀ left right hl hr
      hrhead hrlast hjoined hrightAnc hrightOdo hrightChain hrightLen hrightTileHead
      hrightTileLast hrightNodup hrightMem hrightTileChain hrightHeight hrel hzip
  have hleftChainShape : List.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
      (left.dropLast.zip hl.dropLast ++ [(J, hJ)]) := RespectAppendDetails.hleftChainShape C J hJ
          left hl hleftChain hleftZipShape
  have hrightChainShape : List.IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
      ([(J, hJ)] ++ right.tail.zip hr.tail) := RespectAppendDetails.hrightChainShape C J hJ right
          hr hrightChain hrightZipShape
  have hnewChain : ((left.zip hl).dropLast ++ right.zip hr).IsChain
      (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) := RespectAppendDetails.hnewChain C J hJ
          left right hl hr hleftZipShape hrightZipShape hleftChainShape hrightChainShape
  have hleftZipDrop : (left.zip hl).dropLast = left.dropLast.zip hl.dropLast :=
      RespectAppendDetails.hleftZipDrop J hJ left hl hleftZipShape
  have hjoinedKeep := hjoined
  rcases hjoined with ⟨_, hcatHead, hcatLast, hcatPairwise, _, _, _⟩
  have hcatNodup : List.Nodup (left.dropLast ++ right) := hcatPairwise
  have hdisj : List.Disjoint left.dropLast right :=
    List.disjoint_of_nodup_append hcatNodup
  have hJmem : J ∈ right := RespectAppendDetails.hJmem C C₀ orientation base R J S T₀ hJ h₀ left
      right hl hr hrightAnc hrightOdo hrightChain hrightLen hrightTileHead hrightTileLast
      hrightNodup hrightMem hrightTileChain hrightHeight hrel hzip hrightZipShape
      hrightChainShape hnewChain hjoinedKeep hcatHead hcatLast hcatPairwise hcatNodup hdisj
  have leftPairDrop {U : ProtoTile} {g : PartialOdometer}
      (hpair : (U, g) ∈ left.zip hl) (hUJ : U ≠ J) :
      (U, g) ∈ left.dropLast.zip hl.dropLast := RespectAppendDetails.leftPairDrop J hJ left hl
          hleftZipShape (U := U) (g := g) hpair hUJ
  have leftPairTransfer {U : ProtoTile} {g : PartialOdometer}
      (hpair : (U, g) ∈ left.dropLast.zip hl.dropLast) :
      (U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr) :=
          RespectAppendDetails.leftPairTransfer left right hl hr hzip hleftZipDrop (U := U) (g :=
          g) hpair
  have rightPairTransfer {U : ProtoTile} {g : PartialOdometer}
      (hpair : (U, g) ∈ right.zip hr) :
      (U, g) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr) :=
          RespectAppendDetails.rightPairTransfer left right hl hr hzip (U := U) (g := g) hpair
  have hrespect : OdometerStringRespect C orientation base R S
      (left.dropLast ++ right) (hl.dropLast ++ hr) := RespectAppendDetails.hrespect C orientation
          base R S left right hl hr hrel hzip hnewChain hjoinedKeep
  have hhead : (hl.dropLast ++ hr).head? = some hR := RespectAppendDetails.hhead C C₀ orientation
      base R J S T₀ hR hJ h₀ left right hl hr hlhead hllast hrhead hleftAnc hleftOdo hleftChain
      hleftLen hrel hzip hleftTailChain hleftFunList hleftZipShape hleftChainShape hnewChain
      hleftZipDrop leftPairDrop leftPairTransfer rightPairTransfer hrespect
  have hlast : (hl.dropLast ++ hr).getLast? = some hS := RespectAppendDetails.hlast C C₀
      orientation base R J S T₀ hR hJ hS h₀ left right hl hr hrhead hrlast hrightAnc hrightOdo
      hrightChain hrightLen hrel hzip hrightZipShape hrightChainShape hnewChain leftPairTransfer
      rightPairTransfer hrespect hhead
  refine ⟨hhead, hlast, hrespect, ?_⟩
  intro U hU
  have hUstart : U ∈ (left.dropLast ++ right).drop 1 :=
    List.mem_of_mem_dropLast hU
  have hUall : U ∈ left.dropLast ++ right := List.mem_of_mem_drop hUstart
  have hUdropLast : U ∈ (left.dropLast ++ right).dropLast := RespectAppendProof.hUdropLast left
      right U hU
  have hcatNe : left.dropLast ++ right ≠ [] := RespectAppendDetails.hcatNe R left right hcatHead
  have hcatGetLast : (left.dropLast ++ right).getLast hcatNe = S :=
      RespectAppendDetails.hcatGetLast S left right hcatLast hcatNe
  have hUneS : U ≠ S := RespectAppendDetails.hUneS S left right hcatPairwise U hUdropLast hcatNe
      hcatGetLast
  have hshape : left.dropLast ++ right = R :: (left.dropLast ++ right).tail :=
      RespectAppendDetails.hshape R left right hcatHead
  have hUtail : U ∈ (left.dropLast ++ right).tail := RespectAppendDetails.hUtail R left right U
      hUstart hshape
  have hUneR : U ≠ R := RespectAppendDetails.hUneR R S left right hcatPairwise U hU hUstart hUall
      hUdropLast hUneS hshape hUtail
  rcases List.mem_append.mp hUall with hUL | hUR
  · have hUneJ : U ≠ J := RespectAppendDetails.hUneJ J left right hdisj hJmem U hUL
    cases left with
    | nil => simp at hleftTileHead
    | cons a as =>
      have ha : a = R := by simpa using hleftTileHead
      subst a
      cases as with
      | nil => simp at hUL
      | cons b bs =>
        have hUint : U ∈ (b :: bs).dropLast := RespectAppendDetails.hUintAt389 R U hUneR b bs hUL
        have hleftInterior : U ∈ ((R :: b :: bs).drop 1).dropLast := by
          simpa [List.drop_succ_cons] using hUint
        obtain ⟨g, hpair, hanc⟩ := hleftAnc U hleftInterior
        have hpairDrop := leftPairDrop hpair hUneJ
        have hpairNew := leftPairTransfer hpairDrop
        exact ⟨g, hpairNew, hanc⟩
  · by_cases hUJ : U = J
    · subst U
      have hpairRight : (J, hJ) ∈ right.zip hr := RespectAppendDetails.hpairRight J hJ right hr
          hrightZipShape
      have hpairNew : (J, hJ) ∈ (left.dropLast ++ right).zip (hl.dropLast ++ hr) :=
          RespectAppendDetails.hpairNewAt405 J hJ left right hl hr hzip hpairRight
      exact ⟨hJ, hpairNew, hjoin⟩
    · cases right with
      | nil => simp at hrightTileHead
      | cons a as =>
        have ha : a = J := by simpa using hrightTileHead
        subst a
        have hUint : U ∈ as := RespectAppendDetails.hUintAt414 J U hUJ as hUR
        have hrightGetLast : (J :: as).getLast (by simp) = S :=
            RespectAppendDetails.hrightGetLast J S as hrightTileLast
        have hrightDrop : U ∈ (J :: as).dropLast := RespectAppendDetails.hrightDrop J S U hUneS
            as hUR hrightGetLast
        cases as with
        | nil => simp at hUint
        | cons b bs =>
          have hrightTailDrop : U ∈ (b :: bs).dropLast := RespectAppendDetails.hrightTailDrop J U
              hUJ b bs hrightDrop
          have hrightInterior : U ∈ ((J :: b :: bs).drop 1).dropLast := by
            simpa [List.drop_succ_cons] using hrightTailDrop
          obtain ⟨g, hpair, hanc⟩ := hrightAnc U hrightInterior
          have hpairNew := rightPairTransfer hpair
          exact ⟨g, hpairNew, hanc⟩

end ApollonianSuperharmonic

end
