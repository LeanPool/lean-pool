/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.SwappedAffineTriangularChartAlignment
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.TileStringCoordinateTransport
public import LeanPool.ApollonianSuperharmonic.UnitSquareOpposingStripInterfacePath

-- [TABLET NODE: OpposingStringInterfacePath]

/-!
# OpposingStringInterfacePath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OpposingInterfaceGeometry

private theorem hRmem :
    (by
      classical
      exact
        ∀ (R : ProtoTile), ∀ (forward : List ProtoTile), (forward.head? = some R) → (R ∈ forward)
            ) := by
  classical
  intro R forward hfhead
  have hopt : R ∈ forward.head? := by simp [hfhead]
  rw [List.eq_cons_of_mem_head? hopt]
  simp

private theorem hSmem :
    (by
      classical
      exact
        ∀ (S : ProtoTile), ∀ (forward : List ProtoTile), (forward.getLast? = some S) → (S ∈
            forward) ) := by
  classical
  intro S forward hflast
  have hopt : S ∈ forward.getLast? := by simp [hflast]
  obtain ⟨hne, hget⟩ := List.mem_getLast?_eq_getLast hopt
  rw [hget]
  exact List.getLast_mem hne

private theorem hrs :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), (R ≠ S) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), (R = tileAt r) → ((S = tileAt s) → (r ≠ s))) ) := by
  classical
  intro base R S hRS a b tileAt r s hR hS hrs
  apply hRS
  rw [hR, hS, hrs]

private theorem hnadjCoord :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S
            : ProtoTile), (¬if C.1.1.1 = (1 : ℤ) then ∃ (v : GaussianInt), UnitTriangularStep
            orientation v ∧ TileCentroid S - TileCentroid R = GaussianRealPoint v else
            TileTouching R S) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), (∀ (x : ℤ × ℤ), ∀ (y :
            ℤ × ℤ), (fun (T U : ProtoTile) => if C.1.1.1 = (1 : ℤ) then ∃ (v : GaussianInt),
            UnitTriangularStep orientation v ∧ TileCentroid U - TileCentroid T =
            GaussianRealPoint v else TileTouching T U) ((fun (z : ℤ × ℤ) => TileTranslation base
            ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x) ((fun (z : ℤ × ℤ) =>
            TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) y) ↔
            TriangularLatticeAdjacent x y) → (
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), (R = tileAt r) → ((S = tileAt s) → (¬
            TriangularLatticeAdjacent r s)))) ) := by
  classical
  intro C orientation base R S hnadj a b hadj tileAt r s hR hS hadjrs
  apply hnadj
  rw [hR, hS]
  exact (hadj r s).2 hadjrs

private theorem forall₂_dropLast :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            (List.Forall₂ Rel xs ys) → (List.Forall₂ Rel xs.dropLast ys.dropLast) ) := by
  classical
  intro α β Rel xs ys hall
  induction hall with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
    cases xs with
    | nil =>
      have hy : ys = [] := (List.forall₂_nil_left_iff).mp htail
      subst ys
      simp
    | cons x' xs' =>
      cases ys with
      | nil => simp at htail
      | cons y' ys' =>
        rw [List.dropLast_cons_cons, List.dropLast_cons_cons]
        exact List.Forall₂.cons hxy ih

private theorem forall₂_mem :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            (List.Forall₂ Rel xs ys) → (∀ z ∈ ys, ∃ x ∈ xs, Rel x z) ) := by
  classical
  intro α β Rel xs ys hall
  induction hall with
  | nil => intro z hz; simp at hz
  | @cons x z xs ys hxy htail ih =>
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨x, by simp, hxy⟩
    · obtain ⟨x', hx', hx'z⟩ := ih w hw
      exact ⟨x', by simp [hx'], hx'z⟩

private theorem forwardInterior :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (forward : List ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (F : List (ℤ × ℤ)), (List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ ×
            ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z)
            (List.drop (1 : ℕ) forward).dropLast (List.drop (1 : ℕ) F).dropLast) → ((∀
            {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            (List.Forall₂ Rel xs ys) → (∀ z ∈ ys, ∃ x ∈ xs, Rel x z)) → (∀ (z : Int × Int), (z ∈
            (F.drop 1).dropLast) → (∃ T ∈ (forward.drop 1).dropLast, T = tileAt z))) ) := by
  classical
  intro base forward a b tileAt F forall₂_interior forall₂_mem z hz
  exact forall₂_mem forall₂_interior z hz

private theorem reverseInterior :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (reverse : List ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (G : List (ℤ × ℤ)), (List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ ×
            ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z)
            (List.drop (1 : ℕ) reverse).dropLast (List.drop (1 : ℕ) G).dropLast) → ((∀
            {α : Type}, ∀ {β : Type}, ∀ {Rel : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            (List.Forall₂ Rel xs ys) → (∀ z ∈ ys, ∃ x ∈ xs, Rel x z)) → (∀ (z : Int × Int), (z ∈
            (G.drop 1).dropLast) → (∃ T ∈ (reverse.drop 1).dropLast, T = tileAt z))) ) := by
  classical
  intro base reverse a b tileAt G rfor₂_interior forall₂_mem z hz
  exact forall₂_mem rfor₂_interior z hz

private theorem hshift :
    (by
      classical
      exact
        ∀ (z : Int × Int), (z.1 : GaussianInt) * 1 + (z.2 : GaussianInt) * ⟨0, 1⟩ = (⟨z.1, z.2⟩ :
            GaussianInt) ) := by
  classical
  intro z
  ext <;> simp

private theorem hshift' :
    (by
      classical
      exact
        ∀ (z : Int × Int), (z.1 : GaussianInt) + ⟨0, z.2⟩ = (⟨z.1, z.2⟩ : GaussianInt) ) := by
  classical
  intro z
  ext <;> simp

private theorem hcellsEq :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (x : GaussianInt), (base.cells = {x}) → (
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * 1 + (z.2 : GaussianInt) * (⟨0, 1⟩ :
              GaussianInt))
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x}, x⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        (∀ (z : Int × Int), (z.1 : GaussianInt) + ⟨0, z.2⟩ = (⟨z.1, z.2⟩ : GaussianInt)) → (∀ (z
            : Int × Int), (tileAt z).cells = (unitAt z).cells)) ) := by
  classical
  intro base x hcells tileAt unitAt hshift' z
  simp [tileAt, unitAt, TileTranslation, GaussianTranslation, hcells, hshift']

private theorem hvertsEqAt258 :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (x : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * 1 + (z.2 : GaussianInt) * (⟨0, 1⟩ :
              GaussianInt))
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x}, x⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        (∀ (z : Int × Int), (tileAt z).cells = (unitAt z).cells) → (∀ (z : Int × Int),
            FootprintVertices (tileAt z) = FootprintVertices (unitAt z)) ) := by
  classical
  intro base x tileAt unitAt hcellsEq z
  have hunitne : (unitAt z).cells.Nonempty := by
    simp [unitAt, TileTranslation]
  have htilene : (tileAt z).cells.Nonempty := by
    rw [hcellsEq]
    exact hunitne
  simp [FootprintVertices, hunitne, hcellsEq]

private theorem hedgesEqAt266 :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (x : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * 1 + (z.2 : GaussianInt) * (⟨0, 1⟩ :
              GaussianInt))
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x}, x⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        (∀ (z : Int × Int), (tileAt z).cells = (unitAt z).cells) → (∀ (z : Int × Int),
            FootprintEdges (tileAt z) = FootprintEdges (unitAt z)) ) := by
  classical
  intro base x tileAt unitAt hcellsEq z
  rw [FootprintEdges, FootprintEdges, hcellsEq]

private theorem hcellCalc :
    (by
      classical
      exact
        (BandCircle) → (∀ (base : ProtoTile), ∀ (x : GaussianInt), (base.cells = {x}) → (
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * (⟨0, 1⟩ : GaussianInt) + (z.2 :
              GaussianInt) * (-1))
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        ∀ (z : Int × Int), (tileAt z).cells = (turnedAt z).cells)) ) := by
  classical
  intro C base x hcells tileAt x0 unitAt turnedAt z
  simp only [TileTranslation, Int.reduceNeg, Zsqrtd.smul_val, mul_zero, mul_one, mul_neg,
      hcells, Finset.image_singleton, GaussianTranslation, TileQuarterTurn,
      GaussianQuarterTurn, Zsqrtd.add_def, neg_add_rev, neg_sub, sub_neg_eq_add,
      Finset.singleton_inj, tileAt, turnedAt, unitAt, x0]
  ext <;> simp []; omega

private theorem hvertsEqAt314 :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (x : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * (⟨0, 1⟩ : GaussianInt) + (z.2 :
              GaussianInt) * (-1))
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        (∀ (z : Int × Int), (tileAt z).cells = (turnedAt z).cells) → (∀ (z : Int × Int),
            FootprintVertices (tileAt z) = FootprintVertices (turnedAt z)) ) := by
  classical
  intro base x tileAt x0 unitAt turnedAt hcellCalc z
  have hturnedne : (turnedAt z).cells.Nonempty := by
    simp [turnedAt, unitAt, TileQuarterTurn, TileTranslation]
  have htilene : (tileAt z).cells.Nonempty := by
    rw [hcellCalc]
    exact hturnedne
  simp [FootprintVertices, hturnedne, hcellCalc]

private theorem hedgesEqAt322 :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (x : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * (⟨0, 1⟩ : GaussianInt) + (z.2 :
              GaussianInt) * (-1))
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        (∀ (z : Int × Int), (tileAt z).cells = (turnedAt z).cells) → (∀ (z : Int × Int),
            FootprintEdges (tileAt z) = FootprintEdges (turnedAt z)) ) := by
  classical
  intro base x tileAt x0 unitAt turnedAt hcellCalc z
  rw [FootprintEdges, FootprintEdges, hcellCalc]

private theorem qstep :
    (by
      classical
      exact
        (BandCircle) → (
        let q := GaussianQuarterTurn
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), (v = u + 1 ∨ v = u - 1 ∨
            v = u + ⟨0, 1⟩ ∨ v = u - ⟨0, 1⟩) → (q v = q u + 1 ∨ q v = q u - 1 ∨ q v = q u + ⟨0,
                1⟩ ∨ q v = q u - ⟨0, 1⟩)) ) := by
  classical
  intro C q u v huv
  rcases huv with h | h | h | h
  · subst v
    right; right; left
    ext <;> simp [q, GaussianQuarterTurn]
  · subst v
    right; right; right
    ext <;> simp [q, GaussianQuarterTurn]
  · subst v
    right; left
    ext <;> simp [q, GaussianQuarterTurn]; omega
  · subst v
    left
    ext <;> simp [q, GaussianQuarterTurn]; omega

private theorem hqchain :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), (List.IsChain (fun (x y : GaussianInt) => y = x + (1 :
            GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) p) → (
        let q := GaussianQuarterTurn
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), (v = u + 1 ∨ v = u - 1 ∨ v = u + ⟨0, 1⟩ ∨ v =
            u - ⟨0, 1⟩) → (q v = q u + 1 ∨ q v = q u - 1 ∨ q v = q u + ⟨0, 1⟩ ∨ q v = q u - ⟨0,
            1⟩)) → ((p.map q).IsChain (fun u v : GaussianInt => v = u + 1 ∨ v = u - 1 ∨ v = u +
            ⟨0, 1⟩ ∨ v = u - ⟨0, 1⟩))) ) := by
  classical
  intro p hpchain q qstep
  exact List.isChain_map_of_isChain q qstep hpchain

private theorem hqverts :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        let q := GaussianQuarterTurn
        ∀ (z : Int × Int), FootprintVertices (turnedAt z) = q '' FootprintVertices (unitAt z) )
            := by
  classical
  intro x x0 unitAt turnedAt q z
  change FootprintVertices (TileQuarterTurn (unitAt z)) = _
  exact (TileQuarterTurnFormulas (unitAt z)).2.2.2.2.2.1

private theorem hqedges :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        let q := GaussianQuarterTurn
        ∀ (z : Int × Int), FootprintEdges (turnedAt z) = (fun e : Finset GaussianInt => e.image
            q) '' FootprintEdges (unitAt z) ) := by
  classical
  intro x x0 unitAt turnedAt q z
  change FootprintEdges (TileQuarterTurn (unitAt z)) = _
  exact (TileQuarterTurnFormulas (unitAt z)).2.2.2.2.2.2.1

private theorem hpOrig :
    (by
      classical
      exact
        ∀ (p : List GaussianInt),
        let q := GaussianQuarterTurn
        let qInv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        (∀ (z : GaussianInt), qInv (q z) = z) → (∀ (v : GaussianInt), ∀ (w : GaussianInt), ∀ (l₁
            : List GaussianInt), ∀ (l₂ : List GaussianInt), (List.map q p = l₁ ++ v :: w :: l₂) →
            (p = l₁.map qInv ++ qInv v :: qInv w :: l₂.map qInv)) ) := by
  classical
  intro p q qInv hqInv v w l₁ l₂ hp
  have h := congrArg (List.map qInv) hp
  simpa [List.map_append, List.map_map, Function.comp_def, qInv, q,
    hqInv] using h

private theorem hEdgeA'At404 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        let q := GaussianQuarterTurn
        let qInv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        (∀ (z : GaussianInt), q (qInv z) = z) → ((∀ (z : Int × Int), FootprintEdges (turnedAt z)
            = (fun e : Finset GaussianInt => e.image q) '' FootprintEdges (unitAt z)) → (∀ (v :
            GaussianInt), ∀ (w : GaussianInt), ∀ (a' : ℤ × ℤ), ({qInv v, qInv w} ∈ FootprintEdges
            ((fun (z : ℤ × ℤ) => TileTranslation (⟨{x0}, x0⟩ : ProtoTile) (⟨z.1, z.2⟩ :
            GaussianInt)) a')) → ({v, w} ∈ FootprintEdges (turnedAt a')))) ) := by
  classical
  intro x x0 unitAt turnedAt q qInv hqInv' hqedges v w a' hEdgeA
  rw [hqedges]
  have hmem := Set.mem_image_of_mem
    (fun e : Finset GaussianInt => e.image q) hEdgeA
  simpa [unitAt, Finset.image_insert, q, qInv, hqInv'] using hmem

private theorem hEdgeB'At409 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
        let unitAt : Int × Int → ProtoTile := fun z =>
          TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
            (⟨z.1, z.2⟩ : GaussianInt)
        let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
        let q := GaussianQuarterTurn
        let qInv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        (∀ (z : GaussianInt), q (qInv z) = z) → ((∀ (z : Int × Int), FootprintEdges (turnedAt z)
            = (fun e : Finset GaussianInt => e.image q) '' FootprintEdges (unitAt z)) → (∀ (v :
            GaussianInt), ∀ (w : GaussianInt), ∀ (b' : ℤ × ℤ), ({qInv v, qInv w} ∈ FootprintEdges
            ((fun (z : ℤ × ℤ) => TileTranslation (⟨{x0}, x0⟩ : ProtoTile) (⟨z.1, z.2⟩ :
            GaussianInt)) b')) → ({v, w} ∈ FootprintEdges (turnedAt b')))) ) := by
  classical
  intro x x0 unitAt turnedAt q qInv hqInv' hqedges v w b' hEdgeB
  rw [hqedges]
  have hmem := Set.mem_image_of_mem
    (fun e : Finset GaussianInt => e.image q) hEdgeB
  simpa [unitAt, Finset.image_insert, q, qInv, hqInv'] using hmem

private theorem incident :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ [DecidableEq ι], ∀ (PP : PeriodicTileComplex ι), ∀ (xi : ℤ × ℤ → ι), ∀
            (faceAt :
            AffineTriangularFace → PP.plane.Face), (∀ (f : AffineTriangularFace), Finset.image xi
            (AffineTriangularFaceVertices f) = {PP.plane.faceVertex (faceAt f) (0 : Fin (3 : ℕ)),
            PP.plane.faceVertex (faceAt f) (1 : Fin (3 : ℕ)), PP.plane.faceVertex (faceAt f) (2 :
            Fin (3 : ℕ))}) → (∀ (f : AffineTriangularFace), ∀ (z : Int × Int), (z ∈
            AffineTriangularFaceVertices f) → (∃ i, PP.plane.faceVertex (faceAt f) i = xi z)) )
            := by
  classical
  intro ι equality PP xi faceAt hinc f z hz
  have hm : xi z ∈ (AffineTriangularFaceVertices f).image xi :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  rw [hinc f] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · exact ⟨0, hm.symm⟩
  · exact ⟨1, hm.symm⟩
  · exact ⟨2, hm.symm⟩

private theorem faceStepData :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (F : List (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)), ∀ (ι : Type), ∀ (PP : PeriodicTileComplex ι),
            ∀ (xi : ℤ × ℤ → ι), ∀ (faceAt : AffineTriangularFace → PP.plane.Face), (∀ (u : ℤ ×
            ℤ), ∀ (v : ℤ × ℤ), TriangularLatticeAdjacent u v ↔ PP.plane.adjacent (xi u) (xi v)) →
            ((∀ (z : ℤ × ℤ), PP.tile (xi z) = tileAt z) → ((Function.Injective faceAt) → (
        let goodV : GaussianInt → Prop := fun x =>
          (∃ a ∈ (F.drop 1).dropLast, x ∈ FootprintVertices (tileAt a)) ∧
          (∃ b ∈ (G.drop 1).dropLast, x ∈ FootprintVertices (tileAt b))
        let goodE : GaussianInt → GaussianInt → Prop := fun x y =>
          (∃ a ∈ (F.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt a)) ∧
          (∃ b ∈ (G.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt b))
        (∀ (f : AffineTriangularFace), ∀ (z : Int × Int), (z ∈ AffineTriangularFaceVertices f) →
            (∃ i, PP.plane.faceVertex (faceAt f) i = xi z)) → (∀ (f : AffineTriangularFace), ∀ (g
            : AffineTriangularFace), (AffineTriangularCorridorStep F G f g) → (
        let W := PP.facePath (faceAt f) (faceAt g);
          W.head? = some (PP.rho (faceAt f)) ∧
          W.getLast? = some (PP.rho (faceAt g)) ∧
          (∀ w ∈ W, goodV w) ∧
          ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
            W = l₁ ++ x :: y :: l₂ → goodE x y))))) ) := by
  classical
  intro base a b tileAt F G ι PP xi faceAt hadjXi htileXi hinjFace goodV goodE incident f g hfg
  rcases hfg with ⟨hfg, u, v, huv, hadjuv, huf, hvf, hug, hvg, howners⟩
  have hplane : PP.plane.adjacent (xi u) (xi v) :=
    (hadjXi u v).mp hadjuv
  have hfaceNe : faceAt f ≠ faceAt g := fun h => hfg (hinjFace h)
  have hspec := PP.facePath_spec (xi u) (xi v) hplane
    (faceAt f) (faceAt g) hfaceNe
    (incident f u huf) (incident f v hvf)
    (incident g u hug) (incident g v hvg)
  refine ⟨hspec.1, hspec.2.1, ?_, ?_⟩
  · intro w hw
    have hwu : w ∈ FootprintVertices (tileAt u) := by
      rw [← htileXi u]
      exact hspec.2.2.1 w hw |>.1
    have hwv : w ∈ FootprintVertices (tileAt v) := by
      rw [← htileXi v]
      exact hspec.2.2.1 w hw |>.2
    rcases howners with ⟨hau, hbv⟩ | ⟨hau, hbau⟩
    · exact ⟨⟨u, hau, hwu⟩, ⟨v, hbv, hwv⟩⟩
    · exact ⟨⟨u, hau, hwu⟩, ⟨u, hbau, hwu⟩⟩
  · intro x y l₁ l₂ heq
    have hEdge := hspec.2.2.2 x y l₁ l₂ heq
    have hEu : {x, y} ∈ FootprintEdges (tileAt u) := by
      rw [← htileXi u]
      exact hEdge.1
    have hEv : {x, y} ∈ FootprintEdges (tileAt v) := by
      rw [← htileXi v]
      exact hEdge.2
    rcases howners with ⟨hau, hbv⟩ | ⟨hau, hbau⟩
    · exact ⟨⟨u, hau, hEu⟩, ⟨v, hbv, hEv⟩⟩
    · exact ⟨⟨u, hau, hEu⟩, ⟨u, hbau, hEu⟩⟩

private theorem chainAppendDrop :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (F : List (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)),
        let goodE : GaussianInt → GaussianInt → Prop := fun x y =>
          (∃ a ∈ (F.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt a)) ∧
          (∃ b ∈ (G.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt b))
        ∀ {A : List GaussianInt}, ∀ {B : List GaussianInt}, (A ≠ []) → ((A.getLast? = B.head?) →
            ((A.IsChain goodE) → ((B.IsChain goodE) → ((A ++ B.drop 1).IsChain goodE)))) ) := by
  classical
  intro base a b tileAt F G goodE A B hAn hjoin hA hB
  rw [List.isChain_append]
  refine ⟨hA, ?_, ?_⟩
  · simpa using hB.tail
  · intro x hx y hy
    cases B with
    | nil =>
      cases A with
      | nil => simp at hAn
      | cons a as =>
        rw [List.getLast?_eq_getLast_of_ne_nil hAn] at hjoin
        simp at hjoin
    | cons b bs =>
      change List.IsChain goodE (b :: bs) at hB
      have hxval : b = x := by simpa [hjoin] using hx
      have hy' : y ∈ bs.head? := by simpa using hy
      rw [← hxval]
      exact hB.rel_head? hy'

private theorem hfaceLen :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), (List ProtoTile) → ((List
            ProtoTile) → (∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), (R = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a +
            (↑z.2 : GaussianInt) * b)) r) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ × ℤ) => R = (fun (z : ℤ
            × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b))
            z) y → y = r) → (∀ (s : ℤ × ℤ), (S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1
            : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) s) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ ×
            ℤ) => S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2
            : GaussianInt) * b)) z) y → y = s) → ((R = tileAt r) → ((S = tileAt s) → (∀ (F : List
            (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)), (TriangularStripSegment r s F) →
            ((TriangularStripSegment s r G) → ((r ≠ s) → ((¬ TriangularLatticeAdjacent r s) → (∀
            (faces : List AffineTriangularFace), (faces ≠ []) → ((∃ (f : AffineTriangularFace),
            faces.head? = some f ∧ r ∈ AffineTriangularFaceVertices f) → ((∃ (f :
            AffineTriangularFace), faces.getLast? = some f ∧ s ∈ AffineTriangularFaceVertices f)
            → ((∀ f ∈ faces, (∃ a ∈ (List.drop (1 : ℕ) F).dropLast, a ∈
            AffineTriangularFaceVertices f) ∧ ∃ b ∈ (List.drop (1 : ℕ) G).dropLast, b ∈
            AffineTriangularFaceVertices f) → ((List.IsChain (AffineTriangularCorridorStep F G)
            faces) → (2 ≤ faces.length))))))))))))))))) ) := by
  classical
  intro base R S forward reverse a b tileAt r hrcoord hruniq s hscoord hsuniq hR hS F G hFstrip
      hGstrip hrs hnadjCoord faces hfacesNe hfirst hlast hfaceVertices hfaceChain
  rcases hfirst with ⟨f, hf, hfr⟩
  rcases hlast with ⟨g, hg, hgs⟩
  cases faces with
  | nil => simp at hfacesNe
  | cons f' tail =>
    cases tail with
    | nil =>
      have hfg : f' = f := by simpa using hf
      have hgg : f' = g := by simpa using hg
      subst f
      subst g
      have hAdj : TriangularLatticeAdjacent r s := by
        cases f' <;>
          simp only [AffineTriangularFaceVertices, Finset.mem_insert,
            Finset.mem_singleton] at hfr hgs <;>
          rcases hfr with rfl | rfl | rfl <;>
            rcases hgs with rfl | rfl | rfl <;>
            try contradiction
        all_goals simp [TriangularLatticeAdjacent, Prod.ext_iff,
          ]
      exact (hnadjCoord hAdj).elim
    | cons g' rest => simp

private theorem walkFacts :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (F : List (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)), ∀ (ι : Type), ∀ (PP : PeriodicTileComplex ι),
            ∀ (faceAt : AffineTriangularFace → PP.plane.Face),
        let goodV : GaussianInt → Prop := fun x =>
          (∃ a ∈ (F.drop 1).dropLast, x ∈ FootprintVertices (tileAt a)) ∧
          (∃ b ∈ (G.drop 1).dropLast, x ∈ FootprintVertices (tileAt b))
        let goodE : GaussianInt → GaussianInt → Prop := fun x y =>
          (∃ a ∈ (F.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt a)) ∧
          (∃ b ∈ (G.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt b))
        (∀ (f : AffineTriangularFace), ∀ (g : AffineTriangularFace),
            (AffineTriangularCorridorStep F G f g) → (
        let W := PP.facePath (faceAt f) (faceAt g);
          W.head? = some (PP.rho (faceAt f)) ∧
          W.getLast? = some (PP.rho (faceAt g)) ∧
          (∀ w ∈ W, goodV w) ∧
          ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
            W = l₁ ++ x :: y :: l₂ → goodE x y)) → ((∀ (W : List GaussianInt), (∀ x y :
                GaussianInt, ∀ l₁, ∀ l₂, W = l₁ ++ x :: y :: l₂ → goodE x y) → (W.IsChain goodE))
                → ((∀ {A : List GaussianInt}, ∀ {B : List GaussianInt}, (A ≠ []) → ((A.getLast? =
                B.head?) → ((A.IsChain goodE) → ((B.IsChain goodE) → ((A ++ B.drop 1).IsChain
                goodE))))) → (
        let joinWalk : List AffineTriangularFace → List GaussianInt := fun L =>
          (L.zip L.tail).foldr
            (fun fg acc => PP.facePath (faceAt fg.1) (faceAt fg.2) ++ acc.drop 1) []
        ∀ L : List AffineTriangularFace, L.IsChain (AffineTriangularCorridorStep F G) → 2 ≤
            L.length → (∃ f, L.head? = some f ∧ (joinWalk L).head? = some (PP.rho (faceAt f))) ∧
            (∃ g, L.getLast? = some g ∧ (joinWalk L).getLast? = some (PP.rho (faceAt g))) ∧ (∀ w
            ∈ joinWalk L, goodV w) ∧ (joinWalk L).IsChain goodE))) ) := by
  classical
  intro base a b tileAt F G ι PP faceAt goodV goodE faceStepData chainOfEdges chainAppendDrop
      joinWalk L
  induction L using List.twoStepInduction with
  | nil => intro _ hlen; simp at hlen
  | singleton f => intro _ hlen; simp at hlen
  | cons_cons f g rest ih ih' =>
    intro hchain hlen
    have hfg := (List.isChain_cons_cons.mp hchain).1
    have htail := (List.isChain_cons_cons.mp hchain).2
    have hdata := faceStepData f g hfg
    let W := PP.facePath (faceAt f) (faceAt g)
    have hwalkEq : joinWalk (f :: g :: rest) =
        W ++ (joinWalk (g :: rest)).drop 1 := by
      simp [joinWalk, W]
    have hWhead : W.head? = some (PP.rho (faceAt f)) := hdata.1
    have hWlast : W.getLast? = some (PP.rho (faceAt g)) := hdata.2.1
    have hWnonempty : W ≠ [] := by
      intro hnil
      simp [W, hnil] at hWhead
    have hWchain : W.IsChain goodE := chainOfEdges W (by
      intro x y l₁ l₂ heq
      exact hdata.2.2.2 x y l₁ l₂ heq)
    cases rest with
    | nil =>
      have hsingle : joinWalk [g] = [] := by simp [joinWalk]
      refine ⟨⟨f, rfl, ?_⟩, ⟨g, ?_, ?_⟩, ?_, ?_⟩
      · rw [hwalkEq, hsingle]
        simpa using hWhead
      · simp
      · rw [hwalkEq, hsingle]
        simpa using hWlast
      · intro w hw
        rw [hwalkEq, hsingle] at hw
        have hw' : w ∈ W := by simpa using hw
        exact hdata.2.2.1 w hw'
      · rw [hwalkEq, hsingle]
        simpa using hWchain
    | cons h rest' =>
      have htailLen : 2 ≤ (g :: h :: rest').length := by simp
      have hrec := ih' g htail htailLen
      obtain ⟨⟨g0, hg0, hrecHead⟩, ⟨gend, hgend, hrecLast⟩,
        hrecVerts, hrecChain⟩ := hrec
      have hg0eq : g = g0 := by simpa using hg0
      subst g0
      have hjoin : W.getLast? = (joinWalk (g :: h :: rest')).head? := by
        rw [hrecHead]
        exact hWlast
      have hjoinedChain := chainAppendDrop hWnonempty hjoin hWchain hrecChain
      have hjoinedHead :
          (W ++ (joinWalk (g :: h :: rest')).drop 1).head? =
            some (PP.rho (faceAt f)) := by
        rw [List.head?_append_of_ne_nil _ hWnonempty]
        exact hWhead
      have hjoinedLast :
          (W ++ (joinWalk (g :: h :: rest')).drop 1).getLast? =
            some (PP.rho (faceAt gend)) := by
        by_cases hdrop : (joinWalk (g :: h :: rest')).drop 1 = []
        · have hsingle : joinWalk (g :: h :: rest') =
              [PP.rho (faceAt g)] := by
              cases hp : joinWalk (g :: h :: rest') with
              | nil => simp [hp] at hrecHead
              | cons x xs =>
                cases xs with
                | nil =>
                  have hx : x = PP.rho (faceAt g) := by
                    simpa [hp] using hrecHead
                  subst x
                  simp []
                | cons y ys => simp [hp] at hdrop
          have hends : PP.rho (faceAt g) = PP.rho (faceAt gend) := by
            simpa [hsingle] using hrecLast
          simp [hdrop, hWlast, hends]
        · have hlastdrop :
              ((joinWalk (g :: h :: rest')).drop 1).getLast? =
                (joinWalk (g :: h :: rest')).getLast? := by
                cases hpath : joinWalk (g :: h :: rest') with
                | nil => simp [hpath] at hdrop
                | cons x xs =>
                  cases hxs : xs with
                  | nil => simp [hpath, hxs] at hdrop
                  | cons y ys => rfl
          rw [List.getLast?_append_of_ne_nil _ hdrop, hlastdrop, hrecLast]
      refine ⟨⟨f, rfl, ?_⟩, ⟨gend, ?_, ?_⟩, ?_, ?_⟩
      · rw [hwalkEq]
        exact hjoinedHead
      · simpa using hgend
      · rw [hwalkEq]
        exact hjoinedLast
      · intro w hw
        rw [hwalkEq] at hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hdata.2.2.1 w hw
        · exact hrecVerts w (List.mem_of_mem_drop hw)
      · rw [hwalkEq]
        exact hjoinedChain

private theorem pairStep :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (({x,
            y} : Finset GaussianInt) = {a, b}) → ((b = a + 1 ∨ b = a + ⟨0, 1⟩) → (y = x + 1 ∨ y =
            x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩)) ) := by
  classical
  intro x y a b hp hab
  have hxm : x = a ∨ x = b := by
    have hx : x ∈ ({a, b} : Finset GaussianInt) := by rw [← hp]; simp
    simpa using hx
  have hym : y = a ∨ y = b := by
    have hy : y ∈ ({a, b} : Finset GaussianInt) := by rw [← hp]; simp
    simpa using hy
  have ham : a = x ∨ a = y := by
    have ha : a ∈ ({x, y} : Finset GaussianInt) := by rw [hp]; simp
    simpa using ha
  have hbm : b = x ∨ b = y := by
    have hb : b ∈ ({x, y} : Finset GaussianInt) := by rw [hp]; simp
    simpa using hb
  have habne : a ≠ b := by
    intro he
    subst b
    rcases hab with hab | hab
    · have h := congrArg (fun z : GaussianInt => z.re) hab
      simp at h
    · have h := congrArg (fun z : GaussianInt => z.im) hab
      simp at h
  have hxy : x ≠ y := by
    intro he
    subst y
    rcases ham with hax | hax <;> rcases hbm with hbx | hbx
    all_goals exact habne (hax.trans hbx.symm)
  rcases hxm with hxa | hxb
  · rcases hym with hya | hyb
    · exact (hxy (hxa.trans hya.symm)).elim
    · subst x
      subst y
      rcases hab with hab | hab
      · exact Or.inl (by simp [hab])
      · exact Or.inr (Or.inr (Or.inl (by simp [hab])))
  · rcases hym with hya | hyb
    · subst x
      subst y
      rcases hab with hab | hab
      · exact Or.inr (Or.inl (by rw [hab]; simp))
      · exact Or.inr (Or.inr (Or.inr (by rw [hab]; simp)))
    · exact (hxy (hxb.trans hyb.symm)).elim

private theorem actualEdgeStep :
    (by
      classical
      exact
        (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (({x, y} : Finset GaussianInt) = {a, b}) → ((b = a + 1 ∨ b = a + ⟨0, 1⟩) → (y = x + 1
            ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩))) → (∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, ∀ {T : ProtoTile}, ({x, y} ∈ FootprintEdges T) → (y = x + 1 ∨ y =
            x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩)) ) := by
  classical
  intro pairStep x y T he
  simp only [FootprintEdges, Set.mem_ofPred_eq] at he
  rcases he with ⟨z, hz, hshape⟩
  rcases hshape with hshape | hshape | hshape | hshape
  · exact pairStep x y z (z + 1) hshape (Or.inl rfl)
  · exact pairStep x y z (z + ⟨0, 1⟩) hshape (Or.inr rfl)
  · exact pairStep x y (z + 1) (z + 1 + ⟨0, 1⟩) hshape (Or.inr (by abel))
  · exact pairStep x y (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) hshape
      (Or.inl (by abel))

private theorem hRrho :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), ∀ (ι : Type), ∀ (PP : PeriodicTileComplex ι), ∀ (xi : ℤ × ℤ → ι), ∀
            (faceAt : AffineTriangularFace → PP.plane.Face), (∀ (z : ℤ × ℤ), PP.tile (xi z) =
            tileAt z) → (∀ (f0 : AffineTriangularFace), ∀ (ir : Fin (3 : ℕ)),
            (PP.plane.faceVertex (faceAt f0) ir = xi r) → (PP.rho (faceAt f0) ∈ FootprintVertices
            (tileAt r))) ) := by
  classical
  intro base a b tileAt r ι PP xi faceAt htileXi f0 ir hir
  rw [← htileXi r, ← hir]
  exact PP.rho_common (faceAt f0) ir

private theorem hSrho :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (s : ℤ × ℤ), ∀ (ι : Type), ∀ (PP : PeriodicTileComplex ι), ∀ (xi : ℤ × ℤ → ι), ∀
            (faceAt : AffineTriangularFace → PP.plane.Face), (∀ (z : ℤ × ℤ), PP.tile (xi z) =
            tileAt z) → (∀ (g0 : AffineTriangularFace), ∀ (is : Fin (3 : ℕ)),
            (PP.plane.faceVertex (faceAt g0) is = xi s) → (PP.rho (faceAt g0) ∈ FootprintVertices
            (tileAt s))) ) := by
  classical
  intro base a b tileAt s ι PP xi faceAt htileXi g0 is his
  rw [← htileXi s, ← his]
  exact PP.rho_common (faceAt g0) is

private theorem htileAlign :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (chart : AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation base
            ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) +
            (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))),
            (a = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) → ((b = BandVectors.1
            (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) → (∀ (z : Int × Int), P.tile
            (chart.vertexEquiv z) = tileAt z)) ) := by
  classical
  intro C base a b tileAt q P chart haV hbV z
  rw [chart.tile_eq]
  simp [tileAt, haV, hbV]

private theorem hinjFaceAt766 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (chart : AffineTriangularComplexChart P
            fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1
            : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 :
            Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))),
        let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
          match f with
          | .up z => chart.up z
          | .down z => chart.down z
        Function.Injective faceAt ) := by
  classical
  intro C base q P chart faceAt f g h
  cases f with
  | up u =>
    cases g with
    | up v => exact congrArg AffineTriangularFace.up (chart.up_injective h)
    | down v => exact False.elim (chart.up_ne_down u v h)
  | down u =>
    cases g with
    | up v => exact False.elim ((chart.up_ne_down v u) h.symm)
    | down v => exact congrArg AffineTriangularFace.down (chart.down_injective h)

private theorem hincAt777 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (chart : AffineTriangularComplexChart P
            fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1
            : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 :
            Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))),
        let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
          match f with
          | .up z => chart.up z
          | .down z => chart.down z
        ∀ (f : AffineTriangularFace), (AffineTriangularFaceVertices f).image chart.vertexEquiv =
            {P.plane.faceVertex (faceAt f) 0, P.plane.faceVertex (faceAt f) 1,
            P.plane.faceVertex (faceAt f) 2} ) := by
  classical
  intro C base q P chart faceAt f
  cases f <;> simp [AffineTriangularFaceVertices, faceAt,
    chart.up_vertices, chart.down_vertices, Finset.image_insert,
    Finset.image_singleton]

private theorem hadjXiAt795 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), (List (ℤ × ℤ)) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (chart :
                AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 :
            GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))), ((∀ (x :
                ℤ × ℤ), ∀ (y : ℤ × ℤ), TriangularLatticeAdjacent x.swap y.swap ↔
            TriangularLatticeAdjacent x y) ∧ (∀ (f : AffineTriangularFace), Finset.image
            Prod.swap (AffineTriangularFaceVertices f) = AffineTriangularFaceVertices
            (AffineTriangularFaceCoordinateSwap f)) ∧ (∀ (z : ℤ × ℤ), TileTranslation base ((↑z.1
            : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑z.2 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) = P.tile
            ((chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)) ∧ ∀ (f :
                AffineTriangularFace),
        let F := (match AffineTriangularFaceCoordinateSwap f with
          | AffineTriangularFace.up z => chart.up z
          | AffineTriangularFace.down z => chart.down z); Finset.image (fun (z : ℤ ×
            ℤ) => (chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)
            (AffineTriangularFaceVertices f) = {P.plane.faceVertex F (0 : Fin (3 : ℕ)),
            P.plane.faceVertex F (1 : Fin (3 : ℕ)), P.plane.faceVertex F (2 : Fin (3 : ℕ))}) → (
        let xi := fun z : Int × Int =>
          chart.vertexEquiv (Prod.swap z)
        ∀ (u : Int × Int), ∀ (v : Int × Int), TriangularLatticeAdjacent u v ↔ P.plane.adjacent
            (xi u) (xi v)))) := by
  classical
  intro C base F q P chart halign xi u v
  change TriangularLatticeAdjacent u v ↔
    P.plane.adjacent (chart.vertexEquiv (Prod.swap u))
      (chart.vertexEquiv (Prod.swap v))
  exact (halign.1 u v).symm.trans
    (chart.adjacent_iff (Prod.swap u) (Prod.swap v)).symm

private theorem htileXi :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        (List (ℤ × ℤ)) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice C)), ∀ (chart : AffineTriangularComplexChart P fun (mn : ℤ × ℤ) =>
            TileTranslation base ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q
            (0 : Fin (4 : ℕ))) + (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q
            (0 : Fin (4 : ℕ))))), (a = BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))
            → ((b = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) → (((∀ (x : ℤ ×
            ℤ), ∀ (y : ℤ × ℤ), TriangularLatticeAdjacent x.swap y.swap ↔
            TriangularLatticeAdjacent x y) ∧ (∀ (f : AffineTriangularFace), Finset.image
            Prod.swap (AffineTriangularFaceVertices f) = AffineTriangularFaceVertices
            (AffineTriangularFaceCoordinateSwap f)) ∧ (∀ (z : ℤ × ℤ), TileTranslation base ((↑z.1
            : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑z.2 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) = P.tile
            ((chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)) ∧ ∀ (f :
                AffineTriangularFace),
        let F := (match AffineTriangularFaceCoordinateSwap f with
          | AffineTriangularFace.up z => chart.up z
          | AffineTriangularFace.down z => chart.down z); Finset.image (fun (z : ℤ ×
            ℤ) => (chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)
            (AffineTriangularFaceVertices f) = {P.plane.faceVertex F (0 : Fin (3 : ℕ)),
            P.plane.faceVertex F (1 : Fin (3 : ℕ)), P.plane.faceVertex F (2 : Fin (3 : ℕ))}) → (
        let xi := fun z : Int × Int =>
          chart.vertexEquiv (Prod.swap z)
        ∀ (z : Int × Int), P.tile (xi z) = tileAt z))))) := by
  classical
  intro C base a b tileAt F q P chart haV hbV halign xi z
  change P.tile (chart.vertexEquiv (Prod.swap z)) = tileAt z
  simpa [tileAt, haV, hbV, add_comm] using (halign.2.2.1 z).symm

private theorem hinjFaceAt805 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (chart : AffineTriangularComplexChart P
            fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1
            : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 :
            Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))),
        let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
          match AffineTriangularFaceCoordinateSwap f with
          | .up z => chart.up z
          | .down z => chart.down z
        Function.Injective faceAt ) := by
  classical
  intro C base q P chart faceAt f g h
  cases f with
  | up u =>
    cases g with
    | up v =>
      change chart.down (Prod.swap u) = chart.down (Prod.swap v) at h
      have hv := chart.down_injective h
      exact congrArg AffineTriangularFace.up (Prod.swap_injective hv)
    | down v =>
      change chart.down (Prod.swap u) = chart.up (Prod.swap v) at h
      exact False.elim ((chart.up_ne_down (Prod.swap v) (Prod.swap u)) h.symm)
  | down u =>
    cases g with
    | up v =>
      change chart.up (Prod.swap u) = chart.down (Prod.swap v) at h
      exact False.elim ((chart.up_ne_down (Prod.swap u) (Prod.swap v)) h)
    | down v =>
      change chart.up (Prod.swap u) = chart.up (Prod.swap v) at h
      have hv := chart.up_injective h
      exact congrArg AffineTriangularFace.down (Prod.swap_injective hv)

private theorem hincAt826 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), (List (ℤ × ℤ)) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (chart :
                AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 :
            GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))), ((∀ (x :
                ℤ × ℤ), ∀ (y : ℤ × ℤ), TriangularLatticeAdjacent x.swap y.swap ↔
            TriangularLatticeAdjacent x y) ∧ (∀ (f : AffineTriangularFace), Finset.image
            Prod.swap (AffineTriangularFaceVertices f) = AffineTriangularFaceVertices
            (AffineTriangularFaceCoordinateSwap f)) ∧ (∀ (z : ℤ × ℤ), TileTranslation base ((↑z.1
            : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑z.2 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) = P.tile
            ((chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)) ∧ ∀ (f :
                AffineTriangularFace),
        let F := (match AffineTriangularFaceCoordinateSwap f with
          | AffineTriangularFace.up z => chart.up z
          | AffineTriangularFace.down z => chart.down z); Finset.image (fun (z : ℤ ×
            ℤ) => (chart.vertexEquiv : ℤ × ℤ → ↥(TilingLattice C)) z.swap)
            (AffineTriangularFaceVertices f) = {P.plane.faceVertex F (0 : Fin (3 : ℕ)),
            P.plane.faceVertex F (1 : Fin (3 : ℕ)), P.plane.faceVertex F (2 : Fin (3 : ℕ))}) → (
        let xi := fun z : Int × Int =>
          chart.vertexEquiv (Prod.swap z)
        let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
          match AffineTriangularFaceCoordinateSwap f with
          | .up z => chart.up z
          | .down z => chart.down z
        ∀ (f : AffineTriangularFace), (AffineTriangularFaceVertices f).image xi =
            {P.plane.faceVertex (faceAt f) 0, P.plane.faceVertex (faceAt f) 1,
            P.plane.faceVertex (faceAt f) 2}))) := by
  classical
  intro C base F q P chart halign xi faceAt f
  change (AffineTriangularFaceVertices f).image
      (fun z => chart.vertexEquiv (Prod.swap z)) = _
  exact halign.2.2.2 f

end OpposingInterfaceGeometry

namespace OpposingInterfaceConclusion

private theorem finish :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (forward : List ProtoTile),
            ∀ (reverse : List ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), (R = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a +
            (↑z.2 : GaussianInt) * b)) r) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ × ℤ) => R = (fun (z : ℤ
            × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b))
            z) y → y = r) → (∀ (s : ℤ × ℤ), (S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1
            : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) s) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ ×
            ℤ) => S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2
            : GaussianInt) * b)) z) y → y = s) → ((R = tileAt r) → ((S = tileAt s) → (∀ (F : List
            (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)), (TriangularStripSegment r s F) →
            ((TriangularStripSegment s r G) → ((r ≠ s) → ((¬TriangularLatticeAdjacent r s) → ((∀
            z ∈ (List.drop (1 : ℕ) F).dropLast, ∃ T ∈ (List.drop (1 : ℕ) forward).dropLast, T =
            (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 :
            GaussianInt) * b)) z) → ((∀ z ∈ (List.drop (1 : ℕ) G).dropLast, ∃ T ∈ (List.drop (1 :
            ℕ) reverse).dropLast, T = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 :
            GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z) → (∀ (faces : List
            AffineTriangularFace), (faces ≠ []) → ((∃ (f : AffineTriangularFace), faces.head? =
            some f ∧ r ∈ AffineTriangularFaceVertices f) → ((∃ (f : AffineTriangularFace),
            faces.getLast? = some f ∧ s ∈ AffineTriangularFaceVertices f) → ((∀ f ∈ faces, (∃ a ∈
            (List.drop (1 : ℕ) F).dropLast, a ∈ AffineTriangularFaceVertices f) ∧ ∃ b ∈
            (List.drop (1 : ℕ) G).dropLast, b ∈ AffineTriangularFaceVertices f) → ((List.IsChain
            (AffineTriangularCorridorStep F G) faces) → (∀ {ι : Type}, ∀ [DecidableEq ι], ∀ (PP :
            PeriodicTileComplex ι), ∀ (xi : Int × Int → ι), ∀ (faceAt : AffineTriangularFace →
            PP.plane.Face), (∀ u, ∀ v, TriangularLatticeAdjacent u v ↔
            PP.plane.adjacent (xi u) (xi v)) → ((∀ z, PP.tile (xi z) = tileAt z) →
                ((Function.Injective faceAt) → ((∀ f, (AffineTriangularFaceVertices f).image xi =
            {PP.plane.faceVertex (faceAt f) 0,
              PP.plane.faceVertex (faceAt f) 1,
              PP.plane.faceVertex (faceAt f) 2}) → (∃ p : List GaussianInt, (∃ x, p.head? = some
                  x ∧ x ∈ FootprintVertices R) ∧ (∃ y, p.getLast? = some y ∧ y ∈
                  FootprintVertices S) ∧ p.IsChain (fun x y => y = x + 1 ∨ y = x - 1 ∨ y = x +
                  ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) ∧ (∀ x, x ∈ p → (∃ a ∈ (forward.drop 1).dropLast, x ∈
                  FootprintVertices a) ∧ (∃ b ∈ (reverse.drop 1).dropLast, x ∈ FootprintVertices
                  b)) ∧ ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt, p = l₁ ++ x :: y :: l₂ →
                  (∃ a ∈ (forward.drop 1).dropLast, {x, y} ∈ FootprintEdges a) ∧ (∃ b ∈
                  (reverse.drop 1).dropLast, {x, y} ∈ FootprintEdges b)))))))))))))))))))))) ) := by
  classical
  intro base R S forward reverse a b tileAt r hrcoord hruniq s hscoord hsuniq hR hS F G hFstrip
      hGstrip hrs hnadjCoord forwardInterior reverseInterior faces hfacesNe hfirst hlast
      hfaceVertices hfaceChain ι typeclassInstance0 PP xi faceAt hadjXi htileXi hinjFace hinc
  let goodV : GaussianInt → Prop := fun x =>
    (∃ a ∈ (F.drop 1).dropLast, x ∈ FootprintVertices (tileAt a)) ∧
    (∃ b ∈ (G.drop 1).dropLast, x ∈ FootprintVertices (tileAt b))
  let goodE : GaussianInt → GaussianInt → Prop := fun x y =>
    (∃ a ∈ (F.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt a)) ∧
    (∃ b ∈ (G.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt b))
  have incident := OpposingInterfaceGeometry.incident ι PP xi faceAt hinc
  have chainOfEdges (W : List GaussianInt)
      (hedge : ∀ x y : GaussianInt, ∀ l₁ l₂,
        W = l₁ ++ x :: y :: l₂ → goodE x y) : W.IsChain goodE :=
    (List.isChain_iff_forall_rel_of_append_cons_cons).2 hedge
  let joinWalk : List AffineTriangularFace → List GaussianInt := fun L =>
    (L.zip L.tail).foldr
      (fun fg acc => PP.facePath (faceAt fg.1) (faceAt fg.2) ++ acc.drop 1) []
  have hfaceLen := OpposingInterfaceGeometry.hfaceLen base R S forward reverse a b r hrcoord
      hruniq s hscoord hsuniq hR hS F G hFstrip hGstrip hrs hnadjCoord faces hfacesNe hfirst
      hlast hfaceVertices hfaceChain
  have walkFacts := OpposingInterfaceGeometry.walkFacts base a b F G ι PP faceAt
      (OpposingInterfaceGeometry.faceStepData base a b F G ι PP xi faceAt hadjXi htileXi
      hinjFace incident) chainOfEdges (OpposingInterfaceGeometry.chainAppendDrop base a b F G)
  have actualEdgeStep {x y : GaussianInt} {T : ProtoTile}
      (he : {x, y} ∈ FootprintEdges T) := OpposingInterfaceGeometry.actualEdgeStep
          (OpposingInterfaceGeometry.pairStep) (x := x) (y := y) (T := T) he
  obtain ⟨hWalkHead, hWalkLast, hWalkVertices, hWalkChain⟩ :=
    walkFacts faces hfaceChain hfaceLen
  obtain ⟨f0, hf0, hpHead⟩ := hWalkHead
  obtain ⟨g0, hg0, hpLast⟩ := hWalkLast
  obtain ⟨fFirst, hfFirst, hfr⟩ := hfirst
  obtain ⟨fLast, hfLast, hgs⟩ := hlast
  have hFirstEq : fFirst = f0 := Option.some.inj (hfFirst.symm.trans hf0)
  have hLastEq : fLast = g0 := Option.some.inj (hfLast.symm.trans hg0)
  subst fFirst
  subst fLast
  obtain ⟨ir, hir⟩ := incident f0 r hfr
  obtain ⟨is, his⟩ := incident g0 s hgs
  have hRrho : PP.rho (faceAt f0) ∈ FootprintVertices (tileAt r) :=
      OpposingInterfaceGeometry.hRrho base a b r ι PP xi faceAt htileXi f0 ir hir
  have hSrho : PP.rho (faceAt g0) ∈ FootprintVertices (tileAt s) :=
      OpposingInterfaceGeometry.hSrho base a b s ι PP xi faceAt htileXi g0 is his
  refine ⟨joinWalk faces, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨PP.rho (faceAt f0), hpHead, by rw [hR]; exact hRrho⟩
  · exact ⟨PP.rho (faceAt g0), hpLast, by rw [hS]; exact hSrho⟩
  · apply hWalkChain.imp
    intro x y hxy
    rcases hxy.1 with ⟨a, ha, hedge⟩
    exact actualEdgeStep hedge
  · intro x hx
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := hWalkVertices x hx
    obtain ⟨A, hA, hAeq⟩ := forwardInterior a ha
    obtain ⟨B, hB, hBeq⟩ := reverseInterior b hb
    exact ⟨⟨A, hA, by rw [hAeq]; exact hxa⟩,
      ⟨B, hB, by rw [hBeq]; exact hxb⟩⟩
  · intro x y l₁ l₂ heq
    have hgood : goodE x y :=
      (List.isChain_iff_forall_rel_of_append_cons_cons.mp hWalkChain) heq
    rcases hgood with ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
    obtain ⟨A, hA, hAeq⟩ := forwardInterior a ha
    obtain ⟨B, hB, hBeq⟩ := reverseInterior b hb
    exact ⟨⟨A, hA, by rw [hAeq]; exact hxa⟩,
      ⟨B, hB, by rw [hBeq]; exact hxb⟩⟩

end OpposingInterfaceConclusion

namespace OpposingUnitInterface

private theorem unrotatedInterface :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S
            : ProtoTile), ∀ (forward : List ProtoTile), ∀ (reverse : List ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ((0 : ℤ) < a.re * b.im - a.im * b.re) → ((a ∈
            TilingLattice C) → ((b ∈ TilingLattice C) → ((∀ (w : ↥(TilingLattice C)), ∃! z : ℤ ×
            ℤ, (↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b = (↑w : GaussianInt)) → ((∀ (U
            : ProtoTile), U ∈ RegularTileFamily base (TilingLattice C) ↔ ∃! z : ℤ × ℤ, U = (fun
            (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt)
            * b)) z) → ((∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), (fun (T U : ProtoTile) => if C.1.1.1 = (1
            : ℤ) then ∃ (v : GaussianInt), UnitTriangularStep orientation v ∧ TileCentroid U -
            TileCentroid T = GaussianRealPoint v else TileTouching T U) ((fun (z : ℤ × ℤ) =>
            TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x) ((fun
            (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt)
            * b)) y) ↔ TriangularLatticeAdjacent x y) → ((∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), ∀ (z : ℤ
            × ℤ), ((TileCentroid ((fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt)
            * a + (↑z.2 : GaussianInt) * b)) z)).2 - (TileCentroid ((fun (z : ℤ × ℤ) =>
            TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x)).2) *
            ((TileCentroid ((fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a +
            (↑z.2 : GaussianInt) * b)) y)).1 - (TileCentroid ((fun (z : ℤ × ℤ) => TileTranslation
            base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x)).1) - ((TileCentroid
            ((fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 :
            GaussianInt) * b)) z)).1 - (TileCentroid ((fun (z : ℤ × ℤ) => TileTranslation base
            ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x)).1) * ((TileCentroid ((fun
            (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt)
            * b)) y)).2 - (TileCentroid ((fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 :
            GaussianInt) * a + (↑z.2 : GaussianInt) * b)) x)).2) = (↑(a.re * b.im - a.im * b.re)
            : ℝ) * (↑(TriangularSignedHeight x y z) : ℝ)) → ((∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (tiles : List ProtoTile), ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), R = (fun (z : ℤ
            × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) r
            → S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 :
            GaussianInt) * b)) s → (TileString C orientation base R S tiles ↔ ∃! coordinates :
            List (ℤ × ℤ), List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ × ℤ)
            => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z)
            tiles coordinates ∧ TriangularStripSegment r s coordinates)) → (
        let tileAt : Int × Int → ProtoTile := fun z =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ (r : ℤ × ℤ), (R = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a +
            (↑z.2 : GaussianInt) * b)) r) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ × ℤ) => R = (fun (z : ℤ
            × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b))
            z) y → y = r) → (∀ (s : ℤ × ℤ), (S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1
            : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) s) → ((∀ (y : ℤ × ℤ), (fun (z : ℤ ×
            ℤ) => S = (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2
            : GaussianInt) * b)) z) y → y = s) → ((R = tileAt r) → ((S = tileAt s) → (∀ (F : List
            (ℤ × ℤ)), ∀ (G : List (ℤ × ℤ)), (List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T =
            (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 :
            GaussianInt) * b)) z) forward F) → ((TriangularStripSegment r s F) → ((List.Forall₂
            (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ × ℤ) => TileTranslation base
            ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z) reverse G) →
            ((TriangularStripSegment s r G) → ((r ≠ s) → ((¬TriangularLatticeAdjacent r s) →
            ((List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ × ℤ) =>
            TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z)
            (List.drop (1 : ℕ) forward).dropLast (List.drop (1 : ℕ) F).dropLast) → ((List.Forall₂
            (fun (T : ProtoTile) (z : ℤ × ℤ) => T = (fun (z : ℤ × ℤ) => TileTranslation base
            ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z) (List.drop (1 : ℕ)
            reverse).dropLast (List.drop (1 : ℕ) G).dropLast) → ((∀ z ∈ (List.drop (1 : ℕ)
            F).dropLast, ∃ T ∈ (List.drop (1 : ℕ) forward).dropLast, T = (fun (z : ℤ × ℤ) =>
            TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b)) z) → ((∀
            z ∈ (List.drop (1 : ℕ) G).dropLast, ∃ T ∈ (List.drop (1 : ℕ) reverse).dropLast, T =
            (fun (z : ℤ × ℤ) => TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 :
            GaussianInt) * b)) z) → (∀ (x : GaussianInt), (base.cells = {x}) → ((a = (1 :
            GaussianInt)) → ((b = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (∃ p : List GaussianInt,
            (∃ x, p.head? = some x ∧ x ∈ FootprintVertices R) ∧ (∃ y, p.getLast? = some y ∧ y ∈
            FootprintVertices S) ∧ p.IsChain (fun x y => y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
            y = x - ⟨0, 1⟩) ∧ (∀ x, x ∈ p → (∃ a ∈ (forward.drop 1).dropLast, x ∈
            FootprintVertices a) ∧ (∃ b ∈ (reverse.drop 1).dropLast, x ∈ FootprintVertices b)) ∧
            ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt, p = l₁ ++ x :: y :: l₂ → (∃ a ∈
            (forward.drop 1).dropLast, {x, y} ∈ FootprintEdges a) ∧ (∃ b ∈ (reverse.drop
            1).dropLast, {x, y} ∈ FootprintEdges b)))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base R S forward reverse a b hdet ha hb hcoords hfamily hadj hheight
      htransport tileAt r hrcoord hruniq s hscoord hsuniq hR hS F G hFtiles hFstrip hGtiles
      hGstrip hrs hnadjCoord forall₂_interior rfor₂_interior forwardInterior reverseInterior x
      hcells ha1 hb1
  subst a
  subst b
  obtain ⟨p, hphead, hplast, hpchain, hpvertices, hpedges⟩ :=
    UnitSquareOpposingStripInterfacePath x r s hrs hnadjCoord F G
      hFstrip hGstrip
  let unitAt : Int × Int → ProtoTile := fun z =>
    TileTranslation (⟨{x}, x⟩ : ProtoTile)
      (⟨z.1, z.2⟩ : GaussianInt)
  have hshift := OpposingInterfaceGeometry.hshift
  have hcellsEq := OpposingInterfaceGeometry.hcellsEq base x hcells
      (OpposingInterfaceGeometry.hshift')
  have hvertsEq (z : Int × Int) :
      FootprintVertices (tileAt z) = FootprintVertices (unitAt z) :=
          OpposingInterfaceGeometry.hvertsEqAt258 base x hcellsEq z
  have hedgesEq (z : Int × Int) :
      FootprintEdges (tileAt z) = FootprintEdges (unitAt z) :=
          OpposingInterfaceGeometry.hedgesEqAt266 base x hcellsEq z
  refine ⟨p, ?_, ?_, hpchain, ?_, ?_⟩
  · rcases hphead with ⟨v, hv, hvU⟩
    have hvU' : v ∈ FootprintVertices (unitAt r) := by simpa [unitAt] using hvU
    exact ⟨v, hv, by rw [hR, hvertsEq]; exact hvU'⟩
  · rcases hplast with ⟨v, hv, hvU⟩
    have hvU' : v ∈ FootprintVertices (unitAt s) := by simpa [unitAt] using hvU
    exact ⟨v, hv, by rw [hS, hvertsEq]; exact hvU'⟩
  · intro v hv
    obtain ⟨a', ha', hav⟩ := (hpvertices v hv).1
    obtain ⟨b', hb', hbv⟩ := (hpvertices v hv).2
    have hav' : v ∈ FootprintVertices (unitAt a') := by simpa [unitAt] using hav
    have hbv' : v ∈ FootprintVertices (unitAt b') := by simpa [unitAt] using hbv
    obtain ⟨A, hA, hAeq⟩ := forwardInterior a' ha'
    obtain ⟨B, hB, hBeq⟩ := reverseInterior b' hb'
    refine ⟨⟨A, hA, ?_⟩, ⟨B, hB, ?_⟩⟩
    · rw [hAeq, hvertsEq]
      exact hav'
    · rw [hBeq, hvertsEq]
      exact hbv'
  · intro v w l₁ l₂ hp
    obtain ⟨a', ha', hEdgeA⟩ := (hpedges v w l₁ l₂ hp).1
    obtain ⟨b', hb', hEdgeB⟩ := (hpedges v w l₁ l₂ hp).2
    have hEdgeA' : {v, w} ∈ FootprintEdges (unitAt a') := by simpa [unitAt] using hEdgeA
    have hEdgeB' : {v, w} ∈ FootprintEdges (unitAt b') := by simpa [unitAt] using hEdgeB
    obtain ⟨A, hA, hAeq⟩ := forwardInterior a' ha'
    obtain ⟨B, hB, hBeq⟩ := reverseInterior b' hb'
    refine ⟨⟨A, hA, ?_⟩, ⟨B, hB, ?_⟩⟩
    · rw [hAeq, hedgesEq]
      exact hEdgeA'
    · rw [hBeq, hedgesEq]
      exact hEdgeB'

end OpposingUnitInterface

theorem OpposingStringInterfacePath
    (C : BandCircle) (orientation : Bool) (base R S : ProtoTile)
    (hRS : R ≠ S)
    (hnadj : ¬ (if C.1.1.1 = 1 then
      ∃ v : GaussianInt,
        UnitTriangularStep orientation v ∧
        TileCentroid S - TileCentroid R = GaussianRealPoint v
      else TileTouching R S))
    (forward reverse : List ProtoTile)
    (hf : TileString C orientation base R S forward)
    (hr : TileString C orientation base S R reverse) :
    ∃ p : List GaussianInt,
      (∃ x, p.head? = some x ∧ x ∈ FootprintVertices R) ∧
      (∃ y, p.getLast? = some y ∧ y ∈ FootprintVertices S) ∧
      p.IsChain (fun x y =>
        y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) ∧
      (∀ x, x ∈ p →
        (∃ a ∈ (forward.drop 1).dropLast,
          x ∈ FootprintVertices a) ∧
        (∃ b ∈ (reverse.drop 1).dropLast,
          x ∈ FootprintVertices b)) ∧
      ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ x :: y :: l₂ →
          (∃ a ∈ (forward.drop 1).dropLast,
            {x, y} ∈ FootprintEdges a) ∧
          (∃ b ∈ (reverse.drop 1).dropLast,
            {x, y} ∈ FootprintEdges b) := by
-- BODY
  have hforward := hf
  have hreverse := hr
  rcases hf with ⟨hbase, hfhead, hflast, _, hfin, _, _⟩
  rcases hr with ⟨_, hrhead, hrlast, _, hrin, _, _⟩
  obtain ⟨a, b, hdet, ha, hb, hcoords, hcertificate, hfamily, hadj,
      hheight, htransport⟩ :=
    TileStringCoordinateTransport C orientation base hbase
  let tileAt : Int × Int → ProtoTile := fun z =>
    TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
  have hRfam : R ∈ RegularTileFamily base (TilingLattice C) := hfin R
      (OpposingInterfaceGeometry.hRmem R forward hfhead)
  have hSfam : S ∈ RegularTileFamily base (TilingLattice C) := by
    exact hfin S (OpposingInterfaceGeometry.hSmem S forward hflast)
  obtain ⟨r, hrcoord, hruniq⟩ := (hfamily R).mp hRfam
  obtain ⟨s, hscoord, hsuniq⟩ := (hfamily S).mp hSfam
  have hR : R = tileAt r := hrcoord
  have hS : S = tileAt s := hscoord
  obtain ⟨F, hF, _⟩ := (htransport R S forward r s hR hS).mp hforward
  obtain ⟨G, hG, _⟩ := (htransport S R reverse s r hS hR).mp hreverse
  rcases hF with ⟨hFtiles, hFstrip⟩
  rcases hG with ⟨hGtiles, hGstrip⟩
  have hrs := OpposingInterfaceGeometry.hrs base R S hRS a b r s hR hS
  have hnadjCoord := OpposingInterfaceGeometry.hnadjCoord C orientation base R S hnadj a b hadj r
      s hR hS
  have forall₂_dropLast {α β : Type} {Rel : α → β → Prop}
      {xs : List α} {ys : List β} (hall : List.Forall₂ Rel xs ys) :=
          OpposingInterfaceGeometry.forall₂_dropLast (α := α) (β := β) (Rel := Rel) (xs := xs)
          (ys := ys) hall
  have forall₂_interior :=
    forall₂_dropLast (List.forall₂_drop 1 hFtiles)
  have rfor₂_interior :=
    forall₂_dropLast (List.forall₂_drop 1 hGtiles)
  have forall₂_mem {α β : Type} {Rel : α → β → Prop}
      {xs : List α} {ys : List β} (hall : List.Forall₂ Rel xs ys) :=
          OpposingInterfaceGeometry.forall₂_mem (α := α) (β := β) (Rel := Rel) (xs := xs) (ys :=
          ys) hall
  have forwardInterior := OpposingInterfaceGeometry.forwardInterior base forward a b F
      forall₂_interior forall₂_mem
  have reverseInterior := OpposingInterfaceGeometry.reverseInterior base reverse a b G
      rfor₂_interior forall₂_mem
  rcases hcertificate with hunit | hnonunit
  · rcases hunit with ⟨hcurv, horient⟩
    obtain ⟨x, hcells⟩ :=
      CurvatureOneBandPrototileSingleton C base hcurv hbase
    rcases horient with ⟨horient, ha1, hb1⟩ | ⟨horient, haI, hbM⟩
    · have unrotatedInterface :
        ∃ p : List GaussianInt,
              (∃ x, p.head? = some x ∧ x ∈ FootprintVertices R) ∧
              (∃ y, p.getLast? = some y ∧ y ∈ FootprintVertices S) ∧
              p.IsChain (fun x y =>
                y = x + 1 ∨ y = x - 1 ∨
                y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) ∧
              (∀ x, x ∈ p →
                (∃ a ∈ (forward.drop 1).dropLast,
                  x ∈ FootprintVertices a) ∧
                (∃ b ∈ (reverse.drop 1).dropLast,
                  x ∈ FootprintVertices b)) ∧
              ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
                p = l₁ ++ x :: y :: l₂ →
                  (∃ a ∈ (forward.drop 1).dropLast,
                    {x, y} ∈ FootprintEdges a) ∧
                  (∃ b ∈ (reverse.drop 1).dropLast,
                    {x, y} ∈ FootprintEdges b) := OpposingUnitInterface.unrotatedInterface C
                        orientation base R S forward reverse a b hdet ha hb hcoords hfamily hadj
                        hheight htransport r hrcoord hruniq s hscoord hsuniq hR hS F G hFtiles
                        hFstrip hGtiles hGstrip hrs hnadjCoord forall₂_interior rfor₂_interior
                        forwardInterior reverseInterior x hcells ha1 hb1
      exact unrotatedInterface
    · subst a
      subst b
      let x0 : GaussianInt := ⟨x.im, -x.re - 1⟩
      have hx0 : GaussianQuarterTurn x0 - 1 = x := by
        ext <;> simp [x0, GaussianQuarterTurn]
      let unitAt : Int × Int → ProtoTile := fun z =>
        TileTranslation (⟨{x0}, x0⟩ : ProtoTile)
          (⟨z.1, z.2⟩ : GaussianInt)
      let turnedAt : Int × Int → ProtoTile := fun z => TileQuarterTurn (unitAt z)
      have hcellCalc := OpposingInterfaceGeometry.hcellCalc C base x hcells
      have hvertsEq (z : Int × Int) :
          FootprintVertices (tileAt z) = FootprintVertices (turnedAt z) :=
              OpposingInterfaceGeometry.hvertsEqAt314 base x hcellCalc z
      have hedgesEq (z : Int × Int) :
          FootprintEdges (tileAt z) = FootprintEdges (turnedAt z) :=
              OpposingInterfaceGeometry.hedgesEqAt322 base x hcellCalc z
      obtain ⟨p, hphead, hplast, hpchain, hpvertices, hpedges⟩ :=
        UnitSquareOpposingStripInterfacePath x0 r s hrs hnadjCoord F G
          hFstrip hGstrip
      let q := GaussianQuarterTurn
      let qInv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
      have hqInv (z : GaussianInt) : qInv (q z) = z := by
        ext <;> simp [qInv, q, GaussianQuarterTurn]
      have hqInv' (z : GaussianInt) : q (qInv z) = z := by
        ext <;> simp [qInv, q, GaussianQuarterTurn]
      have hqverts (z : Int × Int) :
          FootprintVertices (turnedAt z) = q '' FootprintVertices (unitAt z) :=
              OpposingInterfaceGeometry.hqverts x z
      have hqedges := OpposingInterfaceGeometry.hqedges x
      refine ⟨p.map q, ?_, ?_, (OpposingInterfaceGeometry.hqchain p hpchain
          (OpposingInterfaceGeometry.qstep C)), ?_, ?_⟩
      · rcases hphead with ⟨v, hv, hvU⟩
        have hvU' : v ∈ FootprintVertices (unitAt r) := by
          simpa [unitAt] using hvU
        refine ⟨q v, ?_, ?_⟩
        · simp [List.head?_map, hv]
        · rw [hR, hvertsEq, hqverts]
          exact Set.mem_image_of_mem q hvU'
      · rcases hplast with ⟨v, hv, hvU⟩
        have hvU' : v ∈ FootprintVertices (unitAt s) := by
          simpa [unitAt] using hvU
        refine ⟨q v, ?_, ?_⟩
        · simp [List.getLast?_map, hv]
        · rw [hS, hvertsEq, hqverts]
          exact Set.mem_image_of_mem q hvU'
      · intro v hv
        have hvp : ∃ u ∈ p, q u = v := by
          simpa [q] using (List.mem_map.mp hv)
        obtain ⟨u, hup, rfl⟩ := hvp
        obtain ⟨a', ha', hav⟩ := (hpvertices u hup).1
        obtain ⟨b', hb', hbv⟩ := (hpvertices u hup).2
        have hav' : u ∈ FootprintVertices (unitAt a') := by simpa [unitAt] using hav
        have hbv' : u ∈ FootprintVertices (unitAt b') := by simpa [unitAt] using hbv
        obtain ⟨A, hA, hAeq⟩ := forwardInterior a' ha'
        obtain ⟨B, hB, hBeq⟩ := reverseInterior b' hb'
        refine ⟨⟨A, hA, ?_⟩, ⟨B, hB, ?_⟩⟩
        · rw [hAeq, hvertsEq, hqverts]
          exact Set.mem_image_of_mem q hav'
        · rw [hBeq, hvertsEq, hqverts]
          exact Set.mem_image_of_mem q hbv'
      · intro v w l₁ l₂ hp
        have hpOrig := OpposingInterfaceGeometry.hpOrig p hqInv v w l₁ l₂ hp
        obtain ⟨a', ha', hEdgeA⟩ := hpedges (qInv v) (qInv w)
          (l₁.map qInv) (l₂.map qInv) hpOrig |>.1
        obtain ⟨b', hb', hEdgeB⟩ := hpedges (qInv v) (qInv w)
          (l₁.map qInv) (l₂.map qInv) hpOrig |>.2
        have hEdgeA' : {v, w} ∈ FootprintEdges (turnedAt a') :=
            OpposingInterfaceGeometry.hEdgeA'At404 x hqInv' hqedges v w a' hEdgeA
        have hEdgeB' : {v, w} ∈ FootprintEdges (turnedAt b') :=
            OpposingInterfaceGeometry.hEdgeB'At409 x hqInv' hqedges v w b' hEdgeB
        obtain ⟨A, hA, hAeq⟩ := forwardInterior a' ha'
        obtain ⟨B, hB, hBeq⟩ := reverseInterior b' hb'
        refine ⟨⟨A, hA, ?_⟩, ⟨B, hB, ?_⟩⟩
        · rw [hAeq, hedgesEq]
          exact hEdgeA'
        · rw [hBeq, hedgesEq]
          exact hEdgeB'
  · rcases hnonunit with ⟨hcurv, q, hq, hqC, hbasis⟩
    have hbaseQ : BandPrototile (q 0) base := by
      simpa [hqC] using hbase
    obtain ⟨faces, hfacesNe, hfirst, hlast, hfaceVertices, hfaceChain⟩ :=
      AffineOpposingStripCorridor r s hrs hnadjCoord F G hFstrip hGstrip
    obtain ⟨P, hPlattice, hPtiles, hPadj, hPposition, hPvertexReps,
        hPedgeReps, hPfaceReps, hchart⟩ :=
      BandRegularTranslatePeriodicComplex C q hq hqC base hbaseQ
    rcases hchart with ⟨chart⟩
    have finish {ι : Type} [DecidableEq ι] (PP : PeriodicTileComplex ι)
        (xi : Int × Int → ι) (faceAt : AffineTriangularFace → PP.plane.Face)
        (hadjXi : ∀ u v, TriangularLatticeAdjacent u v ↔
          PP.plane.adjacent (xi u) (xi v))
        (htileXi : ∀ z, PP.tile (xi z) = tileAt z)
        (hinjFace : Function.Injective faceAt)
        (hinc : ∀ f, (AffineTriangularFaceVertices f).image xi =
          {PP.plane.faceVertex (faceAt f) 0,
            PP.plane.faceVertex (faceAt f) 1,
            PP.plane.faceVertex (faceAt f) 2}) := OpposingInterfaceConclusion.finish base R S
                forward reverse a b r hrcoord hruniq s hscoord hsuniq hR hS F G hFstrip hGstrip
                hrs hnadjCoord forwardInterior reverseInterior faces hfacesNe hfirst hlast
                hfaceVertices hfaceChain (ι := ι) PP xi faceAt hadjXi htileXi hinjFace hinc
    rcases hbasis with hordered | hswapped
    · rcases hordered with ⟨haV, hbV⟩
      let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
        match f with
        | .up z => chart.up z
        | .down z => chart.down z
      have hadjXi (u v : Int × Int) : TriangularLatticeAdjacent u v ↔
          P.plane.adjacent (chart.vertexEquiv u) (chart.vertexEquiv v) :=
        (chart.adjacent_iff u v).symm
      have hinjFace := OpposingInterfaceGeometry.hinjFaceAt766 C base q P chart
      have hinc := OpposingInterfaceGeometry.hincAt777 C base q P chart
      exact finish P chart.vertexEquiv faceAt hadjXi (OpposingInterfaceGeometry.htileAlign C base
          a b q P chart haV hbV) hinjFace hinc
    · rcases hswapped with ⟨haV, hbV⟩
      have halign := SwappedAffineTriangularChartAlignment P base
        (BandVectors.1 (q 1) (q 0)) (BandVectors.1 (q 2) (q 0)) chart
      let xi := fun z : Int × Int =>
        chart.vertexEquiv (Prod.swap z)
      let faceAt : AffineTriangularFace → P.plane.Face := fun f =>
        match AffineTriangularFaceCoordinateSwap f with
        | .up z => chart.up z
        | .down z => chart.down z
      have hadjXi := OpposingInterfaceGeometry.hadjXiAt795 C base F q P chart halign
      have htileXi := OpposingInterfaceGeometry.htileXi C base a b F q P chart haV hbV halign
      have hinjFace := OpposingInterfaceGeometry.hinjFaceAt805 C base q P chart
      have hinc := OpposingInterfaceGeometry.hincAt826 C base F q P chart halign
      exact finish P xi faceAt hadjXi htileXi hinjFace hinc

end ApollonianSuperharmonic

end
