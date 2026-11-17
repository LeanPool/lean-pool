/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.P5253T1TopSquareContacts
public import LeanPool.ApollonianSuperharmonic.P5253T1LeftSquareContacts
public import LeanPool.ApollonianSuperharmonic.P5253T1BottomSquareContact
public import LeanPool.ApollonianSuperharmonic.P5253T1OneEdgeInterface
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: P5290T1UnitContactPaths]

/-!
# P5290T1UnitContactPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace UnitContactProof

private theorem makePath :
    ∀ (T : ProtoTile),
      ∀ (U : ProtoTile),
        ∀ (a : GaussianInt),
          ∀ (b : GaussianInt),
            Finset.Nonempty T.cells →
              Finset.Nonempty U.cells →
                Disjoint T.cells U.cells →
                  BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = { a, b } →
                    { a, b } ∈ BoundaryFootprintEdges T →
                      { a, b } ∈ BoundaryFootprintEdges U →
                        b = a + (1 : GaussianInt) ∨
                            b = a - (1 : GaussianInt) ∨
                            b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩ →
                          Finset.Nonempty T.cells ∧
                            Finset.Nonempty U.cells ∧
                            Disjoint T.cells U.cells ∧
                            SimpleGridPathBetween
                            (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
                            (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a b := by
  classical
  intro T U a b hT hU hd hv heT heU ha
  have interface := P5253T1OneEdgeInterface T U a b hT hU hd hv heT heU ha
  have hab : a ≠ b := by
    rcases ha with h | h | h | h <;>
      intro he <;> rw [← he] at h <;>
      have hr := congrArg Zsqrtd.re h <;>
      have hi := congrArg Zsqrtd.im h <;> simp at hr hi <;> omega
  have path : SimpleGridPathBetween
      (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
      (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a b := by
    refine ⟨[a, b], by simp [hab], by simp, by simp, by simp, ?_, ?_, ?_⟩
    · rw [hv]
      ext z
      simp
    · intro z w l₁ l₂ h
      have llen := congrArg List.length h
      simp only [List.length_cons, List.length_nil, List.length_append] at llen
      have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst l₁
      subst l₂
      simp only [List.nil_append, List.cons.injEq, and_true] at h
      rcases h with ⟨rfl, rfl⟩
      exact ha
    · intro e
      constructor
      · intro he
        have he' : e = {a, b} := by
          have : e ∈ ({{a, b}} : Set (Finset GaussianInt)) := by
            rw [← interface.1]
            exact he
          simpa using this
        subst e
        exact ⟨a, b, [], [], rfl, rfl⟩
      · rintro ⟨z, w, l₁, l₂, h, he⟩
        have llen := congrArg List.length h
        simp only [List.length_cons, List.length_nil, List.length_append] at llen
        have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
        have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst l₁
        subst l₂
        simp only [List.nil_append, List.cons.injEq, and_true] at h
        rcases h with ⟨rfl, rfl⟩
        subst e
        exact ⟨heT, heU⟩
  exact ⟨hT, hU, hd, path⟩

private theorem rightContact :
    ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt), ∀ (h : Int), (h = (k : Int) - 1 ∨ h = k) → (
    let D' := TileTranslation (DiamondTile k) u
      let c := u + (⟨(k : Int), h⟩ : GaussianInt)
      D'.cells.Nonempty ∧ Disjoint D'.cells {c} ∧
        BoundaryFootprintVertices D' ∩
            BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) = {c, c + ⟨0, 1⟩} ∧
        {c, c + ⟨0, 1⟩} ∈ BoundaryFootprintEdges D')) := by
  classical
  intro k hk u h hh
  classical
  dsimp only
  let D' := TileTranslation (DiamondTile k) u
  let c := u + (⟨(k : Int), h⟩ : GaussianInt)
  have cell (z : GaussianInt) : z ∈ D'.cells ↔
      0 ≤ (z - u).im ∧ (z - u).im < 2 * (k : Int) ∧
      -((z - u).im + 1) ≤ (z - u).re ∧ (z - u).re < (z - u).im + 1 ∧
      -(2 * (k : Int) - (z - u).im) ≤ (z - u).re ∧
        (z - u).re < 2 * (k : Int) - (z - u).im  := by
    exact (TileTranslationProperties.mem_cells (DiamondTile k) u z).trans
      (P4194T1DiamondCellRows k (z - u)).1
  have inside : c - 1 ∈ D'.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one]
    rcases hh with rfl | rfl <;> omega
  have outside : c ∉ D'.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    rcases hh with rfl | rfl <;> omega
  have hn : D'.cells.Nonempty := ⟨c - 1, inside⟩
  have edge : {c, c + ⟨0, 1⟩} ∈ BoundaryFootprintEdges D' := by
    refine ⟨c, Or.inr ⟨rfl, Or.inr ⟨outside, ?_⟩⟩⟩
    simpa using inside
  have no (v : GaussianInt) (hv : (v - u).re = (k : Int) + 1) :
      v ∉ BoundaryFootprintVertices D' := by
    simp only [Zsqrtd.re_sub] at hv
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.2.1]
    rintro ⟨w, hw, heq⟩
    have hwv : w = v - u := (eq_sub_iff_add_eq).mpr heq
    rw [hwv, (P4194T1DiamondVertexIncidence k hk (v - u)).2] at hw
    obtain ⟨⟨j, hj⟩, _⟩ := hw
    fin_cases j <;>
      simp only [LatticeVertexIncidentCell, (P4194T1DiamondCellRows _ _).1,
        ] at hj <;>
      norm_num at hj <;> omega
  have vertices : BoundaryFootprintVertices D' ∩
      BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) =
        {c, c + ⟨0, 1⟩} := by
    ext v
    rw [Set.mem_inter_iff, (P5253T1SingletonBoundary c c).1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · have hc : ((c + 1 - u).re : Int) = (k : Int) + 1 := by
          simp [c]
          ring
        exact False.elim (no _ hc hv)
      · exact Or.inr rfl
      · have hc : ((c + 1 + ⟨0, 1⟩ - u).re : Int) = (k : Int) + 1 := by
          simp [c]
          ring
        exact False.elim (no _ hc hv)
    · rintro (rfl | rfl)
      · have hb : c ∈ BoundaryFootprintVertices D' := by
          rw [BoundaryFootprintVertices, ite_eq_left hn]
          exact ⟨_, edge, by simp⟩
        exact ⟨hb, by simp⟩
      · have hb : c + ⟨0, 1⟩ ∈ BoundaryFootprintVertices D' := by
          rw [BoundaryFootprintVertices, ite_eq_left hn]
          exact ⟨_, edge, by simp⟩
        exact ⟨hb, by simp⟩
  exact ⟨hn, Finset.disjoint_singleton_right.mpr outside, vertices, edge⟩

private theorem singletonPath :
    (∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        (T.cells.Nonempty) → ((U.cells.Nonempty) → ((Disjoint T.cells U.cells) →
        ((BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = {a, b}) → (({a, b} ∈
        BoundaryFootprintEdges T) → (({a, b} ∈ BoundaryFootprintEdges U) → ((b = a + 1 ∨ b = a -
        1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint
        T.cells U.cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices T ∩
        BoundaryFootprintVertices U) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a
        b)))))))) → (∀ (T : ProtoTile), ∀ (c : GaussianInt), ∀ (a : GaussianInt), ∀ (b :
        GaussianInt), Finset.Nonempty T.cells → Disjoint T.cells {c} → BoundaryFootprintVertices
        T ∩ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) = {a, b} → {a, b} ∈
        BoundaryFootprintEdges T → {a, b} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile)
        → b = a + (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b
        = a - ⟨(0 : ℤ), (1 : ℤ)⟩ → Finset.Nonempty T.cells ∧ Finset.Nonempty (⟨{c}, c⟩ :
            ProtoTile).cells ∧ Disjoint T.cells (⟨{c}, c⟩ : ProtoTile).cells ∧
        SimpleGridPathBetween (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices (⟨{c}, c⟩
            : ProtoTile)) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges (⟨{c}, c⟩ :
            ProtoTile)) a b) := by
  classical
  intro makePath T c a b hT hd hv heT heU ha
  exact makePath T (⟨{c}, c⟩ : ProtoTile) a b hT (by simp) hd hv heT heU ha

private theorem hTop' :
    ∀ (k : Nat),
    let D := DiamondTile k
    let x0 : GaussianInt := ⟨0, 2 * (k : Int)⟩
    let y0 : GaussianInt := ⟨1, 2 * (k : Int)⟩
    (y0 = x0 + 1) → ((have D := TileTranslation (DiamondTile k) (0 : GaussianInt); have c := (0 :
        GaussianInt) + ⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩; have U := (⟨{c}, c⟩ : ProtoTile);
        Finset.Nonempty D.cells ∧ Disjoint D.cells U.cells ∧ BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices U = {c, c + (1 : GaussianInt)} ∧ {c, c + (1 : GaussianInt)} ∈
        BoundaryFootprintEdges D) → ((TileTranslation D 0 = D) → (D.cells.Nonempty ∧ Disjoint
        D.cells {x0} ∧ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (⟨{x0}, x0⟩ :
        ProtoTile) = {x0, y0} ∧ {x0, y0} ∈ BoundaryFootprintEdges D))) := by
  classical
  intro k D x0 y0 hxy hTop transZero
  have hc : (0 : GaussianInt) + ⟨0, 2 * (k : Int)⟩ = x0 := by
    ext <;> simp [x0]
  have hc1 :
      ((0 : GaussianInt) + ⟨0, 2 * (k : Int)⟩) + 1 = y0 := by
    ext <;> simp [y0]
  simpa [D, transZero, hc, hc1, hxy] using hTop

end UnitContactProof

private def unitContactConclusion (k : Nat) (i : Fin 3) : Prop :=
  let M := P5260T1PlacementLedger k i false
      let D := DiamondTile k
      let W := M.1.1
      let Z := M.1.2
      let x := M.2.2.1
      let y := M.2.2.2
      let d : GaussianInt := if i = 0 then ⟨0, 1⟩ else -1
      let rows : List (ProtoTile × ProtoTile × GaussianInt × GaussianInt) :=
        [(D, W, x, y), (D, W, y, x),
         (TileTranslation D M.2.1.1, W, x, x + d),
         (TileTranslation D M.2.1.2, W, y, y + d),
         (W, Z, y, y + d)]
      (∀ T U a c, (T, U, a, c) ∈ rows →
        T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
        SimpleGridPathBetween
          (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
          (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a c) ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices W = {x, y} ∧
      BoundaryFootprintVertices W ∩ BoundaryFootprintVertices Z = {y, y + d} ∧
      (i = 1 → Z.cells.Nonempty ∧ D.cells.Nonempty ∧ Disjoint Z.cells D.cells ∧
        SimpleGridPathBetween
          (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D)
          (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D) y (y + ⟨0, 1⟩))

private theorem zeroUnitContacts (k : Nat) (hk : 0 < k) (hk1 : 1 < k) :
    unitContactConclusion k 0 := by
  classical
  have makePath := UnitContactProof.makePath
  have rightContact := UnitContactProof.rightContact k hk
  have singletonPath := UnitContactProof.singletonPath makePath
  let M := P5260T1PlacementLedger k 0 false
  let D := DiamondTile k
  let W := M.1.1
  let Z := M.1.2
  let x := M.2.2.1
  let y := M.2.2.2
  let d : GaussianInt := if (0 : Fin 3) = 0 then ⟨0, 1⟩ else -1
  have hkPred : 0 < k - 1 := by omega
  let x0 : GaussianInt := ⟨0, 2 * (k : Int)⟩
  let y0 : GaussianInt := ⟨1, 2 * (k : Int)⟩
  have hxy : y0 = x0 + 1 := by
    ext <;> simp [x0, y0]
  have sqEdges (c : GaussianInt) :
      {c, c + 1} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
      {c, c + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
      {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩} ∈
        BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
      {c + 1, c + 1 + ⟨0, 1⟩} ∈
        BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    rw [(P5253T1SingletonBoundary c c).2]
    simp [Finset.pair_comm]
  have hTop := P5253T1TopSquareContacts k hk 0 0 (Or.inr rfl)
  have transZero : TileTranslation D 0 = D := by
    cases D with
    | mk cells anchor =>
      have hf : GaussianTranslation 0 = id := by
        funext z
        simp [GaussianTranslation]
      simp [TileTranslation, hf, Finset.image_id]
  have hTop' : D.cells.Nonempty ∧ Disjoint D.cells {x0} ∧
      BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices (⟨{x0}, x0⟩ : ProtoTile) = {x0, y0} ∧
      {x0, y0} ∈ BoundaryFootprintEdges D := UnitContactProof.hTop' k hxy hTop transZero
  have hTopPath := singletonPath D x0 x0 y0 hTop'.1 hTop'.2.1
    hTop'.2.2.1 hTop'.2.2.2 (sqEdges x0).1 (Or.inl hxy)
  have hTopPathRev := singletonPath D x0 y0 x0 hTop'.1 hTop'.2.1
    (by rw [hTop'.2.2.1]; ext z; simp [or_comm])
    (by simpa [Finset.pair_comm] using hTop'.2.2.2)
    (by simpa [Finset.pair_comm, hxy] using (sqEdges x0).1)
    (Or.inr (Or.inl (by rw [hxy]; abel)))
  let r : GaussianInt := ⟨-(k : Int), (k : Int) + 1⟩
  have hrc : r + ⟨(k : Int), (k : Int) - 1⟩ = x0 := by
    ext <;> simp [r, x0]; ring
  have hRight := rightContact r ((k : Int) - 1) (Or.inl rfl)
  have hRight' :
      (TileTranslation D r).cells.Nonempty ∧
      Disjoint (TileTranslation D r).cells {x0} ∧
      BoundaryFootprintVertices (TileTranslation D r) ∩
        BoundaryFootprintVertices (⟨{x0}, x0⟩ : ProtoTile) =
          {x0, x0 + ⟨0, 1⟩} ∧
      {x0, x0 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (TileTranslation D r) := by
    simpa [D, r, hrc] using hRight
  have hRightPath := singletonPath (TileTranslation D r) x0 x0
    (x0 + ⟨0, 1⟩) hRight'.1 hRight'.2.1 hRight'.2.2.1 hRight'.2.2.2
    (sqEdges x0).2.1 (Or.inr (Or.inr (Or.inl rfl)))
  let l : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
  have hlc : l + ⟨-(k : Int) - 1, (k : Int)⟩ = x0 := by
    ext <;> simp [l, x0]; ring
  have hLeft := P5253T1LeftSquareContacts k hk l (k : Int) (Or.inr rfl)
  have hLeft' :
      (TileTranslation D l).cells.Nonempty ∧
      Disjoint (TileTranslation D l).cells {x0} ∧
      BoundaryFootprintVertices (TileTranslation D l) ∩
        BoundaryFootprintVertices (⟨{x0}, x0⟩ : ProtoTile) =
          {y0, y0 + ⟨0, 1⟩} ∧
      {y0, y0 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (TileTranslation D l) := by
    simpa [D, l, hlc, hxy] using hLeft
  have hLeftPath := singletonPath (TileTranslation D l) x0 y0
    (y0 + ⟨0, 1⟩) hLeft'.1 hLeft'.2.1 hLeft'.2.2.1 hLeft'.2.2.2
    ((sqEdges x0).2.2.2) (Or.inr (Or.inr (Or.inl rfl)))
  let t : GaussianInt := ⟨(k : Int), (k : Int) + 1⟩
  have htc : t + ⟨-((k - 1 : Nat) : Int) - 1, ((k - 1 : Nat) : Int)⟩ = x0 := by
    ext <;> simp [t, x0] <;> omega
  have hPred := P5253T1LeftSquareContacts (k - 1) hkPred t
    ((k - 1 : Nat) : Int) (Or.inr rfl)
  have hPred' :
      (TileTranslation (DiamondTile (k - 1)) t).cells.Nonempty ∧
      Disjoint (TileTranslation (DiamondTile (k - 1)) t).cells {x0} ∧
      BoundaryFootprintVertices (TileTranslation (DiamondTile (k - 1)) t) ∩
        BoundaryFootprintVertices (⟨{x0}, x0⟩ : ProtoTile) =
          {y0, y0 + ⟨0, 1⟩} ∧
      {y0, y0 + ⟨0, 1⟩} ∈
        BoundaryFootprintEdges (TileTranslation (DiamondTile (k - 1)) t) := by
    simpa [t, htc, hxy] using hPred
  have hPredPath := makePath (⟨{x0}, x0⟩ : ProtoTile)
    (TileTranslation (DiamondTile (k - 1)) t) y0 (y0 + ⟨0, 1⟩)
    (by simp) hPred'.1 hPred'.2.1.symm
    (by rw [Set.inter_comm]; exact hPred'.2.2.1)
    (sqEdges x0).2.2.2 hPred'.2.2.2
    (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T U a b hmem
    simp only [P5260T1PlacementLedger, Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one,
        Nat.reduceAdd, P5124T1ParentModel, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, neg_mul, Zsqrtd.add_def, add_zero,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem | hmem
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, x0, y0] using hTopPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, x0, y0] using hTopPathRev
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, r, x0] using hRightPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, l, x0, y0] using hLeftPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [x0, y0, t] using hPredPath
  · simpa [M, W, Z, x, y, d, D, x0, y0, P5260T1PlacementLedger,
      P5124T1ParentModel] using hTop'.2.2.1
  · simpa [M, W, Z, x, y, d, t, x0, y0, P5260T1PlacementLedger,
      P5124T1ParentModel, Set.inter_comm] using hPred'.2.2.1
  · simp

private theorem singletonSquareEdges (c : GaussianInt) :
    {c, c + 1} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
    {c, c + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
    {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩} ∈
      BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) ∧
    {c + 1, c + 1 + ⟨0, 1⟩} ∈
      BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
  rw [(P5253T1SingletonBoundary c c).2]
  simp [Finset.pair_comm]

private abbrev tileTranslationZero := ApollonianSuperharmonic.TileTranslationProperties.zero

private theorem oneUnitContacts (k : Nat) (hk : 0 < k) :
    unitContactConclusion k 1 := by
  classical
  have makePath := UnitContactProof.makePath
  have singletonPath := UnitContactProof.singletonPath makePath
  let M := P5260T1PlacementLedger k 1 false
  let D := DiamondTile k
  let W := M.1.1
  let Z := M.1.2
  let x := M.2.2.1
  let y := M.2.2.2
  let d : GaussianInt := if (1 : Fin 3) = 0 then ⟨0, 1⟩ else -1
  have hW : W = (⟨{(⟨-(k : Int) - 1, (k : Int) - 1⟩ : GaussianInt)},
      ⟨-(k : Int) - 1, (k : Int) - 1⟩⟩ : ProtoTile) := by
    simp [W, M, P5260T1PlacementLedger, P5124T1ParentModel]
  have hZ : Z = (⟨{(⟨-(k : Int) - 1, (k : Int)⟩ : GaussianInt)},
      ⟨-(k : Int) - 1, (k : Int)⟩⟩ : ProtoTile) := by
    simp [Z, M, P5260T1PlacementLedger, P5124T1ParentModel]
  have hx : x = (⟨-(k : Int), (k : Int) - 1⟩ : GaussianInt) := by
    simp [x, M, P5260T1PlacementLedger]
  have hy : y = (⟨-(k : Int), (k : Int)⟩ : GaussianInt) := by
    simp [y, M, P5260T1PlacementLedger]
  let x1 : GaussianInt := ⟨-(k : Int), (k : Int) - 1⟩
  let y1 : GaussianInt := ⟨-(k : Int), (k : Int)⟩
  let c1 : GaussianInt := ⟨-(k : Int) - 1, (k : Int) - 1⟩
  have hxy : y1 = x1 + ⟨0, 1⟩ := by
    ext <;> simp [x1, y1]
  have sqEdges1 := singletonSquareEdges
  have transZero := tileTranslationZero D
  have hLeftDW := P5253T1LeftSquareContacts k hk 0
    ((k : Int) - 1) (Or.inl rfl)
  have hcLeft : (0 : GaussianInt) + ⟨-(k : Int) - 1,
      (k : Int) - 1⟩ = c1 := by
    ext <;> simp [c1]
  have hcLeft1 : c1 + 1 = x1 := by
    ext <;> simp [c1, x1]
  have hcLeft2 : c1 + 1 + ⟨0, 1⟩ = y1 := by
    ext <;> simp [c1, y1]
  have hLeftDW' : D.cells.Nonempty ∧ Disjoint D.cells {c1} ∧
      BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices (⟨{c1}, c1⟩ : ProtoTile) = {x1, y1} ∧
      {x1, y1} ∈ BoundaryFootprintEdges D := by
    simpa only [D, transZero, hcLeft, hcLeft1, hcLeft2, hxy] using hLeftDW
  have hDWPath := singletonPath D c1 x1 y1 hLeftDW'.1 hLeftDW'.2.1
    hLeftDW'.2.2.1 hLeftDW'.2.2.2
    (by simpa [hcLeft1, hcLeft2, hxy] using (sqEdges1 c1).2.2.2)
    (Or.inr (Or.inr (Or.inl hxy)))
  have hDWPathRev := singletonPath D c1 y1 x1 hLeftDW'.1 hLeftDW'.2.1
    (by rw [hLeftDW'.2.2.1]; ext z; simp [or_comm])
    (by simpa [Finset.pair_comm] using hLeftDW'.2.2.2)
    (by simpa [hcLeft1, hcLeft2, hxy, Finset.pair_comm] using (sqEdges1 c1).2.2.2)
    (Or.inr (Or.inr (Or.inr (by rw [hxy]; abel))))
  let r1 : GaussianInt := ⟨-(k : Int), -(k : Int) - 1⟩
  have hr1c : r1 + ⟨-1, 2 * (k : Int)⟩ = c1 := by
    ext <;> simp [r1, c1] <;> ring
  have hTopR := P5253T1TopSquareContacts k hk r1 (-1) (Or.inl rfl)
  have hTopRPair : ({c1, x1} : Set GaussianInt) = {x1, c1} := by
    ext z
    simp [or_comm]
  have hTopRFinsetPair : ({c1, x1} : Finset GaussianInt) = {x1, c1} := by
    ext z
    simp [or_comm]
  have hTopR' : (TileTranslation D r1).cells.Nonempty ∧
      Disjoint (TileTranslation D r1).cells {c1} ∧
      BoundaryFootprintVertices (TileTranslation D r1) ∩
        BoundaryFootprintVertices (⟨{c1}, c1⟩ : ProtoTile) = {x1, c1} ∧
      {x1, c1} ∈ BoundaryFootprintEdges (TileTranslation D r1) := by
    simpa [D, r1, hr1c, hcLeft1, hTopRPair, hTopRFinsetPair] using hTopR
  have hTopRPath := singletonPath (TileTranslation D r1) c1 x1 c1
    hTopR'.1 hTopR'.2.1 hTopR'.2.2.1 hTopR'.2.2.2
    (by simpa [hcLeft1, Finset.pair_comm] using (sqEdges1 c1).1)
    (Or.inr (Or.inl (by rw [← hcLeft1]; abel)))
  let l1 : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
  have hl1c : l1 - ⟨0, 1⟩ = c1 := by
    ext <;> simp [l1, c1]
  have hc1prev : c1 = x1 - 1 := by
    rw [← hcLeft1]
    abel
  have hxprevC1 : x1 - 1 = c1 := hc1prev.symm
  have hxaddC1 : x1 + (-1 : GaussianInt) = c1 := by
    simpa only [sub_eq_add_neg] using hxprevC1
  have hBottomL := P5253T1BottomSquareContact k hk l1
  have hBottomL' : (TileTranslation D l1).cells.Nonempty ∧
      Disjoint (TileTranslation D l1).cells {c1} ∧
      BoundaryFootprintVertices (TileTranslation D l1) ∩
        BoundaryFootprintVertices (⟨{c1}, c1⟩ : ProtoTile) =
          {y1 - 1, y1} ∧
      {y1 - 1, y1} ∈ BoundaryFootprintEdges (TileTranslation D l1) := by
    have hyedge : l1 = y1 - 1 := by
      ext <;> simp [l1, y1]
    have hcBottom : (y1 - 1) - ⟨0, 1⟩ = c1 := by
      ext <;> simp [c1, y1]
    simpa [D, l1, hl1c, hyedge, hcBottom] using hBottomL
  have hBottomPath := singletonPath (TileTranslation D l1) c1 y1 (y1 - 1)
    hBottomL'.1 hBottomL'.2.1
    (by calc
      _ = {y1 - 1, y1} := hBottomL'.2.2.1
      _ = {y1, y1 - 1} := by ext z; simp [or_comm])
    (by simpa [Finset.pair_comm] using hBottomL'.2.2.2)
    (by
      have hc1i : c1 + ⟨0, 1⟩ = y1 - 1 := by
        ext <;> simp [c1, y1]
      have hc1i1 : c1 + 1 + ⟨0, 1⟩ = y1 := hcLeft2
      simpa [hc1i, hc1i1, Finset.pair_comm] using (sqEdges1 c1).2.2.1)
    (Or.inr (Or.inl rfl))
  have c1ne : c1 ≠ c1 + ⟨0, 1⟩ := by
    intro h
    have hi := congrArg Zsqrtd.im h
    simp [c1] at hi
  have hPairDisj : Disjoint ({c1} : Finset GaussianInt) {c1 + ⟨0, 1⟩} := by
    exact Finset.disjoint_singleton.mpr c1ne
  have hPairVertices :
      BoundaryFootprintVertices (⟨{c1}, c1⟩ : ProtoTile) ∩
        BoundaryFootprintVertices (⟨{c1 + ⟨0, 1⟩}, c1 + ⟨0, 1⟩⟩ : ProtoTile) =
          {y1 - 1, y1} := by
    rw [(P5253T1SingletonBoundary c1 c1).1,
      (P5253T1SingletonBoundary (c1 + ⟨0, 1⟩) (c1 + ⟨0, 1⟩)).1]
    ext z
    rcases z with ⟨a, b⟩
    simp [c1, y1, Set.mem_insert_iff, Set.mem_singleton_iff,
      Zsqrtd.ext_iff]; omega
  have hPairSwap : ({y1 - 1, y1} : Set GaussianInt) = {y1, y1 - 1} := by
    ext z
    simp [or_comm]
  have hPairEdgeLeft : {y1 - 1, y1} ∈
      BoundaryFootprintEdges (⟨{c1}, c1⟩ : ProtoTile) := by
    have hc1i : c1 + ⟨0, 1⟩ = y1 - 1 := by
      ext <;> simp [c1, y1]
    have hc1i1 : c1 + 1 + ⟨0, 1⟩ = y1 := by
      ext <;> simp [c1, y1]
    simpa [hc1i, hc1i1, Finset.pair_comm] using (sqEdges1 c1).2.2.1
  have hPairEdgeRight : {y1 - 1, y1} ∈
      BoundaryFootprintEdges (⟨{c1 + ⟨0, 1⟩}, c1 + ⟨0, 1⟩⟩ : ProtoTile) := by
    have hc1i : c1 + ⟨0, 1⟩ + 1 = y1 := by
      ext <;> simp [c1, y1]
    have hc1i' : c1 + ⟨0, 1⟩ = y1 - 1 := by
      ext <;> simp [c1, y1]
    simpa [hc1i, hc1i', Finset.pair_comm] using
      (sqEdges1 (c1 + ⟨0, 1⟩)).1
  have hPairPath := makePath (⟨{c1}, c1⟩ : ProtoTile)
    (⟨{c1 + ⟨0, 1⟩}, c1 + ⟨0, 1⟩⟩ : ProtoTile) y1 (y1 - 1)
    (by simp) (by simp) hPairDisj
    (by calc
      _ = {y1 - 1, y1} := hPairVertices
      _ = {y1, y1 - 1} := by ext z; simp [or_comm])
    (by simpa [Finset.pair_comm] using hPairEdgeLeft)
    (by simpa [Finset.pair_comm] using hPairEdgeRight)
    (Or.inr (Or.inl rfl))
  let z1 : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
  have hPairBaseCoord :
      (⟨-(k : Int) - 1, (k : Int) - 1⟩ : GaussianInt) + ⟨0, 1⟩ =
        ⟨-(k : Int) - 1, (k : Int)⟩ := by
    ext <;> simp
  have hLeftZD := P5253T1LeftSquareContacts k hk 0 (k : Int) (Or.inr rfl)
  have hz1a : z1 + 1 = y1 := by
    ext <;> simp [z1, y1]
  have hz1b : z1 + 1 + ⟨0, 1⟩ = y1 + ⟨0, 1⟩ := by
    rw [hz1a]
  have hLeftZD' : D.cells.Nonempty ∧ Disjoint D.cells {z1} ∧
      BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices (⟨{z1}, z1⟩ : ProtoTile) =
          {y1, y1 + ⟨0, 1⟩} ∧
      {y1, y1 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges D := by
    simpa [D, transZero, z1, y1, hz1a, hz1b, hx, hy] using hLeftZD
  have hZDPath := makePath (⟨{z1}, z1⟩ : ProtoTile) D y1
    (y1 + ⟨0, 1⟩) (by simp) hLeftZD'.1 hLeftZD'.2.1.symm
    (by rw [Set.inter_comm]; exact hLeftZD'.2.2.1)
    (by simpa [z1, y1, hz1a, hz1b, Finset.pair_comm] using (sqEdges1 z1).2.2.2)
    hLeftZD'.2.2.2
    (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T U a b hmem
    simp only [P5260T1PlacementLedger, Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one,
        Nat.reduceAdd, P5124T1ParentModel, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, neg_mul, Fin.reduceEq, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem | hmem
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, c1, x1, y1] using hDWPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [D, c1, x1, y1] using hDWPathRev
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa only [D, r1, c1, x1, hxaddC1] using hTopRPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa only [D, l1, c1, y1, sub_eq_add_neg] using hBottomPath
    · rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
      simpa [c1, y1, hPairBaseCoord, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hPairPath
  · simpa [M, W, Z, x, y, d, D, c1, x1, y1,
      P5260T1PlacementLedger, P5124T1ParentModel] using hLeftDW'.2.2.1
  · change BoundaryFootprintVertices W ∩ BoundaryFootprintVertices Z = {y, y + d}
    simpa [hW, hZ, hy, d, c1, y1, hPairBaseCoord, sub_eq_add_neg] using
      hPairVertices.trans hPairSwap
  · intro _
    simpa [M, W, Z, x, y, d, D, z1, y1, P5260T1PlacementLedger,
      P5124T1ParentModel] using hZDPath

theorem P5290T1UnitContactPaths (k : Nat) (hk : 0 < k)
    (i : Fin 3) (hi : i ≠ 2) (hreg : 1 < k ∨ i = 1) :
    let M := P5260T1PlacementLedger k i false
    let D := DiamondTile k
    let W := M.1.1
    let Z := M.1.2
    let x := M.2.2.1
    let y := M.2.2.2
    let d : GaussianInt := if i = 0 then ⟨0, 1⟩ else -1
    let rows : List (ProtoTile × ProtoTile × GaussianInt × GaussianInt) :=
      [(D, W, x, y), (D, W, y, x),
       (TileTranslation D M.2.1.1, W, x, x + d),
       (TileTranslation D M.2.1.2, W, y, y + d),
       (W, Z, y, y + d)]
    (∀ T U a c, (T, U, a, c) ∈ rows →
      T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
      SimpleGridPathBetween
        (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
        (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a c) ∧
    BoundaryFootprintVertices D ∩ BoundaryFootprintVertices W = {x, y} ∧
    BoundaryFootprintVertices W ∩ BoundaryFootprintVertices Z = {y, y + d} ∧
    (i = 1 → Z.cells.Nonempty ∧ D.cells.Nonempty ∧ Disjoint Z.cells D.cells ∧
      SimpleGridPathBetween
        (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D)
        (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D) y (y + ⟨0, 1⟩)) := by
-- BODY
  change unitContactConclusion k i
  have hi01 : i = 0 ∨ i = 1 := by
    fin_cases i <;> simp_all
  rcases hi01 with h0 | h1
  · subst i
    apply zeroUnitContacts k hk
    rcases hreg with h | h
    · exact h
    · cases h
  · subst i
    exact oneUnitContacts k hk

end ApollonianSuperharmonic

end
