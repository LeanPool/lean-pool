/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance

-- [TABLET NODE: TileStringCentralCovariance]

/-!
# TileStringCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CentralStringProof

private theorem band_transform :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        (∀ T : ProtoTile, TileCentroid (transform T) = (-(TileCentroid T).1 + (u.re : Real),
        -(TileCentroid T).2 + (u.im : Real))) → ((∀ T : ProtoTile, FootprintVertices (transform
        T) = GaussianTranslation u '' ((fun x : GaussianInt => -x) '' FootprintVertices T)) → (∀
            (D : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile D T → BandPrototile D
        (transform T))) ) := by
  classical
  intro u transform centroid_transform footprint_transform D T hT
  induction hT with
  | line w x hw =>
      apply BandPrototile.line
      exact hw
  | unit z x =>
      apply BandPrototile.unit
  | @decompose q hq S T hS hcells hfoot hcentroid ih =>
      let R : Fin 3 → Bool → ProtoTile :=
        fun i s => transform (S i (!s))
      have hR : ∀ i s, BandPrototile (q i.succ) (R i s) := by
        intro i s
        exact ih i (!s)
      apply BandPrototile.decompose hq hR
      · intro x
        constructor
        · intro hx
          dsimp [transform, TileTranslation, TileHalfTurn] at hx
          rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
          rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
          rcases (hcells y).mp hy with ⟨i, s, hs⟩
          refine ⟨i, !s, ?_⟩
          dsimp [R]
          simp only [Bool.not_not]
          change GaussianTranslation u (-y - 1 - ⟨0, 1⟩) ∈
            (transform (S i s)).cells
          exact Finset.mem_image.mpr ⟨-y - 1 - ⟨0, 1⟩,
            Finset.mem_image.mpr ⟨y, hs, rfl⟩, rfl⟩
        · rintro ⟨i, s, hs⟩
          have hs' : x ∈ (transform (S i (!s))).cells := hs
          have hx' : x ∈ (transform T).cells := by
            dsimp [transform, TileTranslation, TileHalfTurn]
            rcases Finset.mem_image.mp hs' with ⟨z, hz, heq⟩
            rcases Finset.mem_image.mp hz with ⟨y, hy, heq'⟩
            exact Finset.mem_image.mpr ⟨z,
              Finset.mem_image.mpr ⟨y, (hcells y).mpr ⟨i, !s, hy⟩, heq'⟩,
              heq⟩
          exact hx'
      · intro i s
        rw [footprint_transform, footprint_transform]
        intro x hx
        rcases hx with ⟨y, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨-v, ⟨v, hfoot i (!s) hv, rfl⟩, rfl⟩
      · intro i s
        have hp := hcentroid i (!s)
        rw [centroid_transform, centroid_transform]
        have hfirst := congrArg Prod.fst hp
        have hsecond := congrArg Prod.snd hp
        have hsign :
            (if (!s) = true then (1 : Real) else -1) =
              -(if s = true then (1 : Real) else -1) := by
          cases s <;> norm_num
        rw [hsign] at hfirst hsecond
        dsimp [R]
        dsimp [GaussianRealPoint] at hfirst hsecond ⊢
        ring_nf at hfirst hsecond ⊢
        apply Prod.ext
        all_goals try dsimp at *
        all_goals linarith

private theorem transform_translate :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        ∀ (T : ProtoTile), ∀ (v : GaussianInt), transform (TileTranslation T v) = TileTranslation
        (transform T) (-v) ) := by
  classical
  intro u transform T v
  cases T with
  | mk cells anchor =>
    rw [ProtoTile.mk.injEq]
    constructor
    · ext x
      simp only [TileTranslation, TileHalfTurn, Int.reduceNeg, GaussianTranslation,
          Finset.image_image, Finset.image_nonempty, neg_add_rev, Finset.mem_image,
          Function.comp_apply, transform]
      constructor
      · rintro ⟨a, ha, heq⟩
        refine ⟨a, ha, ?_⟩
        calc
          -a - 1 - ⟨0, 1⟩ + u + -v = -v + -a - 1 - ⟨0, 1⟩ + u := by abel
          _ = x := heq
      · rintro ⟨a, ha, heq⟩
        refine ⟨a, ha, ?_⟩
        calc
          -v + -a - 1 - ⟨0, 1⟩ + u = -a - 1 - ⟨0, 1⟩ + u + -v := by abel
          _ = x := heq
    · simp [transform, TileTranslation, TileHalfTurn, GaussianTranslation]; split <;> abel

private theorem transform_involutive :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        (∀ (T : ProtoTile), ∀ (v : GaussianInt), transform (TileTranslation T v) = TileTranslation
        (transform T) (-v)) → (∀ T : ProtoTile, transform (transform T) = T) ) := by
  classical
  intro u transform transform_translate T
  have h := transform_translate (TileHalfTurn T) u
  dsimp [transform] at h ⊢
  rw [(TileHalfTurnFormulas T).2.2.2.1] at h
  have cancel : TileTranslation (TileTranslation T u) (-u) = T := by
    cases T with
    | mk cells anchor =>
        rw [ProtoTile.mk.injEq]
        constructor
        · ext x
          simp [TileTranslation, GaussianTranslation, Finset.image_image]
        · simp [TileTranslation, GaussianTranslation]
  exact h.trans cancel

private theorem touch_same_cells :
    (by
      classical
      exact
        ∀ A B A' B' : ProtoTile, A.cells = A'.cells → B.cells = B'.cells → A.cells.Nonempty →
        B.cells.Nonempty → (TileTouching A B ↔ TileTouching A' B') ) := by
  classical
  intro A B A' B' hA hB ha hb
  have eA : BoundaryFootprintEdges A = BoundaryFootprintEdges A' := by
    ext e
    simp [BoundaryFootprintEdges, hA]
  have ha' : A'.cells.Nonempty := hA ▸ ha
  have eB : BoundaryFootprintEdges B = BoundaryFootprintEdges B' := by
    ext e
    simp [BoundaryFootprintEdges, hB]
  have hb' : B'.cells.Nonempty := hB ▸ hb
  have haEmpty : A'.cells ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ha'
  have hbEmpty : B'.cells ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hb'
  unfold TileTouching
  simp only [BoundaryFootprintVertices, ite_eq_left ha, ite_eq_left hb,
    ite_eq_left ha', ite_eq_left hb']
  rw [hA, hB, eA, eB]
  simp [haEmpty, hbEmpty]

private theorem touch_same_left :
    (by
      classical
      exact
        ∀ A A' B : ProtoTile, A.cells = A'.cells → A.cells.Nonempty → (TileTouching A B ↔
        TileTouching A' B) ) := by
  classical
  intro A A' B hA ha
  have eA : BoundaryFootprintEdges A = BoundaryFootprintEdges A' := by
    ext e
    simp [BoundaryFootprintEdges, hA]
  have ha' : A'.cells.Nonempty := hA ▸ ha
  have haEmpty : A'.cells ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ha'
  unfold TileTouching
  simp only [BoundaryFootprintVertices, ite_eq_left ha, ite_eq_left ha']
  rw [hA, eA]
  simp [haEmpty]

private theorem touch_same_right :
    (by
      classical
      exact
        ∀ A B B' : ProtoTile, B.cells = B'.cells → B.cells.Nonempty → (TileTouching A B ↔
        TileTouching A B') ) := by
  classical
  intro A B B' hB hb
  have eB : BoundaryFootprintEdges B = BoundaryFootprintEdges B' := by
    ext e
    simp [BoundaryFootprintEdges, hB]
  have hb' : B'.cells.Nonempty := hB ▸ hb
  have hbEmpty : B'.cells ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hb'
  unfold TileTouching
  simp only [BoundaryFootprintVertices, ite_eq_left hb, ite_eq_left hb']
  rw [hB, eB]
  simp [hbEmpty]

private theorem touching_half_quarter :
    (by
      classical
      exact
        (∀ A B A' B' : ProtoTile, A.cells = A'.cells → B.cells = B'.cells → A.cells.Nonempty →
        B.cells.Nonempty → (TileTouching A B ↔ TileTouching A' B')) → ((∀ A A' B : ProtoTile,
        A.cells = A'.cells → A.cells.Nonempty → (TileTouching A B ↔ TileTouching A' B)) → ((∀ A B
        B' : ProtoTile, B.cells = B'.cells → B.cells.Nonempty → (TileTouching A B ↔ TileTouching
        A B')) → ((∀ T : ProtoTile, T.cells.Nonempty → (TileHalfTurn T).cells.Nonempty) → (∀ A B
        : ProtoTile, TileTouching (TileHalfTurn A) (TileHalfTurn B) ↔ TileTouching
        (TileQuarterTurn (TileQuarterTurn A)) (TileQuarterTurn (TileQuarterTurn B)))))) ) := by
  classical
  intro touch_same_cells touch_same_left touch_same_right half_nonempty A B
  by_cases ha : A.cells.Nonempty
  · by_cases hb : B.cells.Nonempty
    · exact touch_same_cells (TileHalfTurn A) (TileHalfTurn B)
        (TileQuarterTurn (TileQuarterTurn A))
        (TileQuarterTurn (TileQuarterTurn B))
        (TileHalfTurnFormulas A).2.2.2.2.1
        (TileHalfTurnFormulas B).2.2.2.2.1
        (half_nonempty A ha) (half_nonempty B hb)
    · have eb : B.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      rw [(TileHalfTurnFormulas B).2.2.2.2.2.2.2.2 eb]
      exact touch_same_left (TileHalfTurn A)
        (TileQuarterTurn (TileQuarterTurn A))
        (TileQuarterTurn (TileQuarterTurn B))
        (TileHalfTurnFormulas A).2.2.2.2.1
        (half_nonempty A ha)
  · have ea : A.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    rw [(TileHalfTurnFormulas A).2.2.2.2.2.2.2.2 ea]
    by_cases hb : B.cells.Nonempty
    · exact touch_same_right (TileQuarterTurn (TileQuarterTurn A))
        (TileHalfTurn B) (TileQuarterTurn (TileQuarterTurn B))
        (TileHalfTurnFormulas B).2.2.2.2.1
        (half_nonempty B hb)
    · have eb : B.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      rw [(TileHalfTurnFormulas B).2.2.2.2.2.2.2.2 eb]

private theorem adjacent_cov :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S
            : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (u : GaussianInt), (
        let adjacent := fun (T U :
        ProtoTile) => if C.1.1.1 = (1 : ℤ) then ∃ (v :
        GaussianInt), UnitTriangularStep orientation v ∧ TileCentroid U - TileCentroid T =
        GaussianRealPoint v else TileTouching T U;
        let height := fun (T : ProtoTile) =>
        ((TileCentroid T).2 - (TileCentroid R).2) * ((TileCentroid S).1 - (TileCentroid R).1) -
        ((TileCentroid T).1 - (TileCentroid R).1) * ((TileCentroid S).2 - (TileCentroid R).2);
        BandPrototile C.1.1 base ∧ tiles.head? = some
        R ∧ tiles.getLast? = some S ∧ List.Pairwise (fun (T U : ProtoTile) => T ≠ U) tiles ∧ (∀ T
        ∈ tiles, T ∈ RegularTileFamily base (TilingLattice C)) ∧ List.IsChain adjacent tiles ∧ ∀
            (pre : List ProtoTile), ∀ (T : ProtoTile), ∀ (post : List ProtoTile), tiles = pre ++
            T ::
        post → pre ≠ [] → post ≠ [] → (0 : ℝ) ≤ height T ∧ ∃ U ∈ RegularTileFamily base
        (TilingLattice C), adjacent T U ∧ height U < (0 : ℝ)) → (
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        (∀ T : ProtoTile, TileCentroid (transform T) = (-(TileCentroid T).1 + (u.re : Real),
        -(TileCentroid T).2 + (u.im : Real))) → ((∀ A B : ProtoTile, TileTouching (TileHalfTurn
        A) (TileHalfTurn B) ↔ TileTouching (TileQuarterTurn (TileQuarterTurn A)) (TileQuarterTurn
        (TileQuarterTurn B))) → (∀ A B : ProtoTile, (if C.1.1.1 = 1 then ∃ v : GaussianInt,
        UnitTriangularStep orientation v ∧ TileCentroid B - TileCentroid A = GaussianRealPoint v
        else TileTouching A B) ↔ (if C.1.1.1 = 1 then ∃ v : GaussianInt, UnitTriangularStep
        orientation v ∧ TileCentroid (transform B) - TileCentroid (transform A) =
        GaussianRealPoint v else TileTouching (transform A) (transform B))))) ) := by
  classical
  intro C orientation base R S tiles u hstring transform centroid_transform touching_half_quarter
      A B
  by_cases hc : C.1.1.1 = 1
  · simp only [hc, ↓reduceIte]
    constructor
    · rintro ⟨v, hv, he⟩
      refine ⟨-v, ?_, ?_⟩
      · cases orientation <;> simp [UnitTriangularStep] at hv ⊢ <;> aesop
      · rw [centroid_transform, centroid_transform]
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        dsimp [GaussianRealPoint] at hx hy ⊢
        norm_num at hx hy ⊢
        exact ⟨by linarith [hx], by linarith [hy]⟩
    · rintro ⟨v, hv, he⟩
      refine ⟨-v, ?_, ?_⟩
      · cases orientation <;> simp [UnitTriangularStep] at hv ⊢ <;> aesop
      · rw [centroid_transform, centroid_transform] at he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        dsimp [GaussianRealPoint] at hx hy ⊢
        norm_num at hx hy ⊢
        apply Prod.ext <;> dsimp <;> linarith [hx, hy]
  · simp only [hc, ↓reduceIte]
    have hfirst := (TileTouchingCovariance A B 0).2.1
    have hsecond := (TileTouchingCovariance (TileQuarterTurn A)
      (TileQuarterTurn B) 0).2.1
    have hthird := (TileTouchingCovariance (TileHalfTurn A)
      (TileHalfTurn B) u).1
    rw [touching_half_quarter A B] at hthird
    simpa [transform] using (hfirst.trans hsecond |>.trans hthird)

private theorem map_decompose :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        ∀ xs, ∀ pre, ∀ x, ∀ post, xs.map transform = pre ++ x :: post → ∃ pre₀ y post₀, xs = pre₀ ++
        y :: post₀ ∧ pre = pre₀.map transform ∧ x = transform y ∧ post = post₀.map transform ) := by
  classical
  intro u transform xs
  induction xs with
  | nil => intro pre x post h; simp at h
  | cons a xs ih =>
    intro pre x post h
    cases pre with
    | nil =>
      injection h with hx hp
      exact ⟨[], a, xs, rfl, rfl, hx.symm, hp.symm⟩
    | cons p pre =>
      simp only [List.map_cons, List.cons_append] at h
      injection h with hp hr
      subst p
      rcases ih pre x post hr with ⟨pre₀, y, post₀, hs, hpre, hx, hpost⟩
      refine ⟨a :: pre₀, y, post₀, ?_, ?_, hx, hpost⟩
      · simp [hs]
      · simp [hpre]

private theorem height_transform :
    (by
      classical
      exact
        ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (u : GaussianInt),
        let transform : ProtoTile → ProtoTile :=
        fun T => TileTranslation (TileHalfTurn T) u
        (∀ T : ProtoTile, TileCentroid (transform T) = (-(TileCentroid T).1 + (u.re : Real),
        -(TileCentroid T).2 + (u.im : Real))) → (∀ T : ProtoTile, ((TileCentroid (transform T)).2
        - (TileCentroid (transform R)).2) * ((TileCentroid (transform S)).1 - (TileCentroid
        (transform R)).1) - ((TileCentroid (transform T)).1 - (TileCentroid (transform R)).1) *
        ((TileCentroid (transform S)).2 - (TileCentroid (transform R)).2) = ((TileCentroid T).2 -
        (TileCentroid R).2) * ((TileCentroid S).1 - (TileCentroid R).1) - ((TileCentroid T).1 -
        (TileCentroid R).1) * ((TileCentroid S).2 - (TileCentroid R).2)) ) := by
  classical
  intro R S u transform centroid_transform T
  rw [centroid_transform, centroid_transform, centroid_transform]
  ring

end CentralStringProof

theorem TileStringCentralCovariance
    (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile) (tiles : List ProtoTile) (u : GaussianInt)
    (hstring : TileString C orientation base R S tiles) :
    TileString C orientation
      (TileTranslation (TileHalfTurn base) u)
      (TileTranslation (TileHalfTurn R) u)
      (TileTranslation (TileHalfTurn S) u)
      (tiles.map (fun T => TileTranslation (TileHalfTurn T) u)) := by
-- BODY
  unfold TileString at hstring ⊢
  let transform : ProtoTile → ProtoTile :=
    fun T => TileTranslation (TileHalfTurn T) u
  change BandPrototile C.1.1 (transform base) ∧ _
  have centroid_transform : ∀ T : ProtoTile,
      TileCentroid (transform T) =
        (-(TileCentroid T).1 + (u.re : Real),
         -(TileCentroid T).2 + (u.im : Real)) := by
    intro T
    dsimp [transform]
    rw [(TileTranslationFormulas (TileHalfTurn T) u).2.2.2.2.1,
      (TileHalfTurnFormulas T).2.2.2.2.2.2.2.1]
  have footprint_transform : ∀ T : ProtoTile,
      FootprintVertices (transform T) =
        GaussianTranslation u '' ((fun x : GaussianInt => -x) ''
          FootprintVertices T) := by
    intro T
    dsimp [transform]
    rw [(TileTranslationFormulas (TileHalfTurn T) u).2.2.2.2.2.1,
      (TileHalfTurnFormulas T).2.2.2.2.2.2.1]
  have band_transform : ∀ (D : CircleCoordinates) (T : ProtoTile),
      BandPrototile D T → BandPrototile D (transform T) := CentralStringProof.band_transform u
          centroid_transform footprint_transform
  have transform_translate : ∀ (T : ProtoTile) (v : GaussianInt),
      transform (TileTranslation T v) = TileTranslation (transform T) (-v) :=
          CentralStringProof.transform_translate u
  have transform_involutive : ∀ T : ProtoTile, transform (transform T) = T :=
      CentralStringProof.transform_involutive u transform_translate
  have transform_injective : Function.Injective transform := by
    intro A B hab
    have := congrArg transform hab
    simpa [transform_involutive] using this
  have touch_same_cells : ∀ A B A' B' : ProtoTile,
      A.cells = A'.cells → B.cells = B'.cells →
      A.cells.Nonempty → B.cells.Nonempty →
      (TileTouching A B ↔ TileTouching A' B') := CentralStringProof.touch_same_cells
  have touch_same_left : ∀ A A' B : ProtoTile,
      A.cells = A'.cells → A.cells.Nonempty →
      (TileTouching A B ↔ TileTouching A' B) := CentralStringProof.touch_same_left
  have touch_same_right : ∀ A B B' : ProtoTile,
      B.cells = B'.cells → B.cells.Nonempty →
      (TileTouching A B ↔ TileTouching A B') := CentralStringProof.touch_same_right
  have half_nonempty : ∀ T : ProtoTile, T.cells.Nonempty →
      (TileHalfTurn T).cells.Nonempty := by
    intro T hT
    rw [(TileHalfTurnFormulas T).1]
    exact Finset.image_nonempty.mpr hT
  have touching_half_quarter : ∀ A B : ProtoTile,
      TileTouching (TileHalfTurn A) (TileHalfTurn B) ↔
        TileTouching (TileQuarterTurn (TileQuarterTurn A))
          (TileQuarterTurn (TileQuarterTurn B)) := CentralStringProof.touching_half_quarter
              touch_same_cells touch_same_left touch_same_right half_nonempty
  have adjacent_cov : ∀ A B : ProtoTile,
      (if C.1.1.1 = 1 then
        ∃ v : GaussianInt,
          UnitTriangularStep orientation v ∧
          TileCentroid B - TileCentroid A = GaussianRealPoint v
       else TileTouching A B) ↔
      (if C.1.1.1 = 1 then
        ∃ v : GaussianInt,
          UnitTriangularStep orientation v ∧
          TileCentroid (transform B) - TileCentroid (transform A) =
            GaussianRealPoint v
       else TileTouching (transform A) (transform B)) := CentralStringProof.adjacent_cov C
           orientation base R S tiles u hstring centroid_transform touching_half_quarter
  rcases hstring with ⟨hbase, hhead, hlast, hpair, hreg, hchain, hbelow⟩
  have map_decompose : ∀ xs pre x post,
      xs.map transform = pre ++ x :: post →
      ∃ pre₀ y post₀, xs = pre₀ ++ y :: post₀ ∧
        pre = pre₀.map transform ∧ x = transform y ∧ post = post₀.map transform :=
            CentralStringProof.map_decompose u
  have height_transform : ∀ T : ProtoTile,
      ((TileCentroid (transform T)).2 - (TileCentroid (transform R)).2) *
          ((TileCentroid (transform S)).1 - (TileCentroid (transform R)).1) -
        ((TileCentroid (transform T)).1 - (TileCentroid (transform R)).1) *
          ((TileCentroid (transform S)).2 - (TileCentroid (transform R)).2) =
      ((TileCentroid T).2 - (TileCentroid R).2) *
          ((TileCentroid S).1 - (TileCentroid R).1) -
        ((TileCentroid T).1 - (TileCentroid R).1) *
          ((TileCentroid S).2 - (TileCentroid R).2) := CentralStringProof.height_transform R S u
              centroid_transform
  refine ⟨band_transform C.1.1 base hbase, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, hhead]
    rfl
  · rw [List.getLast?_map, hlast]
    rfl
  · rw [List.pairwise_map]
    exact hpair.imp (fun hab heq => hab (transform_injective heq))
  · intro V hV
    rcases List.mem_map.mp hV with ⟨T, hT, rfl⟩
    rcases hreg T hT with ⟨v, hv, rfl⟩
    refine ⟨-v, (TilingLattice C).neg_mem hv, transform_translate base v⟩
  · revert hchain
    clear hhead hlast hpair hreg hbelow hbase
    induction tiles with
    | nil => intro h; exact .nil
    | cons first rest ih =>
      cases rest with
      | nil => intro h; exact .singleton _
      | cons second tail =>
        intro h
        cases h with
        | cons_cons edge remaining =>
          exact .cons_cons (adjacent_cov first second |>.mp edge) (ih remaining)
  · intro pre T post hsplit hpre hpost
    rcases map_decompose tiles pre T post hsplit with
      ⟨pre₀, V, post₀, hdecomp, hpreeq, hTeq, hposteq⟩
    have hpre₀ : pre₀ ≠ [] := by
      intro hz
      subst pre₀
      simp only [List.map_nil] at hpreeq
      exact hpre hpreeq
    have hpost₀ : post₀ ≠ [] := by
      intro hz
      subst post₀
      simp only [List.map_nil] at hposteq
      exact hpost hposteq
    rcases hbelow pre₀ V post₀ hdecomp hpre₀ hpost₀ with
      ⟨hpos, W, hWreg, hVW, hWneg⟩
    refine ⟨?_, ?_⟩
    · rw [hTeq]
      change 0 ≤
        ((TileCentroid (transform V)).2 - (TileCentroid (transform R)).2) *
            ((TileCentroid (transform S)).1 - (TileCentroid (transform R)).1) -
          ((TileCentroid (transform V)).1 - (TileCentroid (transform R)).1) *
            ((TileCentroid (transform S)).2 - (TileCentroid (transform R)).2)
      rw [height_transform V]
      exact hpos
    · rcases hWreg with ⟨v, hv, rfl⟩
      refine ⟨TileTranslation (transform base) (-v), ?_, ?_, ?_⟩
      · exact ⟨-v, (TilingLattice C).neg_mem hv, rfl⟩
      · simpa [hTeq, transform_translate base v] using
          (adjacent_cov V (TileTranslation base v)).mp hVW
      · rw [← transform_translate base v]
        change
          ((TileCentroid (transform (TileTranslation base v))).2 -
              (TileCentroid (transform R)).2) *
              ((TileCentroid (transform S)).1 - (TileCentroid (transform R)).1) -
            ((TileCentroid (transform (TileTranslation base v))).1 -
              (TileCentroid (transform R)).1) *
              ((TileCentroid (transform S)).2 - (TileCentroid (transform R)).2) < 0
        rw [height_transform (TileTranslation base v)]
        exact hWneg

end ApollonianSuperharmonic

end
