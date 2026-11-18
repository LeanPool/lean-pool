/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordParentVectors

public import LeanPool.ApollonianSuperharmonic.P5269T1FordSquareNormalForm
public import LeanPool.ApollonianSuperharmonic.P5269T1IncomingSquareJunctions
public import LeanPool.ApollonianSuperharmonic.P5269T1CenteredSquareTripleTransport

-- [TABLET NODE: FordOrientedChildParentIncomingEndpoint]

/-!
# FordOrientedChildParentIncomingEndpoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace IncomingEndpointGeometry

private theorem cell :
    (by
      classical
      exact
        let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
        ∀ (n : Nat),
          ∀ (a : GaussianInt),
            ∀ (z : GaussianInt),
              z ∈ (sq n a).cells ↔
                a.re ≤ z.re ∧ z.re < a.re + n ∧ a.im ≤ z.im ∧ z.im < a.im + n
    ) := by
  classical
  intro sq n a z
  change z ∈ (FordTile n).cells.image (GaussianTranslation a) ↔ _
  constructor
  · rintro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw := (P4210T1FordCellRectangles n w).1.mp hw
    dsimp [GaussianTranslation]
    omega
  · intro hz
    exact Finset.mem_image.mpr ⟨z-a,
      (P4210T1FordCellRectangles n _).1.mpr (by dsimp; omega),
      by simp [GaussianTranslation]⟩

private theorem cent :
    (by
      classical
      exact
        let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
        (∀ (n : Nat),
            ∀ (a : GaussianInt),
              ∀ (z : GaussianInt),
                z ∈ (sq n a).cells ↔
                  a.re ≤ z.re ∧ z.re < a.re + n ∧ a.im ≤ z.im ∧ z.im < a.im + n) →
          ∀ (T : ProtoTile),
            ∀ (n : Nat),
              0 < n →
                ∀ (a : GaussianInt),
                  T.cells = (sq n a).cells →
                    TileCentroid T =
                      ((a.re : Real) + (n : Real) / 2, (a.im : Real) + (n : Real) / 2)
    ) := by
  classical
  intro sq cell T n hn a hc
  have hne : (sq n a).cells.Nonempty := ⟨a,(cell n a a).mpr (by omega)⟩
  have ho := ProtoTileObservableExtensionality T (sq n a) hc
    (by intro h; rw [h] at hc; exact (hne.ne_empty hc.symm).elim)
  rw [ho.2.2.2.2,(TileTranslationFormulas _ _).2.2.2.2.1,
    P4210T1FordSquareCentroid n hn]
  dsimp
  congr 1 <;> ring

private theorem translate :
    (by
      classical
      exact
        let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
        ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (a : GaussianInt), ∀ (u : GaussianInt), (T.cells = (sq
            n a).cells) → ((TileTranslation T u).cells = (sq n (a+u)).cells) ) := by
  classical
  intro sq T n a u hc
  change T.cells.image (GaussianTranslation u) = _
  rw [hc]
  simp only [sq,TileTranslation,Finset.image_image]
  apply Finset.image_congr
  intro z hz
  simp [GaussianTranslation,add_assoc]

private theorem disk :
    (by
      classical
      exact
        let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
        ∀ (T : ProtoTile), ∀ (n : Nat), (0 < n) → (∀ (a : GaussianInt), (T.cells = (sq n
            a).cells) → (LatticeTile T)) ) := by
  classical
  intro sq T n hn a hc
  have h := (TileDiskAreaCovariance (FordTile n) a).1.mp (FordTileGeometry n hn).1
  simpa only [LatticeTile,TileRealization,hc] using h

private theorem finish :
    (by
      classical
      exact
        let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
        (∀ (n : Nat),
            ∀ (a : GaussianInt),
              ∀ (z : GaussianInt),
                z ∈ (sq n a).cells ↔
                  a.re ≤ z.re ∧ z.re < a.re + n ∧ a.im ≤ z.im ∧ z.im < a.im + n) →
          (∀ (T : ProtoTile),
              ∀ (n : Nat),
                ∀ (a : GaussianInt),
                  ∀ (u : GaussianInt),
                    T.cells = (sq n a).cells →
                      (TileTranslation T u).cells = (sq n (a + u)).cells) →
            (∀ (T : ProtoTile),
                ∀ (n : Nat),
                  0 < n → ∀ (a : GaussianInt), T.cells = (sq n a).cells → LatticeTile T) →
              ∀ (r : Nat),
                ∀ (s : Nat),
                  0 < r →
                    0 < s →
                      ∀ (j : Fin 4),
                        ∀ (flip : Bool),
                          ∀ (t : GaussianInt),
                            ∀ (U : ProtoTile),
                              ∀ (W : ProtoTile),
                                U.cells = (sq (r + s) t).cells →
                                W.cells =
                                (sq (![r, s, r, s] j)
                                ((if flip then
                                (⟨r + s, r + s⟩ : GaussianInt) -
                                ![⟨s, r + s⟩, ⟨-(s : Int), 0⟩, ⟨-(r : Int), s⟩,
                                ⟨r, -(s : Int)⟩]
                                j -
                                ⟨![r, s, r, s] j, ![r, s, r, s] j⟩
                              else
                                ![⟨s, r + s⟩, ⟨-(s : Int), 0⟩, ⟨-(r : Int), s⟩,
                                ⟨r, -(s : Int)⟩]
                                j) +
                                t)).cells →
                                ∀ (D : GaussianInt),
                                (D =
                                if flip then
                                -![⟨r + s, r⟩, ⟨-(r + s : Int), s⟩,
                                ⟨-(r + s : Int), -(r : Int)⟩, ⟨r + s, -(s : Int)⟩]
                                j
                              else
                                ![⟨r + s, r⟩, ⟨-(r + s : Int), s⟩,
                                ⟨-(r + s : Int), -(r : Int)⟩, ⟨r + s, -(s : Int)⟩]
                                j) →
                                ∃ _ : ExactTileInterfaceTriple U (TileTranslation U D) W,
                                TouchingTriple U (TileTranslation U D) W
    ) := by
  classical
  intro sq cell translate disk r s hr hs j flip t U W hU hW D hD
  let b : GaussianInt := ![⟨r+s,r⟩,⟨-(r+s:Int),s⟩,⟨-(r+s:Int),-(r:Int)⟩,⟨r+s,-(s:Int)⟩] j
  let c : GaussianInt := ![⟨s,r+s⟩,⟨-(s:Int),0⟩,⟨-(r:Int),s⟩,⟨r,-(s:Int)⟩] j
  let n : Nat := ![r,s,r,s] j
  let d : GaussianInt := if flip then -b else b
  change D = d at hD
  subst D
  let w : GaussianInt := (if flip then (⟨r+s,r+s⟩ : GaussianInt)-c-⟨n,n⟩ else c)+t
  have hn : 0 < n := by fin_cases j <;> simp [n] <;> omega
  have hq : 0 < r+s := by omega
  have hV := translate U (r+s) t d hU
  obtain ⟨E, _, _⟩ := P5269T1IncomingSquareJunctions r s hr hs j
  obtain ⟨E', _, _, _, _⟩ := P5269T1CenteredSquareTripleTransport (r+s) flip t
    ![r+s,r+s,n] ![0,b,c]
    (by intro k; fin_cases k <;> simp <;> omega)
    ![U,TileTranslation U d,W] (by
      intro k
      fin_cases k
      · cases flip <;> simpa using hU
      · change (TileTranslation U d).cells =
          (sq (r+s) ((if flip then (⟨r+s,r+s⟩ : GaussianInt)-b-⟨r+s,r+s⟩ else b)+t)).cells
        have he : ((if flip then (⟨r+s,r+s⟩ : GaussianInt)-b-⟨r+s,r+s⟩ else b)+t) = t+d := by
          cases flip <;> simp [d] <;> abel
        rw [he]
        exact hV
      · exact hW) E
  have hab : Disjoint U.cells (TileTranslation U d).cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rw [hU,cell] at hz
    rw [hV,cell] at hz'
    fin_cases j <;> cases flip <;> dsimp [d,b] at hz hz' <;> omega
  have hbc : Disjoint (TileTranslation U d).cells W.cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rw [hV,cell] at hz
    rw [hW,cell] at hz'
    fin_cases j <;> cases flip <;> dsimp [d,b] at hz hz' <;> omega
  have hca : Disjoint W.cells U.cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rw [hW,cell] at hz
    rw [hU,cell] at hz'
    fin_cases j <;> cases flip <;> dsimp at hz hz' <;> omega
  exact ⟨E',ExactTileInterfaceTripleLatticeTouching _ _ _ E'
    (disk U _ hq t hU) (disk _ _ hq (t+d) hV) (disk W n hn w hW) hab hbc hca⟩

private theorem hr :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (1 : ℕ) < P.q → 0 < P.q₁
    ) := by
  classical
  intro P hq
  by_contra h
  have hz : P.q₁ = 0 := by omega
  have hd := P.det₁
  simp [hz] at hd
  have hdv : (P.q:Int) ∣ 1 := ⟨P.p₁,by simpa [mul_comm] using hd.symm⟩
  have hone := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q:Int)) hdv
  omega

end IncomingEndpointGeometry

theorem FordOrientedChildParentIncomingEndpoint
    (P : FordFareyParameter) (hq : 1 < P.q) :
    let q := FordRecursiveQuadruple P
    ∀ (i : Fin 3) (s : Fin 4) (U W : ProtoTile),
      BandPrototile (q 0) U →
      BandPrototile (q i.succ) W →
      0 < (q 0).1 → 0 < (q i.succ).1 →
      TileCentroid W - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q i.succ) (q 0)
          else BandVectors.1 (q 0) (q i.succ))
      ∃ _ : ExactTileInterfaceTriple U (TileTranslation U uL) W,
        TouchingTriple U (TileTranslation U uL) W := by
-- BODY
  classical
  let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
  have cell (n : Nat) (a z : GaussianInt) := IncomingEndpointGeometry.cell n a z
  have cent (T : ProtoTile) (n : Nat) (hn : 0 < n) (a : GaussianInt)
      (hc : T.cells = (sq n a).cells) := IncomingEndpointGeometry.cent cell T n hn a hc
  have translate (T : ProtoTile) (n : Nat) (a u : GaussianInt)
      (hc : T.cells = (sq n a).cells) := IncomingEndpointGeometry.translate T n a u hc
  have disk (T : ProtoTile) (n : Nat) (hn : 0 < n) (a : GaussianInt)
      (hc : T.cells = (sq n a).cells) := IncomingEndpointGeometry.disk T n hn a hc
  have finish (r s : Nat) (hr : 0 < r) (hs : 0 < s) (j : Fin 4)
      (flip : Bool) (t : GaussianInt) (U W : ProtoTile)
      (hU : U.cells = (sq (r+s) t).cells)
      (hW : W.cells = (sq (![r,s,r,s] j)
        ((if flip then (⟨r+s,r+s⟩ : GaussianInt) -
          (![⟨s,r+s⟩,⟨-(s:Int),0⟩,⟨-(r:Int),s⟩,⟨r,-(s:Int)⟩] j) -
          ⟨![r,s,r,s] j,![r,s,r,s] j⟩
          else (![⟨s,r+s⟩,⟨-(s:Int),0⟩,⟨-(r:Int),s⟩,⟨r,-(s:Int)⟩] j))+t)).cells)
      (D : GaussianInt)
      (hD : D = if flip then
        -(![⟨r+s,r⟩,⟨-(r+s:Int),s⟩,⟨-(r+s:Int),-(r:Int)⟩,⟨r+s,-(s:Int)⟩] j)
        else (![⟨r+s,r⟩,⟨-(r+s:Int),s⟩,⟨-(r+s:Int),-(r:Int)⟩,⟨r+s,-(s:Int)⟩] j)) :=
            IncomingEndpointGeometry.finish cell translate disk r s hr hs j flip t U W hU hW D hD
  dsimp only
  intro i s U W hU hW hUpos hWpos hcw
  have hr := IncomingEndpointGeometry.hr P hq
  have hs := P.q₂_pos
  have hqs := P.sum_q
  obtain ⟨hp,h10,h20,_,_⟩ := (FordCoordinateConfiguration P).2 hq
  have hf := (VectorRecursionLaws _ hp.1).2.2.2.2 hp
  have h01 : BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 1) =
      ⟨-(P.q₁:Int),P.q⟩ := FordParentVectors.firstParent P h10 hf
  have h02 : BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 2) =
      ⟨-(P.q₂:Int),-(P.q:Int)⟩ := FordParentVectors.secondParent P h20 hf
  obtain ⟨⟨a,b⟩,hUc⟩ := P5269T1FordSquareNormalForm P hq 0 U hU hUpos
  have hcu := cent U P.q P.q_pos ⟨a,b⟩ hUc
  have he0 : Even (0 : Nat) := by decide
  have he1 : ¬ Even (1 : Nat) := by decide
  have he2 : Even (2 : Nat) := by decide
  have he3 : ¬ Even (3 : Nat) := by decide
  fin_cases i
  · obtain ⟨⟨wa,wb⟩,hWc⟩ := P5269T1FordSquareNormalForm P hq 1 W hW hWpos
    have hcw' := cent W P.q₁ hr ⟨wa,wb⟩ hWc
    rw [hcw',hcu] at hcw
    fin_cases s
    all_goals norm_num [h10,h20,h01,h02,GaussianRealPoint,pow_succ,hqs] at hcw
    · refine finish P.q₁ P.q₂ hr hs 0 false ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₁ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 2 false ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₁ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 0 true ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₁ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 2 true ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₁ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
  · obtain ⟨⟨wa,wb⟩,hWc⟩ := P5269T1FordSquareNormalForm P hq 2 W hW hWpos
    have hcw' := cent W P.q₂ hs ⟨wa,wb⟩ hWc
    rw [hcw',hcu] at hcw
    fin_cases s
    all_goals norm_num [h10,h20,h01,h02,GaussianRealPoint,pow_succ,hqs] at hcw
    · refine finish P.q₁ P.q₂ hr hs 1 false ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₂ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 3 false ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₂ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 1 true ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₂ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
    · refine finish P.q₁ P.q₂ hr hs 3 true ⟨a,b⟩ U W
        (by simpa [hqs] using hUc) ?_ _ ?_
      · apply hWc.trans
        apply congrArg (fun z : GaussianInt => (sq P.q₂ z).cells)
        ext <;> apply Int.cast_injective (α := Real) <;> dsimp <;>
          push_cast <;> linarith [hcw.1,hcw.2]
      · ext <;> norm_num [he0,he1,he2,he3,h10,h20,h01,h02,pow_succ,hqs]
  · norm_num [FordRecursiveQuadruple] at hWpos

end ApollonianSuperharmonic

end
