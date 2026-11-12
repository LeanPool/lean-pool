/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5269T1CenteredSquareTripleTransport]

/-!
# P5269T1CenteredSquareTripleTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5269T1CenteredSquareTripleTransport (q : Int) (flip : Bool)
    (t : GaussianInt) (N : Fin 3 → Nat) (X : Fin 3 → GaussianInt)
    (hN : ∀ k, 0 < N k) (T : Fin 3 → ProtoTile)
    (hc : ∀ k, (T k).cells =
      (TileTranslation (FordTile (N k))
        ((if flip then (⟨q, q⟩ : GaussianInt) - X k - ⟨N k, N k⟩ else X k) + t)).cells)
    (E : ExactTileInterfaceTriple (TileTranslation (FordTile (N 0)) (X 0))
      (TileTranslation (FordTile (N 1)) (X 1))
      (TileTranslation (FordTile (N 2)) (X 2))) :
    let f := fun z : GaussianInt => (if flip then (⟨q, q⟩ : GaussianInt) - z else z) + t
    ∃ E' : ExactTileInterfaceTriple (T 0) (T 1) (T 2),
      E'.point = f E.point ∧ E'.otherAB = f E.otherAB ∧
        E'.otherBC = f E.otherBC ∧ E'.otherCA = f E.otherCA := by
-- BODY
  let f := fun z : GaussianInt => (if flip then (⟨q, q⟩ : GaussianInt) - z else z) + t
  let tr := fun A : ProtoTile => if flip then
    TileTranslation (TileQuarterTurn (TileQuarterTurn A)) (⟨q, q⟩ + t)
    else TileTranslation A t
  let g := fun z : GaussianInt => if flip then (⟨q, q⟩ : GaussianInt) - z - 1 - ⟨0,1⟩ + t
    else z + t
  have cell (n : Nat) (a z : GaussianInt) :
      z ∈ (TileTranslation (FordTile n) a).cells ↔
        a.re ≤ z.re ∧ z.re < a.re + n ∧ a.im ≤ z.im ∧ z.im < a.im + n := by
    change z ∈ (FordTile n).cells.image (GaussianTranslation a) ↔ _
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw := (P4210T1FordCellRectangles n w).1.mp hw
      dsimp [GaussianTranslation]
      omega
    · intro hz
      refine Finset.mem_image.mpr ⟨z-a, (P4210T1FordCellRectangles n _).1.mpr ?_, ?_⟩
      · dsimp; omega
      · simp [GaussianTranslation]
  have trcells (A : ProtoTile) : (tr A).cells = A.cells.image g := by
    cases flip
    · rfl
    · simp only [tr,ite_true,TileTranslation,TileQuarterTurn,Finset.image_image]
      apply Finset.image_congr
      intro z hz
      ext <;> simp [g,GaussianQuarterTurn,GaussianTranslation,Function.comp_def] <;> ring
  have square (n : Nat) (a : GaussianInt) :
      (tr (TileTranslation (FordTile n) a)).cells =
        (TileTranslation (FordTile n)
          ((if flip then (⟨q, q⟩ : GaussianInt) - a - ⟨n,n⟩ else a) + t)).cells := by
    rw [trcells]
    ext z
    rw [cell]
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw := (cell n a w).mp hw
      cases flip <;> dsimp [g] at * <;> omega
    · intro hz
      cases flip
      · refine Finset.mem_image.mpr ⟨z-t, (cell n a _).mpr ?_, ?_⟩
        · dsimp at hz ⊢; omega
        · simp [g]
      · refine Finset.mem_image.mpr ⟨⟨q, q⟩ - z - 1 - ⟨0,1⟩ + t,
          (cell n a _).mpr ?_, ?_⟩
        · dsimp at hz ⊢; omega
        · simp [g]; abel
  have vertices (A : ProtoTile) : FootprintVertices (tr A) = f '' FootprintVertices A := by
    cases flip
    · exact (TileTranslationFormulas A t).2.2.2.2.2.1
    · rw [show tr A = TileTranslation (TileQuarterTurn (TileQuarterTurn A)) (⟨q, q⟩+t) from rfl,
        (TileTranslationFormulas _ _).2.2.2.2.2.1,
        (TileQuarterTurnFormulas _).2.2.2.2.2.1,
        (TileQuarterTurnFormulas _).2.2.2.2.2.1]
      simp only [Set.image_image]
      congr 1
      funext z
      ext <;> simp [f,GaussianQuarterTurn,GaussianTranslation] <;> ring
  have edges (A : ProtoTile) : FootprintEdges (tr A) =
      (fun e : Finset GaussianInt => e.image f) '' FootprintEdges A := by
    cases flip
    · exact (TileTranslationFormulas A t).2.2.2.2.2.2.1
    · rw [show tr A = TileTranslation (TileQuarterTurn (TileQuarterTurn A)) (⟨q, q⟩+t) from rfl,
        (TileTranslationFormulas _ _).2.2.2.2.2.2.1,
        (TileQuarterTurnFormulas _).2.2.2.2.2.2.1,
        (TileQuarterTurnFormulas _).2.2.2.2.2.2.1]
      simp only [Set.image_image]
      congr 1
      funext e
      simp only [Function.comp_def,Finset.image_image]
      apply Finset.image_congr
      intro z hz
      ext <;> simp [f,GaussianQuarterTurn,GaussianTranslation] <;> ring
  have hv (k : Fin 3) : FootprintVertices (T k) =
      f '' FootprintVertices (TileTranslation (FordTile (N k)) (X k)) := by
    have hne : (tr (TileTranslation (FordTile (N k)) (X k))).cells.Nonempty := by
      rw [square]
      exact ⟨((if flip then (⟨q, q⟩ : GaussianInt) - X k - ⟨N k, N k⟩ else X k) + t),
        (cell _ _ _).mpr (by dsimp; have := hN k; omega)⟩
    have hc' := (hc k).trans (square (N k) (X k)).symm
    exact (ProtoTileObservableExtensionality _ _ hc'
      (by intro h; rw [h] at hc'; exact (hne.ne_empty hc'.symm).elim)).1.trans (vertices _)
  have he (k : Fin 3) : FootprintEdges (T k) =
      (fun e : Finset GaussianInt => e.image f) ''
        FootprintEdges (TileTranslation (FordTile (N k)) (X k)) := by
    have hc' := (hc k).trans (square (N k) (X k)).symm
    have ho : FootprintEdges (T k) = FootprintEdges (tr (TileTranslation (FordTile (N k)) (X k)))
        := by
      simp only [FootprintEdges,hc']
    exact ho.trans (edges _)
  apply P4055T1ExactTripleImage f _ _ _ _ _ _ _ _ (hv 0) (hv 1) (hv 2) (he 0) (he 1) (he 2) E
  · cases flip <;> intro x y h <;> simpa [f] using h
  · intro x y h
    cases flip <;> simp only [f,Bool.false_eq_true,ite_false,ite_true,Zsqrtd.ext_iff] at * <;>
      dsimp at * <;> omega

end ApollonianSuperharmonic

end
