/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordInteriorSquareCoordinates

public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: P4062T1LiteralReduction]

/-!
# P4062T1LiteralReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LiteralReductionGeometry


private theorem hcurv :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), 0 < (FordCircleCoordinate P.p P.q).1 ) := by
  classical
  intro P
  change (0 : ℤ) < ((P.q * P.q : Nat) : ℤ)
  exact_mod_cast Nat.mul_pos P.q_pos P.q_pos

private theorem hFcells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (FordTile P.q).cells.Nonempty ) := by
  classical
  intro P
  refine ⟨⟨0, 0⟩, ?_⟩
  simp only [FordTile, FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod,
      Finset.mem_image, Finset.mem_product, Finset.mem_range, Zsqrtd.mk.injEq,
      Int.natCast_eq_zero, Prod.exists, exists_eq_right_right, exists_eq_right, and_self]
  exact P.q_pos

private theorem hTcells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile P.q)
            u).cells ∧ (T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧ ∃
            (a : GaussianInt) (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ k.domain) ∧ ∀
            x ∈ h.domain, h.value x = k.value (x - u) + a.re * x.re + a.im * x.im + b) →
            (((FordTile P.q).cells.Nonempty) → (T.cells.Nonempty)) ) := by
  classical
  intro P T h k u htrans hFcells
  rw [htrans.1]
  simpa [TileTranslation] using hFcells.image (GaussianTranslation u)

private theorem hboundaryTransport :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile P.q)
            u).cells ∧ (T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧ ∃
            (a : GaussianInt) (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ k.domain) ∧ ∀
            x ∈ h.domain, h.value x = k.value (x - u) + a.re * x.re + a.im * x.im + b) →
            (((TileTranslation (FordTile P.q) u).cells.Nonempty) → (BoundaryFootprintVertices T =
            GaussianTranslation u '' BoundaryFootprintVertices (FordTile P.q))) ) := by
  classical
  intro P T h k u htrans htranslatedCells
  have heq : BoundaryFootprintVertices T =
      BoundaryFootprintVertices (TileTranslation (FordTile P.q) u) := by
    simp [BoundaryFootprintVertices, BoundaryFootprintEdges,
      htranslatedCells, htrans.1]
  exact heq.trans
    (TileTranslationFormulas (FordTile P.q) u).2.2.2.2.2.2.2.1

private theorem hboundaryPoint :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
            (BoundaryFootprintVertices T = GaussianTranslation u '' BoundaryFootprintVertices
            (FordTile P.q)) → (∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices T ↔ x - u ∈
            BoundaryFootprintVertices (FordTile P.q)) ) := by
  classical
  intro P T u hboundaryTransport x
  rw [hboundaryTransport]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have heq' : y + u = x := by simpa [GaussianTranslation] using heq
    rw [← heq']
    simpa using hy
  · intro hy
    refine ⟨x - u, hy, ?_⟩
    simp [GaussianTranslation]

private theorem hstrictTranslation :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (u : GaussianInt), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈
            k.domain) → ((∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices T ↔ x - u ∈
            BoundaryFootprintVertices (FordTile P.q)) → (h.domain.filter (fun x => @decide (x ∉
            BoundaryFootprintVertices T) (Classical.propDecidable _)) = (k.domain.filter (fun y
            => @decide (y ∉ BoundaryFootprintVertices (FordTile P.q)) (Classical.propDecidable
            _))).image (GaussianTranslation u))) ) := by
  classical
  intro P T h k u hdomshift hboundaryPoint
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hxdom, hxnot⟩
    have hyDom := (hdomshift x).mp hxdom
    have hxnot' : x ∉ BoundaryFootprintVertices T :=
      @of_decide_eq_true _ (Classical.propDecidable _) hxnot
    have hyNot : x - u ∉ BoundaryFootprintVertices (FordTile P.q) := by
      intro hyb
      exact hxnot' ((hboundaryPoint x).2 hyb)
    refine ⟨x - u, ⟨hyDom, ?_⟩, ?_⟩
    · simp [hyNot]
    · simp [GaussianTranslation]
  · rintro ⟨y, ⟨hydom, hynot⟩, heq⟩
    have heq' : y + u = x := by simpa [GaussianTranslation] using heq
    have hnot : y ∉ BoundaryFootprintVertices (FordTile P.q) :=
      @of_decide_eq_true _ (Classical.propDecidable _) hynot
    have hxdom : x ∈ h.domain := by
      apply (hdomshift x).mpr
      have hxy : x - u = y := by calc
        x - u = (y + u) - u := by rw [heq']
        _ = y := by abel
      rw [hxy]
      exact hydom
    have hxnot : x ∉ BoundaryFootprintVertices T := by
      intro hxb
      have hyb := (hboundaryPoint x).mp hxb
      have hxy : x - u = y := by calc
        x - u = (y + u) - u := by rw [heq']
        _ = y := by abel
      exact hnot (hxy ▸ hyb)
    exact ⟨hxdom, by simp [hxnot]⟩

private theorem hstrictBounds :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FordVertexDomain P.q) → ((0 < P.q) → ((BoundaryFootprintVertices (FordTile P.q) = {x
            : GaussianInt | (0 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q :
            ℤ) ∧ (x.re = (0 : ℤ) ∨ x.re = (↑P.q : ℤ) ∨ x.im = (0 : ℤ) ∨ x.im = (↑P.q : ℤ))}) → (∀
            (y : GaussianInt), (y ∈ k.domain) → ((y ∉ BoundaryFootprintVertices (FordTile P.q)) →
            (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1))))) ) := by
  classical
  intro P k hkdom hqpos hboundarySquare y hy hynot
  have hybox : 0 ≤ y.re ∧ y.re ≤ (P.q : Int) ∧
      0 ≤ y.im ∧ y.im ≤ (P.q : Int) := by
    have hy' : y ∈ FordVertexDomain P.q := by
      have hset : y ∈ (k.domain : Set GaussianInt) := hy
      rw [hkdom] at hset
      exact hset
    simpa [FordVertexDomain] using hy'
  rw [hboundarySquare] at hynot
  simp only [Set.mem_ofPred_eq] at hynot
  omega

private theorem hDcoords :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (u : GaussianInt), (h.domain.filter (fun x => @decide (x ∉
            BoundaryFootprintVertices T) (Classical.propDecidable _)) = (k.domain.filter (fun y
            => @decide (y ∉ BoundaryFootprintVertices (FordTile P.q)) (Classical.propDecidable
            _))).image (GaussianTranslation u)) → ((∀ (y : GaussianInt), (y ∈ k.domain) → ((y ∉
            BoundaryFootprintVertices (FordTile P.q)) → (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤
            y.im ∧ y.im ≤ (P.q : Int) - 1))) → (∀ x, x ∈ h.domain.filter (fun x => @decide (x ∉
            BoundaryFootprintVertices T) (Classical.propDecidable _)) → 1 ≤ (x - u).re ∧ (x -
            u).re ≤ (P.q : Int) - 1 ∧ 1 ≤ (x - u).im ∧ (x - u).im ≤ (P.q : Int) - 1)) ) := by
  classical
  intro P T h k u hstrictTranslation hstrictBounds x hx
  rw [hstrictTranslation] at hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, heq⟩
  rcases Finset.mem_filter.mp hy with ⟨hydom, hynot⟩
  have hynot' : y ∉ BoundaryFootprintVertices (FordTile P.q) :=
    @of_decide_eq_true _ (Classical.propDecidable _) hynot
  have hbounds := hstrictBounds y hydom hynot'
  have heq' : y + u = x := by simpa [GaussianTranslation] using heq
  have hxy : x - u = y := by calc
    x - u = (y + u) - u := by rw [heq']
    _ = y := by abel
  rw [hxy]
  exact hbounds

private theorem hcanonicalFoot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FordVertexDomain P.q) → (∀ (y : GaussianInt), (0 ≤ y.re) → ((y.re ≤ (P.q : Int)) →
            ((0 ≤ y.im) → ((y.im ≤ (P.q : Int)) → (y ∈ k.domain))))) ) := by
  classical
  intro P k hkdom y hy hy' hz hz'
  have hbox : y ∈ FordVertexDomain P.q := by
    simp only [FordVertexDomain, Int.reduceNeg, Set.mem_ofPred_eq]
    exact ⟨hy, hy', hz, hz'⟩
  have hset : y ∈ (k.domain : Set GaussianInt) := by
    rw [hkdom]
    exact hbox
  exact hset

private theorem hcanonicalDomain :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (k : PartialOdometer), (∀ (y : GaussianInt), (0 ≤ y.re) →
            ((y.re ≤ (P.q : Int)) → ((0 ≤ y.im) → ((y.im ≤ (P.q : Int)) → (y ∈ k.domain))))) → (∀
            (y : GaussianInt), (1 ≤ y.re) → ((y.re ≤ (P.q : Int) - 1) → ((1 ≤ y.im) → ((y.im ≤
            (P.q : Int) - 1) → (y ∈ k.domain))))) ) := by
  classical
  intro P k hcanonicalFoot y hy hy' hz hz'
  apply hcanonicalFoot y <;> omega

private theorem hstencilDomain :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (u : GaussianInt), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈
            k.domain) → ((∀ x, x ∈ h.domain.filter (fun x => @decide (x ∉
            BoundaryFootprintVertices T) (Classical.propDecidable _)) → 1 ≤ (x - u).re ∧ (x -
            u).re ≤ (P.q : Int) - 1 ∧ 1 ≤ (x - u).im ∧ (x - u).im ≤ (P.q : Int) - 1) → ((∀ (y :
            GaussianInt), (0 ≤ y.re) → ((y.re ≤ (P.q : Int)) → ((0 ≤ y.im) → ((y.im ≤ (P.q :
            Int)) → (y ∈ k.domain))))) → (∀ (x : GaussianInt), (x ∈ h.domain.filter (fun x =>
            @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _))) → (x ∈
                h.domain ∧ x - 1 ∈ h.domain ∧ x + 1 ∈ h.domain ∧ x - ⟨0, 1⟩ ∈ h.domain ∧ x + ⟨0,
                1⟩ ∈ h.domain)))) ) := by
  classical
  intro P T h k u hdomshift hDcoords hcanonicalFoot x hx
  have hcoord := hDcoords x hx
  rcases hcoord with ⟨hr, hr', hi, hi'⟩
  let y := x - u
  have hyr : 1 ≤ y.re := by simpa [y] using hr
  have hyr' : y.re ≤ (P.q : Int) - 1 := by simpa [y] using hr'
  have hyi : 1 ≤ y.im := by simpa [y] using hi
  have hyi' : y.im ≤ (P.q : Int) - 1 := by simpa [y] using hi'
  have hrePlus : (y + 1).re = y.re + 1 := by simp
  have hreMinus : (y - 1).re = y.re - 1 := by simp
  have himPlus : (y + ⟨0, 1⟩).im = y.im + 1 := by simp
  have himMinus : (y - ⟨0, 1⟩).im = y.im - 1 := by simp
  have hreSamePlus : (y + 1).im = y.im := by simp
  have hreSameMinus : (y - 1).im = y.im := by simp
  have himSamePlus : (y + ⟨0, 1⟩).re = y.re := by simp
  have himSameMinus : (y - ⟨0, 1⟩).re = y.re := by simp
  have hy : x - u ∈ k.domain := by
    exact (hdomshift x).mp (Finset.mem_filter.mp hx).1
  have hEast : 0 ≤ (y + 1).re ∧ (y + 1).re ≤ (P.q : Int) ∧
      0 ≤ (y + 1).im ∧ (y + 1).im ≤ (P.q : Int) := by
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
      Zsqrtd.im_one]
    omega
  have hWest : 0 ≤ (y - 1).re ∧ (y - 1).re ≤ (P.q : Int) ∧
      0 ≤ (y - 1).im ∧ (y - 1).im ≤ (P.q : Int) := by
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
      Zsqrtd.im_one]
    omega
  have hNorth : 0 ≤ (y + ⟨0, 1⟩).re ∧
      (y + ⟨0, 1⟩).re ≤ (P.q : Int) ∧
      0 ≤ (y + ⟨0, 1⟩).im ∧ (y + ⟨0, 1⟩).im ≤ (P.q : Int) := by
    simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      ]
    omega
  have hSouth : 0 ≤ (y - ⟨0, 1⟩).re ∧
      (y - ⟨0, 1⟩).re ≤ (P.q : Int) ∧
      0 ≤ (y - ⟨0, 1⟩).im ∧ (y - ⟨0, 1⟩).im ≤ (P.q : Int) := by
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
      ]
    omega
  refine ⟨(hdomshift x).mpr hy, ?_, ?_, ?_, ?_⟩
  · apply (hdomshift (x - 1)).mpr
    have hz := hcanonicalFoot (y - 1) hWest.1 hWest.2.1
      hWest.2.2.1 hWest.2.2.2
    simpa only [show x - 1 - u = (x - u) - 1 by abel] using hz
  · apply (hdomshift (x + 1)).mpr
    have hz := hcanonicalFoot (y + 1) hEast.1 hEast.2.1
      hEast.2.2.1 hEast.2.2.2
    simpa only [show x + 1 - u = (x - u) + 1 by abel] using hz
  · apply (hdomshift (x - ⟨0, 1⟩)).mpr
    have hz := hcanonicalFoot (y - ⟨0, 1⟩) hSouth.1 hSouth.2.1
      hSouth.2.2.1 hSouth.2.2.2
    simpa only [show x - ⟨0, 1⟩ - u =
      (x - u) - ⟨0, 1⟩ by abel] using hz
  · apply (hdomshift (x + ⟨0, 1⟩)).mpr
    have hz := hcanonicalFoot (y + ⟨0, 1⟩) hNorth.1 hNorth.2.1
      hNorth.2.2.1 hNorth.2.2.2
    simpa only [show x + ⟨0, 1⟩ - u =
      (x - u) + ⟨0, 1⟩ by abel] using hz

private theorem hlapshift :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (h : PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (k
            : PartialOdometer), (∀ x ∈ k.domain, k.value x = FordOdometer P x) → (∀ (u :
            GaussianInt), ∀ (a : GaussianInt), ∀ (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x
            - u ∈ k.domain) → ((∀ x ∈ h.domain, h.value x = k.value (x - u) + a.re * x.re + a.im
            * x.im + b) → (∀ (c : ℤ), (∀ x ∈ h.domain, g x = h.value x + c) → (∀ (x :
            GaussianInt), (x ∈ h.domain) → ((x - 1 ∈ h.domain) → ((x + 1 ∈ h.domain) → ((x - ⟨0,
            1⟩ ∈ h.domain) → ((x + ⟨0, 1⟩ ∈ h.domain) → (FourNeighborLaplacian g x =
            FourNeighborLaplacian (FordOdometer P) (x - u)))))))))) ) := by
  classical
  intro P h g k hkval u a b hdomshift hvalueshift c hextval x hx hxm hxp hym hyp
  have hg0 : g x = FordOdometer P (x - u) +
      a.re * x.re + a.im * x.im + b + c := by
    rw [hextval x hx, hvalueshift x hx,
      hkval (x - u) ((hdomshift x).mp hx)]
  have hgm : g (x - 1) = FordOdometer P ((x - u) - 1) +
      a.re * (x - 1).re + a.im * (x - 1).im + b + c := by
    rw [hextval (x - 1) hxm, hvalueshift (x - 1) hxm,
      hkval (x - 1 - u) ((hdomshift (x - 1)).mp hxm)]
    congr 1
    · congr 1
      abel
  have hgp : g (x + 1) = FordOdometer P ((x - u) + 1) +
      a.re * (x + 1).re + a.im * (x + 1).im + b + c := by
    rw [hextval (x + 1) hxp, hvalueshift (x + 1) hxp,
      hkval (x + 1 - u) ((hdomshift (x + 1)).mp hxp)]
    congr 1
    · congr 1
      abel
  have hgi : g (x - ⟨0, 1⟩) =
      FordOdometer P ((x - u) - ⟨0, 1⟩) +
        a.re * (x - ⟨0, 1⟩).re + a.im * (x - ⟨0, 1⟩).im + b + c := by
    rw [hextval (x - ⟨0, 1⟩) hym,
      hvalueshift (x - ⟨0, 1⟩) hym,
      hkval (x - ⟨0, 1⟩ - u)
        ((hdomshift (x - ⟨0, 1⟩)).mp hym)]
    congr 1
    · congr 1
      abel
  have hgo : g (x + ⟨0, 1⟩) =
      FordOdometer P ((x - u) + ⟨0, 1⟩) +
        a.re * (x + ⟨0, 1⟩).re + a.im * (x + ⟨0, 1⟩).im + b + c := by
    rw [hextval (x + ⟨0, 1⟩) hyp,
      hvalueshift (x + ⟨0, 1⟩) hyp,
      hkval (x + ⟨0, 1⟩ - u)
        ((hdomshift (x + ⟨0, 1⟩)).mp hyp)]
    congr 1
    · congr 1
      abel
  rw [FourNeighborLaplacian, hgm, hgp, hgi, hgo, hg0,
    FourNeighborLaplacian]
  rw [show x - u - 1 = (x - u) - 1 by abel,
    show x - u + 1 = (x - u) + 1 by abel,
    show x - u - ⟨0, 1⟩ = (x - u) - ⟨0, 1⟩ by rfl,
    show x - u + ⟨0, 1⟩ = (x - u) + ⟨0, 1⟩ by rfl]
  simp
  ring

private theorem hDcanCoords :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (k : PartialOdometer), (BoundaryFootprintVertices (FordTile
            P.q) = {x : GaussianInt | (0 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ x.im ∧ x.im
            ≤ (↑P.q : ℤ) ∧ (x.re = (0 : ℤ) ∨ x.re = (↑P.q : ℤ) ∨ x.im = (0 : ℤ) ∨ x.im = (↑P.q :
            ℤ))}) → ((∀ (y : GaussianInt), (y ∈ k.domain) → ((y ∉ BoundaryFootprintVertices
            (FordTile P.q)) → (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int)
            - 1))) → ((∀ (y : GaussianInt), (1 ≤ y.re) → ((y.re ≤ (P.q : Int) - 1) → ((1 ≤ y.im)
            → ((y.im ≤ (P.q : Int) - 1) → (y ∈ k.domain))))) → (
        let Dcan := k.domain.filter (fun y =>
          @decide (y ∉ BoundaryFootprintVertices (FordTile P.q))
            (Classical.propDecidable _))
        ∀ (y : GaussianInt), y ∈ Dcan ↔ 1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤
            (P.q : Int) - 1))) ) := by
  classical
  intro P k hboundarySquare hstrictBounds hcanonicalDomain Dcan y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hydom, hnotdec⟩
    have hnot : y ∉ BoundaryFootprintVertices (FordTile P.q) :=
      @of_decide_eq_true _ (Classical.propDecidable _) hnotdec
    exact hstrictBounds y hydom hnot
  · rintro ⟨hy0, hy1, hz0, hz1⟩
    have hydom := hcanonicalDomain y hy0 hy1 hz0 hz1
    have hnot : y ∉ BoundaryFootprintVertices (FordTile P.q) := by
      rw [hboundarySquare]
      simp only [Set.mem_ofPred_eq]
      omega
    refine Finset.mem_filter.mpr ⟨hydom, ?_⟩
    exact (@decide_eq_true_eq (y ∉ BoundaryFootprintVertices (FordTile P.q))
      (Classical.propDecidable _)).mpr hnot

private theorem heqAt410 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (∀ (q : Nat), ∀ (x : GaussianInt), x ∈
            P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q :
            Int) - 1) → (∀ (k : PartialOdometer),
        let Dcan := k.domain.filter (fun y =>
          @decide (y ∉ BoundaryFootprintVertices (FordTile P.q))
            (Classical.propDecidable _))
        (∀ (y : GaussianInt), y ∈ Dcan ↔ 1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤
            (P.q : Int) - 1) → (Dcan = P4062T1InteriorSquare P.q)) ) := by
  classical
  intro P squareCoordinates k Dcan hDcanCoords
  ext x
  exact (hDcanCoords x).trans (squareCoordinates P.q x).symm

end LiteralReductionGeometry

theorem P4062T1LiteralReduction :
    ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g :
        IntegerLatticeFunction), (BandPrototile (FordCircleCoordinate P.p P.q) T) →
        ((TileOdometer (FordCircleCoordinate P.p P.q) T h) → (((h.domain : Set GaussianInt) =
        FootprintVertices T) → ((GlobalOdometerExtends g h) → (
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    ∃ u : GaussianInt,
      D = (P4062T1InteriorSquare P.q).image (fun x => x+u) ∧
      ∀ x ∈ D, FourNeighborLaplacian g x =
        FourNeighborLaplacian (FordOdometer P) (x-u))))) := by
  intro P T h g hT hodo hdom hext
-- BODY
  classical
  have squareCoordinates (q : Nat) (x : GaussianInt) :
      x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := FordInteriorSquareCoordinates.membership q x
  obtain ⟨k, hkodo, hkdom, hkval⟩ := FordTileOdometerRestriction P
  have hcurv : 0 < (FordCircleCoordinate P.p P.q).1 := LiteralReductionGeometry.hcurv P
  obtain ⟨u, htrans, _⟩ :=
    TileOdometerTranslationUniqueness (FordCircleCoordinate P.p P.q)
      T (FordTile P.q) h k hcurv hodo hkodo
  obtain ⟨a, b, hdomshift, hvalueshift⟩ := htrans.2.2
  obtain ⟨c, hextval⟩ := hext
  have hqpos : 0 < P.q := P.q_pos
  obtain ⟨hfootSquare, hboundarySquare⟩ := P4062T1CanonicalSupport P.q P.q_pos
  have hFcells : (FordTile P.q).cells.Nonempty := LiteralReductionGeometry.hFcells P
  have hTcells : T.cells.Nonempty := LiteralReductionGeometry.hTcells P T h k u htrans hFcells
  have htranslatedCells : (TileTranslation (FordTile P.q) u).cells.Nonempty := by
    simpa [TileTranslation] using hFcells.image (GaussianTranslation u)
  have hboundaryTransport :
      BoundaryFootprintVertices T =
        GaussianTranslation u '' BoundaryFootprintVertices (FordTile P.q) :=
            LiteralReductionGeometry.hboundaryTransport P T h k u htrans htranslatedCells
  have hboundaryPoint (x : GaussianInt) :
      x ∈ BoundaryFootprintVertices T ↔
        x - u ∈ BoundaryFootprintVertices (FordTile P.q) :=
            LiteralReductionGeometry.hboundaryPoint P T u hboundaryTransport x
  have hstrictTranslation :
      h.domain.filter (fun x =>
        @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)) =
      (k.domain.filter (fun y =>
        @decide (y ∉ BoundaryFootprintVertices (FordTile P.q))
          (Classical.propDecidable _))).image (GaussianTranslation u) :=
              LiteralReductionGeometry.hstrictTranslation P T h k u hdomshift hboundaryPoint
  have hstrictBounds (y : GaussianInt) (hy : y ∈ k.domain)
      (hynot : y ∉ BoundaryFootprintVertices (FordTile P.q)) :
      1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧
        1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1 := LiteralReductionGeometry.hstrictBounds P k hkdom
            hqpos hboundarySquare y hy hynot
  have hDcoords : ∀ x, x ∈ h.domain.filter (fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)) →
      1 ≤ (x - u).re ∧ (x - u).re ≤ (P.q : Int) - 1 ∧
        1 ≤ (x - u).im ∧ (x - u).im ≤ (P.q : Int) - 1 := LiteralReductionGeometry.hDcoords P T h
            k u hstrictTranslation hstrictBounds
  have hcanonicalFoot (y : GaussianInt)
      (hy : 0 ≤ y.re) (hy' : y.re ≤ (P.q : Int))
      (hz : 0 ≤ y.im) (hz' : y.im ≤ (P.q : Int)) :
      y ∈ k.domain := LiteralReductionGeometry.hcanonicalFoot P k hkdom y hy hy' hz hz'
  have hcanonicalDomain (y : GaussianInt)
      (hy : 1 ≤ y.re) (hy' : y.re ≤ (P.q : Int) - 1)
      (hz : 1 ≤ y.im) (hz' : y.im ≤ (P.q : Int) - 1) :
      y ∈ k.domain := LiteralReductionGeometry.hcanonicalDomain P k hcanonicalFoot y hy hy' hz hz'
  have hstencilDomain (x : GaussianInt)
      (hx : x ∈ h.domain.filter (fun x =>
        @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _))) :
      x ∈ h.domain ∧ x - 1 ∈ h.domain ∧ x + 1 ∈ h.domain ∧
        x - ⟨0, 1⟩ ∈ h.domain ∧ x + ⟨0, 1⟩ ∈ h.domain := LiteralReductionGeometry.hstencilDomain
            P T h k u hdomshift hDcoords hcanonicalFoot x hx
  have hlapshift (x : GaussianInt) (hx : x ∈ h.domain)
      (hxm : x - 1 ∈ h.domain) (hxp : x + 1 ∈ h.domain)
      (hym : x - ⟨0, 1⟩ ∈ h.domain)
      (hyp : x + ⟨0, 1⟩ ∈ h.domain) :
      FourNeighborLaplacian g x =
        FourNeighborLaplacian (FordOdometer P) (x - u) := LiteralReductionGeometry.hlapshift P h
            g k hkval u a b hdomshift hvalueshift c hextval x hx hxm hxp hym hyp
  let Dcan := k.domain.filter (fun y =>
    @decide (y ∉ BoundaryFootprintVertices (FordTile P.q))
      (Classical.propDecidable _))
  have hDcanCoords (y : GaussianInt) :
      y ∈ Dcan ↔
        1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧
          1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1 := LiteralReductionGeometry.hDcanCoords P k
              hboundarySquare hstrictBounds hcanonicalDomain y
  let Dact := h.domain.filter (fun x =>
    @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _))
  have himage : Dact = Dcan.image (GaussianTranslation u) := hstrictTranslation
  have heq : Dcan = P4062T1InteriorSquare P.q := LiteralReductionGeometry.heqAt410 P
      squareCoordinates k hDcanCoords
  refine ⟨u, ?_, ?_⟩
  · change Dact = _
    rw [himage, heq]
    rfl
  · intro x hx
    have hs := hstencilDomain x hx
    exact hlapshift x hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

end ApollonianSuperharmonic

end
