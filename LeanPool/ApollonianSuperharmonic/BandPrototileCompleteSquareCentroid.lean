/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidBounds

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares

-- [TABLET NODE: BandPrototileCompleteSquareCentroid]

/-!
# BandPrototileCompleteSquareCentroid

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CompleteSquareProof

private theorem hboundRe :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty), ∀ p ∈ TileRealization T, (↑(reCells.min' reNe) : Real) ≤ p.1
            ∧ p.1 ≤ (↑(reCells.max' reNe) : Real) + 1
    ) := by
  classical
  intro T reCells reNe p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · have hm := Finset.min'_le (T.cells.image (fun x => x.re)) x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    exact le_trans (by exact_mod_cast hm) hpx.1.1
  · have hh := Finset.le_max' (T.cells.image (fun x => x.re))
        (x.re) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hhreal : (x.re : Real) ≤
        (reCells.max' reNe : Real) := by
      exact_mod_cast hh
    linarith [hhreal, hpx.2.1]

private theorem centerRe :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let c := TileCentroid T
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty), (∀ p ∈ TileRealization T, (↑(reCells.min' reNe) : Real) ≤
            p.1 ∧ p.1 ≤ (↑(reCells.max' reNe) : Real) + 1) → ((∀ p ∈ TileRealization T, (2 * c.1
            - p.1, 2 * c.2 - p.2) ∈ TileRealization T) → (
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        (∃ x ∈ T.cells, x.re = mRe) → ((∃ x ∈ T.cells, x.re = MRe) → (2 * c.1 = (mRe : Real) +
            MRe + 1))))
    ) := by
  classical
  intro T c reCells reNe hboundRe reflect_mem mRe MRe minReCell maxReCell
  rcases minReCell with ⟨xmin, hxmin, hxminre⟩
  rcases maxReCell with ⟨xmax, hmax, hmaxre⟩
  have pmin : ((mRe : Real), (xmin.im : Real)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmin, hxmin, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hxminre], by simp []⟩,
      ⟨by simp [hxminre], by simp⟩⟩
  have pmax : (((MRe : Real) + 1), (xmax.im : Real)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmax, hmax, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hmaxre], by simp⟩,
      ⟨by simp [hmaxre], by simp⟩⟩
  have qmin := reflect_mem _ pmin
  have qmax := reflect_mem _ pmax
  have bmin := hboundRe _ qmin
  have bmax := hboundRe _ qmax
  dsimp at bmin bmax
  norm_num at bmin bmax ⊢
  linarith [bmin.2, bmax.1]

private theorem boundIm :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (imNe : imCells.Nonempty), ∀ p ∈ TileRealization T, (imCells.min' imNe : Real) ≤ p.2 ∧
            p.2 ≤ (imCells.max' imNe : Real) + 1
    ) := by
  classical
  intro T imCells imNe p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · exact le_trans (Int.cast_le.mpr (Finset.min'_le _ x.im
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))) hpx.1.2
  · have hh := Finset.le_max' (T.cells.image (fun x => x.im))
        x.im (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hhreal : (x.im : Real) ≤
        ((imCells.max' imNe : Int) : Real) := by
      exact_mod_cast hh
    linarith [hpx.2.2]

private abbrev centerIm :=
  BandPrototileCentroidBounds.imaginaryCenter

private theorem tau_cell :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          let c := TileCentroid T;
          let reCells : Finset Int := T.cells.image fun x => x.re;
          let imCells : Finset Int := T.cells.image fun x => x.im;
          ∀ (reNe : reCells.Nonempty),
            ∀ (imNe : imCells.Nonempty),
              (∀ p ∈ TileRealization T,
                  (2 * c.1 - p.1, 2 * c.2 - p.2) ∈ TileRealization T) →
                let mRe := reCells.min' reNe;
                let MRe := reCells.max' reNe;
                2 * c.1 = (mRe : Real) + MRe + 1 →
                  let mIm := imCells.min' imNe;
                  let MIm := imCells.max' imNe;
                  2 * c.2 = (mIm : Real) + MIm + 1 →
                    let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
                    let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
                    ∀ x ∈ T.cells, tau x ∈ T.cells
    ) := by
  classical
  intro T c reCells imCells reNe imNe reflect_mem mRe MRe centerRe mIm MIm centerIm t tau x hx
  have hp : ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) ∈
      TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    norm_num
  have hq := reflect_mem _ hp
  simp only [TileRealization, Set.mem_iUnion] at hq
  rcases hq with ⟨y, hy, hqy⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hqy
  change (((y.re : Real) ≤ 2 * c.1 - ((x.re : Real) + 1 / 2) ∧
    (y.im : Real) ≤ 2 * c.2 - ((x.im : Real) + 1 / 2)) ∧
    2 * c.1 - ((x.re : Real) + 1 / 2) ≤ (y.re : Real) + 1 ∧
    2 * c.2 - ((x.im : Real) + 1 / 2) ≤ (y.im : Real) + 1) at hqy
  have hxr : (y.re : Real) <
      ((t.re - x.re - 1 : Int) : Real) + 1 := by
    dsimp [t] at hqy ⊢
    rw [centerRe] at hqy
    norm_num at hqy ⊢
    rw [← GaussianInt.intCast_re y, ← GaussianInt.intCast_re x] at hqy
    rw [← GaussianInt.intCast_re y, ← GaussianInt.intCast_re x] at ⊢
    have hyupper : (y.re : Real) ≤ (mRe : Real) + MRe + 1 - ((x.re : Real) + 1 / 2) := by
      exact hqy.1.1
    have hgoal : (y.re : Real) < (mRe : Real) + MRe + 1 - (x.re : Real) - 1 + 1 := by
      linarith
    convert hgoal using 1; norm_num [t]
  have hxl : (((t.re - x.re - 1 : Int) : Real)) ≤ (y.re : Real) := by
    dsimp [t] at hqy ⊢
    rw [centerRe] at hqy
    norm_num at hqy ⊢
    rw [← GaussianInt.intCast_re y, ← GaussianInt.intCast_re x] at hqy
    have hylower : (mRe : Real) + MRe + 1 ≤ (y.re : Real) + 1 + ((x.re : Real) + 1 / 2) := by
      exact hqy.2.1
    have hgoal : (mRe : Real) + MRe + 1 - (x.re : Real) - 1 < (y.re : Real) + 1 := by
      linarith
    have hgoalInt : mRe + MRe + 1 - x.re - 1 < y.re + 1 := by
      exact_mod_cast hgoal
    have hgoalInt' : mRe + MRe + 1 - x.re - 1 ≤ y.re := by omega
    have hreal0 : (mRe : Real) + MRe + 1 - (x.re : Real) - 1 ≤ (y.re : Real) := by
      exact_mod_cast hgoalInt'
    have hreal : (mRe : Real) + MRe + 1 ≤ (y.re : Real) + 1 + (x.re : Real) := by
      linarith
    simpa only [GaussianInt.intCast_re] using hreal
  have hyr : (y.im : Real) <
      ((t.im - x.im - 1 : Int) : Real) + 1 := by
    dsimp [t] at hqy ⊢
    rw [centerIm] at hqy
    norm_num at hqy ⊢
    rw [← GaussianInt.intCast_im y, ← GaussianInt.intCast_im x] at hqy
    rw [← GaussianInt.intCast_im y, ← GaussianInt.intCast_im x] at ⊢
    have hyupper : (y.im : Real) ≤ (mIm : Real) + MIm + 1 - ((x.im : Real) + 1 / 2) := by
      exact hqy.1.2
    have hgoal : (y.im : Real) < (mIm : Real) + MIm + 1 - (x.im : Real) - 1 + 1 := by
      linarith
    convert hgoal using 1; norm_num [t]
  have hyl : (((t.im - x.im - 1 : Int) : Real)) ≤ (y.im : Real) := by
    dsimp [t] at hqy ⊢
    rw [centerIm] at hqy
    norm_num at hqy ⊢
    rw [← GaussianInt.intCast_im y, ← GaussianInt.intCast_im x] at hqy
    have hylower : (mIm : Real) + MIm + 1 ≤ (y.im : Real) + 1 + ((x.im : Real) + 1 / 2) := by
      exact hqy.2.2
    have hgoal : (mIm : Real) + MIm + 1 - (x.im : Real) - 1 < (y.im : Real) + 1 := by
      linarith
    have hgoalInt : mIm + MIm + 1 - x.im - 1 < y.im + 1 := by
      exact_mod_cast hgoal
    have hgoalInt' : mIm + MIm + 1 - x.im - 1 ≤ y.im := by omega
    have hreal0 : (mIm : Real) + MIm + 1 - (x.im : Real) - 1 ≤ (y.im : Real) := by
      exact_mod_cast hgoalInt'
    have hreal : (mIm : Real) + MIm + 1 ≤ (y.im : Real) + 1 + (x.im : Real) := by
      linarith
    simpa only [GaussianInt.intCast_im] using hreal
  have hre : y.re = t.re - x.re - 1 := by
    have hu : y.re < t.re - x.re - 1 + 1 := by exact_mod_cast hxr
    have hl : t.re - x.re - 1 ≤ y.re := by exact_mod_cast hxl
    omega
  have him : y.im = t.im - x.im - 1 := by
    have hu : y.im < t.im - x.im - 1 + 1 := by exact_mod_cast hyr
    have hl : t.im - x.im - 1 ≤ y.im := by exact_mod_cast hyl
    omega
  have heq : y = tau x := by
    apply Zsqrtd.ext <;> dsimp [tau] <;> simp [t, hre, him]
  simpa [heq] using hy

private theorem footprint_forward :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (Finset.Nonempty T.cells) → (
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        (∀ x ∈ T.cells, tau x ∈ T.cells) → (
        let rho : GaussianInt → GaussianInt := fun v => t - v
        ∀ v, v ∈ FootprintVertices T → rho v ∈ FootprintVertices T))
    ) := by
  classical
  intro T hne reCells imCells reNe imNe mRe MRe mIm MIm t tau tau_cell rho v hv
  simp only [FootprintVertices, ite_eq_left hne] at hv ⊢
  rcases hv with ⟨x, hx, hv⟩
  rcases hv with hcase | hcase | hcase | hcase
  · refine ⟨tau x, tau_cell x hx, ?_⟩
    dsimp [rho, tau, t]
    simp [hcase, sub_eq_add_neg, add_comm, add_left_comm]
  · refine ⟨tau x, tau_cell x hx, ?_⟩
    dsimp [rho, tau, t]
    simp [hcase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · refine ⟨tau x, tau_cell x hx, ?_⟩
    dsimp [rho, tau, t]
    simp [hcase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · refine ⟨tau x, tau_cell x hx, ?_⟩
    dsimp [rho, tau, t]
    simp [hcase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private theorem dom_rho :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ((↑h.domain : Set GaussianInt) =
            FootprintVertices T) → (
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let rho : GaussianInt → GaussianInt := fun v => t - v
        (∀ v, v ∈ FootprintVertices T ↔ rho v ∈ FootprintVertices T) → (∀ v, v ∈ h.domain ↔ rho v
            ∈ h.domain))
    ) := by
  classical
  intro T h hdom reCells imCells reNe imNe mRe MRe mIm MIm t rho footprint_rho v
  constructor
  · intro hv
    have hv0 : v ∈ (h.domain : Set GaussianInt) := hv
    have hv' : v ∈ FootprintVertices T := by simpa [hdom] using hv0
    have hw := (footprint_rho v).mp hv'
    change rho v ∈ (h.domain : Set GaussianInt)
    rw [hdom]
    exact hw
  · intro hv
    have hv0 : rho v ∈ (h.domain : Set GaussianInt) := hv
    have hv' : rho v ∈ FootprintVertices T := by simpa [hdom] using hv0
    have hw := (footprint_rho v).mpr hv'
    change v ∈ (h.domain : Set GaussianInt)
    rw [hdom]
    exact hw

private theorem square_tau :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        (∀ x, tau (tau x) = x) → (
        let rho : GaussianInt → GaussianInt := fun v => t - v
        (∀ v, v ∈ h.domain ↔ rho v ∈ h.domain) → (
        let squares := PartialOdometerSquares h
        ∀ x, x ∈ squares ↔ tau x ∈ squares))
    ) := by
  classical
  intro T h reCells imCells reNe imNe mRe MRe mIm MIm t tau tau_involution rho dom_rho squares x
  have forward : ∀ z, z ∈ squares → tau z ∈ squares := by
    intro z hz
    simp only [squares, PartialOdometerSquares, Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hz, hz1, hzi, hz1i⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [rho, tau, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (dom_rho (z +
        1 + ⟨0, 1⟩)).mp hz1i
    · simpa [rho, tau, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (dom_rho (z +
        ⟨0, 1⟩)).mp hzi
    · simpa [rho, tau, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (dom_rho (z +
        1)).mp hz1
    · simpa [rho, tau, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (dom_rho
        z).mp hz
  constructor
  · exact forward x
  · intro hz
    have hw := forward (tau x) hz
    simpa [tau_involution] using hw

private theorem squares_nonempty :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), (Finset.Nonempty T.cells) → (((↑h.domain :
            Set GaussianInt) = FootprintVertices T) → (
        let squares := PartialOdometerSquares h
        squares.Nonempty))
    ) := by
  classical
  intro T h hne hdom squares
  have hne' : T.cells.Nonempty := hne
  rcases hne with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [squares, PartialOdometerSquares, Finset.mem_filter]
  have hd0 : x ∈ h.domain := by
    have hv : x ∈ FootprintVertices T := by
      simp only [FootprintVertices, ite_eq_left hne']
      exact ⟨x, hx, by simp⟩
    exact (show x ∈ (h.domain : Set GaussianInt) from hdom ▸ hv)
  have hd1 : x + 1 ∈ h.domain := by
    have hv : x + 1 ∈ FootprintVertices T := by
      simp only [FootprintVertices, ite_eq_left hne']
      exact ⟨x, hx, by simp⟩
    exact (show x + 1 ∈ (h.domain : Set GaussianInt) from hdom ▸ hv)
  have hdi : x + ⟨0, 1⟩ ∈ h.domain := by
    have hv : x + ⟨0, 1⟩ ∈ FootprintVertices T := by
      simp only [FootprintVertices, ite_eq_left hne']
      exact ⟨x, hx, by simp⟩
    exact (show x + ⟨0, 1⟩ ∈ (h.domain : Set GaussianInt) from hdom ▸ hv)
  have hd1i : x + 1 + ⟨0, 1⟩ ∈ h.domain := by
    have hv : x + 1 + ⟨0, 1⟩ ∈ FootprintVertices T := by
      simp only [FootprintVertices, ite_eq_left hne']
      exact ⟨x, hx, by simp⟩
    exact (show x + 1 + ⟨0, 1⟩ ∈ (h.domain : Set GaussianInt) from hdom ▸ hv)
  exact ⟨hd0, hd1, hdi, hd1i⟩

private theorem sumRe :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        (∀ x, tau (tau x) = x) → (
        let squares := PartialOdometerSquares h
        (∀ x, x ∈ squares ↔ tau x ∈ squares) → (squares.sum (fun x => (x.re : Real)) =
            squares.sum (fun x => ((tau x).re : Real))))
    ) := by
  classical
  intro T h reCells imCells reNe imNe mRe MRe mIm MIm t tau tau_involution squares square_tau
  apply Finset.sum_bij (fun x hx => tau x)
  · intro x hx
    exact (square_tau x).mp hx
  · intro x hx y hy heq
    have hi := congrArg tau heq
    simpa [tau_involution] using hi
  · intro y hy
    refine ⟨tau y, (square_tau y).mp hy, ?_⟩
    exact tau_involution y
  · intro x hx
    exact (congrArg (fun z => (z.re : Real)) (tau_involution x)).symm

private theorem sumIm :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        (∀ x, tau (tau x) = x) → (
        let squares := PartialOdometerSquares h
        (∀ x, x ∈ squares ↔ tau x ∈ squares) → (squares.sum (fun x => (x.im : Real)) =
            squares.sum (fun x => ((tau x).im : Real))))
    ) := by
  classical
  intro T h reCells imCells reNe imNe mRe MRe mIm MIm t tau tau_involution squares square_tau
  apply Finset.sum_bij (fun x hx => tau x)
  · intro x hx
    exact (square_tau x).mp hx
  · intro x hx y hy heq
    have hi := congrArg tau heq
    simpa [tau_involution] using hi
  · intro y hy
    refine ⟨tau y, (square_tau y).mp hy, ?_⟩
    exact tau_involution y
  · intro x hx
    exact (congrArg (fun z => (z.im : Real)) (tau_involution x)).symm

private theorem sumRe_formula :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        let squares := PartialOdometerSquares h
        (squares.sum (fun x => (x.re : Real)) = squares.sum (fun x => ((tau x).re : Real))) → (2
            * squares.sum (fun x => (x.re : Real)) = (squares.card : Real) * (t.re : Real) -
            squares.card)
    ) := by
  classical
  intro T h reCells imCells reNe imNe mRe MRe mIm MIm t tau squares sumRe
  have hs := sumRe
  dsimp [tau, t] at hs
  simp only [
    sub_zero,
    ] at hs
  push_cast at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const] at hs
  simp only [Int.reduceNeg, GaussianInt.intCast_re, smul_add, nsmul_eq_mul, Finset.sum_const,
      mul_one] at hs
  have hEq : squares.sum (fun x => (x.re : Real)) =
      squares.sum (fun x => (GaussianInt.toComplex x).re) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (GaussianInt.intCast_re x)
  have hs' : squares.sum (fun x => (x.re : Real)) =
      (squares.card : Real) * (mRe : Real) + squares.card * MRe +
        squares.card - squares.sum (fun x => (x.re : Real)) - squares.card := by
    rw [hEq]
    simpa using hs
  dsimp [t]
  push_cast
  ring_nf at hs' ⊢
  linarith

private theorem sumIm_formula :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
        let squares := PartialOdometerSquares h
        (squares.sum (fun x => (x.im : Real)) = squares.sum (fun x => ((tau x).im : Real))) → (2
            * squares.sum (fun x => (x.im : Real)) = (squares.card : Real) * (t.im : Real) -
            squares.card)
    ) := by
  classical
  intro T h reCells imCells reNe imNe mRe MRe mIm MIm t tau squares sumIm
  have hs := sumIm
  dsimp [tau, t] at hs
  simp only [
    sub_zero,
    ] at hs
  push_cast at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const] at hs
  simp only [Int.reduceNeg, GaussianInt.intCast_im, smul_add, nsmul_eq_mul, Finset.sum_const,
      mul_one] at hs
  have hEq : squares.sum (fun x => (x.im : Real)) =
      squares.sum (fun x => (GaussianInt.toComplex x).im) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (GaussianInt.intCast_im x)
  have hs' : squares.sum (fun x => (x.im : Real)) =
      (squares.card : Real) * (mIm : Real) + squares.card * MIm +
        squares.card - squares.sum (fun x => (x.im : Real)) - squares.card := by
    rw [hEq]
    simpa using hs
  dsimp [t]
  push_cast
  ring_nf at hs' ⊢
  linarith

private theorem result_re :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let c := TileCentroid T
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        (2 * c.1 = (mRe : Real) + MRe + 1) → (
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let squares := PartialOdometerSquares h
        (2 * squares.sum (fun x => (x.re : Real)) = (squares.card : Real) * (t.re : Real) -
            squares.card) → (((0 : Real) < squares.card) → (squares.sum (fun x => ((x.re : Real)
            + 1 / 2)) / (squares.card : Real) = c.1)))
    ) := by
  classical
  intro T h c reCells imCells reNe imNe mRe MRe centerRe mIm MIm t squares sumRe_formula card_pos
  dsimp [t] at sumRe_formula
  have hcenter : (t.re : Real) = 2 * c.1 := by
    dsimp [t]
    push_cast
    linarith [centerRe]
  rw [hcenter] at sumRe_formula
  have hshift : squares.sum (fun x => ((x.re : Real) + 1 / 2)) =
      squares.sum (fun x => (x.re : Real)) + squares.card / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const]
    ring
  rw [hshift]
  field_simp
  ring_nf at sumRe_formula ⊢
  linarith

private theorem result_im :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let c := TileCentroid T
        let reCells : Finset Int := T.cells.image (fun x => x.re)
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        (2 * c.2 = (mIm : Real) + MIm + 1) → (
        let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let squares := PartialOdometerSquares h
        (2 * squares.sum (fun x => (x.im : Real)) = (squares.card : Real) * (t.im : Real) -
            squares.card) → (((0 : Real) < squares.card) → (squares.sum (fun x => ((x.im : Real)
            + 1 / 2)) / (squares.card : Real) = c.2)))
    ) := by
  classical
  intro T h c reCells imCells reNe imNe mRe MRe mIm MIm centerIm t squares sumIm_formula card_pos
  dsimp [t] at sumIm_formula
  have hcenter : (t.im : Real) = 2 * c.2 := by
    dsimp [t]
    push_cast
    linarith [centerIm]
  rw [hcenter] at sumIm_formula
  have hshift : squares.sum (fun x => ((x.im : Real) + 1 / 2)) =
      squares.sum (fun x => (x.im : Real)) + squares.card / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const]
    ring
  rw [hshift]
  field_simp
  ring_nf at sumIm_formula ⊢
  linarith

end CompleteSquareProof

theorem BandPrototileCompleteSquareCentroid
    (C : CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
    (hT : BandPrototile C T) (hne : T.cells.Nonempty)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T) :
    let S := PartialOdometerSquares h
    S.Nonempty ∧
      ((∑ x ∈ S, ((x.re : Real) + 1 / 2)) / (S.card : Real),
        (∑ x ∈ S, ((x.im : Real) + 1 / 2)) / (S.card : Real)) =
        TileCentroid T := by
-- BODY
  dsimp
  let c := TileCentroid T
  let reCells : Finset Int := T.cells.image (fun x => x.re)
  let imCells : Finset Int := T.cells.image (fun x => x.im)
  have reNe : reCells.Nonempty := by
    dsimp [reCells]
    exact Finset.image_nonempty.mpr hne
  have imNe : imCells.Nonempty := by
    dsimp [imCells]
    exact Finset.image_nonempty.mpr hne
  have hcentral : CentrallyReflectedAt c T T :=
    BandPrototileCentralSymmetry C T hT
  have hboundRe : ∀ p ∈ TileRealization T,
      (↑(reCells.min' reNe) : Real) ≤ p.1 ∧
        p.1 ≤ (↑(reCells.max' reNe) : Real) + 1 := CompleteSquareProof.hboundRe T reNe
  have reflect_mem : ∀ p ∈ TileRealization T,
      (2 * c.1 - p.1, 2 * c.2 - p.2) ∈ TileRealization T := by
    intro p hp
    rw [hcentral]
    exact ⟨p, hp, rfl⟩
  let mRe := reCells.min' reNe
  let MRe := reCells.max' reNe
  have minReCell : ∃ x ∈ T.cells, x.re = mRe := by
    have hm := Finset.min'_mem reCells reNe
    rcases Finset.mem_image.mp hm with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  have maxReCell : ∃ x ∈ T.cells, x.re = MRe := by
    have hm := Finset.max'_mem reCells reNe
    rcases Finset.mem_image.mp hm with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  have centerRe : 2 * c.1 = (mRe : Real) + MRe + 1 := CompleteSquareProof.centerRe T reNe
      hboundRe reflect_mem minReCell maxReCell
  have boundIm : ∀ p ∈ TileRealization T,
      (imCells.min' imNe : Real) ≤ p.2 ∧ p.2 ≤ (imCells.max' imNe : Real) + 1 :=
          CompleteSquareProof.boundIm T imNe
  let mIm := imCells.min' imNe
  let MIm := imCells.max' imNe
  have minImCell : ∃ x ∈ T.cells, x.im = mIm := by
    rcases Finset.mem_image.mp (Finset.min'_mem imCells imNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  have maxImCell : ∃ x ∈ T.cells, x.im = MIm := by
    rcases Finset.mem_image.mp (Finset.max'_mem imCells imNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  have centerIm : 2 * c.2 = (mIm : Real) + MIm + 1 := CompleteSquareProof.centerIm T imNe
      reflect_mem boundIm minImCell maxImCell
  let t : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
  let tau : GaussianInt → GaussianInt := fun x => t - x - 1 - ⟨0, 1⟩
  have tau_involution : ∀ x, tau (tau x) = x := by
    intro x
    dsimp [tau]
    apply Zsqrtd.ext <;> dsimp [t] <;> ring
  have tau_cell : ∀ x ∈ T.cells, tau x ∈ T.cells := CompleteSquareProof.tau_cell T reNe imNe
      reflect_mem centerRe centerIm
  let rho : GaussianInt → GaussianInt := fun v => t - v
  have footprint_forward : ∀ v, v ∈ FootprintVertices T →
      rho v ∈ FootprintVertices T := CompleteSquareProof.footprint_forward T hne reNe imNe tau_cell
  have rho_involution : ∀ v, rho (rho v) = v := by
    intro v
    simp [rho]
  have footprint_rho : ∀ v, v ∈ FootprintVertices T ↔
      rho v ∈ FootprintVertices T := by
    intro v
    constructor
    · exact footprint_forward v
    · intro hv
      have hi := rho_involution v
      rw [← hi]
      exact footprint_forward (rho v) hv
  have dom_rho : ∀ v, v ∈ h.domain ↔ rho v ∈ h.domain := CompleteSquareProof.dom_rho T h hdom
      reNe imNe footprint_rho
  let squares := PartialOdometerSquares h
  have square_tau : ∀ x, x ∈ squares ↔ tau x ∈ squares := CompleteSquareProof.square_tau T h reNe
      imNe tau_involution dom_rho
  have squares_nonempty : squares.Nonempty := CompleteSquareProof.squares_nonempty T h hne hdom
  have sumRe : squares.sum (fun x => (x.re : Real)) =
      squares.sum (fun x => ((tau x).re : Real)) := CompleteSquareProof.sumRe T h reNe imNe
          tau_involution square_tau
  have sumIm : squares.sum (fun x => (x.im : Real)) =
      squares.sum (fun x => ((tau x).im : Real)) := CompleteSquareProof.sumIm T h reNe imNe
          tau_involution square_tau
  have sumRe_formula : 2 * squares.sum (fun x => (x.re : Real)) =
      (squares.card : Real) * (t.re : Real) - squares.card := CompleteSquareProof.sumRe_formula T
          h reNe imNe sumRe
  have sumIm_formula : 2 * squares.sum (fun x => (x.im : Real)) =
      (squares.card : Real) * (t.im : Real) - squares.card := CompleteSquareProof.sumIm_formula T
          h reNe imNe sumIm
  have card_pos : (0 : Real) < squares.card := by
    exact_mod_cast squares_nonempty.card_pos
  have result_re :
      squares.sum (fun x => ((x.re : Real) + 1 / 2)) /
          (squares.card : Real) = c.1 := CompleteSquareProof.result_re T h reNe imNe centerRe
              sumRe_formula card_pos
  have result_im :
      squares.sum (fun x => ((x.im : Real) + 1 / 2)) /
          (squares.card : Real) = c.2 := CompleteSquareProof.result_im T h reNe imNe centerIm
              sumIm_formula card_pos
  exact ⟨by simpa [squares] using squares_nonempty,
    Prod.ext (by simpa [squares, c] using result_re)
      (by simpa [squares, c] using result_im)⟩

end ApollonianSuperharmonic

end
