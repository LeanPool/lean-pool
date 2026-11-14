/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.TopologicalDiskLocallyPuncturedPreconnected

/-!
# LatticeTileNoCheckerboard

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped Topology

-- [TABLET NODE: LatticeTileNoCheckerboard]
namespace NoCheckerboardProof

private theorem square_mem_realization :
    ∀ (T : ProtoTile), ∀ {x : GaussianInt}, (x ∈ T.cells) → (∀ {p : Real × Real}, (p ∈
        ClosedSquareRealization x) → (p ∈ TileRealization T)) := by
  classical
  intro T x hx p hp
  simp only [TileRealization, Set.mem_iUnion]
  exact ⟨x, ⟨hx, hp⟩⟩

private theorem local_cell :
    ∀ (z : GaussianInt),
    let zR : Real × Real := (((z.re : Int) : Real), ((z.im : Int) : Real))
    ∀ {x : GaussianInt}, ∀ {p : Real × Real}, (dist p zR < (1 / 2 : Real)) → ((p ∈
        ClosedSquareRealization x) → (x = z ∨ x = z - 1 ∨ x = z - ⟨0, 1⟩ ∨ x = z - 1 - ⟨0, 1⟩))
            := by
  classical
  intro z zR x p hpnear hpsq
  have hdist1 : |p.1 - zR.1| < (1 / 2 : Real) := by
    have := lt_of_le_of_lt (le_max_left (dist p.1 zR.1) (dist p.2 zR.2)) hpnear
    simpa [Prod.dist_eq, Real.dist_eq] using this
  have hdist2 : |p.2 - zR.2| < (1 / 2 : Real) := by
    have := lt_of_le_of_lt (le_max_right (dist p.1 zR.1) (dist p.2 zR.2)) hpnear
    simpa [Prod.dist_eq, Real.dist_eq] using this
  have hsquare := hpsq
  change (((x.re : Int) : Real), ((x.im : Int) : Real)) ≤ p ∧
    p ≤ ((((x.re : Int) : Real) + 1), (((x.im : Int) : Real) + 1)) at hsquare
  have hrele : x.re ≤ z.re := by
    by_contra hn
    have hstep : ((z.re : Int) : Real) + 1 ≤ ((x.re : Int) : Real) := by
      exact_mod_cast (show z.re + 1 ≤ x.re by omega)
    have habs := (abs_lt.mp hdist1).2
    dsimp [zR] at habs
    linarith [hsquare.1.1]
  have hrige : z.re - 1 ≤ x.re := by
    by_contra hn
    have hstep : ((x.re : Int) : Real) + 1 ≤ ((z.re : Int) : Real) - 1 := by
      exact_mod_cast (show x.re + 1 ≤ z.re - 1 by omega)
    have habs := (abs_lt.mp hdist1).1
    dsimp [zR] at habs
    linarith [hsquare.2.1]
  have himle : x.im ≤ z.im := by
    by_contra hn
    have hstep : ((z.im : Int) : Real) + 1 ≤ ((x.im : Int) : Real) := by
      exact_mod_cast (show z.im + 1 ≤ x.im by omega)
    have habs := (abs_lt.mp hdist2).2
    dsimp [zR] at habs
    linarith [hsquare.1.2]
  have himge : z.im - 1 ≤ x.im := by
    by_contra hn
    have hstep : ((x.im : Int) : Real) + 1 ≤ ((z.im : Int) : Real) - 1 := by
      exact_mod_cast (show x.im + 1 ≤ z.im - 1 by omega)
    have habs := (abs_lt.mp hdist2).1
    dsimp [zR] at habs
    linarith [hsquare.2.2]
  have hre : x.re = z.re ∨ x.re = z.re - 1 := by omega
  have him : x.im = z.im ∨ x.im = z.im - 1 := by omega
  rcases hre with hre | hre <;> rcases him with him | him
  · left
    apply Zsqrtd.ext <;> simp_all
  · right; right; left
    apply Zsqrtd.ext <;> simp_all
  · right; left
    apply Zsqrtd.ext <;> simp_all
  · right; right; right
    apply Zsqrtd.ext <;> simp_all

end NoCheckerboardProof

namespace NoCheckerboardGeometry

private theorem hpminusSq :
    ∀ (z : GaussianInt),
    let zR : Real × Real := (((z.re : Int) : Real), ((z.im : Int) : Real))
    ∀ (e : ℝ),
    let η : Real := min (e / 2) (1 / 4)
    (0 < η) → ((η ≤ 1) → (
    let pminus : Real × Real := (zR.1 - η, zR.2 - η)
    pminus ∈ ClosedSquareRealization (z - 1 - ⟨0, 1⟩))) := by
  classical
  intro z zR e η hη hη1 pminus
  change (((((z - 1 - ⟨0, 1⟩).re : Int) : Real)),
      (((z - 1 - ⟨0, 1⟩).im : Int) : Real)) ≤ pminus ∧
    pminus ≤ (((((z - 1 - ⟨0, 1⟩).re : Int) : Real)) + 1,
      (((z - 1 - ⟨0, 1⟩).im : Int) : Real) + 1)
  dsimp [pminus, zR]
  simp only [Int.reduceNeg, sub_zero, Int.cast_sub,
    GaussianInt.intCast_re, Int.cast_one,
    GaussianInt.intCast_im, Prod.mk_le_mk]
  constructor <;> constructor <;> linarith

private theorem hfnzAt271 :
    ∀ (T : ProtoTile), ∀ (z : GaussianInt),
    let zR : Real × Real := (((z.re : Int) : Real), ((z.im : Int) : Real))
    (∀ {x : GaussianInt}, ∀ {p : Real × Real}, (dist p zR < (1 / 2 : Real)) → ((p ∈
        ClosedSquareRealization x) → (x = z ∨ x = z - 1 ∨ x = z - ⟨0, 1⟩ ∨ x = z - 1 - ⟨0, 1⟩)))
        → ((z ∈ (↑T.cells : Set LatticeCell) ∧ z - (1 : GaussianInt) - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈
        (↑T.cells : Set LatticeCell) ∧ z - (1 : GaussianInt) ∉ (↑T.cells : Set LatticeCell) ∧ z -
        ⟨(0 : ℤ), (1 : ℤ)⟩ ∉ (↑T.cells : Set LatticeCell)) → (
    let S : Set (Real × Real) := TileRealization T
    ∀ (hzRmem : zR ∈ S),
    let zS : S := ⟨zR, hzRmem⟩
    let U : Set S := {p | dist (p : Real × Real) zR < (1 / 2 : Real)}
    ∀ (W : Set (↑S : Type)), (W ⊆ U) → (
    let f : S → Real := fun q =>
      ((q : Real × Real).1 - zR.1) + ((q : Real × Real).2 - zR.2)
    ∀ y ∈ W \ {zS}, f y ≠ 0))) := by
  classical
  intro T z zR local_cell hdiag S hzRmem zS U W hWU f y hy hyzero
  have hyU := hWU hy.1
  have hynear : dist (y : Real × Real) zR < (1 / 2 : Real) := hyU
  have hymem : (y : Real × Real) ∈ TileRealization T := y.property
  simp only [TileRealization, Set.mem_iUnion] at hymem
  rcases hymem with ⟨x, hxcell, hysq⟩
  rcases local_cell hynear hysq with hx | hx | hx | hx
  · subst x
    have hsquare := hysq
    change (((z.re : Int) : Real), ((z.im : Int) : Real)) ≤ (y : Real × Real) ∧
      (y : Real × Real) ≤
        ((((z.re : Int) : Real) + 1), (((z.im : Int) : Real) + 1)) at hsquare
    have hy1 : (y : Real × Real).1 = zR.1 := by
      dsimp [f, zR] at hyzero
      dsimp [zR]
      linarith [hsquare.1.1, hsquare.1.2]
    have hy2 : (y : Real × Real).2 = zR.2 := by
      dsimp [f, zR] at hyzero
      dsimp [zR]
      linarith [hsquare.1.1, hsquare.1.2]
    apply hy.2
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    exact Prod.ext hy1 hy2
  · rw [hx] at hxcell
    exact hdiag.2.2.1 hxcell
  · rw [hx] at hxcell
    exact hdiag.2.2.2 hxcell
  · rw [hx] at hysq
    have hsquare := hysq
    change (((((z - 1 - ⟨0, 1⟩).re : Int) : Real)),
        (((z - 1 - ⟨0, 1⟩).im : Int) : Real)) ≤ (y : Real × Real) ∧
      (y : Real × Real) ≤
        (((((z - 1 - ⟨0, 1⟩).re : Int) : Real)) + 1,
        (((z - 1 - ⟨0, 1⟩).im : Int) : Real) + 1) at hsquare
    have hupper1 : (y : Real × Real).1 ≤ zR.1 := by
      dsimp [zR]
      have := hsquare.2.1
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      linarith
    have hupper2 : (y : Real × Real).2 ≤ zR.2 := by
      dsimp [zR]
      have := hsquare.2.2
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      linarith
    have hy1 : (y : Real × Real).1 = zR.1 := by
      dsimp [f] at hyzero
      linarith
    have hy2 : (y : Real × Real).2 = zR.2 := by
      dsimp [f] at hyzero
      linarith
    apply hy.2
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    exact Prod.ext hy1 hy2

private theorem hfnzAt414 :
    ∀ (T : ProtoTile), ∀ (z : GaussianInt),
    let zR : Real × Real := (((z.re : Int) : Real), ((z.im : Int) : Real))
    (∀ {x : GaussianInt}, ∀ {p : Real × Real}, (dist p zR < (1 / 2 : Real)) → ((p ∈
        ClosedSquareRealization x) → (x = z ∨ x = z - 1 ∨ x = z - ⟨0, 1⟩ ∨ x = z - 1 - ⟨0, 1⟩)))
        → ((z - (1 : GaussianInt) ∈ (↑T.cells : Set LatticeCell) ∧ z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈
        (↑T.cells : Set LatticeCell) ∧ z ∉ (↑T.cells : Set LatticeCell) ∧ z - (1 : GaussianInt) -
        ⟨(0 : ℤ), (1 : ℤ)⟩ ∉ (↑T.cells : Set LatticeCell)) → (
    let S : Set (Real × Real) := TileRealization T
    ∀ (hzRmem : zR ∈ S),
    let zS : S := ⟨zR, hzRmem⟩
    let U : Set S := {p | dist (p : Real × Real) zR < (1 / 2 : Real)}
    ∀ (W : Set (↑S : Type)), (W ⊆ U) → (
    let f : S → Real := fun q =>
      ((q : Real × Real).1 - zR.1) - ((q : Real × Real).2 - zR.2)
    ∀ y ∈ W \ {zS}, f y ≠ 0))) := by
  classical
  intro T z zR local_cell hdiag S hzRmem zS U W hWU f y hy hyzero
  have hyU := hWU hy.1
  have hynear : dist (y : Real × Real) zR < (1 / 2 : Real) := hyU
  have hymem : (y : Real × Real) ∈ TileRealization T := y.property
  simp only [TileRealization, Set.mem_iUnion] at hymem
  rcases hymem with ⟨x, hxcell, hysq⟩
  rcases local_cell hynear hysq with hx | hx | hx | hx
  · rw [hx] at hxcell
    exact hdiag.2.2.1 hxcell
  · rw [hx] at hysq
    have hsquare := hysq
    change (((((z - 1).re : Int) : Real)), (((z - 1).im : Int) : Real)) ≤
        (y : Real × Real) ∧
      (y : Real × Real) ≤ (((((z - 1).re : Int) : Real)) + 1,
        (((z - 1).im : Int) : Real) + 1) at hsquare
    have hupper1 : (y : Real × Real).1 ≤ zR.1 := by
      dsimp [zR]
      have := hsquare.2.1
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      linarith
    have hlower2 : zR.2 ≤ (y : Real × Real).2 := by
      dsimp [zR]
      have := hsquare.1.2
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      exact this
    have hy1 : (y : Real × Real).1 = zR.1 := by
      dsimp [f] at hyzero
      linarith
    have hy2 : (y : Real × Real).2 = zR.2 := by
      dsimp [f] at hyzero
      linarith
    apply hy.2
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    exact Prod.ext hy1 hy2
  · rw [hx] at hysq
    have hsquare := hysq
    change (((((z - ⟨0, 1⟩).re : Int) : Real)),
        (((z - ⟨0, 1⟩).im : Int) : Real)) ≤ (y : Real × Real) ∧
      (y : Real × Real) ≤ (((((z - ⟨0, 1⟩).re : Int) : Real)) + 1,
        (((z - ⟨0, 1⟩).im : Int) : Real) + 1) at hsquare
    have hlower1 : zR.1 ≤ (y : Real × Real).1 := by
      dsimp [zR]
      have := hsquare.1.1
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      exact this
    have hupper2 : (y : Real × Real).2 ≤ zR.2 := by
      dsimp [zR]
      have := hsquare.2.2
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub] at this ⊢
      linarith
    have hy1 : (y : Real × Real).1 = zR.1 := by
      dsimp [f] at hyzero
      linarith
    have hy2 : (y : Real × Real).2 = zR.2 := by
      dsimp [f] at hyzero
      linarith
    apply hy.2
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    exact Prod.ext hy1 hy2
  · rw [hx] at hxcell
    exact hdiag.2.2.2 hxcell

end NoCheckerboardGeometry

theorem LatticeTileNoCheckerboard (T : ProtoTile) (hT : LatticeTile T) :
    NoCheckerboardCellVertex (T.cells : Set LatticeCell) := by
-- BODY
  unfold NoCheckerboardCellVertex
  intro z hz
  let zR : Real × Real := (((z.re : Int) : Real), ((z.im : Int) : Real))
  have square_mem_realization {x : GaussianInt} (hx : x ∈ T.cells)
      {p : Real × Real} (hp : p ∈ ClosedSquareRealization x) :
      p ∈ TileRealization T := NoCheckerboardProof.square_mem_realization T (x := x) hx (p := p) hp
  have local_cell {x : GaussianInt} {p : Real × Real}
      (hpnear : dist p zR < (1 / 2 : Real))
      (hpsq : p ∈ ClosedSquareRealization x) :
      x = z ∨ x = z - 1 ∨ x = z - ⟨0, 1⟩ ∨ x = z - 1 - ⟨0, 1⟩ := NoCheckerboardProof.local_cell z
          (x := x) (p := p) hpnear hpsq
  rcases hz with hdiag | hdiag
  · let S : Set (Real × Real) := TileRealization T
    have hzRSq : zR ∈ ClosedSquareRealization z := by
      change (((z.re : Int) : Real), ((z.im : Int) : Real)) ≤ zR ∧
        zR ≤ ((((z.re : Int) : Real) + 1), (((z.im : Int) : Real) + 1))
      dsimp [zR]
      constructor <;> constructor <;> norm_num
    have hzRmem : zR ∈ S := square_mem_realization hdiag.1 hzRSq
    let zS : S := ⟨zR, hzRmem⟩
    let U : Set S := {p | dist (p : Real × Real) zR < (1 / 2 : Real)}
    have hUnhds : U ∈ nhds zS := by
      change (fun p : S => (p : Real × Real)) ⁻¹' Metric.ball zR (1 / 2) ∈ nhds zS
      exact continuous_subtype_val.continuousAt
        (Metric.ball_mem_nhds zR (by norm_num))
    have hdisk : TopologicalDisk S := hT
    rcases TopologicalDiskLocallyPuncturedPreconnected S hdisk zS U hUnhds with
      ⟨W, hWnhds, hWU, hWconn⟩
    have hWpre := hWconn.isPreconnected
    rcases Metric.mem_nhds_iff.mp hWnhds with ⟨e, he, heW⟩
    let η : Real := min (e / 2) (1 / 4)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηe : η < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hη1 : η ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    let pplus : Real × Real := (zR.1 + η, zR.2 + η)
    let pminus : Real × Real := (zR.1 - η, zR.2 - η)
    have hpplusSq : pplus ∈ ClosedSquareRealization z := by
      change (((z.re : Int) : Real), ((z.im : Int) : Real)) ≤ pplus ∧
        pplus ≤ ((((z.re : Int) : Real) + 1), (((z.im : Int) : Real) + 1))
      dsimp [pplus, zR]
      constructor <;> constructor <;> linarith
    have hpplusS : pplus ∈ S := square_mem_realization hdiag.1 hpplusSq
    have hpminusSq : pminus ∈ ClosedSquareRealization (z - 1 - ⟨0, 1⟩) :=
        NoCheckerboardGeometry.hpminusSq z e hη hη1
    have hpminusS : pminus ∈ S := square_mem_realization hdiag.2.1 hpminusSq
    let P : S := ⟨pplus, hpplusS⟩
    let M : S := ⟨pminus, hpminusS⟩
    have hdistP : dist P zS = η := by
      change dist pplus zR = η
      rw [Prod.dist_eq]
      dsimp [pplus]
      rw [Real.dist_eq, Real.dist_eq]
      simp [abs_of_pos hη]
    have hdistM : dist M zS = η := by
      change dist pminus zR = η
      rw [Prod.dist_eq]
      dsimp [pminus]
      rw [Real.dist_eq, Real.dist_eq]
      simp [abs_of_pos hη]
    have hPW : P ∈ W := heW (by simpa [hdistP] using hηe)
    have hMW : M ∈ W := heW (by simpa [hdistM] using hηe)
    have hPne : P ≠ zS := by
      intro heq
      have := congrArg (fun q : S => (q : Real × Real).1) heq
      dsimp [P, zS, pplus, zR] at this
      linarith
    have hMne : M ≠ zS := by
      intro heq
      have := congrArg (fun q : S => (q : Real × Real).1) heq
      dsimp [M, zS, pminus, zR] at this
      linarith
    have hPdiff : P ∈ W \ {zS} := ⟨hPW, by simpa using hPne⟩
    have hMdiff : M ∈ W \ {zS} := ⟨hMW, by simpa using hMne⟩
    let f : S → Real := fun q =>
      ((q : Real × Real).1 - zR.1) + ((q : Real × Real).2 - zR.2)
    have hfcont : Continuous f := by
      dsimp [f]
      fun_prop
    have hfP : f P = 2 * η := by
      dsimp [f, P, pplus, zR]
      ring
    have hfM : f M = -(2 * η) := by
      dsimp [f, M, pminus, zR]
      ring
    have hfnz : ∀ y ∈ W \ {zS}, f y ≠ 0 := NoCheckerboardGeometry.hfnzAt271 T z local_cell hdiag
        hzRmem W hWU
    have hzeroIcc : (0 : Real) ∈ Set.Icc (f M) (f P) := by
      rw [hfM, hfP]
      constructor <;> linarith
    rcases hWpre.intermediate_value hMdiff hPdiff hfcont.continuousOn hzeroIcc with
      ⟨y, hy, hyzero⟩
    exact hfnz y hy hyzero
  · let S : Set (Real × Real) := TileRealization T
    have hzRSq : zR ∈ ClosedSquareRealization (z - 1) := by
      change (((((z - 1).re : Int) : Real)), (((z - 1).im : Int) : Real)) ≤ zR ∧
        zR ≤ (((((z - 1).re : Int) : Real)) + 1,
          (((z - 1).im : Int) : Real) + 1)
      dsimp [zR]
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub]
    have hzRmem : zR ∈ S := square_mem_realization hdiag.1 hzRSq
    let zS : S := ⟨zR, hzRmem⟩
    let U : Set S := {p | dist (p : Real × Real) zR < (1 / 2 : Real)}
    have hUnhds : U ∈ nhds zS := by
      change (fun p : S => (p : Real × Real)) ⁻¹' Metric.ball zR (1 / 2) ∈ nhds zS
      exact continuous_subtype_val.continuousAt
        (Metric.ball_mem_nhds zR (by norm_num))
    have hdisk : TopologicalDisk S := hT
    rcases TopologicalDiskLocallyPuncturedPreconnected S hdisk zS U hUnhds with
      ⟨W, hWnhds, hWU, hWconn⟩
    have hWpre := hWconn.isPreconnected
    rcases Metric.mem_nhds_iff.mp hWnhds with ⟨e, he, heW⟩
    let η : Real := min (e / 2) (1 / 4)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηe : η < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hη1 : η ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    let pNW : Real × Real := (zR.1 - η, zR.2 + η)
    let pSE : Real × Real := (zR.1 + η, zR.2 - η)
    have hpNWSq : pNW ∈ ClosedSquareRealization (z - 1) := by
      change (((((z - 1).re : Int) : Real)), (((z - 1).im : Int) : Real)) ≤ pNW ∧
        pNW ≤ (((((z - 1).re : Int) : Real)) + 1,
          (((z - 1).im : Int) : Real) + 1)
      dsimp [pNW, zR]
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> constructor <;> linarith
    have hpNWS : pNW ∈ S := square_mem_realization hdiag.1 hpNWSq
    have hpSESq : pSE ∈ ClosedSquareRealization (z - ⟨0, 1⟩) := by
      change (((((z - ⟨0, 1⟩).re : Int) : Real)),
          (((z - ⟨0, 1⟩).im : Int) : Real)) ≤ pSE ∧
        pSE ≤ (((((z - ⟨0, 1⟩).re : Int) : Real)) + 1,
          (((z - ⟨0, 1⟩).im : Int) : Real) + 1)
      dsimp [pSE, zR]
      norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> constructor <;> linarith
    have hpSES : pSE ∈ S := square_mem_realization hdiag.2.1 hpSESq
    let NW : S := ⟨pNW, hpNWS⟩
    let SE : S := ⟨pSE, hpSES⟩
    have hdistNW : dist NW zS = η := by
      change dist pNW zR = η
      rw [Prod.dist_eq]
      dsimp [pNW]
      rw [Real.dist_eq, Real.dist_eq]
      simp [abs_of_pos hη]
    have hdistSE : dist SE zS = η := by
      change dist pSE zR = η
      rw [Prod.dist_eq]
      dsimp [pSE]
      rw [Real.dist_eq, Real.dist_eq]
      simp [abs_of_pos hη]
    have hNWW : NW ∈ W := heW (by simpa [hdistNW] using hηe)
    have hSEW : SE ∈ W := heW (by simpa [hdistSE] using hηe)
    have hNWne : NW ≠ zS := by
      intro heq
      have := congrArg (fun q : S => (q : Real × Real).1) heq
      dsimp [NW, zS, pNW, zR] at this
      linarith
    have hSEne : SE ≠ zS := by
      intro heq
      have := congrArg (fun q : S => (q : Real × Real).1) heq
      dsimp [SE, zS, pSE, zR] at this
      linarith
    have hNWdiff : NW ∈ W \ {zS} := ⟨hNWW, by simpa using hNWne⟩
    have hSEdiff : SE ∈ W \ {zS} := ⟨hSEW, by simpa using hSEne⟩
    let f : S → Real := fun q =>
      ((q : Real × Real).1 - zR.1) - ((q : Real × Real).2 - zR.2)
    have hfcont : Continuous f := by
      dsimp [f]
      fun_prop
    have hfNW : f NW = -(2 * η) := by
      dsimp [f, NW, pNW, zR]
      ring
    have hfSE : f SE = 2 * η := by
      dsimp [f, SE, pSE, zR]
      ring
    have hfnz : ∀ y ∈ W \ {zS}, f y ≠ 0 := NoCheckerboardGeometry.hfnzAt414 T z local_cell hdiag
        hzRmem W hWU
    have hzeroIcc : (0 : Real) ∈ Set.Icc (f NW) (f SE) := by
      rw [hfNW, hfSE]
      constructor <;> linarith
    rcases hWpre.intermediate_value hNWdiff hSEdiff hfcont.continuousOn hzeroIcc with
      ⟨y, hy, hyzero⟩
    exact hfnz y hy hyzero

end ApollonianSuperharmonic

end
