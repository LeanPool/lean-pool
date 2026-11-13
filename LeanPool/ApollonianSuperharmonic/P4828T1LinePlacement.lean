/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P4903T1ScalarTangencies
public import LeanPool.ApollonianSuperharmonic.P4903T1SignedDiskHull
public import LeanPool.ApollonianSuperharmonic.P4828T1Disk

-- [TABLET NODE: P4828T1LinePlacement]

/-!
# P4828T1LinePlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LinePlacementConstruction

private theorem hparent_nonneg (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) : ∀ i
    : Fin 3, 0 ≤ (q i.succ).1 := by
  classical
  have hc := ProperBandCurvatureStructure q hq
  exact hc.2.1

private theorem hparent_pos (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (j : Fin
    3) (hj : (q j.succ).1 = 0) : ∀ i : Fin 3, i ≠ j → 0 < (q i.succ).1 := by
  classical
  have hc := ProperBandCurvatureStructure q hq
  have hparent_nonneg : ∀ i : Fin 3, 0 ≤ (q i.succ).1 := hparent_nonneg q hq
  have hline_unique := hc.2.2
  intro i hij
  have hnonneg := hparent_nonneg i
  by_contra hnot
  have hzero : (q i.succ).1 = 0 := by omega
  have heq := hline_unique i j hzero hj
  exact (hij heq).elim

private theorem hchild_pos (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) : 0 < (q
    0).1 := by
  classical
  have hc := ProperBandCurvatureStructure q hq
  exact hc.1

private noncomputable abbrev center (q : Fin 4 → CircleCoordinates) (k : Fin 4) : ℂ := by
  classical
  exact ((q k).2 : ℂ) / ((q k).1 : ℝ)

private theorem centerDistance (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) : ∀ i
    j : Fin 4, i ≠ j → 0 < (q i).1 → 0 < (q j).1 →
      dist ((center q) i) ((center q) j) = 1 / (q i).1 + 1 / (q j).1 := by
  classical
  let center (k : Fin 4) : ℂ := ((q k).2 : ℂ) / ((q k).1 : ℝ)
  change (∀ i j : Fin 4, i ≠ j → 0 < (q i).1 → 0 < (q j).1 →
      dist (center i) (center j) = 1 / (q i).1 + 1 / (q j).1)
  as_aux_lemma =>
    intro i j hij hi hj
    let a : ℝ := (q i).1
    let b : ℝ := (q j).1
    let x : ℂ := (q i).2
    let y : ℂ := (q j).2
    change dist (x / a) (y / b) = 1 / a + 1 / b
    have hh := TangencyCoordinateIdentity q hq.1 i j hij
    have hn : (Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) : ℝ) =
        ((q i).1 + (q j).1 : ℤ) ^ 2 := by exact_mod_cast hh
    have hns : Complex.normSq ((b : ℝ) * x - a * y) = (a + b)^2 := by
      dsimp [a, b, x, y]
      norm_num [Complex.normSq_apply, Zsqrtd.norm] at hn ⊢
      nlinarith
    have haPos : 0 < a := by simpa [a] using hi
    have hbPos : 0 < b := by simpa [b] using hj
    have ha : a ≠ 0 := ne_of_gt haPos
    have hb : b ≠ 0 := ne_of_gt hbPos
    have hdiv : (x / a - y / b) * (a * b) = (b : ℂ) * x - a * y := by
      field_simp [ha, hb]
    have hratio : x / a - y / b = ((b : ℂ) * x - a * y) / (a * b) := by
      rw [← hdiv]
      field_simp [ha, hb]
    have hnumNorm : ‖(b : ℝ) * x - a * y‖ = a + b := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (add_pos haPos hbPos).le]
      rw [← Complex.normSq_eq_norm_sq]
      exact hns
    have hA : ‖(a : ℂ)‖ = a := by
      simp [Complex.norm_real, abs_of_pos haPos]
    have hB : ‖(b : ℂ)‖ = b := by
      simp [Complex.norm_real, abs_of_pos hbPos]
    rw [dist_eq_norm, hratio, Complex.norm_div, hnumNorm,
      Complex.norm_mul, hA, hB]
    field_simp [ha, hb]; ring

private theorem hsupport (L : ℝ) (q : Fin 4 → CircleCoordinates) (hs : P4828T1LineSupport L q)
    (j : Fin 3) (hj : (q j.succ).1 = 0) : ∃ n b : ℝ, n^2 = 1 ∧
      (∀ k : Fin 4, 0 < (q k).1 →
        -n * (((center q) k).re - b) = 1 / (q k).1) ∧
      (if (q j.succ).2 = -1 then L else L + 2) = b := by
  classical
  let center (k : Fin 4) : ℂ := ((q k).2 : ℂ) / ((q k).1 : ℝ)
  change (∃ n b : ℝ, n^2 = 1 ∧
      (∀ k : Fin 4, 0 < (q k).1 →
        -n * ((center k).re - b) = 1 / (q k).1) ∧
      (if (q j.succ).2 = -1 then L else L + 2) = b)
  rcases hs.normals j.succ hj with hneg | hpos
  · refine ⟨-1, L, by norm_num, ?_, by simp [hneg]⟩
    intro k hk
    have hh := hs.signed j.succ k hj hk
    rw [hneg] at hh
    norm_num at hh
    have hre : ((q k).2 : ℂ).re = (q k).2.re := by norm_num
    rw [hre] at hh
    have hcne : (q k).1 ≠ 0 := by omega
    have hcenter_re : (center k).re = (q k).2.re / (q k).1 := by
      dsimp [center]
      rw [Complex.div_re]
      simp []
      field_simp [hcne]
    rw [hcenter_re]
    field_simp [hcne]
    nlinarith only [hh]
  · refine ⟨1, L + 2, by norm_num, ?_, by norm_num [hpos]⟩
    intro k hk
    have hh := hs.signed j.succ k hj hk
    rw [hpos] at hh
    norm_num at hh
    have hre : ((q k).2 : ℂ).re = (q k).2.re := by norm_num
    rw [hre] at hh
    have hcne : (q k).1 ≠ 0 := by omega
    have hcenter_re : (center k).re = (q k).2.re / (q k).1 := by
      dsimp [center]
      rw [Complex.div_re]
      simp []
      field_simp [hcne]
    rw [hcenter_re]
    field_simp [hcne]
    nlinarith only [hh]

private theorem centerCoordSq (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) : ∀ u
    v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      (((center q) u).re - ((center q) v).re)^2 + (((center q) u).im - ((center q) v).im)^2 =
        (1 / (q u).1 + 1 / (q v).1)^2 := by
  classical
  let center (k : Fin 4) : ℂ := ((q k).2 : ℂ) / ((q k).1 : ℝ)
  have centerDistance : ∀ i j : Fin 4, i ≠ j → 0 < (q i).1 → 0 < (q j).1 →
      dist (center i) (center j) = 1 / (q i).1 + 1 / (q j).1 := centerDistance q hq
  change (∀ u v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      ((center u).re - (center v).re)^2 + ((center u).im - (center v).im)^2 =
        (1 / (q u).1 + 1 / (q v).1)^2)
  clear * - q center centerDistance
  intro u v huv hu hv
  have hdist := centerDistance u v huv hu hv
  have hnorm : ‖center u - center v‖ = 1 / (q u).1 + 1 / (q v).1 := by
    simpa [dist_eq_norm, center] using hdist
  have hnorm2 := congrArg (fun z : ℝ => z^2) hnorm
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im] at hnorm2
  nlinarith

private theorem verticalSq (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (n : ℝ)
    (boundary : ℝ) (hn : n ^ 2 = 1) : ∀ u v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      -n * (((center q) u).re - boundary) = 1 / (q u).1 →
      -n * (((center q) v).re - boundary) = 1 / (q v).1 →
      (((center q) u).im - ((center q) v).im)^2 =
        4 * (1 / (q u).1) * (1 / (q v).1) := by
  classical
  let center (k : Fin 4) : ℂ := ((q k).2 : ℂ) / ((q k).1 : ℝ)
  have centerCoordSq : ∀ u v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      ((center u).re - (center v).re)^2 + ((center u).im - (center v).im)^2 =
        (1 / (q u).1 + 1 / (q v).1)^2 := centerCoordSq q hq
  change (∀ u v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      -n * ((center u).re - boundary) = 1 / (q u).1 →
      -n * ((center v).re - boundary) = 1 / (q v).1 →
      ((center u).im - (center v).im)^2 =
        4 * (1 / (q u).1) * (1 / (q v).1))
  clear * - q center centerCoordSq n boundary hn
  intro u v huv hu hv hxu hxv
  have hcoords := centerCoordSq u v huv hu hv
  have hsdiff : -n * ((center u).re - (center v).re) =
      1 / (q u).1 - 1 / (q v).1 := by
    calc
      -n * ((center u).re - (center v).re) =
          -n * ((center u).re-boundary) - (-n * ((center v).re-boundary)) := by ring
      _ = 1 / (q u).1 - 1 / (q v).1 := by rw [hxu,hxv]
  have hnn : n * n = 1 := by simpa [pow_two] using hn
  have hdx : (center u).re - (center v).re =
      -n * (1 / (q u).1 - 1 / (q v).1) := by
    calc
      (center u).re - (center v).re =
          n * n * ((center u).re - (center v).re) := by rw [hnn]; ring
      _ = (-n) * ((-n) * ((center u).re - (center v).re)) := by ring
      _ = -n * (1 / (q u).1 - 1 / (q v).1) := by rw [hsdiff]
  rw [hdx] at hcoords
  nlinarith [hn]

end LinePlacementConstruction

theorem P4828T1LinePlacement (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q)
    (hline : ∃ j : Fin 3, (q j.succ).1 = 0) :
    P4828T1Disk (q 0) ⊆ P4828T1Gap L q := by
-- BODY
  rcases hline with ⟨j, hj⟩
  have hparent_pos : ∀ i : Fin 3, i ≠ j → 0 < (q i.succ).1 :=
      LinePlacementConstruction.hparent_pos q hq j hj
  have hchild_pos : 0 < (q 0).1 := LinePlacementConstruction.hchild_pos q hq
  let center (k : Fin 4) : ℂ := ((q k).2 : ℂ) / ((q k).1 : ℝ)
  have centerDistance : ∀ i j : Fin 4, i ≠ j → 0 < (q i).1 → 0 < (q j).1 →
      dist (center i) (center j) = 1 / (q i).1 + 1 / (q j).1 :=
          LinePlacementConstruction.centerDistance q hq
  have hsupport : ∃ n b : ℝ, n^2 = 1 ∧
      (∀ k : Fin 4, 0 < (q k).1 →
        -n * ((center k).re - b) = 1 / (q k).1) ∧
      (if (q j.succ).2 = -1 then L else L + 2) = b := LinePlacementConstruction.hsupport L q hs j hj
  rcases hsupport with ⟨n, boundary, hn, hcenterX, hfoot⟩
  have verticalSq : ∀ u v : Fin 4, u ≠ v → 0 < (q u).1 → 0 < (q v).1 →
      -n * ((center u).re - boundary) = 1 / (q u).1 →
      -n * ((center v).re - boundary) = 1 / (q v).1 →
      ((center u).im - (center v).im)^2 =
        4 * (1 / (q u).1) * (1 / (q v).1) := LinePlacementConstruction.verticalSq q hq n boundary hn
  let i : Fin 3 := if j = 0 then 1 else 0
  let k : Fin 3 := if j = 2 then 1 else 2
  have hij : i ≠ j := by
    clear * - i j
    fin_cases j <;> decide
  have hkj : k ≠ j := by
    clear * - k j
    fin_cases j <;> decide
  have hik : i ≠ k := by
    clear * - i k j
    fin_cases j <;> decide
  have hiPos := hparent_pos i hij
  have hkPos := hparent_pos k hkj
  have hik4 : i.succ ≠ k.succ := (Fin.succ_injective 3).ne hik
  have hABsq := verticalSq i.succ k.succ hik4 hiPos hkPos
    (hcenterX i.succ hiPos) (hcenterX k.succ hkPos)
  have htneq : (center i.succ).im ≠ (center k.succ).im := by
    intro heq
    have hpos : 0 < 4 * (1 / ((q i.succ).1 : ℝ)) * (1 / ((q k.succ).1 : ℝ)) := by
      positivity
    rw [heq, sub_self, zero_pow (by decide : 2 ≠ 0)] at hABsq
    linarith only [hABsq, hpos]
  have ordered : ∃ low high : Fin 3,
      0 < (q low.succ).1 ∧ 0 < (q high.succ).1 ∧ low ≠ high ∧
      (center low.succ).im < (center high.succ).im := by
    rcases lt_or_gt_of_ne htneq with h | h
    · exact ⟨i, k, hiPos, hkPos, hik, h⟩
    · exact ⟨k, i, hkPos, hiPos, hik.symm, h⟩
  rcases ordered with ⟨low, high, hlowPos, hhighPos, hlowHigh, hheight⟩
  let r : ℝ := 1 / (q 0).1
  let a : ℝ := 1 / (q low.succ).1
  let b : ℝ := 1 / (q high.succ).1
  let tL : ℝ := (center low.succ).im
  let D : ℝ := (center high.succ).im - tL
  let x : ℝ := (center 0).im - tL
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hapos : 0 < a := by dsimp [a]; positivity
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hDpos : 0 < D := sub_pos.mpr hheight
  have hra : r < a := by
    dsimp [r, a]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    simpa using hq.2 low
  have hrb : r < b := by
    dsimp [r, b]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    simpa using hq.2 high
  have hDsq : D^2 = 4*a*b := by
    have hh := verticalSq low.succ high.succ
      ((Fin.succ_injective 3).ne hlowHigh) hlowPos hhighPos
      (hcenterX low.succ hlowPos) (hcenterX high.succ hhighPos)
    change ((center high.succ).im - (center low.succ).im)^2 = 4*a*b
    change ((center low.succ).im - (center high.succ).im)^2 = 4*a*b at hh
    nlinarith only [hh]
  have hxsq : x^2 = 4*r*a :=
    verticalSq 0 low.succ (Fin.succ_ne_zero low).symm hchild_pos hlowPos
      (hcenterX 0 hchild_pos) (hcenterX low.succ hlowPos)
  have hysq : (D-x)^2 = 4*r*b := by
    have hh := verticalSq 0 high.succ (Fin.succ_ne_zero high).symm hchild_pos hhighPos
      (hcenterX 0 hchild_pos) (hcenterX high.succ hhighPos)
    have heq : D-x = -((center 0).im - (center high.succ).im) := by
      dsimp [D, x]; ring
    rw [heq, neg_sq]
    exact hh
  rcases P4903T1ScalarTangencies a b r D x hapos hbpos hrpos hDpos
      hra hrb hDsq hxsq hysq with ⟨hxpos, hypos, hrel, hxD⟩
  have hrx : r < x := by nlinarith only [hxsq, hxpos, hrpos, hra]
  have hry : r < D-x := by nlinarith only [hysq, hypos, hrpos, hrb]
  have hmargin : D*a+(b-a)*x-D*r = r*(a+b)+a*b := by
    as_aux_lemma =>
      clear * - a b r D x hDpos hxD hDsq hrel
      have hDne : D ≠ 0 := ne_of_gt hDpos
      have hxf : x=(D^2+4*r*(a-b))/(2*D) := by
        field_simp [hDne]
        nlinarith only [hxD]
      have hD2rel : D^2=4*r*(a+b+D) := by
        calc
          D^2=4*a*b := hDsq
          _=4*r*(a+b+D) := by nlinarith only [hrel]
      rw [hxf]
      field_simp [hDne]
      have hrelA := congrArg (fun z : ℝ => 4*(a+b)*z) hrel
      have hrelR := congrArg (fun z : ℝ => 8*r*z) hrel
      have hrelD := congrArg (fun z : ℝ => 2*D*z) hrel
      have hDsqA := congrArg (fun z : ℝ => (a+b)*z) hDsq
      have hDsqR := congrArg (fun z : ℝ => 2*r*z) hDsq
      nlinarith only [hrelA,hrelR,hrelD,hDsqA,hDsqR,hD2rel]
  have hnn : n*n = 1 := by simpa only [pow_two] using hn
  have hcenterRe : ∀ m : Fin 4, 0 < (q m).1 →
      (center m).re = boundary-n*(1/(q m).1) := by
    intro m hm
    have hh := congrArg (fun z : ℝ => -n*z) (hcenterX m hm)
    ring_nf at hh
    rw [hn] at hh
    simp only [one_mul] at hh
    rw [one_div]
    linarith only [hh]
  let verts : Fin 4 → ℂ :=
    ![⟨boundary,tL⟩,center low.succ,center high.succ,⟨boundary,tL+D⟩]
  let gapCenter (m : Fin 3) : ℂ := center m.succ
  let gapVertices : Set ℂ := {z | ∃ m : Fin 3, 0 < (q m.succ).1 ∧
    (z=gapCenter m ∨ ∃ l : Fin 3, (q l.succ).1=0 ∧
      z=⟨if (q l.succ).2 = -1 then L else L+2,(gapCenter m).im⟩)}
  have hverts : ∀ m : Fin 4, verts m ∈ gapVertices := by
    intro m
    fin_cases m
    · refine ⟨low, hlowPos, Or.inr ⟨j, hj, ?_⟩⟩
      apply Complex.ext
      · simp [verts, hfoot]
      · rfl
    · exact ⟨low, hlowPos, Or.inl rfl⟩
    · exact ⟨high, hhighPos, Or.inl rfl⟩
    · refine ⟨high, hhighPos, Or.inr ⟨j, hj, ?_⟩⟩
      apply Complex.ext
      · simp [verts, hfoot]
      · change tL+D = (center high.succ).im
        dsimp [D]; ring
  have hrange : Set.range verts ⊆ gapVertices := by
    rintro z ⟨m, rfl⟩
    exact hverts m
  have vertsEq : verts = ![⟨boundary,tL⟩,⟨boundary-n*a,tL⟩,
      ⟨boundary-n*b,tL+D⟩,⟨boundary,tL+D⟩] := by
    funext m
    fin_cases m
    · rfl
    · apply Complex.ext
      · exact hcenterRe low.succ hlowPos
      · rfl
    · apply Complex.ext
      · exact hcenterRe high.succ hhighPos
      · change (center high.succ).im = tL+D
        dsimp [D]; ring
    · rfl
  have hcenter0 : center 0 = ⟨boundary-n*r,tL+x⟩ := by
    apply Complex.ext
    · exact hcenterRe 0 hchild_pos
    · change (center 0).im = tL+x
      dsimp [x]; ring
  have hball : Metric.ball (center 0) r ⊆ convexHull ℝ gapVertices := by
    have htrap := P4903T1SignedDiskHull a b r D x tL boundary n
      hapos hbpos hrpos hDpos hnn hDsq hrx hry hmargin
    rw [← hcenter0, ← vertsEq] at htrap
    exact htrap.trans (convexHull_mono hrange)
  intro p hp
  simp only [P4828T1Disk, Metric.mem_ball] at hp
  unfold P4828T1Gap
  refine ⟨?_, ?_⟩
  · change p ∈ interior (convexHull ℝ gapVertices)
    have hpball : p ∈ Metric.ball (center 0) r := hp
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hpball) hball)
  · intro m hm
    have hdist := centerDistance 0 m.succ (Fin.succ_ne_zero m).symm hchild_pos hm
    have htri := dist_triangle (center 0) p (center m.succ)
    change 1 / (q m.succ).1 < dist p (center m.succ)
    have hp' : dist (center 0) p < 1 / (q 0).1 := by
      rw [dist_comm]
      exact hp
    have hlt := lt_of_le_of_lt htri
      (add_lt_add_left hp' (dist p (center m.succ)))
    rw [hdist] at hlt
    exact lt_of_add_lt_add_left hlt

end ApollonianSuperharmonic

end
