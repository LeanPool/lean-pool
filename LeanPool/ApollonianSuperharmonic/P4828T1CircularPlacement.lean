/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.MetricSpace.Lipschitz

-- [TABLET NODE: P4828T1CircularPlacement]

/-!
# P4828T1CircularPlacement

Adapted from Wesley Pegden’s Apache - 2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CircularPlacementConstruction

private theorem hchild (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) : 0 < (q 0).1
    := by
  classical
  exact (ProperBandCurvatureStructure q hq).1

private theorem hcpos (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : ∀ i : Fin 4, 0 < (q i).1 := by
  classical
  have hchild : 0 < (q 0).1 := hchild q hq
  intro i
  fin_cases i
  · exact hchild
  · exact hpositive 0
  · exact hpositive 1
  · exact hpositive 2

private theorem normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) := by
  classical
  simp [Complex.normSq, Zsqrtd.norm_def]

private theorem circleDist (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (i j :
    Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (((q i).2 : Complex) / (q i).1)
          (((q j).2 : Complex) / (q j).1) =
        1 / (q i).1 + 1 / (q j).1 := by
  classical
  have normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) := normCast w
  let v : GaussianInt := (q j).1 • (q i).2 - (q i).1 • (q j).2
  have ht := TangencyCoordinateIdentity q hq.1 i j hij
  have hn : Complex.normSq (v : Complex) =
      (((q i).1 + (q j).1 : ℤ) ^ 2 : Real) := by
    change Complex.normSq
        (((q j).1 • (q i).2 - (q i).1 • (q j).2 : GaussianInt) : Complex) = _
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(v : Complex)‖ ^ 2 =
      (((q i).1 + (q j).1 : ℤ) : Real) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hnorm : ‖(v : Complex)‖ =
      (((q i).1 + (q j).1 : ℤ) : Real) := by
    have hnonneg := norm_nonneg (v : Complex)
    have hsum : 0 ≤ (((q i).1 + (q j).1 : ℤ) : Real) := by positivity
    nlinarith
  have hdiff :
      ((q i).2 : Complex) / (q i).1 - ((q j).2 : Complex) / (q j).1 =
        (v : Complex) / (((q i).1 * (q j).1 : ℤ) : Complex) := by
    dsimp [v]
    push_cast
    simp only [map_sub, map_zsmul]
    have hia : (q i).1 ≠ 0 := ne_of_gt hi
    have hjb : (q j).1 ≠ 0 := ne_of_gt hj
    field_simp [hia, hjb]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have ha : 0 < ((q i).1 : Real) := by exact_mod_cast hi
  have hb : 0 < ((q j).1 : Real) := by exact_mod_cast hj
  have hab : 0 < (((q i).1 * (q j).1 : ℤ) : Real) := by
    exact_mod_cast mul_pos hi hj
  rw [abs_of_pos hab]
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

private noncomputable abbrev ctr (q : Fin 4 → CircleCoordinates) (i : Fin 4) : Complex := by
  classical
  exact ((q i).2 : Complex) / (q i).1

private noncomputable abbrev rad (q : Fin 4 → CircleCoordinates) (i : Fin 4) : Real := by
  classical
  exact 1 / (q i).1

private theorem rpos (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) (i : Fin 4) : 0 < (rad q) i := by
  classical
  have hcpos : ∀ i : Fin 4, 0 < (q i).1 := hcpos q hq hpositive
  let rad (i : Fin 4) : Real := 1 / (q i).1
  change (0 < rad i)
  dsimp [rad]
  have hi : 0 < ((q i).1 : Real) := by exact_mod_cast hcpos i
  exact one_div_pos.mpr hi

private theorem ctrDist (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive :
    ∀ j : Fin 3, 0 < (q j.succ).1) (i j : Fin 4) (hij : i ≠ j) :
      dist ((ctr q) i) ((ctr q) j) = (rad q) i + (rad q) j := by
  classical
  have hcpos : ∀ i : Fin 4, 0 < (q i).1 := hcpos q hq hpositive
  have circleDist (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (((q i).2 : Complex) / (q i).1)
          (((q j).2 : Complex) / (q j).1) =
        1 / (q i).1 + 1 / (q j).1 := circleDist q hq i j hij hi hj
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  change (dist (ctr i) (ctr j) = rad i + rad j)
  simpa [ctr, rad] using circleDist i j hij (hcpos i) (hcpos j)

private theorem hd21 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : dist ((ctr q) 2) ((ctr q) 1) = (rad q) 2 + (rad q) 1 := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd12 := ctrDist 1 2 (by decide)
  change (dist (ctr 2) (ctr 1) = rad 2 + rad 1)
  simpa [dist_comm, add_comm] using hd12

private theorem hd31 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : dist ((ctr q) 3) ((ctr q) 1) = (rad q) 3 + (rad q) 1 := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd13 := ctrDist 1 3 (by decide)
  change (dist (ctr 3) (ctr 1) = rad 3 + rad 1)
  simpa [dist_comm, add_comm] using hd13

private theorem hd32 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : dist ((ctr q) 3) ((ctr q) 2) = (rad q) 3 + (rad q) 2 := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd23 := ctrDist 2 3 (by decide)
  change (dist (ctr 3) (ctr 2) = rad 3 + rad 2)
  simpa [dist_comm, add_comm] using hd23

private noncomputable abbrev crossC : Complex → Complex → Real := by
  classical
  exact fun z w => z.re * w.im - z.im * w.re

private noncomputable abbrev dotC : Complex → Complex → Real := by
  classical
  exact fun z w => z.re * w.re + z.im * w.im

private theorem soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 := by
  classical
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  let dotC : Complex → Complex → Real := fun z w => z.re * w.re + z.im * w.im
  change (0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2)
  exact (by
      let e := B - A
      let u := C - A
      let v := D - A
      have hlen (x y : Complex) (r : Real) (h : dist x y = r) :
          Complex.normSq (y - x) = r ^ 2 := by
        have hn : ‖y - x‖ = r := by
          simpa [Complex.dist_eq, norm_sub_rev] using h
        rw [Complex.normSq_eq_norm_sq, hn]
      have he : Complex.normSq e = (a + b) ^ 2 := hlen A B (a + b) hAB
      have hu : Complex.normSq u = (a + c) ^ 2 := hlen A C (a + c) hAC
      have hv : Complex.normSq v = (a + d) ^ 2 := hlen A D (a + d) hAD
      have heu : Complex.normSq (e - u) = (b + c) ^ 2 := by
        have h := hlen C B (b + c) (by simpa [dist_comm] using hBC)
        simpa [e, u] using h
      have hev : Complex.normSq (e - v) = (b + d) ^ 2 := by
        have h := hlen D B (b + d) (by simpa [dist_comm] using hBD)
        simpa [e, v] using h
      have huv : Complex.normSq (u - v) = (c + d) ^ 2 := by
        have h := hlen D C (c + d) (by simpa [dist_comm] using hCD)
        simpa [u, v] using h
      have dotEU : 2 * dotC e u = Complex.normSq e + Complex.normSq u - Complex.normSq (e - u) := by
        simp [dotC, Complex.normSq, e, u]
        ring
      have dotEV : 2 * dotC e v = Complex.normSq e + Complex.normSq v - Complex.normSq (e - v) := by
        simp [dotC, Complex.normSq, e, v]
        ring
      have dotUV : 2 * dotC u v = Complex.normSq u + Complex.normSq v - Complex.normSq (u - v) := by
        simp [dotC, Complex.normSq, u, v]
        ring
      have areaProduct : crossC e u * crossC e v =
          Complex.normSq e * dotC u v - dotC e u * dotC e v := by
        simp [crossC, dotC, Complex.normSq, e, u, v]
        ring
      have hdotEU : 2 * dotC e u = (a + b) ^ 2 + (a + c) ^ 2 - (b + c) ^ 2 := by rw [dotEU, he,
          hu, heu]
      have hdotEV : 2 * dotC e v = (a + b) ^ 2 + (a + d) ^ 2 - (b + d) ^ 2 := by rw [dotEV, he,
          hv, hev]
      have hdotUV : 2 * dotC u v = (a + c) ^ 2 + (a + d) ^ 2 - (c + d) ^ 2 := by rw [dotUV, hu,
          hv, huv]
      have hp : crossC e u * crossC e v =
          2 * (a * b * (a + b) * (c + d) - c * d * (a ^ 2 + b ^ 2)) := by
        have h1 : dotC e u = ((a + b) ^ 2 + (a + c) ^ 2 - (b + c) ^ 2) / 2 := by linarith [hdotEU]
        have h2 : dotC e v = ((a + b) ^ 2 + (a + d) ^ 2 - (b + d) ^ 2) / 2 := by linarith [hdotEV]
        have h3 : dotC u v = ((a + c) ^ 2 + (a + d) ^ 2 - (c + d) ^ 2) / 2 := by linarith [hdotUV]
        rw [areaProduct, he, h1, h2, h3]
        ring
      have areaSquare : crossC e v ^ 2 =
          Complex.normSq e * Complex.normSq v - dotC e v ^ 2 := by
        simp [crossC, dotC, Complex.normSq, e, v]
        ring
      have hmarginEq : crossC e v ^ 2 = 4 * a * b * d * (a + b + d) := by
        rw [areaSquare, he, hv]
        have hdv : dotC e v = a ^ 2 + a * b + a * d - b * d :=
          by
            have hpoly : (a + b) ^ 2 + (a + d) ^ 2 - (b + d) ^ 2 =
                2 * (a ^ 2 + a * b + a * d - b * d) := by ring
            rw [hpoly] at hdotEV
            linarith [hdotEV]
        rw [hdv]
        ring
      constructor
      · change 0 < crossC e u * crossC e v
        rw [hp]
        have hcore : 0 < a * b * (a + b) - d * (a ^ 2 + b ^ 2) := by
          rcases le_total a b with hab | hba
          · calc
              0 ≤ a * b * (a + b) - a * (a ^ 2 + b ^ 2) := by
                rw [show a * b * (a + b) - a * (a ^ 2 + b ^ 2) = a ^ 2 * (b - a) by ring]
                exact mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hab)
              _ < a * b * (a + b) - d * (a ^ 2 + b ^ 2) := by
                have hsq : 0 < a ^ 2 + b ^ 2 := by positivity
                have hgap : a * b * (a + b) - d * (a ^ 2 + b ^ 2) =
                    a * b * (a + b) - a * (a ^ 2 + b ^ 2) + (a - d) * (a ^ 2 + b ^ 2) := by ring
                rw [hgap]
                exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hdA) hsq)
          · calc
              0 ≤ a * b * (a + b) - b * (a ^ 2 + b ^ 2) := by
                rw [show a * b * (a + b) - b * (a ^ 2 + b ^ 2) = b ^ 2 * (a - b) by ring]
                exact mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hba)
              _ < a * b * (a + b) - d * (a ^ 2 + b ^ 2) := by
                have hsq : 0 < a ^ 2 + b ^ 2 := by positivity
                have hgap : a * b * (a + b) - d * (a ^ 2 + b ^ 2) =
                    a * b * (a + b) - b * (a ^ 2 + b ^ 2) + (b - d) * (a ^ 2 + b ^ 2) := by ring
                rw [hgap]
                exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hdB) hsq)
        have hpos : 0 < c * (a * b * (a + b) - d * (a ^ 2 + b ^ 2)) + a * b * (a + b) * d := by
          positivity
        have hrew (X Y : Real) :
            X * (c + d) - c * d * Y = c * (X - d * Y) + X * d := by
          calc
            X * (c + d) - c * d * Y = X * c + X * d - c * d * Y := by ring
            _ = c * (X - d * Y) + X * d := by ring
        have hrew' : a * b * (a + b) * (c + d) - c * d * (a ^ 2 + b ^ 2) =
            c * (a * b * (a + b) - d * (a ^ 2 + b ^ 2)) + a * b * (a + b) * d := by
          simpa using hrew (a * b * (a + b)) (a ^ 2 + b ^ 2)
        rw [hrew']
        exact mul_pos (by norm_num : (0 : Real) < 2) hpos
      · rw [hmarginEq]
        have hfactor : 0 < 4 * a * b - d * (a + b) := by
          rcases le_total a b with hab | hba
          · have habsum : a + b ≤ 2 * b := by
              calc
                a + b ≤ b + b := by simpa [add_comm] using add_le_add_right hab b
                _ = 2 * b := by ring
            have hprod : d * (a + b) < a * (a + b) := by
              exact (mul_lt_mul_of_pos_right hdA (by positivity))
            have hbound : a * (a + b) ≤ 2 * a * b := by
              calc
                a * (a + b) ≤ a * (2 * b) := mul_le_mul_of_nonneg_left habsum (le_of_lt ha)
                _ = 2 * a * b := by ring
            have hprod' : d * (a + b) < 2 * a * b := lt_of_lt_of_le hprod hbound
            have habpos : 0 < a * b := mul_pos ha hb
            linarith
          · have hbasum : a + b ≤ 2 * a := by
              calc
                a + b ≤ a + a := by simpa [add_comm] using add_le_add_left hba a
                _ = 2 * a := by ring
            have hprod : d * (a + b) < b * (a + b) := by
              exact (mul_lt_mul_of_pos_right hdB (by positivity))
            have hbound : b * (a + b) ≤ 2 * a * b := by
              calc
                b * (a + b) ≤ b * (2 * a) := mul_le_mul_of_nonneg_left hbasum (le_of_lt hb)
                _ = 2 * a * b := by ring
            have hprod' : d * (a + b) < 2 * a * b := lt_of_lt_of_le hprod hbound
            have habpos : 0 < a * b := mul_pos ha hb
            linarith
        have hmargin : 0 < 4 * a * b * (a + b + d) - d * (a + b) ^ 2 := by
          rw [show 4 * a * b * (a + b + d) - d * (a + b) ^ 2 =
            (a + b) * (4 * a * b - d * (a + b)) + 4 * a * b * d by ring]
          positivity
        have hm' : d * (d * (a + b) ^ 2) < d * (4 * a * b * (a + b + d)) :=
          mul_lt_mul_of_pos_left (sub_pos.mp hmargin) hd
        calc
          (d * (a + b)) ^ 2 = d * (d * (a + b) ^ 2) := by ring
          _ < d * (4 * a * b * (a + b + d)) := hm'
          _ = 4 * a * b * d * (a + b + d) := by ring
  )

private theorem crossSq_le (z w : Complex) :
      crossC z w ^ 2 ≤ Complex.normSq z * Complex.normSq w := by
  classical
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  change (crossC z w ^ 2 ≤ Complex.normSq z * Complex.normSq w)
  simp [crossC, Complex.normSq]
  nlinarith [sq_nonneg (z.re * w.re + z.im * w.im)]

private theorem diskEdgeSide (A B D p : Complex) (a d : Real)
      (ha : 0 < a) (hd : 0 < d)
      (hAB : dist A B = a)
      (hmargin : (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2)
      (hpD : dist D p < d) :
      0 < crossC (B - A) (D - A) * crossC (B - A) (p - A) := by
  classical
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  have crossSq_le (z w : Complex) :
      crossC z w ^ 2 ≤ Complex.normSq z * Complex.normSq w := crossSq_le z w
  change (0 < crossC (B - A) (D - A) * crossC (B - A) (p - A))
  change (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2 at hmargin
  let e := B - A
  let w := p - D
  have he : Complex.normSq e = a ^ 2 := by
    have hn : ‖B - A‖ = a := by simpa [Complex.dist_eq, norm_sub_rev] using hAB
    rw [Complex.normSq_eq_norm_sq, hn]
  have hw : Complex.normSq w < d ^ 2 := by
    have hn : ‖p - D‖ < d := by simpa [Complex.dist_eq, norm_sub_rev] using hpD
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (p - D)]
  have herr : crossC e w ^ 2 < (d * a) ^ 2 := by
    have hcross := crossSq_le e w
    have hprod : Complex.normSq e * Complex.normSq w < a ^ 2 * d ^ 2 := by
      rw [he]
      exact mul_lt_mul_of_pos_left hw (by positivity)
    nlinarith [hcross, hprod]
  have hmargin' : crossC e w ^ 2 < crossC e (D - A) ^ 2 := lt_trans herr hmargin
  have hne : crossC e (D - A) ≠ 0 := by
    intro hz
    rw [hz] at hmargin
    have hsq : 0 ≤ (d * a) ^ 2 := sq_nonneg _
    linarith
  have hsign (x y : Real) (hx : x ≠ 0) (hxy : y ^ 2 < x ^ 2) : 0 < x * (x + y) := by
    have habs : |y| < |x| := by
      apply (sq_lt_sq₀ (abs_nonneg y) (abs_nonneg x)).mp
      simpa [sq_abs] using hxy
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hy : y < -x := by
        have hh := (abs_lt.mp (by simpa [abs_of_neg hneg] using habs)).2
        linarith
      have hs : x + y < 0 := by linarith
      exact mul_pos_of_neg_of_neg hneg hs
    · have hy : -x < y := by
        have hh := (abs_lt.mp (by simpa [abs_of_pos hpos] using habs)).1
        linarith
      have hs : 0 < x + y := by linarith
      exact mul_pos hpos hs
  have hlinear : crossC e (p - A) = crossC e (D - A) + crossC e w := by
    simp [crossC, e, w]
    ring
  rw [hlinear]
  exact hsign _ _ hne hmargin'

private theorem sideTrans (x y z : Real) (hxy : 0 < x * y) (hyz : 0 < y * z) :
      0 < x * z := by
  classical
  rcases (mul_pos_iff.mp hxy) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases (mul_pos_iff.mp hyz) with ⟨hy', hz⟩ | ⟨hy', hz⟩
    · exact mul_pos hx hz
    · linarith
  · rcases (mul_pos_iff.mp hyz) with ⟨hy', hz⟩ | ⟨hy', hz⟩
    · linarith
    · exact mul_pos_of_neg_of_neg hx hz

private theorem ratioPos (x y : Real) (hxy : 0 < x * y) : 0 < y / x := by
  classical
  rw [div_pos_iff]
  rcases (mul_pos_iff.mp hxy) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨hy, hx⟩
  · exact Or.inr ⟨hy, hx⟩

private theorem strictSides (A B C p : Complex)
      (harea : crossC (B - A) (C - A) ≠ 0)
      (hC : 0 < crossC (B - A) (p - A) / crossC (B - A) (C - A))
      (hB : 0 < crossC (p - A) (C - A) / crossC (B - A) (C - A))
      (hA : 0 < 1 - crossC (p - A) (C - A) / crossC (B - A) (C - A) -
        crossC (B - A) (p - A) / crossC (B - A) (C - A)) :
      p ∈ interior (convexHull Real ({A, B, C} : Set Complex)) := by
  classical
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  exact (by
    let den : Real := crossC (B - A) (C - A)
    let nb (x : Complex) : Real := crossC (x - A) (C - A)
    let nc (x : Complex) : Real := crossC (B - A) (x - A)
    let wB (x : Complex) := nb x / den
    let wC (x : Complex) := nc x / den
    let wA (x : Complex) := 1 - wB x - wC x
    let verts : Fin 3 → Complex :=
      Fin.cases A (fun i : Fin 2 => Fin.cases B (fun _ : Fin 1 => C) i)
    let weights (x : Complex) : Fin 3 → Real :=
      Fin.cases (wA x) (fun i : Fin 2 => Fin.cases (wB x) (fun _ : Fin 1 => wC x) i)
    let U : Set Complex := {x | 0 < wA x ∧ 0 < wB x ∧ 0 < wC x}
    have hden : den ≠ 0 := by
      intro hz
      apply harea
      simpa [den] using hz
    have hcontRe : Continuous (fun z : Complex => z.re) := by
      apply (LipschitzWith.of_dist_le_mul (K := 1) fun z w => ?_).continuous
      rw [Real.dist_eq, Complex.dist_eq]
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    have hcontIm : Continuous (fun z : Complex => z.im) := by
      apply (LipschitzWith.of_dist_le_mul (K := 1) fun z w => ?_).continuous
      rw [Real.dist_eq, Complex.dist_eq]
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - w)
    have hcontSub (A : Complex) : Continuous (fun z : Complex => z - A) := by
      apply (LipschitzWith.of_dist_le_mul (K := 1) fun z w => ?_).continuous
      rw [Complex.dist_eq, Complex.dist_eq]
      simp
    have hcontNB : Continuous nb := by
      dsimp [nb, crossC]
      exact ((hcontRe.comp (hcontSub A)).mul continuous_const).sub
        ((hcontIm.comp (hcontSub A)).mul continuous_const)
    have hcontNC : Continuous nc := by
      dsimp [nc, crossC]
      exact (continuous_const.mul
          (hcontIm.comp (hcontSub A))).sub
        (continuous_const.mul
          (hcontRe.comp (hcontSub A)))
    have hcontB : Continuous wB := by
      dsimp [wB]
      exact hcontNB.div_const den
    have hcontC : Continuous wC := by
      dsimp [wC]
      exact hcontNC.div_const den
    have hcontA : Continuous wA := by
      dsimp [wA]
      exact Continuous.sub (continuous_const.sub hcontB) hcontC
    have hopen : IsOpen U := by
      apply (isOpen_lt continuous_const hcontA).inter
      apply (isOpen_lt continuous_const hcontB).inter
      exact isOpen_lt continuous_const hcontC
    have expandReal (b c a y z : Real) :
        (1 - b - c) * a + b * y + c * z = a + b * (y - a) + c * (z - a) := by
      ring
    have hU : p ∈ U := by
      change 0 < wA p ∧ 0 < wB p ∧ 0 < wC p
      constructor
      · dsimp [wA, wB, wC, nb, nc, den]
        exact hA
      · constructor
        · dsimp [wB, nb, den]
          exact hB
        · dsimp [wC, nc, den]
          exact hC
    have hsubset : U ⊆ convexHull Real ({A, B, C} : Set Complex) := by
      intro x hx
      change 0 < wA x ∧ 0 < wB x ∧ 0 < wC x at hx
      let verts : Fin 3 → Complex :=
        Fin.cases A (fun i : Fin 2 => Fin.cases B (fun _ : Fin 1 => C) i)
      let weights (x : Complex) : Fin 3 → Real :=
        Fin.cases (wA x) (fun i : Fin 2 => Fin.cases (wB x) (fun _ : Fin 1 => wC x) i)
      have hs : ∑ i : Fin 3, weights x i = 1 := by
        rw [Fin.sum_univ_three]
        simp only [weights]
        change wA x + wB x + wC x = 1
        dsimp [wA]
        abel
      have hcombo : ∑ i : Fin 3, weights x i • verts i = x := by
        rw [Fin.sum_univ_three]
        have hw0 : weights x 0 = wA x := rfl
        have hw1 : weights x 1 = wB x := rfl
        have hw2 : weights x 2 = wC x := rfl
        have hv0 : verts 0 = A := rfl
        have hv1 : verts 1 = B := rfl
        have hv2 : verts 2 = C := rfl
        rw [hw0, hw1, hw2, hv0, hv1, hv2]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.smul_re]
          change (1 - wB x - wC x) • A.re +
            wB x • B.re + wC x • C.re = x.re
          simp only [smul_eq_mul]
          calc
            (1 - wB x - wC x) * A.re + wB x * B.re + wC x * C.re =
                A.re + wB x * (B.re - A.re) + wC x * (C.re - A.re) :=
              expandReal (wB x) (wC x) A.re B.re C.re
            _ = x.re := by
              dsimp [wB, wC]
              field_simp [hden]
              dsimp [nb, nc, crossC, den]
              ring
        · simp only [Complex.add_im, Complex.smul_im]
          change (1 - wB x - wC x) • A.im +
            wB x • B.im + wC x • C.im = x.im
          simp only [smul_eq_mul]
          calc
            (1 - wB x - wC x) * A.im + wB x * B.im + wC x * C.im =
                A.im + wB x * (B.im - A.im) + wC x * (C.im - A.im) :=
              expandReal (wB x) (wC x) A.im B.im C.im
            _ = x.im := by
              dsimp [wB, wC]
              field_simp [hden]
              dsimp [nb, nc, crossC, den]
              ring
      exact mem_convexHull_of_exists_fintype (weights x) verts
        (by
          intro i
          fin_cases i
          · change 0 ≤ wA x
            exact le_of_lt hx.1
          · change 0 ≤ wB x
            exact le_of_lt hx.2.1
          · change 0 ≤ wC x
            exact le_of_lt hx.2.2)
        hs
        (by
          intro i
          fin_cases i
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl))
        hcombo
    exact (interior_maximal hsubset hopen) hU
  )

private theorem radChildLtParent (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hpositive : ∀ j : Fin 3, 0 < (q j.succ).1) (j : Fin 3) : (rad q) 0 < (rad q) j.succ := by
  classical
  let rad (i : Fin 4) : Real := 1 / (q i).1
  change (rad 0 < rad j.succ)
  dsimp [rad]
  have hp : 0 < ((q j.succ).1 : Real) := by exact_mod_cast hpositive j
  have hc : ((q j.succ).1 : Real) < ((q 0).1 : Real) := by
    exact_mod_cast hq.2 j
  exact one_div_lt_one_div_of_lt hp hc

private theorem hr01 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : (rad q) 0 < (rad q) 1 := by
  classical
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have radChildLtParent (j : Fin 3) : rad 0 < rad j.succ := radChildLtParent q hq hpositive j
  change (rad 0 < rad 1)
  simpa using radChildLtParent 0

private theorem hr02 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : (rad q) 0 < (rad q) 2 := by
  classical
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have radChildLtParent (j : Fin 3) : rad 0 < rad j.succ := radChildLtParent q hq hpositive j
  change (rad 0 < rad 2)
  simpa using radChildLtParent 1

private theorem hr03 (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : (rad q) 0 < (rad q) 3 := by
  classical
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have radChildLtParent (j : Fin 3) : rad 0 < rad j.succ := radChildLtParent q hq hpositive j
  change (rad 0 < rad 3)
  simpa using radChildLtParent 2

private noncomputable abbrev den (q : Fin 4 → CircleCoordinates) : Real := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  exact crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)

private theorem harea (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) : crossC ((ctr q) 2 - (ctr q) 1) ((ctr q) 3 - (ctr q) 1) ≠ 0 := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have rpos (i : Fin 4) : 0 < rad i := rpos q hq hpositive i
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd12 := ctrDist 1 2 (by decide)
  have hd13 := ctrDist 1 3 (by decide)
  have hd10 := ctrDist 1 0 (by decide)
  have hd23 := ctrDist 2 3 (by decide)
  have hd20 := ctrDist 2 0 (by decide)
  have hd30 := ctrDist 3 0 (by decide)
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  have soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 := soddySameSide A B C D a b c d ha hb
              hc hd hdA
              hdB hAB hAC hAD hBC hBD hCD
  have hr01 : rad 0 < rad 1 := hr01 q hq hpositive
  have hr02 : rad 0 < rad 2 := hr02 q hq hpositive
  have hside123 := soddySameSide (ctr 1) (ctr 2) (ctr 3) (ctr 0)
    (rad 1) (rad 2) (rad 3) (rad 0)
    (rpos 1) (rpos 2) (rpos 3) (rpos 0) hr01 hr02
    hd12 hd13 hd10 hd23 hd20 hd30
  change (crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1) ≠ 0)
  have hprod : 0 < crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1) *
      crossC (ctr 2 - ctr 1) (ctr 0 - ctr 1) := hside123.1
  intro hz
  rw [hz] at hprod
  norm_num at hprod

private theorem hLamC (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) (p : ℂ) (hp : dist p (((q 0).2 : ℂ) / ((q 0).1 : ℝ)) < 1 / ((q
    0).1 : ℝ)) : 0 < crossC ((ctr q) 2 - (ctr q) 1) (p - (ctr q) 1) / (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have rpos (i : Fin 4) : 0 < rad i := rpos q hq hpositive i
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd12 := ctrDist 1 2 (by decide)
  have hd13 := ctrDist 1 3 (by decide)
  have hd10 := ctrDist 1 0 (by decide)
  have hd23 := ctrDist 2 3 (by decide)
  have hd20 := ctrDist 2 0 (by decide)
  have hd30 := ctrDist 3 0 (by decide)
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  have soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 := soddySameSide A B C D a b c d ha hb
              hc hd hdA
              hdB hAB hAC hAD hBC hBD hCD
  have diskEdgeSide (A B D p : Complex) (a d : Real)
      (ha : 0 < a) (hd : 0 < d)
      (hAB : dist A B = a)
      (hmargin : (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2)
      (hpD : dist D p < d) :
      0 < crossC (B - A) (D - A) * crossC (B - A) (p - A) := diskEdgeSide A B D p a d ha hd hAB
          hmargin hpD
  have sideTrans (x y z : Real) (hxy : 0 < x * y) (hyz : 0 < y * z) :
      0 < x * z := sideTrans x y z hxy hyz
  have ratioPos (x y : Real) (hxy : 0 < x * y) : 0 < y / x := ratioPos x y hxy
  have hr01 : rad 0 < rad 1 := hr01 q hq hpositive
  have hr02 : rad 0 < rad 2 := hr02 q hq hpositive
  have hside123 := soddySameSide (ctr 1) (ctr 2) (ctr 3) (ctr 0)
    (rad 1) (rad 2) (rad 3) (rad 0)
    (rpos 1) (rpos 2) (rpos 3) (rpos 0) hr01 hr02
    hd12 hd13 hd10 hd23 hd20 hd30
  have hp12 := diskEdgeSide (ctr 1) (ctr 2) (ctr 0) p
    (rad 1 + rad 2) (rad 0) (add_pos (rpos 1) (rpos 2)) (rpos 0)
    (ctrDist 1 2 (by decide)) hside123.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have htri123 := sideTrans
    (crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1))
    (crossC (ctr 2 - ctr 1) (ctr 0 - ctr 1))
    (crossC (ctr 2 - ctr 1) (p - ctr 1)) hside123.1 hp12
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  change (0 < crossC (ctr 2 - ctr 1) (p - ctr 1) / den)
  exact ratioPos _ _ (by simpa [den] using htri123)

private theorem hden312 (q : Fin 4 → CircleCoordinates) : crossC ((ctr q) 1 - (ctr q) 3) ((ctr q)
    2 - (ctr q) 3) = (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  change (crossC (ctr 1 - ctr 3) (ctr 2 - ctr 3) = den)
  dsimp [den, crossC]
  ring

private theorem hnum312 (q : Fin 4 → CircleCoordinates) (p : ℂ) : crossC ((ctr q) 1 - (ctr q) 3)
    (p - (ctr q) 3) =
      crossC (p - (ctr q) 1) ((ctr q) 3 - (ctr q) 1) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  change (crossC (ctr 1 - ctr 3) (p - ctr 3) =
      crossC (p - ctr 1) (ctr 3 - ctr 1))
  dsimp [crossC]
  ring

private theorem hLamB (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) (p : ℂ) (hp : dist p (((q 0).2 : ℂ) / ((q 0).1 : ℝ)) < 1 / ((q
    0).1 : ℝ)) : 0 < crossC (p - (ctr q) 1) ((ctr q) 3 - (ctr q) 1) / (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have rpos (i : Fin 4) : 0 < rad i := rpos q hq hpositive i
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd12 := ctrDist 1 2 (by decide)
  have hd10 := ctrDist 1 0 (by decide)
  have hd20 := ctrDist 2 0 (by decide)
  have hd30 := ctrDist 3 0 (by decide)
  have hd31 : dist (ctr 3) (ctr 1) = rad 3 + rad 1 := hd31 q hq hpositive
  have hd32 : dist (ctr 3) (ctr 2) = rad 3 + rad 2 := hd32 q hq hpositive
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  have soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 := soddySameSide A B C D a b c d ha hb
              hc hd hdA
              hdB hAB hAC hAD hBC hBD hCD
  have diskEdgeSide (A B D p : Complex) (a d : Real)
      (ha : 0 < a) (hd : 0 < d)
      (hAB : dist A B = a)
      (hmargin : (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2)
      (hpD : dist D p < d) :
      0 < crossC (B - A) (D - A) * crossC (B - A) (p - A) := diskEdgeSide A B D p a d ha hd hAB
          hmargin hpD
  have sideTrans (x y z : Real) (hxy : 0 < x * y) (hyz : 0 < y * z) :
      0 < x * z := sideTrans x y z hxy hyz
  have ratioPos (x y : Real) (hxy : 0 < x * y) : 0 < y / x := ratioPos x y hxy
  have hr01 : rad 0 < rad 1 := hr01 q hq hpositive
  have hr03 : rad 0 < rad 3 := hr03 q hq hpositive
  have hside312 := soddySameSide (ctr 3) (ctr 1) (ctr 2) (ctr 0)
    (rad 3) (rad 1) (rad 2) (rad 0)
    (rpos 3) (rpos 1) (rpos 2) (rpos 0) hr03 hr01
    hd31 hd32 hd30 hd12 hd10 hd20
  have hp31 := diskEdgeSide (ctr 3) (ctr 1) (ctr 0) p
    (rad 3 + rad 1) (rad 0) (add_pos (rpos 3) (rpos 1)) (rpos 0)
    (ctrDist 3 1 (by decide)) hside312.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have htri312 := sideTrans
    (crossC (ctr 1 - ctr 3) (ctr 2 - ctr 3))
    (crossC (ctr 1 - ctr 3) (ctr 0 - ctr 3))
    (crossC (ctr 1 - ctr 3) (p - ctr 3)) hside312.1 hp31
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  have hden312 : crossC (ctr 1 - ctr 3) (ctr 2 - ctr 3) = den := hden312 q
  have hnum312 : crossC (ctr 1 - ctr 3) (p - ctr 3) =
      crossC (p - ctr 1) (ctr 3 - ctr 1) := hnum312 q p
  change (0 < crossC (p - ctr 1) (ctr 3 - ctr 1) / den)
  have hh := ratioPos _ _ htri312
  rw [hden312, hnum312] at hh
  exact hh

private theorem hden231 (q : Fin 4 → CircleCoordinates) : crossC ((ctr q) 3 - (ctr q) 2) ((ctr q)
    1 - (ctr q) 2) = (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  change (crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) = den)
  dsimp [den, crossC]
  ring

private theorem hnum231 (q : Fin 4 → CircleCoordinates) (p : ℂ) : crossC ((ctr q) 3 - (ctr q) 2)
    (p - (ctr q) 2) =
      crossC ((ctr q) 3 - (ctr q) 2) ((ctr q) 1 - (ctr q) 2) -
        crossC (p - (ctr q) 1) ((ctr q) 3 - (ctr q) 1) -
        crossC ((ctr q) 2 - (ctr q) 1) (p - (ctr q) 1) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  change (crossC (ctr 3 - ctr 2) (p - ctr 2) =
      crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) -
        crossC (p - ctr 1) (ctr 3 - ctr 1) -
        crossC (ctr 2 - ctr 1) (p - ctr 1))
  dsimp [crossC]
  ring

private theorem hLamA (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀
    j : Fin 3, 0 < (q j.succ).1) (p : ℂ) (hp : dist p (((q 0).2 : ℂ) / ((q 0).1 : ℝ)) < 1 / ((q
    0).1 : ℝ)) : 0 < crossC ((ctr q) 3 - (ctr q) 2) (p - (ctr q) 2) / (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have rpos (i : Fin 4) : 0 < rad i := rpos q hq hpositive i
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := ctrDist q hq hpositive i j hij
  have hd10 := ctrDist 1 0 (by decide)
  have hd23 := ctrDist 2 3 (by decide)
  have hd20 := ctrDist 2 0 (by decide)
  have hd30 := ctrDist 3 0 (by decide)
  have hd21 : dist (ctr 2) (ctr 1) = rad 2 + rad 1 := hd21 q hq hpositive
  have hd31 : dist (ctr 3) (ctr 1) = rad 3 + rad 1 := hd31 q hq hpositive
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  have soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 := soddySameSide A B C D a b c d ha hb
              hc hd hdA
              hdB hAB hAC hAD hBC hBD hCD
  have diskEdgeSide (A B D p : Complex) (a d : Real)
      (ha : 0 < a) (hd : 0 < d)
      (hAB : dist A B = a)
      (hmargin : (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2)
      (hpD : dist D p < d) :
      0 < crossC (B - A) (D - A) * crossC (B - A) (p - A) := diskEdgeSide A B D p a d ha hd hAB
          hmargin hpD
  have sideTrans (x y z : Real) (hxy : 0 < x * y) (hyz : 0 < y * z) :
      0 < x * z := sideTrans x y z hxy hyz
  have ratioPos (x y : Real) (hxy : 0 < x * y) : 0 < y / x := ratioPos x y hxy
  have hr02 : rad 0 < rad 2 := hr02 q hq hpositive
  have hr03 : rad 0 < rad 3 := hr03 q hq hpositive
  have hside231 := soddySameSide (ctr 2) (ctr 3) (ctr 1) (ctr 0)
    (rad 2) (rad 3) (rad 1) (rad 0)
    (rpos 2) (rpos 3) (rpos 1) (rpos 0) hr02 hr03
    hd23 hd21 hd20 hd31 hd30 hd10
  have hp23 := diskEdgeSide (ctr 2) (ctr 3) (ctr 0) p
    (rad 2 + rad 3) (rad 0) (add_pos (rpos 2) (rpos 3)) (rpos 0)
    (ctrDist 2 3 (by decide)) hside231.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have htri231 := sideTrans
    (crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2))
    (crossC (ctr 3 - ctr 2) (ctr 0 - ctr 2))
    (crossC (ctr 3 - ctr 2) (p - ctr 2)) hside231.1 hp23
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  have hden231 : crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) = den := hden231 q
  change (0 < crossC (ctr 3 - ctr 2) (p - ctr 2) / den)
  have hh := ratioPos _ _ htri231
  rw [hden231] at hh
  exact hh

private theorem hA (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (hpositive : ∀ j
    : Fin 3, 0 < (q j.succ).1) (p : ℂ) (hp : dist p (((q 0).2 : ℂ) / ((q 0).1 : ℝ)) < 1 / ((q
    0).1 : ℝ)) : 0 < 1 -
      crossC (p - (ctr q) 1) ((ctr q) 3 - (ctr q) 1) / (den q) -
      crossC ((ctr q) 2 - (ctr q) 1) (p - (ctr q) 1) / (den q) := by
  classical
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  have harea : crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1) ≠ 0 := harea q hq hpositive
  have hden231 : crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) = den := hden231 q
  have hnum231 : crossC (ctr 3 - ctr 2) (p - ctr 2) =
      crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) -
        crossC (p - ctr 1) (ctr 3 - ctr 1) -
        crossC (ctr 2 - ctr 1) (p - ctr 1) := hnum231 q p
  have hLamA : 0 < crossC (ctr 3 - ctr 2) (p - ctr 2) / den := hLamA q hq hpositive p hp
  change (0 < 1 -
      crossC (p - ctr 1) (ctr 3 - ctr 1) / den -
      crossC (ctr 2 - ctr 1) (p - ctr 1) / den)
  have hAeq : 1 -
      crossC (p - ctr 1) (ctr 3 - ctr 1) / den -
      crossC (ctr 2 - ctr 1) (p - ctr 1) / den =
      crossC (ctr 3 - ctr 2) (p - ctr 2) / den := by
    have hnum : crossC (ctr 3 - ctr 2) (p - ctr 2) =
        den - crossC (p - ctr 1) (ctr 3 - ctr 1) -
          crossC (ctr 2 - ctr 1) (p - ctr 1) := by
      rw [hnum231, hden231]
    have hdenne : den ≠ 0 := by simpa [den] using harea
    rw [hnum]
    have fracComplement (d y z : Real) (hd : d ≠ 0) :
        1 - y / d - z / d=(d - y - z) / d := by
      field_simp [hd]
    exact fracComplement den
      (crossC (p - ctr 1) (ctr 3 - ctr 1))
      (crossC (ctr 2 - ctr 1) (p - ctr 1)) hdenne
  rw [hAeq]
  exact hLamA

end CircularPlacementConstruction

theorem P4828T1CircularPlacement (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hpositive : ∀ j : Fin 3, 0 < (q j.succ).1) :
    P4828T1Disk (q 0) ⊆ P4828T1Gap L q := by
-- BODY
  have hchild : 0 < (q 0).1 := CircularPlacementConstruction.hchild q hq
  have hcpos : ∀ i : Fin 4, 0 < (q i).1 := CircularPlacementConstruction.hcpos q hq hpositive
  have normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) :=
          CircularPlacementConstruction.normCast w
  have circleDist (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (((q i).2 : Complex) / (q i).1)
          (((q j).2 : Complex) / (q j).1) =
        1 / (q i).1 + 1 / (q j).1 := CircularPlacementConstruction.circleDist q hq i j hij hi hj
  let ctr (i : Fin 4) : Complex := ((q i).2 : Complex) / (q i).1
  let rad (i : Fin 4) : Real := 1 / (q i).1
  have rpos (i : Fin 4) : 0 < rad i := CircularPlacementConstruction.rpos q hq hpositive i
  have ctrDist (i j : Fin 4) (hij : i ≠ j) :
      dist (ctr i) (ctr j) = rad i + rad j := CircularPlacementConstruction.ctrDist q hq
          hpositive i j hij
  have hd12 := ctrDist 1 2 (by decide)
  have hd13 := ctrDist 1 3 (by decide)
  have hd10 := ctrDist 1 0 (by decide)
  have hd23 := ctrDist 2 3 (by decide)
  have hd20 := ctrDist 2 0 (by decide)
  have hd30 := ctrDist 3 0 (by decide)
  have hd21 : dist (ctr 2) (ctr 1) = rad 2 + rad 1 := CircularPlacementConstruction.hd21 q hq
      hpositive
  have hd31 : dist (ctr 3) (ctr 1) = rad 3 + rad 1 := CircularPlacementConstruction.hd31 q hq
      hpositive
  have hd32 : dist (ctr 3) (ctr 2) = rad 3 + rad 2 := CircularPlacementConstruction.hd32 q hq
      hpositive
  let crossC : Complex → Complex → Real := fun z w => z.re * w.im - z.im * w.re
  let dotC : Complex → Complex → Real := fun z w => z.re * w.re + z.im * w.im
  have soddySameSide (A B C D : Complex) (a b c d : Real)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
        (hdA : d < a) (hdB : d < b)
        (hAB : dist A B = a + b) (hAC : dist A C = a + c) (hAD : dist A D = a + d)
        (hBC : dist B C = b + c) (hBD : dist B D = b + d) (hCD : dist C D = c + d) :
        0 < crossC (B - A) (C - A) * crossC (B - A) (D - A) ∧
          (d * (a + b)) ^ 2 < crossC (B - A) (D - A) ^ 2 :=
              CircularPlacementConstruction.soddySameSide A
              B C D a b c d ha hb hc hd hdA hdB hAB hAC hAD hBC hBD hCD
  have crossSq_le (z w : Complex) :
      crossC z w ^ 2 ≤ Complex.normSq z * Complex.normSq w :=
          CircularPlacementConstruction.crossSq_le z w
  have diskEdgeSide (A B D p : Complex) (a d : Real)
      (ha : 0 < a) (hd : 0 < d)
      (hAB : dist A B = a)
      (hmargin : (d * a) ^ 2 < crossC (B - A) (D - A) ^ 2)
      (hpD : dist D p < d) :
      0 < crossC (B - A) (D - A) * crossC (B - A) (p - A) :=
          CircularPlacementConstruction.diskEdgeSide A
          B D p a d ha hd hAB hmargin hpD
  have sideTrans (x y z : Real) (hxy : 0 < x * y) (hyz : 0 < y * z) :
      0 < x * z := CircularPlacementConstruction.sideTrans x y z hxy hyz
  have ratioPos (x y : Real) (hxy : 0 < x * y) : 0 < y / x :=
      CircularPlacementConstruction.ratioPos x y hxy
  have strictSides (A B C p : Complex)
      (harea : crossC (B - A) (C - A) ≠ 0)
      (hC : 0 < crossC (B - A) (p - A) / crossC (B - A) (C - A))
      (hB : 0 < crossC (p - A) (C - A) / crossC (B - A) (C - A))
      (hA : 0 < 1 - crossC (p - A) (C - A) / crossC (B - A) (C - A) -
        crossC (B - A) (p - A) / crossC (B - A) (C - A)) :
      p ∈ interior (convexHull Real ({A, B, C} : Set Complex)) :=
          CircularPlacementConstruction.strictSides A B C p harea hC hB hA
  have radChildLtParent (j : Fin 3) : rad 0 < rad j.succ :=
      CircularPlacementConstruction.radChildLtParent q hq hpositive j
  have hr01 : rad 0 < rad 1 := CircularPlacementConstruction.hr01 q hq hpositive
  have hr02 : rad 0 < rad 2 := CircularPlacementConstruction.hr02 q hq hpositive
  have hr03 : rad 0 < rad 3 := CircularPlacementConstruction.hr03 q hq hpositive
  have hside123 := soddySameSide (ctr 1) (ctr 2) (ctr 3) (ctr 0)
    (rad 1) (rad 2) (rad 3) (rad 0)
    (rpos 1) (rpos 2) (rpos 3) (rpos 0) hr01 hr02
    hd12 hd13 hd10 hd23 hd20 hd30
  have hside231 := soddySameSide (ctr 2) (ctr 3) (ctr 1) (ctr 0)
    (rad 2) (rad 3) (rad 1) (rad 0)
    (rpos 2) (rpos 3) (rpos 1) (rpos 0) hr02 hr03
    hd23 hd21 hd20 hd31 hd30 hd10
  have hside312 := soddySameSide (ctr 3) (ctr 1) (ctr 2) (ctr 0)
    (rad 3) (rad 1) (rad 2) (rad 0)
    (rpos 3) (rpos 1) (rpos 2) (rpos 0) hr03 hr01
    hd31 hd32 hd30 hd12 hd10 hd20
  intro p hp
  change dist p (ctr 0) < rad 0 at hp
  have hp12 := diskEdgeSide (ctr 1) (ctr 2) (ctr 0) p
    (rad 1 + rad 2) (rad 0) (add_pos (rpos 1) (rpos 2)) (rpos 0)
    (ctrDist 1 2 (by decide)) hside123.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have hp23 := diskEdgeSide (ctr 2) (ctr 3) (ctr 0) p
    (rad 2 + rad 3) (rad 0) (add_pos (rpos 2) (rpos 3)) (rpos 0)
    (ctrDist 2 3 (by decide)) hside231.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have hp31 := diskEdgeSide (ctr 3) (ctr 1) (ctr 0) p
    (rad 3 + rad 1) (rad 0) (add_pos (rpos 3) (rpos 1)) (rpos 0)
    (ctrDist 3 1 (by decide)) hside312.2 (by simpa only [ctr, rad, Complex.ofReal_intCast,
        dist_comm] using hp)
  have htri123 := sideTrans
    (crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1))
    (crossC (ctr 2 - ctr 1) (ctr 0 - ctr 1))
    (crossC (ctr 2 - ctr 1) (p - ctr 1)) hside123.1 hp12
  have htri231 := sideTrans
    (crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2))
    (crossC (ctr 3 - ctr 2) (ctr 0 - ctr 2))
    (crossC (ctr 3 - ctr 2) (p - ctr 2)) hside231.1 hp23
  have htri312 := sideTrans
    (crossC (ctr 1 - ctr 3) (ctr 2 - ctr 3))
    (crossC (ctr 1 - ctr 3) (ctr 0 - ctr 3))
    (crossC (ctr 1 - ctr 3) (p - ctr 3)) hside312.1 hp31
  let den : Real := crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1)
  have harea : crossC (ctr 2 - ctr 1) (ctr 3 - ctr 1) ≠ 0 := CircularPlacementConstruction.harea
      q hq hpositive
  have hLamC : 0 < crossC (ctr 2 - ctr 1) (p - ctr 1) / den :=
      CircularPlacementConstruction.hLamC q hq hpositive p hp
  have hden312 : crossC (ctr 1 - ctr 3) (ctr 2 - ctr 3) = den :=
      CircularPlacementConstruction.hden312 q
  have hnum312 : crossC (ctr 1 - ctr 3) (p - ctr 3) =
      crossC (p - ctr 1) (ctr 3 - ctr 1) := CircularPlacementConstruction.hnum312 q p
  have hLamB : 0 < crossC (p - ctr 1) (ctr 3 - ctr 1) / den :=
      CircularPlacementConstruction.hLamB q hq hpositive p hp
  have hden231 : crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) = den :=
      CircularPlacementConstruction.hden231 q
  have hnum231 : crossC (ctr 3 - ctr 2) (p - ctr 2) =
      crossC (ctr 3 - ctr 2) (ctr 1 - ctr 2) -
        crossC (p - ctr 1) (ctr 3 - ctr 1) -
        crossC (ctr 2 - ctr 1) (p - ctr 1) := CircularPlacementConstruction.hnum231 q p
  have hLamA : 0 < crossC (ctr 3 - ctr 2) (p - ctr 2) / den :=
      CircularPlacementConstruction.hLamA q hq hpositive p hp
  have hA : 0 < 1 -
      crossC (p - ctr 1) (ctr 3 - ctr 1) / den -
      crossC (ctr 2 - ctr 1) (p - ctr 1) / den := CircularPlacementConstruction.hA q hq hpositive
          p hp
  have hinside := strictSides (ctr 1) (ctr 2) (ctr 3) p harea hLamC hLamB hA
  constructor
  · have hverts :
        ({x : Complex | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
          (x = ctr j.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧
            x = ⟨if (q k.succ).2 = -1 then L else L + 2,
              (ctr j.succ).im⟩)} : Set Complex) =
          ({ctr 1, ctr 2, ctr 3} : Set Complex) := by
      ext x
      constructor
      · intro hx
        change ∃ j : Fin 3, 0 < (q j.succ).1 ∧
          (x = ctr j.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧
            x = ⟨if (q k.succ).2 = -1 then L else L + 2,
              (ctr j.succ).im⟩) at hx
        rcases hx with ⟨j, hj, hx | ⟨k, hk, _⟩⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          fin_cases j
          · exact Or.inl hx
          · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inr hx)
        · have hz := hpositive k
          omega
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx
        · exact ⟨0, hpositive 0, Or.inl hx⟩
        · exact ⟨1, hpositive 1, Or.inl hx⟩
        · exact ⟨2, hpositive 2, Or.inl hx⟩
    · change p ∈ interior (convexHull Real
        {x : Complex | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
          (x = ctr j.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧
            x = ⟨if (q k.succ).2 = -1 then L else L + 2,
              (ctr j.succ).im⟩)})
      rw [hverts]
      exact hinside
  · intro j hj
    have hd := circleDist 0 j.succ (by intro h; exact Fin.succ_ne_zero j h.symm)
      hchild (hpositive j)
    have htri := dist_triangle
      (((q 0).2 : Complex) / (q 0).1) p
      (((q j.succ).2 : Complex) / (q j.succ).1)
    have hlower :
        1 / (q j.succ).1 <
          dist p (((q j.succ).2 : Complex) / (q j.succ).1) := by
      rw [hd, dist_comm (((q 0).2 : Complex) / (q 0).1) p] at htri
      linarith
    exact hlower

end ApollonianSuperharmonic

end
