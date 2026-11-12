/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P5023T1ContactVertices
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import LeanPool.ApollonianSuperharmonic.P4953T1HullHeight
public import LeanPool.ApollonianSuperharmonic.P4828T1Disk

-- [TABLET NODE: P5023T1LineSideGeometry]

/-!
# P5023T1LineSideGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5023T1LineSideGeometry (L : ℝ) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (hs : P4828T1LineSupport L q)
    (hi : P4828T1Disk (q 0) ⊆ P4828T1Gap L q)
    (i : Fin 3) (hzero : (q i.succ).1 = 0) :
    let p (j : Fin 4) : ℂ := (q j).2 / ((q j).1 : ℝ)
    let r (j : Fin 4) : ℝ := 1 / ((q j).1 : ℝ)
    let j : Fin 3 := i + 1
    let k : Fin 3 := i + 2
    (min (p j.succ).im (p k.succ).im < (p 0).im ∧
      (p 0).im < max (p j.succ).im (p k.succ).im) ∧
    ((p 0).im - (p j.succ).im) ^ 2 = 4 * r 0 * r j.succ ∧
    ((p 0).im - (p k.succ).im) ^ 2 = 4 * r 0 * r k.succ ∧
    dist (P5023T1ContactVertices L q (i + 1))
      (P5023T1ContactVertices L q (i + 2)) =
        |(p j.succ).im - (p k.succ).im| := by
-- BODY
  let p (k : Fin 4) : ℂ := (q k).2 / ((q k).1 : ℝ)
  let r (k : Fin 4) : ℝ := 1 / ((q k).1 : ℝ)
  let j : Fin 3 := i + 1
  let k : Fin 3 := i + 2
  let h : ℝ := if (q i.succ).2 = -1 then L else L + 2
  have curv := ProperBandCurvatureStructure q hq
  have hR : 0 < r 0 := one_div_pos.mpr (by exact_mod_cast curv.1)
  have hjne : j ≠ i := by fin_cases i <;> decide
  have hkne : k ≠ i := by fin_cases i <;> decide
  have hjk : j ≠ k := by fin_cases i <;> decide
  have other_pos (a : Fin 3) (ha : a ≠ i) : 0 < (q a.succ).1 := by
    have hn := curv.2.1 a
    by_contra hnp
    have hz : (q a.succ).1 = 0 := by omega
    exact ha (curv.2.2 i a hzero hz).symm
  have hj := other_pos j hjne
  have hk := other_pos k hkne
  have centerDistance (a b : Fin 4) (hab : a ≠ b)
      (ha : 0 < (q a).1) (hb : 0 < (q b).1) :
      dist (p a) (p b) = r a + r b := by
    let w : GaussianInt := (q b).1 • (q a).2 - (q a).1 • (q b).2
    have ht := TangencyCoordinateIdentity q hq.1 a b hab
    have normCast (z : GaussianInt) :
        Complex.normSq (z : ℂ) = (Zsqrtd.norm z : ℝ) := by
      simp [Complex.normSq, Zsqrtd.norm_def]
    have hn : Complex.normSq (w : ℂ) = (((q a).1 + (q b).1 : ℤ) ^ 2 : ℝ) := by
      change Complex.normSq
        (((q b).1 • (q a).2 - (q a).1 • (q b).2 : GaussianInt) : ℂ) = _
      rw [normCast]
      exact_mod_cast ht
    have hnsq : ‖(w : ℂ)‖ ^ 2 = (((q a).1 + (q b).1 : ℤ) : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hn]
    have hnorm : ‖(w : ℂ)‖ = (((q a).1 + (q b).1 : ℤ) : ℝ) := by
      have hnonneg := norm_nonneg (w : ℂ)
      have hsum : 0 ≤ (((q a).1 + (q b).1 : ℤ) : ℝ) := by positivity
      nlinarith
    have hdiff : p a - p b =
        (w : ℂ) / (((q a).1 * (q b).1 : ℤ) : ℂ) := by
      dsimp [p, w]
      push_cast
      simp only [map_sub, map_zsmul]
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring
    rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
    have haR : 0 < ((q a).1 : ℝ) := by exact_mod_cast ha
    have hbR : 0 < ((q b).1 : ℝ) := by exact_mod_cast hb
    have habR : 0 < (((q a).1 * (q b).1 : ℤ) : ℝ) := by
      exact_mod_cast mul_pos ha hb
    rw [abs_of_pos habR]
    push_cast
    dsimp [r]
    field_simp [ne_of_gt haR, ne_of_gt hbR]
    ring
  have signedDistance (a : Fin 4) (ha : 0 < (q a).1) :
      (if (q i.succ).2 = -1 then 1 else -1) * ((p a).re - h) = r a := by
    have hnormal := hs.normals i.succ hzero
    have hh := hs.signed i.succ a hzero ha
    have hcne : (q a).1 ≠ 0 := ne_of_gt ha
    have hpre : (p a).re = (q a).2.re / (q a).1 := by
      dsimp [p]
      rw [Complex.div_re]
      simp
      field_simp [hcne]
    have hre : ((q a).2 : ℂ).re = (q a).2.re := by norm_num
    by_cases hneg : (q i.succ).2 = -1
    · rw [hneg] at hh
      norm_num at hh
      rw [hre] at hh
      simp only [h, hneg, ite_eq_left, one_mul, r]
      rw [hpre]
      field_simp [hcne]
      nlinarith
    · have hpos : (q i.succ).2 = 1 := by rcases hnormal with h' | h' <;> tauto
      rw [hpos] at hh
      norm_num at hh
      rw [hre] at hh
      simp only [h, hneg, ite_false, neg_one_mul, r]
      rw [hpre]
      field_simp [hcne]
      nlinarith
  have verticalSquare (a b : Fin 4) (ha : 0 < (q a).1)
      (hb : 0 < (q b).1) (hab : a ≠ b) :
      ((p a).im - (p b).im) ^ 2 = 4 * r a * r b := by
    let σ : ℝ := if (q i.succ).2 = -1 then 1 else -1
    have hσ : σ * σ = 1 := by dsimp [σ]; split_ifs <;> norm_num
    have hd := centerDistance a b hab ha hb
    have hn : ‖p a - p b‖ = r a + r b := by simpa [dist_eq_norm] using hd
    have hn2 := congrArg (fun x : ℝ => x ^ 2) hn
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im] at hn2
    have hsa := signedDistance a ha
    have hsb := signedDistance b hb
    have hdiff : σ * ((p a).re - (p b).re) = r a - r b := by
      dsimp [σ] at hsa hsb ⊢
      linear_combination hsa - hsb
    have hre : (p a).re - (p b).re = σ * (r a - r b) := by
      calc
        (p a).re - (p b).re = σ * σ * ((p a).re - (p b).re) := by rw [hσ]; ring
        _ = σ * (σ * ((p a).re - (p b).re)) := by ring
        _ = σ * (r a - r b) := by rw [hdiff]
    rw [hre] at hn2
    nlinarith [hσ]
  have hc : p 0 ∈ interior (P4909T1ParentPolygon L q) := by
    have hb : p 0 ∈ P4828T1Disk (q 0) := by
      change dist (p 0) (p 0) < r 0
      simpa only [dist_self] using hR
    exact (hi hb).1
  have hull : P4909T1ParentPolygon L q =
      convexHull ℝ ({p j.succ, p k.succ, ⟨h, (p j.succ).im⟩,
        ⟨h, (p k.succ).im⟩} : Set ℂ) :=
    (P4953T1LiteralHulls L q i j k hjne hkne hjk hzero hj hk curv.1).1
  have hheight : min (p j.succ).im (p k.succ).im < (p 0).im ∧
      (p 0).im < max (p j.succ).im (p k.succ).im := by
    apply P4953T1HullHeight h (p j.succ) (p k.succ) (p 0)
    rw [← hull]
    exact hc
  refine ⟨hheight, verticalSquare 0 j.succ curv.1 hj (Fin.succ_ne_zero j).symm,
    verticalSquare 0 k.succ curv.1 hk (Fin.succ_ne_zero k).symm, ?_⟩
  have hjz : (q j.succ).1 ≠ 0 := ne_of_gt hj
  have hkz : (q k.succ).1 ≠ 0 := ne_of_gt hk
  have hfeet :
      dist (P5023T1ContactVertices L q (i + 1))
        (P5023T1ContactVertices L q (i + 2)) =
      dist (⟨h, (p k.succ).im⟩ : ℂ) (⟨h, (p j.succ).im⟩ : ℂ) := by
    fin_cases i <;>
      simp_all [P5023T1ContactVertices, j, k, h, p]
  rw [hfeet, Complex.dist_eq_re_im]
  simp [Real.sqrt_sq_eq_abs, abs_sub_comm, p, j, k]

end ApollonianSuperharmonic

end
