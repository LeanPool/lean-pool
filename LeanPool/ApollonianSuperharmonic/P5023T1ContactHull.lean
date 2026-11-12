/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5023T1ContactVertices
public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import LeanPool.ApollonianSuperharmonic.P5090T1TangentCircleMetric
public import LeanPool.ApollonianSuperharmonic.P5090T1ThreeDiskContactTriangle
public import LeanPool.ApollonianSuperharmonic.P5090T1TwoDiskLineTriangle

-- [TABLET NODE: P5023T1ContactHull]

/-!
# P5023T1ContactHull

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ContactHullLemmas

private theorem curv :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → 0 < (q 0).1 ∧ (∀ (i : Fin 3), 0
        ≤ (q i.succ).1) ∧ ∀ (i : Fin 3), ∀ (j : Fin 3), (q i.succ).1 = 0 → (q j.succ).1 = 0 → i =
        j := by
  classical
  intro q hq
  exact ProperBandCurvatureStructure q hq

private theorem pair :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    ∀ (i : Fin 4), ∀ (j : Fin 4), (i ≠ j) → (0 < (q i).1) → (0 < (q j).1) → dist (p i) (p j) = r
        i + r j ∧
      ((q i).2 + (q j).2 : ℂ) / (((q i).1 : ℝ) + ((q j).1 : ℝ)) =
        (r j / (r i + r j)) • p i + (r i / (r i + r j)) • p j := by
  classical
  intro q hq p r i j hij hi hj
  let w : GaussianInt := (q j).1 • (q i).2 - (q i).1 • (q j).2
  have ht := TangencyCoordinateIdentity q hq.1 i j hij
  have normCast (z : GaussianInt) :
      Complex.normSq (z : ℂ) = (Zsqrtd.norm z : ℝ) := by
    simp [Complex.normSq, Zsqrtd.norm_def]
  have hn : Complex.normSq (w : ℂ) = (((q i).1 + (q j).1 : ℤ) ^ 2 : ℝ) := by
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(w : ℂ)‖ ^ 2 = (((q i).1 : ℝ) + ((q j).1 : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
    push_cast
    rfl
  have hw : (w : ℂ) = ((q j).1 : ℂ) * (q i).2 -
      ((q i).1 : ℂ) * (q j).2 := by
    simp [w, zsmul_eq_mul]
  rw [hw] at hnsq
  simpa only [Complex.ofReal_add, p, r] using
    P5090T1TangentCircleMetric ((q i).1 : ℝ) ((q j).1 : ℝ)
      (q i).2 (q j).2 (by exact_mod_cast hi) (by exact_mod_cast hj) hnsq

private theorem contact :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (∀ (i : Fin 4), ∀ (j : Fin 4), (i ≠ j) → (0 < (q i).1) → (0 < (q j).1) → dist (p i) (p j) = r
        i + r j ∧ ((q i).2 + (q j).2 : ℂ) / (((q i).1 : ℝ) + ((q j).1 : ℝ)) = (r j / (r i + r j))
        • p i + (r i / (r i + r j)) • p j) → ∀ (k : Fin 3), (0 < (q (k + 1).succ).1) → (0 < (q (k
        + 2).succ).1) → P5023T1ContactVertices L q k =
        (r (k + 2).succ / (r (k + 1).succ + r (k + 2).succ)) • p (k + 1).succ +
        (r (k + 1).succ / (r (k + 1).succ + r (k + 2).succ)) • p (k + 2).succ := by
  classical
  intro L q p r pair k ha hb
  dsimp only [P5023T1ContactVertices]
  rw [ite_eq_right (ne_of_gt ha), ite_eq_right (ne_of_gt hb)]
  exact (pair _ _ (by fin_cases k <;> decide) ha hb).2

end ContactHullLemmas

namespace ContactHullGeometry

private theorem signedDistance :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1LineSupport L q) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    ∀ (i : Fin (3 : ℕ)), ((q i.succ).1 = (0 : ℤ)) →
    let h : ℝ := if (q i.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q i.succ).2 = -1 then 1 else -1
    ∀ (c : Fin 4), (0 < (q c).1) → σ * ((p c).re - h) = r c := by
  classical
  intro L q hs p r i hi h σ c hc
  have hh := hs.signed i.succ c hi hc
  have hcne : (q c).1 ≠ 0 := ne_of_gt hc
  have hpre : (p c).re = (q c).2.re / (q c).1 := by
    dsimp [p]
    rw [Complex.div_re]
    simp
    field_simp [hcne]
  have hre : ((q c).2 : ℂ).re = (q c).2.re := by norm_num
  by_cases hneg : (q i.succ).2 = -1
  · rw [hneg] at hh
    norm_num at hh
    rw [hre] at hh
    simp only [σ, h, hneg, ite_eq_left, one_mul, r]
    rw [hpre]
    field_simp [hcne]
    nlinarith
  · have hn : (q i.succ).2 = 1 := by
      rcases hs.normals i.succ hi with hn | hn
      · exact (hneg hn).elim
      · exact hn
    rw [hn] at hh
    norm_num at hh
    rw [hre] at hh
    simp only [σ, h, hneg, ite_false, neg_one_mul, r]
    rw [hpre]
    field_simp [hcne]
    nlinarith

end ContactHullGeometry

theorem P5023T1ContactHull (L : ℝ) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (hs : P4828T1LineSupport L q) :
    P4984T1ClosedGap L q ⊆
      convexHull ℝ (Set.range (P5023T1ContactVertices L q)) := by
-- BODY
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  have curv := ContactHullLemmas.curv q hq
  have pair (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (p i) (p j) = r i + r j ∧
      ((q i).2 + (q j).2 : ℂ) / (((q i).1 : ℝ) + ((q j).1 : ℝ)) =
        (r j / (r i + r j)) • p i + (r i / (r i + r j)) • p j := ContactHullLemmas.pair q hq i j
            hij hi hj
  have contact (k : Fin 3)
      (ha : 0 < (q (k + 1).succ).1) (hb : 0 < (q (k + 2).succ).1) :
      P5023T1ContactVertices L q k =
        (r (k + 2).succ / (r (k + 1).succ + r (k + 2).succ)) • p (k + 1).succ +
        (r (k + 1).succ / (r (k + 1).succ + r (k + 2).succ)) • p (k + 2).succ :=
            ContactHullLemmas.contact L q pair k ha hb
  intro z hz
  rcases hz with ⟨hzPoly, hzOutside⟩
  by_cases hline : ∃ i : Fin 3, (q i.succ).1 = 0
  · obtain ⟨i, hi⟩ := hline
    let j : Fin 3 := i + 1
    let k : Fin 3 := i + 2
    have hji : j ≠ i := by fin_cases i <;> decide
    have hki : k ≠ i := by fin_cases i <;> decide
    have hjk : j ≠ k := by fin_cases i <;> decide
    have positive (a : Fin 3) (hai : a ≠ i) : 0 < (q a.succ).1 := by
      have hn := curv.2.1 a
      have hne : (q a.succ).1 ≠ 0 := fun h => hai (curv.2.2 a i h hi)
      omega
    have hj := positive j hji
    have hk := positive k hki
    let a := r j.succ
    let b := r k.succ
    have ha : 0 < a := one_div_pos.mpr (by exact_mod_cast hj)
    have hb : 0 < b := one_div_pos.mpr (by exact_mod_cast hk)
    let h : ℝ := if (q i.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q i.succ).2 = -1 then 1 else -1
    let A := p j.succ
    let B := p k.succ
    let F : ℂ := ⟨h, A.im⟩
    let G : ℂ := ⟨h, B.im⟩
    have hσsq : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
    have signedDistance (c : Fin 4) (hc : 0 < (q c).1) :
      σ * ((p c).re - h) = r c := ContactHullGeometry.signedDistance L q hs i hi c hc
    let f : ℂ →ᵃ[ℝ] ℂ :=
      { toFun := fun x => ⟨σ * (x.re - h), x.im⟩
        linear :=
          { toFun := fun x => ⟨σ * x.re, x.im⟩
            map_add' := by
              intro x y
              apply Complex.ext <;> simp; ring
            map_smul' := by
              intro t x
              apply Complex.ext <;> simp []; ring }
        map_vadd' := by
          intro x y
          apply Complex.ext <;> simp; ring }
    have fd (x y : ℂ) : dist (f x) (f y) = dist x y := by
      rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
      congr 1
      change (σ * (x.re - h) - σ * (y.re - h)) ^ 2 + (x.im - y.im) ^ 2 = _
      rw [show σ * (x.re - h) - σ * (y.re - h) = σ * (x.re - y.re) by ring,
        mul_pow, hσsq, one_mul]
    have finj : Function.Injective f := by
      intro x y hxy
      apply dist_eq_zero.mp
      rw [← fd, hxy, dist_self]
    have fA : f A = (⟨a, A.im⟩ : ℂ) := by
      apply Complex.ext
      · exact signedDistance j.succ hj
      · rfl
    have fB : f B = (⟨b, B.im⟩ : ℂ) := by
      apply Complex.ext
      · exact signedDistance k.succ hk
      · rfl
    have fF : f F = (⟨0, A.im⟩ : ℂ) := by simp [f, F]
    have fG : f G = (⟨0, B.im⟩ : ℂ) := by simp [f, G]
    have hpoly := (P4953T1LiteralHulls L q i j k hji hki hjk hi hj hk curv.1).1
    have hzf : f z ∈ convexHull ℝ
        ({⟨a, A.im⟩, ⟨b, B.im⟩, ⟨0, A.im⟩, ⟨0, B.im⟩} : Set ℂ) := by
      have hz' : z ∈ convexHull ℝ ({A, B, F, G} : Set ℂ) := by
        rw [← hpoly]
        exact hzPoly
      have himage := f.image_convexHull ({A, B, F, G} : Set ℂ)
      have hm : f z ∈ f '' convexHull ℝ ({A, B, F, G} : Set ℂ) := ⟨z, hz', rfl⟩
      rw [himage] at hm
      simpa only [Set.image_insert_eq, Set.image_singleton, fA, fB, fF, fG] using hm
    have hAB : dist A B = a + b :=
      (pair _ _ (fun heq => hjk (Fin.succ_inj.mp heq)) hj hk).1
    have hheight : (A.im - B.im) ^ 2 = 4 * a * b := by
      have hh := hAB
      rw [← fd, fA, fB, Complex.dist_eq_re_im] at hh
      have hh' := congrArg (fun x : ℝ => x ^ 2) hh
      rw [Real.sq_sqrt (by positivity)] at hh'
      nlinarith only [hh']
    have hheightpos : 0 < (A.im - B.im) ^ 2 := by rw [hheight]; positivity
    have htri := P5090T1TwoDiskLineTriangle a b A.im B.im (f z) ha hb
      (by rw [← fA, ← fB, fd]; exact hAB) hzf
      (by rw [← fA, fd]; exact hzOutside j hj)
      (by rw [← fB, fd]; exact hzOutside k hk)
    let K := (b / (a + b)) • A + (a / (a + b)) • B
    have hweights : b / (a + b) + a / (a + b) = 1 := by
      field_simp; ring
    have fK : f K = (b / (a + b)) • (f A) + (a / (a + b)) • (f B) := by
      apply Complex.ext
      · change σ * (K.re - h) = _
        simp only [K, Complex.add_re, Complex.smul_re, smul_eq_mul]
        change σ * (b / (a + b) * A.re + a / (a + b) * B.re - h) =
          b / (a + b) * (σ * (A.re - h)) + a / (a + b) * (σ * (B.re - h))
        linear_combination (σ * h) * hweights
      · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        change K.im = b / (a + b) * A.im + a / (a + b) * B.im
        simp only [K, Complex.add_im, Complex.smul_im, smul_eq_mul]
    have hK : P5023T1ContactVertices L q i = K := contact i hj hk
    have hfeet :
        P5023T1ContactVertices L q j = G ∧
        P5023T1ContactVertices L q k = F := by
      fin_cases i
      all_goals dsimp [j, k] at hi hj hk ⊢
      all_goals constructor
      all_goals simp [P5023T1ContactVertices, hi, ne_of_gt hk,
        F, G, A, B, p, h, j, k]
    have hset : Set.range (P5023T1ContactVertices L q) = ({F, K, G} : Set ℂ) := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        have ht : t = i ∨ t = j ∨ t = k := by
          fin_cases i <;> fin_cases t <;> simp [j, k]
        rcases ht with rfl | rfl | rfl <;> simp [hK, hfeet]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (rfl | rfl | rfl)
        · exact ⟨k, hfeet.2⟩
        · exact ⟨i, hK⟩
        · exact ⟨j, hfeet.1⟩
    rw [hset]
    have hmap : f '' ({F, K, G} : Set ℂ) =
        ({⟨0, A.im⟩, (b / (a + b)) • (⟨a, A.im⟩ : ℂ) +
          (a / (a + b)) • (⟨b, B.im⟩ : ℂ), ⟨0, B.im⟩} : Set ℂ) := by
      simp only [Set.image_insert_eq, Set.image_singleton, fF, fG, fK, fA, fB]
    rw [← hmap, ← f.image_convexHull] at htri
    obtain ⟨x, hx, hfx⟩ := htri
    exact finj hfx ▸ hx
  · have hpos (i : Fin 3) : 0 < (q i.succ).1 := by
      have hn := curv.2.1 i
      have hne : (q i.succ).1 ≠ 0 := fun hi => hline ⟨i, hi⟩
      omega
    have hpoly : P4909T1ParentPolygon L q =
        convexHull ℝ ({p 1, p 2, p 3} : Set ℂ) := by
      unfold P4909T1ParentPolygon
      apply congrArg (convexHull ℝ)
      ext x
      constructor
      · rintro ⟨i, _, hxi | ⟨k, hk, _⟩⟩
        · fin_cases i <;> simp_all [p]
        · exact (ne_of_gt (hpos k) hk).elim
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (rfl | rfl | rfl)
        · exact ⟨0, hpos 0, Or.inl rfl⟩
        · exact ⟨1, hpos 1, Or.inl rfl⟩
        · exact ⟨2, hpos 2, Or.inl rfl⟩
    have htri := P5090T1ThreeDiskContactTriangle (p 1) (p 2) (p 3) z
      (r 1) (r 2) (r 3)
      (one_div_pos.mpr (by exact_mod_cast hpos 0))
      (one_div_pos.mpr (by exact_mod_cast hpos 1))
      (one_div_pos.mpr (by exact_mod_cast hpos 2))
      (pair 1 2 (by decide) (hpos 0) (hpos 1)).1
      (pair 1 3 (by decide) (hpos 0) (hpos 2)).1
      (pair 2 3 (by decide) (hpos 1) (hpos 2)).1
      (hpoly ▸ hzPoly) (hzOutside 0 (hpos 0))
      (hzOutside 1 (hpos 1)) (hzOutside 2 (hpos 2))
    have hC0 := contact 0 (hpos 1) (hpos 2)
    have hC1 := contact 1 (hpos 2) (hpos 0)
    have hC2 := contact 2 (hpos 0) (hpos 1)
    change P5023T1ContactVertices L q 0 =
      (r 3 / (r 2 + r 3)) • p 2 + (r 2 / (r 2 + r 3)) • p 3 at hC0
    change P5023T1ContactVertices L q 2 =
      (r 2 / (r 1 + r 2)) • p 1 + (r 1 / (r 1 + r 2)) • p 2 at hC2
    have hC1' : P5023T1ContactVertices L q 1 =
        (r 3 / (r 1 + r 3)) • p 1 + (r 1 / (r 1 + r 3)) • p 3 := by
      simpa only [show (1 + 1 : Fin 3).succ = 3 by rfl,
        show (1 + 2 : Fin 3).succ = 1 by rfl, add_comm] using hC1
    rw [← hC2, ← hC1', ← hC0] at htri
    apply convexHull_mono _ htri
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

end ApollonianSuperharmonic

end
