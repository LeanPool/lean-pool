/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5050T1RadialSection
public import LeanPool.ApollonianSuperharmonic.P4953T1QuadrilateralSections
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P5050T1TangentLineSection]

/-!
# P5050T1TangentLineSection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TangentLineSectionProof

private theorem hmem :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ), (σ ^ (2 : ℕ) = (1 : ℝ)) →
        (((0 : ℝ) < r) → (((0 : ℝ) < s) → ((σ * (a.re - h) = r) → ((σ * (b.re - h) = s) → (
    let fa : ℂ := ⟨h, a.im⟩
    let fb : ℂ := ⟨h, b.im⟩
    let Q := convexHull ℝ ({a, b, fa, fb} : Set ℂ)
    (b.im - a.im ≠ 0) → ((σ * σ = 1) → ((∀ x : ℝ, σ * (σ * x) = x) → (∀ z ∈ Q,
      min a.im b.im ≤ z.im ∧ z.im ≤ max a.im b.im ∧
      0 ≤ σ * (z.re - h) ∧
      σ * (z.re - h) ≤ r * (1 - (z.im - a.im) / (b.im - a.im)) +
        s * ((z.im - a.im) / (b.im - a.im)))))))))) := by
  classical
  intro h σ a b r s hσ hr hs ha hb fa fb Q hdne hσsq hσmul z hz
  by_cases habh : a.im < b.im
  · have hq := P4953T1QuadrilateralSections h σ a b hσ
      (by simpa [ha] using hr) (by simpa [hb] using hs) habh
    have hz' : z ∈ convexHull ℝ ({a,b,⟨h,a.im⟩,⟨h,b.im⟩} : Set ℂ) := by
      simpa [fa, fb] using hz
    have hm := (hq.1 z).mp hz'
    have hupper : σ * (z.re - h) ≤
        r * (1 - (z.im - a.im) / (b.im - a.im)) +
          s * ((z.im - a.im) / (b.im - a.im)) := by
      have hlin := hm.2.2.2
      change 0 ≤ σ * (a.re + (b.re-a.re) * (z.im-a.im) /
        (b.im-a.im) - z.re) at hlin
      have hσa : a.re = h + σ * r := by
        calc
          a.re = h + (a.re-h) := by ring
          _ = h + σ * (σ * (a.re-h)) := by rw [hσmul]
          _ = h + σ * r := by rw [ha]
      have hσb : b.re = h + σ * s := by
        calc
          b.re = h + (b.re-h) := by ring
          _ = h + σ * (σ * (b.re-h)) := by rw [hσmul]
          _ = h + σ * s := by rw [hb]
      have hinterp :
          a.re + (b.re - a.re) * (z.im - a.im) / (b.im - a.im) =
            h + σ * (r * (1 - (z.im - a.im) / (b.im - a.im)) +
              s * ((z.im - a.im) / (b.im - a.im))) := by
        rw [hσa, hσb]
        field_simp
        ring
      rw [hinterp] at hlin
      have hsign : σ * (h + σ * (r * (1 - (z.im-a.im)/(b.im-a.im)) +
          s * ((z.im-a.im)/(b.im-a.im))) - z.re) =
          r * (1 - (z.im-a.im)/(b.im-a.im)) +
            s * ((z.im-a.im)/(b.im-a.im)) - σ * (z.re-h) := by
        calc
          _ = (σ*σ) * (r * (1 - (z.im-a.im)/(b.im-a.im)) +
              s * ((z.im-a.im)/(b.im-a.im))) - σ*(z.re-h) := by ring
          _ = _ := by rw [hσsq]; ring
      rw [hsign] at hlin
      linarith
    exact ⟨(min_le_iff.mpr (Or.inl hm.1)), (le_max_iff.mpr (Or.inr hm.2.1)),
      hm.2.2.1, hupper⟩
  · have hba : b.im < a.im := by
      have hle : b.im ≤ a.im := le_of_not_gt habh
      have hne : b.im ≠ a.im := by
        intro he
        apply hdne
        linarith
      exact lt_of_le_of_ne hle hne
    have hq := P4953T1QuadrilateralSections h σ b a hσ
      (by simpa [hb] using hs) (by simpa [ha] using hr) hba
    have hz' : z ∈ convexHull ℝ ({b,a,⟨h,b.im⟩,⟨h,a.im⟩} : Set ℂ) := by
      apply convexHull_mono (s := ({a,b,fa,fb} : Set ℂ))
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
        tauto
      · exact hz
    have hm := (hq.1 z).mp hz'
    have hupper : σ * (z.re - h) ≤
        r * (1 - (z.im - a.im) / (b.im - a.im)) +
          s * ((z.im - a.im) / (b.im - a.im)) := by
      have hlin := hm.2.2.2
      change 0 ≤ σ * (b.re + (a.re-b.re) * (z.im-b.im) /
        (a.im-b.im) - z.re) at hlin
      have hσa : a.re = h + σ * r := by
        calc
          a.re = h + (a.re-h) := by ring
          _ = h + σ * (σ * (a.re-h)) := by rw [hσmul]
          _ = h + σ * r := by rw [ha]
      have hσb : b.re = h + σ * s := by
        calc
          b.re = h + (b.re-h) := by ring
          _ = h + σ * (σ * (b.re-h)) := by rw [hσmul]
          _ = h + σ * s := by rw [hb]
      have hparam : (z.im-b.im)/(a.im-b.im) =
          1 - (z.im-a.im)/(b.im-a.im) := by
        have hne : a.im-b.im ≠ 0 := by linarith [hba]
        field_simp [hdne, hne]
        ring
      have hinterp :
          b.re + (a.re - b.re) * (z.im - b.im) / (a.im - b.im) =
            h + σ * (r * (1 - (z.im - a.im) / (b.im - a.im)) +
              s * ((z.im - a.im) / (b.im - a.im))) := by
        rw [show (a.re-b.re)*(z.im-b.im)/(a.im-b.im) =
          (a.re-b.re)*((z.im-b.im)/(a.im-b.im)) by ring, hparam, hσa, hσb]
        ring
      rw [hinterp] at hlin
      have hsign : σ * (h + σ * (r * (1 - (z.im-a.im)/(b.im-a.im)) +
          s * ((z.im-a.im)/(b.im-a.im))) - z.re) =
          r * (1 - (z.im-a.im)/(b.im-a.im)) +
            s * ((z.im-a.im)/(b.im-a.im)) - σ * (z.re-h) := by
        calc
          _ = (σ*σ) * (r * (1 - (z.im-a.im)/(b.im-a.im)) +
              s * ((z.im-a.im)/(b.im-a.im))) - σ*(z.re-h) := by ring
          _ = _ := by rw [hσsq]; ring
      rw [hsign] at hlin
      linarith
    exact ⟨(min_le_iff.mpr (Or.inr hm.1)), (le_max_iff.mpr (Or.inl hm.2.1)),
      hm.2.2.1, hupper⟩

private theorem ht0 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ), (b.im - a.im ≠ 0) → (∀ (z :
        ℂ), (min a.im b.im ≤ z.im ∧ z.im ≤ max a.im b.im ∧ (0 : ℝ) ≤ σ * (z.re - h) ∧ σ * (z.re -
        h) ≤ r * ((1 : ℝ) - (z.im - a.im) / (b.im - a.im)) + s * ((z.im - a.im) / (b.im - a.im)))
        → (
    let t := (z.im - a.im) / (b.im - a.im)
    0 ≤ t)) := by
  classical
  intro h σ a b r s hdne z hm t
  dsimp [t]
  by_cases hdb : 0 < b.im - a.im
  · have habh : a.im < b.im := by linarith
    have hzge : a.im ≤ z.im := by
      simpa [min_eq_left habh.le] using hm.1
    exact div_nonneg (sub_nonneg.mpr hzge) hdb.le
  · have hdvals : b.im ≠ a.im := by
      intro hh
      apply hdne
      linarith
    have hdb' : b.im - a.im < 0 := lt_of_le_of_ne (le_of_not_gt hdb) hdne
    have hzle : z.im ≤ a.im := by
      rcases le_max_iff.mp hm.2.1 with hza | hzb
      · exact hza
      · linarith
    exact div_nonneg_of_nonpos (by linarith) hdb'.le

private theorem ht1 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ), (b.im - a.im ≠ 0) → (∀ (z :
        ℂ), (min a.im b.im ≤ z.im ∧ z.im ≤ max a.im b.im ∧ (0 : ℝ) ≤ σ * (z.re - h) ∧ σ * (z.re -
        h) ≤ r * ((1 : ℝ) - (z.im - a.im) / (b.im - a.im)) + s * ((z.im - a.im) / (b.im - a.im)))
        → (
    let t := (z.im - a.im) / (b.im - a.im)
    t ≤ 1)) := by
  classical
  intro h σ a b r s hdne z hm t
  dsimp [t]
  by_cases hdb : 0 < b.im - a.im
  · have hzle : z.im ≤ b.im := by
      rcases le_max_iff.mp hm.2.1 with hza | hzb
      · linarith
      · exact hzb
    exact (div_le_one₀ hdb).2 (by linarith)
  · have hdvals : b.im ≠ a.im := by
      intro hh
      apply hdne
      linarith
    have hdb' : b.im - a.im < 0 := lt_of_le_of_ne (le_of_not_gt hdb) hdne
    have hzge : b.im ≤ z.im := by
      rcases min_le_iff.mp hm.1 with hza | hzb
      · exact (sub_nonpos.mp hdb'.le).trans hza
      · exact hzb
    exact (div_le_iff_of_neg hdb').2 (by linarith [hzge])

private theorem hzcoordAt300 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ), ((0 : ℝ) < s) → ((σ * (a.re
        - h) = r) → ((σ * (b.re - h) = s) → (
    let fb : ℂ := ⟨h, b.im⟩
    (b.im - a.im ≠ 0) → ((∀ x : ℝ, σ * (σ * x) = x) → (∀ (z : ℂ),
    let t := (z.im - a.im) / (b.im - a.im)
    let X := σ * (z.re - h)
    let v := (X - r * (1 - t)) / s
    z =
      (1 - t) • a + v • b + (t - v) • fb))))) := by
  classical
  intro h σ a b r s hs ha hb fb hdne hσmul z t X v
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re,
      fb, smul_eq_mul]
    have haR : a.re = h + σ * r := by
      calc
        a.re = h + (a.re-h) := by ring
        _ = h + σ * (σ * (a.re-h)) := by rw [hσmul]
        _ = h + σ * r := by rw [ha]
    have hbR : b.re = h + σ * s := by
      calc
        b.re = h + (b.re-h) := by ring
        _ = h + σ * (σ * (b.re-h)) := by rw [hσmul]
        _ = h + σ * s := by rw [hb]
    have hzR : z.re = h + σ * X := by dsimp [X]; rw [hσmul]; ring
    rw [haR, hbR, hzR]
    have hx : X = r * (1-t) + s*v := by
      dsimp [v]
      field_simp [ne_of_gt hs]
      ring
    rw [hx]
    ring
  · simp only [Complex.add_im, Complex.smul_im,
      fb, smul_eq_mul]
    have hzI : z.im = a.im + t * (b.im - a.im) := by
      dsimp [t]
      field_simp [hdne]
      ring
    rw [hzI]
    ring

private theorem hwAt331 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ),
    let fb : ℂ := ⟨h, b.im⟩
    ∀ (z : ℂ),
    let t := (z.im - a.im) / (b.im - a.im)
    let X := σ * (z.re - h)
    (t ≤ 1) → (
    let v := (X - r * (1 - t)) / s
    (0 ≤ v) → ((v ≤ t) → ((1 - t) • a + v • b + (t-v) • fb ∈
      convexHull ℝ ({a,b,fb} : Set ℂ)))) := by
  classical
  intro h σ a b r s fb z t X ht1 v hv0 hvt
  apply mem_convexHull_of_exists_fintype (ι := Fin 3)
    ![1-t,v,t-v] ![a,b,fb]
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> simp
  · simp [Fin.sum_univ_succ, add_assoc]

private theorem hzcoordAt349 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ((0 : ℝ) < r) → ((σ * (a.re - h) = r) → (
    let fa : ℂ := ⟨h, a.im⟩
    let fb : ℂ := ⟨h, b.im⟩
    (b.im - a.im ≠ 0) → ((∀ x : ℝ, σ * (σ * x) = x) → (∀ (z : ℂ),
    let t := (z.im - a.im) / (b.im - a.im)
    let X := σ * (z.re - h)
    let u := X / r
    z = u • a + t • fb + (1-t-u) • fa)))) := by
  classical
  intro h σ a b r hr ha fa fb hdne hσmul z t X u
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re,
      fa, fb, smul_eq_mul]
    have haR : a.re = h + σ * r := by
      calc
        a.re = h + (a.re-h) := by ring
        _ = h + σ * (σ * (a.re-h)) := by rw [hσmul]
        _ = h + σ * r := by rw [ha]
    have hzR : z.re = h + σ * X := by dsimp [X]; rw [hσmul]; ring
    rw [haR, hzR]
    have hx : u * r = X := by
      dsimp [u]
      field_simp [ne_of_gt hr]
    calc
      h + σ * X = h + σ * (u * r) := by rw [hx]
      _ = u * (h + σ * r) + t * h + (1-t-u) * h := by ring
  · simp only [Complex.add_im, Complex.smul_im,
      fa, fb, smul_eq_mul]
    have hzI : z.im = a.im + t * (b.im - a.im) := by
      dsimp [t]
      field_simp [hdne]
      ring
    rw [hzI]
    ring

private theorem hwAt374 :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ),
    let fa : ℂ := ⟨h, a.im⟩
    let fb : ℂ := ⟨h, b.im⟩
    ∀ (z : ℂ),
    let t := (z.im - a.im) / (b.im - a.im)
    let X := σ * (z.re - h)
    (0 ≤ t) → (
    let u := X / r
    (0 ≤ u) → ((u ≤ 1-t) → (u • a + t • fb + (1-t-u) • fa ∈
      convexHull ℝ ({a,fb,fa} : Set ℂ)))) := by
  classical
  intro h σ a b r fa fb z t X ht0 u hu0 hu1
  apply mem_convexHull_of_exists_fintype (ι := Fin 3)
    ![u,t,1-t-u] ![a,fb,fa]
  · intro i
    fin_cases i <;> simp <;> linarith
  · simpa [Fin.sum_univ_succ, add_assoc] using
      (show u+t+(1-t-u)=1 by ring)
  · intro i
    fin_cases i <;> simp
  · simp [Fin.sum_univ_succ, add_assoc]

private theorem sepOne :
    ∀ (h : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ∀ (s : ℝ), ((0 : ℝ) < s) → ((dist a b = r + s) → (
    let fb : ℂ := ⟨h, b.im⟩
    (dist b fb = s) → (∀ w ∈ convexHull ℝ ({b, fb} : Set ℂ), r ≤ ‖w - a‖))) := by
  classical
  intro h a b r s hs hab fb hbf w hw
  rw [convexHull_pair] at hw
  have hwb : w ∈ Metric.closedBall b s :=
    (convex_closedBall b s).segment_subset
      (Metric.mem_closedBall.mpr (by simpa using hs.le))
      (Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hbf.le)) hw
  have ht := dist_triangle a w b
  rw [hab] at ht
  have hwa : dist a w = ‖w - a‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hbnd := Metric.mem_closedBall.mp hwb
  linarith

private theorem sepTwo :
    ∀ (h : ℝ), ∀ (σ : ℝ), ∀ (a : ℂ), ∀ (b : ℂ), ∀ (r : ℝ), ((0 : ℝ) < r) → ((σ * (a.re - h) = r) → (
    let fa : ℂ := ⟨h, a.im⟩
    let fb : ℂ := ⟨h, b.im⟩
    (∀ (y : ℝ), ∀ (t : ℝ), (0 < t) → ((σ * (y - h) = t) → (|y - h| = t))) → (∀ w ∈ convexHull ℝ
        ({fb, fa} : Set ℂ), r ≤ ‖w - a‖))) := by
  classical
  intro h σ a b r hr ha fa fb absSigned w hw
  rw [convexHull_pair, segment_eq_image] at hw
  obtain ⟨t, _, rfl⟩ := hw
  have hre : ((1 - t) • fb + t • fa).re = h := by
    simp only [Complex.add_re, Complex.smul_re, fa, fb, smul_eq_mul]
    ring
  have hh := Complex.abs_re_le_norm ((1 - t) • fb + t • fa - a)
  rw [Complex.sub_re, hre, abs_sub_comm] at hh
  rw [absSigned a.re r hr ha] at hh
  exact hh

end TangentLineSectionProof

theorem P5050T1TangentLineSection (h σ : ℝ) (a b : ℂ) (r s : ℝ)
    (hσ : σ ^ 2 = 1) (hr : 0 < r) (hs : 0 < s)
    (ha : σ * (a.re - h) = r) (hb : σ * (b.re - h) = s)
    (hab : dist a b = r + s) :
    let fa : ℂ := ⟨h, a.im⟩
    let fb : ℂ := ⟨h, b.im⟩
    let F (w : ℂ) := a + (r / ‖w - a‖) • (w - a)
    let Q := convexHull ℝ ({a, b, fa, fb} : Set ℂ)
    Q = convexHull ℝ ({a, b, fb} : Set ℂ) ∪
      convexHull ℝ ({a, fb, fa} : Set ℂ) ∧
    Metric.sphere a r ∩ Q = F '' segment ℝ b fb ∪ F '' segment ℝ fb fa ∧
    IsPreconnected (Metric.sphere a r ∩ Q) := by
-- BODY
  exact (by
  dsimp only
  let fa : ℂ := ⟨h, a.im⟩
  let fb : ℂ := ⟨h, b.im⟩
  let F (w : ℂ) := a + (r / ‖w - a‖) • (w - a)
  let Q := convexHull ℝ ({a, b, fa, fb} : Set ℂ)
  have hsplit : Q = convexHull ℝ ({a, b, fb} : Set ℂ) ∪
      convexHull ℝ ({a, fb, fa} : Set ℂ) := by
    classical
    have hnorm : ‖a - b‖ = r + s := by
      simpa [dist_eq_norm] using hab
    have hnorm2 := congrArg (fun x : ℝ => x ^ 2) hnorm
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im] at hnorm2
    have hre : (a.re - b.re) ^ 2 = (r - s) ^ 2 := by
      have hσsq : σ * σ = 1 := by nlinarith [hσ]
      nlinarith [ha, hb]
    have hd2 : (b.im - a.im) ^ 2 = 4 * r * s := by nlinarith [hnorm2, hre]
    have hdne : b.im - a.im ≠ 0 := by
      intro hz
      rw [hz] at hd2
      nlinarith [mul_pos hr hs]
    have hσsq : σ * σ = 1 := by nlinarith [hσ]
    have hσmul : ∀ x : ℝ, σ * (σ * x) = x := by
      intro x
      calc
        σ * (σ * x) = (σ * σ) * x := by ring
        _ = x := by rw [hσsq]; ring
    have hmem : ∀ z ∈ Q,
        min a.im b.im ≤ z.im ∧ z.im ≤ max a.im b.im ∧
        0 ≤ σ * (z.re - h) ∧
        σ * (z.re - h) ≤ r * (1 - (z.im - a.im) / (b.im - a.im)) +
          s * ((z.im - a.im) / (b.im - a.im)) := TangentLineSectionProof.hmem h σ a b r s hσ hr
              hs ha hb hdne hσsq hσmul
    apply Set.Subset.antisymm
    · intro z hz
      have hm := hmem z hz
      let t := (z.im - a.im) / (b.im - a.im)
      let X := σ * (z.re - h)
      have ht0 : 0 ≤ t := TangentLineSectionProof.ht0 h σ a b r s hdne z hm
      have ht1 : t ≤ 1 := TangentLineSectionProof.ht1 h σ a b r s hdne z hm
      have hX0 : 0 ≤ X := by exact hm.2.2.1
      have hXupper : X ≤ r * (1 - t) + s * t := by exact hm.2.2.2
      by_cases hcut : r * (1 - t) ≤ X
      · let v := (X - r * (1 - t)) / s
        have hv0 : 0 ≤ v := by dsimp [v]; exact div_nonneg (by linarith) hs.le
        have hvt : v ≤ t := by
          dsimp [v]
          apply (div_le_iff₀ hs).2
          nlinarith [hXupper]
        have hzcoord : z =
            (1 - t) • a + v • b + (t - v) • fb := TangentLineSectionProof.hzcoordAt300 h σ a b r
                s hs ha hb hdne hσmul z
        have hw : (1 - t) • a + v • b + (t-v) • fb ∈
            convexHull ℝ ({a,b,fb} : Set ℂ) := TangentLineSectionProof.hwAt331 h σ a b r s z ht1
                hv0 hvt
        rw [hzcoord]
        exact Or.inl hw
      · let u := X / r
        have hu0 : 0 ≤ u := by dsimp [u]; exact div_nonneg hX0 hr.le
        have hu1 : u ≤ 1-t := by
          dsimp [u]
          apply (div_le_iff₀ hr).2
          linarith
        have hzcoord : z = u • a + t • fb + (1-t-u) • fa := TangentLineSectionProof.hzcoordAt349
            h σ a b r hr ha hdne hσmul z
        have hw : u • a + t • fb + (1-t-u) • fa ∈
            convexHull ℝ ({a,fb,fa} : Set ℂ) := TangentLineSectionProof.hwAt374 h σ a b r z ht0
                hu0 hu1
        rw [hzcoord]
        exact Or.inr hw
    · intro z hz
      rcases hz with hzOne | hzTwo
      · have hs : ({a,b,fb} : Set ℂ) ⊆ ({a,b,fa,fb} : Set ℂ) := by
          exact Set.insert_subset_insert
            (Set.insert_subset_insert (Set.subset_insert fa ({fb} : Set ℂ)))
        exact convexHull_mono hs hzOne
      · have hperm : ({a,fb,fa} : Set ℂ) = ({a,fa,fb} : Set ℂ) := by
          ext w
          simp [eq_comm, or_comm]
        have hsub : ({a,fa,fb} : Set ℂ) ⊆ ({a,b,fa,fb} : Set ℂ) := by
          exact Set.insert_subset_insert (Set.subset_insert b (insert fa ({fb} : Set ℂ)))
        have hs : ({a,fb,fa} : Set ℂ) ⊆ ({a,b,fa,fb} : Set ℂ) := by
          rw [hperm]
          exact hsub
        exact convexHull_mono hs hzTwo
  have hσsqOuter : σ * σ = 1 := by nlinarith [hσ]
  have hσmulOuter : ∀ x : ℝ, σ * (σ * x) = x := by
    intro x
    calc
      σ * (σ * x) = (σ * σ) * x := by ring
      _ = x := by rw [hσsqOuter]; ring
  have absSigned (y t : ℝ) (ht : 0 < t) (hy : σ * (y - h) = t) :
      |y - h| = t := by
    have hh := congrArg (fun x : ℝ => x ^ 2) hy
    rw [mul_pow, hσ, one_mul] at hh
    nlinarith [sq_abs (y - h), abs_nonneg (y - h)]
  have hbf : dist b fb = s := by
    rw [Complex.dist_eq]
    have hv : b - fb = ((b.re - h : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [fb]
    rw [hv, Complex.norm_real, Real.norm_eq_abs]
    exact absSigned b.re s hs hb
  have sepOne : ∀ w ∈ convexHull ℝ ({b, fb} : Set ℂ), r ≤ ‖w - a‖ :=
      TangentLineSectionProof.sepOne h a b r s hs hab hbf
  have sepTwo : ∀ w ∈ convexHull ℝ ({fb, fa} : Set ℂ), r ≤ ‖w - a‖ :=
      TangentLineSectionProof.sepTwo h σ a b r hr ha absSigned
  have hOne := P5050T1RadialSection a r {b, fb} hr ⟨b, by simp⟩ sepOne
  have hTwo := P5050T1RadialSection a r {fb, fa} hr ⟨fb, by simp⟩ sepTwo
  have heq : Metric.sphere a r ∩ Q = F '' segment ℝ b fb ∪ F '' segment ℝ fb fa := by
    rw [hsplit, Set.inter_union_distrib_left, hOne.1, hTwo.1, convexHull_pair,
      convexHull_pair]
  refine ⟨hsplit, heq, ?_⟩
  have hmOne : F fb ∈ Metric.sphere a r ∩ convexHull ℝ ({a, b, fb} : Set ℂ) := by
    rw [hOne.1]
    exact ⟨fb, by rw [convexHull_pair]; exact right_mem_segment ℝ b fb, rfl⟩
  have hmTwo : F fb ∈ Metric.sphere a r ∩ convexHull ℝ ({a, fb, fa} : Set ℂ) := by
    rw [hTwo.1]
    exact ⟨fb, by rw [convexHull_pair]; exact left_mem_segment ℝ fb fa, rfl⟩
  change IsPreconnected (Metric.sphere a r ∩ Q)
  rw [hsplit, Set.inter_union_distrib_left]
  exact IsPreconnected.union (F fb) hmOne hmTwo hOne.2 hTwo.2
  )

end ApollonianSuperharmonic

end
