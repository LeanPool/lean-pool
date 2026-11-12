/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandDiskExteriorDensity
public import LeanPool.ApollonianSuperharmonic.BandTangencyDensity
public import LeanPool.ApollonianSuperharmonic.EuclideanCircleData

-- [TABLET NODE: BandCircleEnclosureDichotomy]

/-!
# BandCircleEnclosureDichotomy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandCircleEnclosureDichotomy (E : EuclideanCircleData) :
    (∃ C : BandCircle,
      dist E.center (BandCircleEuclideanData C).center + E.radius ≤
        (BandCircleEuclideanData C).radius) ∨
    (∃ C : BandCircle,
      dist E.center (BandCircleEuclideanData C).center +
          (BandCircleEuclideanData C).radius < E.radius) := by
-- BODY
  by_cases hfirst : ∃ C : BandCircle,
      dist E.center (BandCircleEuclideanData C).center + E.radius ≤
        (BandCircleEuclideanData C).radius
  · exact Or.inl hfirst
  by_cases hexterior : BandPackingExterior E.center
  · obtain ⟨C, hC, hdist⟩ := BandDiskExteriorDensity E.center hexterior (E.radius / 4) (by
      linarith [E.radius_pos])
    right
    refine ⟨C, ?_⟩
    nlinarith [E.radius_pos, hC, hdist]
  · simp only [BandPackingExterior, not_forall] at hexterior
    obtain ⟨D, hD⟩ := hexterior
    let d : Real := dist E.center (BandCircleEuclideanData D).center
    let r : Real := (BandCircleEuclideanData D).radius
    have hd : d < r := by
      dsimp [d, r]
      exact lt_of_not_ge hD
    have hrd : r < d + E.radius := by
      by_contra h
      have hh : d + E.radius ≤ r := le_of_not_gt h
      apply hfirst
      exact ⟨D, by simpa [d, r, add_comm] using hh⟩
    let p : Complex := if d = 0 then
      (BandCircleEuclideanData D).center + (r : Complex) else
      (BandCircleEuclideanData D).center + (r / d) •
        (E.center - (BandCircleEuclideanData D).center)
    have hp : dist p (BandCircleEuclideanData D).center = r := by
      dsimp [p]
      by_cases hd0 : d = 0
      · rw [ite_eq_left hd0]
        simp only [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real]
        exact abs_of_pos (by simpa [r] using (BandCircleEuclideanData D).radius_pos)
      · rw [ite_eq_right hd0, Complex.dist_eq]
        change ‖(BandCircleEuclideanData D).center + (r / d) •
          (E.center - (BandCircleEuclideanData D).center) -
          (BandCircleEuclideanData D).center‖ = r
        have hident : (BandCircleEuclideanData D).center + (r / d) •
              (E.center - (BandCircleEuclideanData D).center) -
              (BandCircleEuclideanData D).center =
              (r / d) • (E.center - (BandCircleEuclideanData D).center) := by module
        rw [hident, norm_smul]
        simp only [Real.norm_eq_abs]
        rw [abs_of_pos (div_pos (by simpa [r] using (BandCircleEuclideanData D).radius_pos) (by
            positivity))]
        dsimp [d] at hd0 ⊢
        rw [show ‖E.center - (BandCircleEuclideanData D).center‖ = d by
          simpa [d] using (Complex.dist_eq E.center (BandCircleEuclideanData D).center).symm]
        field_simp
        dsimp [d]
    have hpz : dist p E.center < E.radius := by
      dsimp [p]
      by_cases hd0 : d = 0
      · rw [ite_eq_left hd0]
        have hc : E.center = (BandCircleEuclideanData D).center := by
          have hz : dist E.center (BandCircleEuclideanData D).center = 0 := by
            simpa [d] using hd0
          have hz' : ‖E.center - (BandCircleEuclideanData D).center‖ = 0 := by
            simpa [Complex.dist_eq] using hz
          exact sub_eq_zero.mp (norm_eq_zero.mp hz')
        rw [hc, Complex.dist_eq]
        simp only [add_sub_cancel_left, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_pos (by simpa [r] using (BandCircleEuclideanData
            D).radius_pos)]
        linarith
      · rw [ite_eq_right hd0, Complex.dist_eq]
        have hdpos : 0 < d := by
          dsimp [d]
          exact dist_pos.mpr (by
            intro h
            apply hd0
            simp [d, h])
        have hcoef : 0 < r / d - 1 := by
          apply (sub_pos.mpr)
          rw [lt_div_iff₀ hdpos]
          linarith
        change ‖(BandCircleEuclideanData D).center + (r / d) •
          (E.center - (BandCircleEuclideanData D).center) - E.center‖ < E.radius
        have hident : (BandCircleEuclideanData D).center + (r / d) •
              (E.center - (BandCircleEuclideanData D).center) - E.center =
              (r / d - 1) • (E.center - (BandCircleEuclideanData D).center) := by module
        rw [hident, norm_smul]
        simp only [Real.norm_eq_abs, abs_of_pos hcoef]
        dsimp [d] at hd0 ⊢
        rw [show ‖E.center - (BandCircleEuclideanData D).center‖ = d by
          simpa [d] using (Complex.dist_eq E.center (BandCircleEuclideanData D).center).symm]
        field_simp
        nlinarith [hrd, hdpos]
    obtain ⟨C, hDC, hCr, t, htp, htD, htC, hcent⟩ :=
      BandTangencyDensity D p hp ((E.radius - dist p E.center) / 4) (by linarith)
    right
    refine ⟨C, ?_⟩
    have htri : dist E.center (BandCircleEuclideanData C).center ≤
        dist E.center p + dist p t + dist t (BandCircleEuclideanData C).center := by
      calc
        dist E.center (BandCircleEuclideanData C).center ≤
            dist E.center t + dist t (BandCircleEuclideanData C).center :=
          dist_triangle _ _ _
        _ ≤ dist E.center p + dist p t + dist t (BandCircleEuclideanData C).center := by
          gcongr
          exact dist_triangle _ _ _
    calc
      dist E.center (BandCircleEuclideanData C).center +
          (BandCircleEuclideanData C).radius ≤
        dist E.center p + dist p t + dist t (BandCircleEuclideanData C).center +
          (BandCircleEuclideanData C).radius := by linarith
      _ < E.radius := by
        have hbound : dist p t + dist t (BandCircleEuclideanData C).center +
            (BandCircleEuclideanData C).radius < E.radius - dist E.center p := by
          rw [htC]
          have htp0 : dist p t < (E.radius - dist E.center p) / 4 := by
            simpa [dist_comm] using htp
          have hCr0 : (BandCircleEuclideanData C).radius <
              (E.radius - dist E.center p) / 4 := by
            simpa [dist_comm] using hCr
          have htp' : dist p t * 4 < E.radius - dist E.center p :=
            (lt_div_iff₀ (by norm_num)).mp htp0
          have hCr' : (BandCircleEuclideanData C).radius * 4 <
              E.radius - dist E.center p :=
            (lt_div_iff₀ (by norm_num)).mp hCr0
          have hsum : 4 * (dist p t + 2 * (BandCircleEuclideanData C).radius) <
              3 * (E.radius - dist E.center p) := by
            linarith [htp', hCr']
          have hpz0 : dist E.center p < E.radius := by simpa [dist_comm] using hpz
          have heta : 0 < E.radius - dist E.center p := by linarith [hpz0]
          have hmul : 4 * (dist p t + 2 * (BandCircleEuclideanData C).radius) <
              4 * (E.radius - dist E.center p) := by
            linarith [hsum, heta]
          have hsmall : dist p t + 2 * (BandCircleEuclideanData C).radius <
              E.radius - dist E.center p :=
            lt_of_mul_lt_mul_left hmul (by norm_num)
          convert hsmall using 1; ring
        calc
          dist E.center p + dist p t + dist t (BandCircleEuclideanData C).center +
              (BandCircleEuclideanData C).radius =
              dist E.center p + (dist p t + dist t (BandCircleEuclideanData C).center +
                (BandCircleEuclideanData C).radius) := by ring
          _ < dist E.center p + (E.radius - dist E.center p) := by
            have hsum := add_lt_add_right hbound (dist E.center p)
            convert hsum using 1
          _ = E.radius := by ring

end ApollonianSuperharmonic

end
