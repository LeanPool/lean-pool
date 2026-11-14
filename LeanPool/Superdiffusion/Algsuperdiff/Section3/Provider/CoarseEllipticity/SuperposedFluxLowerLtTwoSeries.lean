/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerTwoLe

/-!
# SuperposedFluxLowerLtTwoSeries

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scale-series estimates below exponent two

For `1 ≤ q < 2`, the amplitude remains inside the `q/2` power.  This file
retains the collar exponent exactly and bounds only the dimension-only and
polynomial factors.  The resulting statements are conditional Provider
helpers and assert no source-node status.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- Uniform replacement of the dimension-only amplitude under powers in
`[1/2,1]`. -/
def superposedFluxDepthAmpMaxConst (d : ℕ) : ℝ :=
  max 1 (superposedFluxDepthAmpConst d)

theorem superposedFluxDepthAmpMaxConst_pos (d : ℕ) :
    0 < superposedFluxDepthAmpMaxConst d :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Fixed prefactor in the subquadratic amplitude series. -/
def superposedFluxLtTwoSeriesConst (d : ℕ) : ℝ :=
  32 * superposedFluxDepthAmpMaxConst d * superposedFluxLowerPoleConst

theorem superposedFluxLtTwoSeriesConst_pos (d : ℕ) :
    0 < superposedFluxLtTwoSeriesConst d :=
  mul_pos (mul_pos (by norm_num) (superposedFluxDepthAmpMaxConst_pos d))
    superposedFluxLowerPoleConst_pos

/-- Fixed prefactor in the subquadratic final Orlicz budget. -/
def superposedFluxLtTwoBudgetConst (d : ℕ) : ℝ :=
  2 * superposedFluxTriangleConst * superposedFluxLtTwoSeriesConst d

theorem superposedFluxLtTwoBudgetConst_pos (d : ℕ) :
    0 < superposedFluxLtTwoBudgetConst d := by
  have htri : 0 < superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    positivity
  exact mul_pos (mul_pos (by norm_num) htri) (superposedFluxLtTwoSeriesConst_pos d)

private theorem depthAmp_rpow_half_le
    (hd : 2 ≤ d) (M : ABKModel d) (E q : ℝ) (n : ℕ)
    (hqOne : 1 ≤ q) (hqTwo : q ≤ 2) :
    superposedFluxDepthAmpProfile M E n ^ (q / 2) ≤
      superposedFluxDepthAmpMaxConst d * (((n : ℝ) + 1) ^ (4 : ℕ)) *
        (3 : ℝ) ^ (M.gamma * (n : ℝ) * (q / 2)) *
        Real.exp (-(superposedFluxBfaRate d / 2 *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let D : ℝ := superposedFluxDepthAmpConst d
  let P : ℝ := ((n : ℝ) + 1) ^ (4 : ℕ)
  let G : ℝ := (3 : ℝ) ^ (M.gamma * (n : ℝ))
  let X : ℝ := E⁻¹ ^ 2 * M.gamma⁻¹
  let A : ℝ := Real.exp (-(superposedFluxBfaRate d * X))
  let t : ℝ := q / 2
  have htHalf : 1 / 2 ≤ t := by dsimp [t]; linarith
  have htOne : t ≤ 1 := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := by linarith
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact (superposedFluxDepthAmpConst_pos hd).le
  have hP1 : 1 ≤ P := by
    dsimp [P]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact one_le_pow₀ (by linarith)
  have hP0 : 0 ≤ P := le_trans zero_le_one hP1
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; exact (Real.exp_pos _).le
  have hDrpow : D ^ t ≤ superposedFluxDepthAmpMaxConst d := by
    by_cases hD : D ≤ 1
    · exact (Real.rpow_le_one hD0 hD ht0).trans (le_max_left _ _)
    · have hDone : 1 ≤ D := le_of_not_ge hD
      exact (Real.rpow_le_self_of_one_le hDone htOne).trans (le_max_right _ _)
  have hPrpow : P ^ t ≤ P := Real.rpow_le_self_of_one_le hP1 htOne
  have hGrpow : G ^ t = (3 : ℝ) ^ (M.gamma * (n : ℝ) * t) := by
    dsimp [G]
    exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
      (M.gamma * (n : ℝ)) t).symm
  have hArpow : A ^ t ≤ Real.exp (-(superposedFluxBfaRate d / 2 * X)) := by
    have hX : 0 ≤ X := by
      dsimp [X]
      exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
    have hrateX : 0 ≤ superposedFluxBfaRate d * X :=
      mul_nonneg (superposedFluxBfaRate_pos d).le hX
    have heq : A ^ t = Real.exp (-(superposedFluxBfaRate d * X) * t) := by
      dsimp [A]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hfactor :
      superposedFluxDepthAmpProfile M E n ^ (q / 2) =
        D ^ t * P ^ t * G ^ t * A ^ t := by
    change (D * P * G * A) ^ t = _
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hD0 hP0) hG0) hA0,
      Real.mul_rpow (mul_nonneg hD0 hP0) hG0,
      Real.mul_rpow hD0 hP0]
  have hDP : D ^ t * P ^ t ≤ superposedFluxDepthAmpMaxConst d * P :=
    mul_le_mul hDrpow hPrpow (Real.rpow_nonneg hP0 t)
      (superposedFluxDepthAmpMaxConst_pos d).le
  have hDPG : D ^ t * P ^ t * G ^ t ≤
      superposedFluxDepthAmpMaxConst d * P * G ^ t :=
    mul_le_mul hDP le_rfl (Real.rpow_nonneg hG0 t)
      (mul_nonneg (superposedFluxDepthAmpMaxConst_pos d).le hP0)
  have hAll : D ^ t * P ^ t * G ^ t * A ^ t ≤
      superposedFluxDepthAmpMaxConst d * P * G ^ t *
        Real.exp (-(superposedFluxBfaRate d / 2 * X)) :=
    mul_le_mul hDPG hArpow (Real.rpow_nonneg hA0 t)
      (mul_nonneg
        (mul_nonneg (superposedFluxDepthAmpMaxConst_pos d).le hP0)
        (Real.rpow_nonneg hG0 t))
  rw [hfactor, hGrpow]
  rw [hGrpow] at hAll
  simpa [t, X] using hAll

private theorem geometricWeight_mul_collar_rpow_eq
    {s q gamma : ℝ} (n : ℕ) :
    Book.Ch02.geometricWeight s q n *
        (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2)) =
      Book.Ch02.geometricDiscount s q *
        endpointWeight ((q / 2) * (2 * s - gamma)) n := by
  unfold Book.Ch02.geometricWeight
  rw [endpointWeight_eq_rpow]
  calc
    _ = Book.Ch02.geometricDiscount s q *
        ((3 : ℝ) ^ (-s * q * (n : ℝ)) *
          (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2))) := by ac_rfl
    _ = Book.Ch02.geometricDiscount s q *
        (3 : ℝ) ^ (-s * q * (n : ℝ) + gamma * (n : ℝ) * (q / 2)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = _ := by
      congr 2
      ring

private theorem weighted_depthAmp_rpow_le
    (hd : 2 ≤ d) (M : ABKModel d) (E s q : ℝ) (n : ℕ)
    (hs : 0 < s) (hqOne : 1 ≤ q) (hqTwo : q ≤ 2) :
    Book.Ch02.geometricWeight s q n *
        superposedFluxDepthAmpProfile M E n ^ (q / 2) ≤
      (superposedFluxDepthAmpMaxConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 *
          (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        ((((n : ℝ) + 1) ^ (4 : ℕ)) *
          endpointWeight ((q / 2) * (2 * s - M.gamma)) n) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hqOne
  have hw0 : 0 ≤ Book.Ch02.geometricWeight s q n :=
    HCPolySupport.geometricWeight_nonneg n (mul_pos hs hq0).le
  have hamp := depthAmp_rpow_half_le hd M E q n hqOne hqTwo
  have hdisc0 : 0 ≤ Book.Ch02.geometricDiscount s q :=
    Book.Ch02.book_geometricDiscount_nonneg (mul_pos hs hq0).le
  have hdisc1 : Book.Ch02.geometricDiscount s q ≤ 1 := by
    unfold Book.Ch02.geometricDiscount
    exact sub_le_self 1 (Real.rpow_nonneg (by norm_num) _)
  have htail0 : 0 ≤ superposedFluxDepthAmpMaxConst d *
      Real.exp (-(superposedFluxBfaRate d / 2 *
        (E⁻¹ ^ 2 * M.gamma⁻¹))) *
      ((((n : ℝ) + 1) ^ (4 : ℕ)) *
        endpointWeight ((q / 2) * (2 * s - M.gamma)) n) := by
    exact mul_nonneg
      (mul_nonneg (superposedFluxDepthAmpMaxConst_pos d).le (Real.exp_pos _).le)
      (mul_nonneg (by positivity) (endpointWeight_nonneg _ _))
  calc
    _ ≤ Book.Ch02.geometricWeight s q n *
        (superposedFluxDepthAmpMaxConst d * (((n : ℝ) + 1) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (M.gamma * (n : ℝ) * (q / 2)) *
          Real.exp (-(superposedFluxBfaRate d / 2 *
            (E⁻¹ ^ 2 * M.gamma⁻¹)))) :=
      mul_le_mul_of_nonneg_left hamp hw0
    _ = Book.Ch02.geometricDiscount s q *
        (superposedFluxDepthAmpMaxConst d *
          Real.exp (-(superposedFluxBfaRate d / 2 *
            (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          ((((n : ℝ) + 1) ^ (4 : ℕ)) *
            endpointWeight ((q / 2) * (2 * s - M.gamma)) n)) := by
      calc
        _ = (superposedFluxDepthAmpMaxConst d *
              Real.exp (-(superposedFluxBfaRate d / 2 *
                (E⁻¹ ^ 2 * M.gamma⁻¹))) * (((n : ℝ) + 1) ^ (4 : ℕ))) *
              (Book.Ch02.geometricWeight s q n *
                (3 : ℝ) ^ (M.gamma * (n : ℝ) * (q / 2))) := by ring
        _ = (superposedFluxDepthAmpMaxConst d *
              Real.exp (-(superposedFluxBfaRate d / 2 *
                (E⁻¹ ^ 2 * M.gamma⁻¹))) * (((n : ℝ) + 1) ^ (4 : ℕ))) *
              (Book.Ch02.geometricDiscount s q *
                endpointWeight ((q / 2) * (2 * s - M.gamma)) n) := by
            rw [geometricWeight_mul_collar_rpow_eq n]
        _ = _ := by ring
    _ ≤ 1 * (superposedFluxDepthAmpMaxConst d *
          Real.exp (-(superposedFluxBfaRate d / 2 *
            (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          ((((n : ℝ) + 1) ^ (4 : ℕ)) *
            endpointWeight ((q / 2) * (2 * s - M.gamma)) n)) :=
      mul_le_mul_of_nonneg_right hdisc1 htail0
    _ = _ := by ring

theorem summable_geometricWeight_mul_depthAmp_rpow_lt_two
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) {s q : ℝ}
    (hs : 0 < s) (hqOne : 1 ≤ q) (hqTwo : q < 2)
    (hgap : 0 < 2 * s - M.gamma) :
    Summable fun n : ℕ => Book.Ch02.geometricWeight s q n *
      superposedFluxDepthAmpProfile M E n ^ (q / 2) := by
  let rho : ℝ := (q / 2) * (2 * s - M.gamma)
  have hrho : 0 < rho := mul_pos (by linarith) hgap
  have hcore := summable_poly_mul_endpointWeight rho hrho
  have hright := hcore.mul_left
    (superposedFluxDepthAmpMaxConst d *
      Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))))
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (HCPolySupport.geometricWeight_nonneg n (mul_pos hs (by linarith)).le)
      (Real.rpow_nonneg (superposedFluxDepthAmpProfile_pos
        hd M E n).le _))
    (fun n => by
      simpa [rho] using weighted_depthAmp_rpow_le hd M E s q n hs hqOne hqTwo.le)
    hright

theorem tsum_geometricWeight_mul_depthAmp_rpow_lt_two_le
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) {s q rare : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hqOne : 1 ≤ q) (hqTwo : q < 2)
    (hrare : 0 < rare) (hrareOne : rare ≤ 1)
    (hwindow : M.gamma / 2 + rare ≤ s) :
    ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        superposedFluxDepthAmpProfile M E n ^ (q / 2) ≤
      superposedFluxLtTwoSeriesConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
        rare⁻¹ ^ (5 : ℕ) := by
  let rho : ℝ := (q / 2) * (2 * s - M.gamma)
  have ht0 : 0 ≤ q / 2 := by linarith
  have htHalf : 1 / 2 ≤ q / 2 := by linarith
  have htOne : q / 2 ≤ 1 := by linarith
  have hgap : 0 < 2 * s - M.gamma := by linarith
  have hgapTwo : 2 * s - M.gamma ≤ 2 := by
    linarith [M.shellPrefix.gamma_pos]
  have hrho : 0 < rho := mul_pos (by linarith) hgap
  have hrhoTwo : rho ≤ 2 := by
    calc
      rho = (q / 2) * (2 * s - M.gamma) := rfl
      _ ≤ 1 * 2 := mul_le_mul htOne hgapTwo hgap.le (by norm_num)
      _ = 2 := by norm_num
  have hrareRho : rare ≤ rho := by
    calc
      rare = (1 / 2 : ℝ) * (2 * rare) := by ring
      _ ≤ (q / 2) * (2 * s - M.gamma) :=
        mul_le_mul htHalf (by linarith [hwindow]) (by positivity) ht0
      _ = rho := rfl
  have hhalfRare : 0 < rare / 2 := div_pos hrare (by norm_num)
  have hhalfRareOne : rare / 2 ≤ 1 := by linarith
  have hcore := tsum_poly_mul_endpointWeight_le_frozenPole hrho hrhoTwo
    hhalfRare hhalfRareOne (by linarith)
  have hcore' :
      ∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n ≤
        (32 * superposedFluxLowerPoleConst) * rare⁻¹ ^ (5 : ℕ) := by
    calc
      _ ≤ superposedFluxLowerPoleConst * (rare / 2)⁻¹ ^ (5 : ℕ) := hcore
      _ = (32 * superposedFluxLowerPoleConst) * rare⁻¹ ^ (5 : ℕ) := by
        field_simp
        ring
  have hterm := weighted_depthAmp_rpow_le hd M E s q
  have hleft := summable_geometricWeight_mul_depthAmp_rpow_lt_two hd M E hs
    hqOne hqTwo hgap
  have hright := (summable_poly_mul_endpointWeight rho hrho).mul_left
    (superposedFluxDepthAmpMaxConst d *
      Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))))
  have htsum :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        superposedFluxDepthAmpProfile M E n ^ (q / 2)) ≤
      ∑' n : ℕ, (superposedFluxDepthAmpMaxConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          ((((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n) :=
    hleft.tsum_le_tsum (fun n => by
      simpa [rho] using hterm n hs hqOne hqTwo.le) hright
  calc
    _ ≤ ∑' n : ℕ, (superposedFluxDepthAmpMaxConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          ((((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n) := htsum
    _ = (superposedFluxDepthAmpMaxConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          (∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n) := by
      rw [tsum_mul_left]
    _ ≤ (superposedFluxDepthAmpMaxConst d *
        Real.exp (-(superposedFluxBfaRate d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          ((32 * superposedFluxLowerPoleConst) * rare⁻¹ ^ (5 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcore'
        (mul_nonneg (superposedFluxDepthAmpMaxConst_pos d).le (Real.exp_pos _).le)
    _ = _ := by
      unfold superposedFluxLtTwoSeriesConst
      ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
