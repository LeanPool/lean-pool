/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryLayer

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyLocalLayer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local boundary layers of convex domains

A ball sandwich of a convex domain remains quantitatively useful after
localization.  The localization used here intersects the domain with an ambient
metric ball.  A point in the corresponding Euclidean ball is shifted a short
distance toward the center of the sandwich; convexity then supplies an interior
Euclidean ball at the shifted point.

The resulting local sandwich turns the global convex boundary-layer estimate
into an explicit estimate on every Euclidean localization.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem div_four_mul_le_quarter {r S q : ℝ}
    (hr : 0 ≤ r) (hS : 0 < S) (hq : q ≤ S) :
    r / (4 * S) * q ≤ r / 4 := by
  have hden : 0 < 4 * S := mul_pos (by norm_num) hS
  rw [show r / (4 * S) * q = (r * q) / (4 * S) by ring]
  apply (div_le_iff₀ hden).2
  calc
    r * q ≤ r * S := mul_le_mul_of_nonneg_left hq hr
    _ = r / 4 * (4 * S) := by ring

/-- Dilating a point of a convex set toward the center of an interior ball
produces another interior ball, with the complementary dilation factor as its
radius factor. -/
theorem euclideanBallAt_dilate_subset_of_convex
    {U : Set (Vec d)} (hconv : Convex ℝ U) {c : Vec d} {rho lam : ℝ}
    (hrho : 0 < rho) (hball : euclideanBallAt c rho ⊆ U)
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) {x : Vec d} (hx : x ∈ U) :
    euclideanBallAt (c + lam • (x - c)) ((1 - lam) * rho) ⊆ U := by
  have hgap : 0 < 1 - lam := sub_pos.mpr hlam.2
  intro z hz
  let b : Vec d := c + (1 - lam)⁻¹ • (z - (c + lam • (x - c)))
  have hbc : b - c = (1 - lam)⁻¹ • (z - (c + lam • (x - c))) := by
    dsimp [b]
    abel
  have hscale : (0 : ℝ) < (1 - lam)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hgap)
  have hcancel : (1 - lam)⁻¹ ^ 2 * (((1 - lam) * rho) ^ 2) = rho ^ 2 := by
    field_simp [hgap.ne']
  have hbball : b ∈ euclideanBallAt c rho := by
    rw [mem_euclideanBallAt_iff, hbc, vecNormSq_smul]
    calc
      (1 - lam)⁻¹ ^ 2 * vecNormSq (z - (c + lam • (x - c))) <
          (1 - lam)⁻¹ ^ 2 * (((1 - lam) * rho) ^ 2) :=
        mul_lt_mul_of_pos_left hz hscale
      _ = rho ^ 2 := hcancel
  have hb : b ∈ U := hball hbball
  have hzU : (1 - lam) • b + lam • x ∈ U :=
    hconv hb hx (sub_nonneg.mpr hlam.2.le) hlam.1 (by ring)
  have heq : (1 - lam) • b + lam • x = z := by
    dsimp [b]
    have hgapne : 1 - lam ≠ 0 := hgap.ne'
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hgapne]
    ring
  rwa [heq] at hzU

/-- Intersecting a bounded open convex domain with an ambient ball preserves
the domain class. -/
theorem IsOpenBoundedConvexDomain.inter_metricBall
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (z : Vec d)
    (r : ℝ) :
    IsOpenBoundedConvexDomain (U ∩ Metric.ball z r) := by
  refine ⟨hU.isOpen.inter Metric.isOpen_ball, ?_,
    hU.convex.inter (convex_ball z r)⟩
  exact Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset Set.inter_subset_right)

/-- A nonempty Euclidean localization of a convex ball-sandwiched domain gives
an explicit ball sandwich for the domain intersected with the doubled ambient
ball. -/
theorem hasBallSandwich_inter_metricBall (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad r : ℝ} (hsand : HasBallSandwich U rho Rad)
    (hr : 0 < r) (hrRad : r ≤ Rad) {z : Vec d}
    (hne : (U ∩ euclideanBallAt z r).Nonempty) :
    HasBallSandwich (U ∩ Metric.ball z (2 * r))
      (r * rho / (4 * (rho + Rad))) ((4 * r) * Real.sqrt d) := by
  obtain ⟨hrho, hRad, c, hball, hout⟩ := hsand
  obtain ⟨x₀, hx₀U, hx₀z⟩ := hne
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hRadpos : 0 < Rad := lt_of_lt_of_le hr hrRad
  have hsum : 0 < rho + Rad := add_pos_of_pos_of_nonneg hrho hRad
  let alpha : ℝ := r / (4 * (rho + Rad))
  have halpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halpha_lt_one : alpha < 1 := by
    apply (div_lt_one (show 0 < 4 * (rho + Rad) by positivity)).2
    linarith only [hrho, hRad, hrRad]
  have hlam : 1 - alpha ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨by linarith only [halpha_lt_one], by linarith only [halpha]⟩
  let b : Vec d := x₀ + alpha • (c - x₀)
  have hcenter : c + (1 - alpha) • (x₀ - c) = b := by
    dsimp [b]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hradius :
      (1 - (1 - alpha)) * rho = r * rho / (4 * (rho + Rad)) := by
    dsimp [alpha]
    ring
  have hballU :
      euclideanBallAt b (r * rho / (4 * (rho + Rad))) ⊆ U := by
    have h := euclideanBallAt_dilate_subset_of_convex hU.convex hrho hball
      hlam hx₀U
    simpa only [hcenter, hradius] using h
  have hrho_le : rho ≤ rho + Rad := by
    linarith only [hRad]
  have hRad_le : Rad ≤ rho + Rad := by
    linarith only [hrho]
  have halpha_rho : alpha * rho ≤ r / 4 := by
    simpa only [alpha] using
      (div_four_mul_le_quarter hr.le hsum hrho_le)
  have halpha_Rad : alpha * Rad ≤ r / 4 := by
    simpa only [alpha] using
      (div_four_mul_le_quarter hr.le hsum hRad_le)
  have hlocal_eq :
      r * rho / (4 * (rho + Rad)) = alpha * rho := by
    dsimp [alpha]
    ring
  have hlocal_pos : 0 < r * rho / (4 * (rho + Rad)) := by
    positivity
  have hlocal_le : r * rho / (4 * (rho + Rad)) ≤ r / 4 := by
    rw [hlocal_eq]
    exact halpha_rho
  have hx₀zMetric : x₀ ∈ Metric.ball z r :=
    euclideanBallAt_subset_metricBall z hr hx₀z
  have hx₀zDist : dist x₀ z < r := Metric.mem_ball.mp hx₀zMetric
  have hx₀cMetric : x₀ ∈ Metric.ball c Rad :=
    euclideanBallAt_subset_metricBall c hRadpos (hout hx₀U)
  have hcx₀Dist : dist c x₀ < Rad := by
    rw [dist_comm]
    exact Metric.mem_ball.mp hx₀cMetric
  have hbx₀Dist : dist b x₀ = alpha * dist c x₀ := by
    have hsub : b - x₀ = alpha • (c - x₀) := by
      dsimp [b]
      abel
    calc
      dist b x₀ = ‖b - x₀‖ := dist_eq_norm _ _
      _ = ‖alpha • (c - x₀)‖ := by rw [hsub]
      _ = |alpha| * ‖c - x₀‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = alpha * ‖c - x₀‖ := by rw [abs_of_pos halpha]
      _ = alpha * dist c x₀ := by rw [dist_eq_norm]
  have hbx₀Quarter : dist b x₀ < r / 4 := by
    calc
      dist b x₀ = alpha * dist c x₀ := hbx₀Dist
      _ < alpha * Rad := mul_lt_mul_of_pos_left hcx₀Dist halpha
      _ ≤ r / 4 := halpha_Rad
  have hballMetric :
      euclideanBallAt b (r * rho / (4 * (rho + Rad))) ⊆
        Metric.ball z (2 * r) := by
    intro y hy
    have hybMetric : y ∈ Metric.ball b (r * rho / (4 * (rho + Rad))) :=
      euclideanBallAt_subset_metricBall b hlocal_pos hy
    have hybQuarter : dist y b < r / 4 :=
      lt_of_lt_of_le (Metric.mem_ball.mp hybMetric) hlocal_le
    have htri :
        dist y z ≤ dist y b + (dist b x₀ + dist x₀ z) := by
      calc
        dist y z ≤ dist y b + dist b z := dist_triangle y b z
        _ ≤ dist y b + (dist b x₀ + dist x₀ z) :=
          add_le_add le_rfl (dist_triangle b x₀ z)
    apply Metric.mem_ball.mpr
    calc
      dist y z ≤ dist y b + (dist b x₀ + dist x₀ z) := htri
      _ < r / 4 + (r / 4 + r) :=
        add_lt_add hybQuarter (add_lt_add hbx₀Quarter hx₀zDist)
      _ < 2 * r := by linarith only [hr]
  have hbzDist : dist b z < r / 4 + r := by
    calc
      dist b z ≤ dist b x₀ + dist x₀ z := dist_triangle b x₀ z
      _ < r / 4 + r := add_lt_add hbx₀Quarter hx₀zDist
  have houterMetric :
      U ∩ Metric.ball z (2 * r) ⊆ Metric.ball b (4 * r) := by
    rintro y ⟨_yU, hyz⟩
    have hyzDist : dist y z < 2 * r := Metric.mem_ball.mp hyz
    have hzbDist : dist z b < r / 4 + r := by
      rwa [dist_comm]
    apply Metric.mem_ball.mpr
    calc
      dist y b ≤ dist y z + dist z b := dist_triangle y z b
      _ < 2 * r + (r / 4 + r) := add_lt_add hyzDist hzbDist
      _ < 4 * r := by linarith only [hr]
  have houterEuclidean :
      U ∩ Metric.ball z (2 * r) ⊆
        euclideanBallAt b ((4 * r) * Real.sqrt d) := by
    intro y hy
    have hsq := vecNormSq_sub_lt_of_mem_metricBall hdpos (houterMetric hy)
    change vecNormSq (y - b) < ((4 * r) * Real.sqrt d) ^ 2
    calc
      vecNormSq (y - b) < (d : ℝ) * (4 * r) ^ 2 := hsq
      _ = ((4 * r) * Real.sqrt d) ^ 2 := by
        calc
          (d : ℝ) * (4 * r) ^ 2 = (4 * r) ^ 2 * (d : ℝ) := by ring
          _ = (4 * r) ^ 2 * (Real.sqrt d) ^ 2 := by
            rw [Real.sq_sqrt (Nat.cast_nonneg d)]
          _ = ((4 * r) * Real.sqrt d) ^ 2 := (mul_pow _ _ 2).symm
  refine ⟨hlocal_pos, by positivity, b, ?_, houterEuclidean⟩
  intro y hy
  exact ⟨hballU hy, hballMetric hy⟩

end

end HighContrast
end HCPolySupport
