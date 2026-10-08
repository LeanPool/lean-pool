/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalMoment

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalScaling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Homogeneous local boundary-weight moments
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The local negative boundary-distance moment has homogeneous order
`d-p`, uniformly over the center and radius. -/
theorem exists_bound_lintegral_local_euclideanBoundaryWeight_scaled
    (hd : 1 ≤ d) {rho Rad p : ℝ} (hrho : 0 < rho) (hRad : 0 < Rad)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ (z : Vec d) {r : ℝ},
          0 < r → r ≤ Rad → (U ∩ euclideanBallAt z r).Nonempty →
          (∫⁻ x in U ∩ euclideanBallAt z r,
            euclideanBoundaryWeight U p x ∂volume) ≤
              C * ENNReal.ofReal (r ^ ((d : ℝ) - p)) := by
  let A : ℝ := (d : ℝ) * 4 * (rho + Rad) / rho
  let C : ℝ≥0∞ := ENNReal.ofReal
    ((4 : ℝ) ^ d * (A ^ p / (1 - p)))
  refine ⟨C, ENNReal.ofReal_ne_top, ?_⟩
  intro U hU hsand z r hr hrRad hne
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hsum : 0 < rho + Rad := add_pos hrho hRad
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 - p := sub_pos.mpr hp1
  have hraw := lintegral_local_euclideanBoundaryWeight_le
    hd hU hsand hr hrRad hp0 hp1 hne
  rw [volume_ball_eq z (by positivity : 0 < 2 * r)] at hraw
  calc
    (∫⁻ x in U ∩ euclideanBallAt z r,
        euclideanBoundaryWeight U p x ∂volume) ≤
        ENNReal.ofReal ((2 * (2 * r)) ^ d) *
          ENNReal.ofReal ((((d : ℝ) /
            (r * rho / (4 * (rho + Rad)))) ^ p) / (1 - p)) := hraw
    _ = ENNReal.ofReal
        (((2 * (2 * r)) ^ d) *
          ((((d : ℝ) / (r * rho / (4 * (rho + Rad)))) ^ p) /
            (1 - p))) := by
      rw [ENNReal.ofReal_mul]
      positivity
    _ = C * ENNReal.ofReal (r ^ ((d : ℝ) - p)) := by
      rw [← ENNReal.ofReal_mul]
      · congr 1
        have hquot : (d : ℝ) / (r * rho / (4 * (rho + Rad))) = A / r := by
          dsimp only [A]
          field_simp [hr.ne', hrho.ne', hsum.ne']
        have hrpow : r ^ d = r ^ (d : ℝ) :=
          (Real.rpow_natCast r d).symm
        have hApow : (A / r) ^ p = A ^ p * r ^ (-p) := by
          rw [Real.div_rpow hA.le hr.le, Real.rpow_neg hr.le]
          ring
        rw [hquot, hApow, show (2 * (2 * r)) ^ d =
          (4 : ℝ) ^ d * r ^ d by ring, hrpow]
        calc
          (4 : ℝ) ^ d * r ^ (d : ℝ) *
              (A ^ p * r ^ (-p) / (1 - p)) =
              4 ^ d * (A ^ p / (1 - p)) *
                (r ^ (d : ℝ) * r ^ (-p)) := by ring
          _ = 4 ^ d * (A ^ p / (1 - p)) *
                r ^ ((d : ℝ) + (-p)) := by rw [Real.rpow_add hr]
          _ = 4 ^ d * (A ^ p / (1 - p)) *
                r ^ ((d : ℝ) - p) := by ring_nf
      · positivity

end

end HighContrast
end HCPolySupport
