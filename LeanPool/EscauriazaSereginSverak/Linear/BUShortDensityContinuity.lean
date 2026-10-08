/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellWeightsIntegrable
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalDensities

/-!
# Continuity of short-time density factors

The fixed scalar factors are continuous where the normal height and
normalized time are positive.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The tangential Gaussian and normal polynomial are continuous on
positive normalized times (`lem:bu-small-time`). -/
theorem bu_short_tangential_factor_continuousOn_positive :
    ContinuousOn (fun z : ParabolicPoint =>
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        (1 + z.1 2) ^ 4)
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
  let U : Set ParabolicPoint := {z | 0 < z.1 2 ∧ 0 < z.2}
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have h0 : Continuous (fun z : ParabolicPoint => z.1 0) :=
    (continuous_apply 0).comp hspace
  have h1 : Continuous (fun z : ParabolicPoint => z.1 1) :=
    (continuous_apply 1).comp hspace
  have h2 : Continuous (fun z : ParabolicPoint => z.1 2) :=
    (continuous_apply 2).comp hspace
  have hnum : Continuous (fun z : ParabolicPoint =>
      -(z.1 0 ^ 2 + z.1 1 ^ 2)) := ((h0.pow 2).add (h1.pow 2)).neg
  have hden : Continuous (fun z : ParabolicPoint => 4 * z.2) :=
    continuous_const.mul htime
  have hdenNe : ∀ z ∈ U, 4 * z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (mul_pos (by norm_num) hz.2)
  have hbase : ContinuousOn (fun z : ParabolicPoint =>
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2))) U :=
    Real.continuous_exp.comp_continuousOn
      (hnum.continuousOn.div hden.continuousOn hdenNe)
  have hpoly : ContinuousOn (fun z : ParabolicPoint => (1 + z.1 2) ^ 4) U :=
    (continuousOn_const.add h2.continuousOn).pow 4
  exact hbase.mul hpoly

/-- The shifted Carleman factor is continuous on the positive cylinder
(`lem:bu-small-time`). -/
theorem bu_short_shifted_factor_continuousOn_positive
    (scale a : ℝ) :
    ContinuousOn (buShortShiftedWeight scale a)
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
  change ContinuousOn (fun z : ParabolicPoint =>
    Real.exp (-(2 * a * buShortB scale)) * buShortCarlemanWeight a z) _
  exact continuousOn_const.mul (buShortCarlemanWeight_continuousOn_positive a)

/-- The shifted Carleman factor times the normal polynomial is
continuous on the positive cylinder (`lem:bu-small-time`). -/
theorem bu_short_shifted_polynomial_factor_continuousOn_positive
    (scale a : ℝ) :
    ContinuousOn (fun z : ParabolicPoint =>
      buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4)
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have h2 : Continuous (fun z : ParabolicPoint => z.1 2) :=
    (continuous_apply 2).comp hspace
  exact (bu_short_shifted_factor_continuousOn_positive scale a).mul
    ((continuousOn_const.add h2.continuousOn).pow 4)

end ESS
