/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyIndicator
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightCompact

/-!
# Uniform weight bound on a fixed spatial cylinder

For a fixed Carleman parameter and spatial radius, the weight remains
bounded as the lower-time transition approaches one half.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Carleman density is continuous where height and time are both
positive. -/
theorem buShortCarlemanWeight_continuousOn_positive
    (a : ℝ) :
    ContinuousOn (buShortCarlemanWeight a)
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
  let U : Set ParabolicPoint := {z | 0 < z.1 2 ∧ 0 < z.2}
  have htoProduct : Continuous
      (parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) :=
    parabolicHomeomorph.continuous
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp htoProduct using 1
    funext z
    rfl
  have htime : ContinuousOn (fun z : ParabolicPoint => z.2) U :=
    (by convert continuous_snd.comp htoProduct using 1
        funext z
        rfl : Continuous (fun z : ParabolicPoint => z.2)).continuousOn
  have hx : ContinuousOn (fun z : ParabolicPoint => z.1 2) U :=
    ((continuous_apply 2).comp hspace).continuousOn
  have hxpos (z : ParabolicPoint) (hz : z ∈ U) : 0 < z.1 2 := hz.1
  have htpos (z : ParabolicPoint) (hz : z ∈ U) : 0 < z.2 := hz.2
  have hxpow : ContinuousOn (fun z : ParabolicPoint => z.1 2 ^ (3 / 2 : ℝ)) U :=
    hx.rpow_const fun z hz => Or.inl (ne_of_gt (hxpos z hz))
  have htpow : ContinuousOn (fun z : ParabolicPoint => z.2 ^ (3 / 4 : ℝ)) U :=
    htime.rpow_const fun z hz => Or.inl (ne_of_gt (htpos z hz))
  have hfirstNum : ContinuousOn
      (fun z : ParabolicPoint => -(z.1 0 ^ 2 + z.1 1 ^ 2)) U := by
    have h0 : ContinuousOn (fun z : ParabolicPoint => z.1 0) U :=
      ((continuous_apply 0).comp hspace).continuousOn
    have h1 : ContinuousOn (fun z : ParabolicPoint => z.1 1) U :=
      ((continuous_apply 1).comp hspace).continuousOn
    exact ((h0.pow 2).add (h1.pow 2)).neg
  have hfirstDen : ContinuousOn (fun z : ParabolicPoint => 8 * z.2) U :=
    continuousOn_const.mul htime
  have hfirstDenNe : ∀ z ∈ U, 8 * z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (mul_pos (by norm_num) (htpos z hz))
  have hfirst := hfirstNum.div hfirstDen hfirstDenNe
  have hsecondNum : ContinuousOn
      (fun z : ParabolicPoint => a * (1 - z.2) * z.1 2 ^ (3 / 2 : ℝ)) U := by
    have hconst : ContinuousOn (fun _ : ParabolicPoint => a) U := continuousOn_const
    have hone : ContinuousOn (fun _ : ParabolicPoint => (1 : ℝ)) U :=
      continuousOn_const
    convert hconst.mul ((hone.sub htime).mul hxpow) using 1
    funext z
    dsimp
    ring
  have hsecondDenNe : ∀ z ∈ U, z.2 ^ (3 / 4 : ℝ) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (htpos z hz) _)
  have hphase : ContinuousOn (halfSpacePhase a (3 / 4)) U := by
    have hphase' : ContinuousOn (fun z : ParabolicPoint =>
      -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
      a * (1 - z.2) * z.1 2 ^ (3 / 2 : ℝ) / z.2 ^ (3 / 4 : ℝ)) U :=
      hfirst.add (hsecondNum.div htpow hsecondDenNe)
    convert hphase' using 1
    funext z
    dsimp [halfSpacePhase]
    norm_num
  change ContinuousOn (fun z : ParabolicPoint =>
    z.2 ^ 2 * Real.exp (2 * halfSpacePhase a (3 / 4) z)) U
  exact (htime.pow 2).mul ((Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul hphase)))

/-- The weight has a bound on the fixed cylinder that is independent of
the lower-time transition width. -/
theorem buShortCarlemanWeight_fixedCylinder_bound
    (R a : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ buShortFixedCylinder R, buShortCarlemanWeight a z ≤ C := by
  let K := buShortFixedCylinder R
  have hK : IsCompact K := buShortFixedCylinder_isCompact hR
  have hKU : K ⊆ {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
    intro z hz
    rcases hz with ⟨⟨_, hy⟩, ht⟩
    exact ⟨lt_of_lt_of_le (by norm_num) hy,
      lt_of_lt_of_le (by norm_num) ht.1⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((buShortCarlemanWeight_continuousOn_positive a).mono hKU)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z hz
  exact (le_abs_self _ |>.trans (hC z hz)).trans (le_max_right _ _)

end ESS
