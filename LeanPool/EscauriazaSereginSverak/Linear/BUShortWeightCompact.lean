/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportGeometry

/-!
# Weight on the compact cutoff support

The half-space Carleman weight is continuous on the compact support of the
short-time cutoff, so it is bounded there for each fixed parameter.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The half-space Carleman density at exponent three quarters. -/
@[expose] def buShortCarlemanWeight (a : ℝ) (z : ParabolicPoint) : ℝ :=
  z.2 ^ 2 * Real.exp (2 * halfSpacePhase a (3 / 4) z)

/-- The Carleman density is continuous on the compact support of the
short-time scalar cutoff. -/
theorem buShortCarlemanWeight_continuousOn_support
    (scale R ε a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    ContinuousOn (buShortCarlemanWeight a)
      (buCutSupportSet (buShortFullCutoff scale R hR ε)) := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  have hK := (bu_short_cutoff_support_geometry
    scale R ε hscale hscale1 hR hε).2.1
  have htoProduct : Continuous
      (parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) :=
    parabolicHomeomorph.continuous
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp htoProduct using 1
    funext z
    rfl
  have htime : ContinuousOn (fun z : ParabolicPoint => z.2) K :=
    (by convert continuous_snd.comp htoProduct using 1
        funext z
        rfl : Continuous (fun z : ParabolicPoint => z.2)).continuousOn
  have hx : ContinuousOn (fun z : ParabolicPoint => z.1 2) K :=
    ((continuous_apply 2).comp hspace).continuousOn
  have hxpos (z : ParabolicPoint) (hz : z ∈ K) : 0 < z.1 2 :=
    lt_trans (by norm_num) (hK hz).1
  have htpos (z : ParabolicPoint) (hz : z ∈ K) : 0 < z.2 := (hK hz).2.1
  have hxpow : ContinuousOn (fun z : ParabolicPoint => z.1 2 ^ (3 / 2 : ℝ)) K :=
    hx.rpow_const fun z hz => Or.inl (ne_of_gt (hxpos z hz))
  have htpow : ContinuousOn (fun z : ParabolicPoint => z.2 ^ (3 / 4 : ℝ)) K :=
    htime.rpow_const fun z hz => Or.inl (ne_of_gt (htpos z hz))
  have hfirstNum : ContinuousOn
      (fun z : ParabolicPoint => -(z.1 0 ^ 2 + z.1 1 ^ 2)) K := by
    have h0 : ContinuousOn (fun z : ParabolicPoint => z.1 0) K :=
      ((continuous_apply 0).comp hspace).continuousOn
    have h1 : ContinuousOn (fun z : ParabolicPoint => z.1 1) K :=
      ((continuous_apply 1).comp hspace).continuousOn
    exact ((h0.pow 2).add (h1.pow 2)).neg
  have hfirstDen : ContinuousOn (fun z : ParabolicPoint => 8 * z.2) K :=
    continuousOn_const.mul htime
  have hfirstDenNe : ∀ z ∈ K, 8 * z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (mul_pos (by norm_num) (htpos z hz))
  have hfirst := hfirstNum.div hfirstDen hfirstDenNe
  have hsecondNum : ContinuousOn
      (fun z : ParabolicPoint => a * (1 - z.2) * z.1 2 ^ (3 / 2 : ℝ)) K := by
    have hconst : ContinuousOn (fun _ : ParabolicPoint => a) K := continuousOn_const
    have hone : ContinuousOn (fun _ : ParabolicPoint => (1 : ℝ)) K :=
      continuousOn_const
    convert hconst.mul ((hone.sub htime).mul hxpow) using 1
    funext z
    dsimp
    ring
  have hsecondDenNe : ∀ z ∈ K, z.2 ^ (3 / 4 : ℝ) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (htpos z hz) _)
  have hphase : ContinuousOn (halfSpacePhase a (3 / 4)) K := by
    have hphase' : ContinuousOn (fun z : ParabolicPoint =>
      -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
      a * (1 - z.2) * z.1 2 ^ (3 / 2 : ℝ) / z.2 ^ (3 / 4 : ℝ)) K :=
      hfirst.add (hsecondNum.div htpow hsecondDenNe)
    convert hphase' using 1
    funext z
    dsimp [halfSpacePhase]
    norm_num
  change ContinuousOn (fun z : ParabolicPoint =>
    z.2 ^ 2 * Real.exp (2 * halfSpacePhase a (3 / 4) z)) K
  exact (htime.pow 2).mul ((Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul hphase)))

end ESS
