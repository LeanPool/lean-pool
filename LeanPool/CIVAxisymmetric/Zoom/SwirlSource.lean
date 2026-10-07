/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RescaledBounds
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Analysis.SegmentQuotient
public import LeanPool.CIVAxisymmetric.Statements.Circulation

/-!
# Swirl Source

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The identity `p.1.1 * zoomS = lam^(2h) * circulation` at the zoomed point
(`eq:aniso:zoom:finite:source:a`). Unfolding the definitions of `zoomS` and `circulation`
and the `meridional` plane component gives `p.1.1 * lam * lam^(2h) * u_θ = lam^(2h) * (lam *
p.1.1 * u_θ)`. -/
theorem mul_zoomS_eq_circulation (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) :
    p.1.1 * zoomS lam h zc u p = lam ^ (2 * h) * circulation u (zoomPoint lam h zc p) := by
  unfold zoomS circulation zoomPoint
  simp [meridional]
  ring

/-- The absolute value of `p.1.1 * zoomS` is bounded by `CΓ * lam^(2h)` whenever the
circulation at the zoomed point is bounded by `CΓ` (`eq:aniso:zoom:finite:source:a`). -/
theorem abs_mul_zoomS_le_of_circulation {lam h zc CΓ : ℝ} (hlam : 0 < lam) {u : ParabolicPoint →
    Vec3}
    {p : (ℝ × ℝ) × ℝ} (hΓ : |circulation u (zoomPoint lam h zc p)| ≤ CΓ) :
    |p.1.1 * zoomS lam h zc u p| ≤ CΓ * lam ^ (2 * h) := by
  rw [mul_zoomS_eq_circulation lam h zc u p, abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
  have hpos : 0 ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  rw [mul_comm (lam ^ (2 * h))]
  apply mul_le_mul_of_nonneg_right hΓ hpos

/-- The zoom point of a convex combination of `p` with `s ∈ [0,1]` stays in the unit cylinder
whenever `p` does: the radial segment to the axis stays in the preimage because the
unit ball is convex, as in the remark preceding `eq:aniso:zoom:finite:bound`. The time
coordinate is unchanged, and the spatial ball condition follows from `(lam * s * p.1.1)^2 ≤ (lam
* p.1.1)^2` since `0 ≤ s ≤ 1`. -/
theorem zoomPoint_segment_mem (lam h zc : ℝ) (hlam : 0 < lam) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    zoomPoint lam h zc ((s * p.1.1, p.1.2), p.2) ∈ unitCylinder := by
  rw [zoomPoint_mem_unitCylinder_iff lam h zc p] at hp
  rcases hp with ⟨hball, htime⟩
  rw [zoomPoint_mem_unitCylinder_iff lam h zc ((s * p.1.1, p.1.2), p.2)]
  have hsq : (lam * (s * p.1.1)) ^ 2 ≤ (lam * p.1.1) ^ 2 := by
    have h_s_sq : s ^ 2 ≤ (1 : ℝ) ^ 2 := by
      have h_s_nonneg : 0 ≤ s := hs.1
      have h_s_le_one : s ≤ 1 := hs.2
      nlinarith only [h_s_nonneg, h_s_le_one]
    calc
      (lam * (s * p.1.1)) ^ 2 = (s * (lam * p.1.1)) ^ 2 := by ring
      _ = s ^ 2 * (lam * p.1.1) ^ 2 := by ring
      _ ≤ (1 : ℝ) ^ 2 * (lam * p.1.1) ^ 2 := by nlinarith only [h_s_sq]
      _ = (lam * p.1.1) ^ 2 := by simp
  have hlam' : 0 ≤ lam := hlam.le
  refine ⟨?_, htime⟩
  change (lam * (s * p.1.1)) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2 < 1
  nlinarith only [hsq, hball]

/-- The radial-segment form of `zoomPoint_segment_mem`: every `s` between `0` and the radius
`p.1.1` — in either order — has its zoom point in the unit cylinder whenever `p` does. The
scaling parameter handed to `zoomPoint_segment_mem` is `s / p.1.1`, which lies in `[0, 1]`
exactly when `s` lies in `uIcc 0 p.1.1`. -/
theorem zoomPoint_slice_mem (lam h zc : ℝ) (hlam : 0 < lam) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) {s : ℝ}
    (hs : s ∈ uIcc (0 : ℝ) p.1.1) :
    zoomPoint lam h zc ((s, p.1.2), p.2) ∈ unitCylinder := by
  have hratio : s / p.1.1 ∈ Icc (0 : ℝ) 1 := by
    rcases le_total (0 : ℝ) p.1.1 with hpos | hneg
    · have hp_pos : 0 < p.1.1 := lt_of_le_of_ne hpos (Ne.symm hR)
      rw [uIcc_of_le hpos] at hs
      exact ⟨div_nonneg hs.1 hpos, (div_le_one hp_pos).mpr hs.2⟩
    · have hp_neg : (0 : ℝ) < -p.1.1 := by
        have hlt := lt_of_le_of_ne hneg hR
        linarith only [hlt]
      rw [uIcc_of_ge hneg] at hs
      have heq : s / p.1.1 = -s / -p.1.1 := by rw [neg_div_neg_eq]
      constructor
      · rw [heq]
        exact div_nonneg (by linarith only [hs.2]) hp_neg.le
      · rw [heq, div_le_one hp_neg]
        linarith only [hs.1]
  have hseg := zoomPoint_segment_mem lam h zc hlam hp hratio
  have heq : ((s / p.1.1) * p.1.1, p.1.2) = (s, p.1.2) := by field_simp [hR]
  simpa [heq] using hseg

/-- The swirl of an axisymmetric field vanishes on the axis of the zoom-in map, as `u_θ`
does (the remark preceding `eq:aniso:zoom:finite:source:b`). At `p.1.1 = 0` the zoom point
lies on the rotation axis,
so `apply_axis_one` forces `u_θ = 0` and hence `zoomS = 0`. -/
theorem zoomS_axis (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (haxi : IsAxisymmetricOn u
    unitCylinder)
    {Z τ : ℝ} (hp : zoomPoint lam h zc ((0, Z), τ) ∈ unitCylinder) :
    zoomS lam h zc u ((0, Z), τ) = 0 := by
  have h0 : (zoomPoint lam h zc ((0, Z), τ)).1 0 = 0 := by
    simp [zoomPoint, meridional]
  have h1 : (zoomPoint lam h zc ((0, Z), τ)).1 1 = 0 := by
    simp [zoomPoint, meridional]
  have hu : u (zoomPoint lam h zc ((0, Z), τ)) 1 = 0 :=
    apply_axis_one haxi hp h0 h1
  unfold zoomS
  rw [hu]
  simp

/-- Bound on `|zoomS / r|` away from the axis (`eq:aniso:zoom:finite:source:b`).
Applies `abs_div_le_of_deriv_bound` to `g(r) = zoomS(..., (r, Z), τ)` on the interval
between `0` and `p.1.1`.  The derivative bound comes from
`abs_dr_zoomW_add_abs_dr_zoomS_le`, dropping the `W` term and using that
`(-p.2)^(-1-h) ≤ 1` when `-p.2 ≥ 1` and `h ≥ 0`. -/
theorem abs_zoomS_div_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ} (hp : zoomPoint lam h zc p ∈
      unitCylinder)
    (hR : p.1.1 ≠ 0) (hτ : p.2 ≤ -1) (hC : 0 ≤ C) (hh : 0 ≤ h) :
    |zoomS lam h zc u p / p.1.1| ≤ C := by
  set g := fun r : ℝ => zoomS lam h zc u ((r, p.1.2), p.2) with hg
  have hg0 : g 0 = 0 := by
    rw [hg]
    have hmem : zoomPoint lam h zc ((0, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR left_mem_uIcc
    have hzero : zoomS lam h zc u ((0, p.1.2), p.2) = 0 :=
      zoomS_axis lam h zc u haxi hmem
    simp [hzero]
  have h_diff : ∀ s ∈ uIcc (0 : ℝ) p.1.1, DifferentiableAt ℝ g s := by
    intro s hs
    rw [hg]
    have hmem : zoomPoint lam h zc ((s, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR hs
    have h_deriv : HasDerivAt (fun r : ℝ => u (zoomPoint lam h zc ((r, p.1.2), p.2)) 1)
        (lam * spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc ((s, p.1.2), p.2)))
        s :=
      hasDerivAt_comp_spatialSlice (hu.of_le (by norm_num)) hmem
        (hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) s) rfl 1
    have h_zoomS : HasDerivAt (fun r : ℝ => zoomS lam h zc u ((r, p.1.2), p.2))
        (lam * lam ^ (2 * h) * (lam * spatialPartial (fun w => u w 1) 0
          (zoomPoint lam h zc ((s, p.1.2), p.2)))) s := by
      simpa [zoomS, mul_assoc] using h_deriv.const_mul (lam * lam ^ (2 * h))
    exact h_zoomS.differentiableAt
  have h_bound : ∀ s ∈ uIcc (0 : ℝ) p.1.1, |deriv g s| ≤ C := by
    intro s hs
    have hmem : zoomPoint lam h zc ((s, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR hs
    have hgoal : |dr (zoomS lam h zc u) ((s, p.1.2), p.2)| ≤ C := by
      have h_total := abs_dr_zoomW_add_abs_dr_zoomS_le C h lam zc hlam u hb hu
        ((s, p.1.2), p.2) hmem
      have h_nonneg_W : 0 ≤ |dr (zoomW lam h zc u) ((s, p.1.2), p.2)| := abs_nonneg _
      have hS : |dr (zoomS lam h zc u) ((s, p.1.2), p.2)| ≤
          C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 0) := by
        linarith only [h_nonneg_W, h_total]
      have h_exp : -(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 0 = -1 - h := by ring
      rw [h_exp] at hS
      have h_neg_tau_ge_one : 1 ≤ -p.2 := by linarith only [hτ]
      have h_exp_nonpos : -1 - h ≤ 0 := by linarith only [hh]
      have h_pow_le_one : (-p.2) ^ (-1 - h) ≤ 1 := by
        calc
          (-p.2) ^ (-1 - h) ≤ (-p.2) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h_neg_tau_ge_one h_exp_nonpos
          _ = 1 := by simp
      have h_final : C * (-p.2) ^ (-1 - h) ≤ C := by
        have : C * (-p.2) ^ (-1 - h) ≤ C * 1 := mul_le_mul_of_nonneg_left h_pow_le_one hC
        simpa using this
      exact le_trans hS h_final
    simpa [hg, dr] using hgoal
  exact abs_div_le_of_deriv_bound hg0 h_diff h_bound hR

end CIV
