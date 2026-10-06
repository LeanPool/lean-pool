/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteLiftBounds
public import LeanPool.CIVAxisymmetric.Zoom.FiniteDriftSliceLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.WLipschitz

/-!
# The lifted finite-axis drift is Lipschitz across the axis

For the lifted drift `B_n = (V_n X/R, W_n)` of `eq:drift:Bn:def` and its divergence
`2 V_n / R` (continued to the axis by `2 ∂_R V_n`), at a fixed time `τ ≤ -1` and on a ball of
the lifted space mapped into the unit cylinder, both are bounded and Lipschitz with constants
depending only on the constant of `eq:aniso:bounds`: the footnote to `eq:drift:Bn:def`,
`|B_n| + |∇B_n| ≤ C |τ|^{-1/2}`, read as a Lipschitz bound across the axis. The direction
`X/R` is singular at the axis, but `|V_n| ≤ C R` there, and
`R₂ |X/R₁ - Y/R₂| ≤ |R₁ - R₂| + |X - Y|`.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The lifted radius is `2`-Lipschitz for the sup norm of `Vec 5`. -/
theorem abs_zoomLiftRadius_sub_le (x y : Vec 5) :
    |zoomLiftRadius x - zoomLiftRadius y| ≤ 2 * ‖x - y‖ := by
  set e : Vec 5 → PiLp 2 (fun _ : Fin 4 => ℝ) :=
    fun x => WithLp.toLp 2 (fun i : Fin 4 => x (Fin.castSucc i)) with he
  have hn : ∀ x : Vec 5, ‖e x‖ = zoomLiftRadius x := by
    intro x
    rw [PiLp.norm_eq_of_L2, zoomLiftRadius]
    simp [he, Fin.sum_univ_four, sq_abs]
  have hsub : e x - e y = e (x - y) := by
    ext i; simp [he]
  have hle : ‖e (x - y)‖ ≤ 2 * ‖x - y‖ := by
    rw [PiLp.norm_eq_of_L2]
    have hi : ∀ i : Fin 4, ‖(e (x - y)) i‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      intro i
      have := norm_le_pi_norm (x - y) (Fin.castSucc i)
      simp only [he]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using this) 2
    rw [Real.sqrt_le_left (by positivity)]
    calc ∑ i, ‖(e (x - y)) i‖ ^ 2 ≤ ∑ _i : Fin 4, ‖x - y‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (2 * ‖x - y‖) ^ 2 := by simp; ring
  rw [← hn, ← hn]
  exact (abs_norm_sub_norm_le _ _).trans (by rw [hsub]; exact hle)

theorem zoomLiftRadius_le_two_mul_norm (x : Vec 5) : zoomLiftRadius x ≤ 2 * ‖x‖ := by
  have h := abs_zoomLiftRadius_sub_le x 0
  have h0 : zoomLiftRadius 0 = 0 := by simp [zoomLiftRadius]
  rw [h0, sub_zero, sub_zero, abs_of_nonneg (zoomLiftRadius_nonneg x)] at h
  exact h

/-- The singular direction `X/R` against a factor vanishing linearly on the axis. -/
theorem abs_mul_div_sub_div_le {C a R1 R2 x1 y1 : ℝ} (hC : 0 ≤ C) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2)
    (ha : |a| ≤ C * R2) (hx1 : |x1| ≤ R1) (hy1 : |y1| ≤ R2) :
    |a * (x1 / R1 - y1 / R2)| ≤ C * (|R1 - R2| + |x1 - y1|) := by
  have hrhs : 0 ≤ C * (|R1 - R2| + |x1 - y1|) := by positivity
  rcases eq_or_lt_of_le hR2 with h2 | h2
  · subst h2
    have : a = 0 := abs_nonpos_iff.mp (by simpa using ha)
    rw [this, zero_mul, abs_zero]; exact hrhs
  rcases eq_or_lt_of_le hR1 with h1 | h1
  · subst h1
    have hx : x1 = 0 := abs_nonpos_iff.mp hx1
    subst hx
    rw [zero_div, zero_sub, mul_neg, abs_neg, abs_mul, abs_div, abs_of_pos h2]
    have hq : |y1| / R2 ≤ 1 := (div_le_one h2).mpr hy1
    calc |a| * (|y1| / R2) ≤ C * R2 * 1 :=
          mul_le_mul ha hq (by positivity) (by positivity)
      _ ≤ C * (|0 - R2| + |0 - y1|) := by
          rw [zero_sub, abs_neg, abs_of_pos h2]; nlinarith only [hC, abs_nonneg (0 - y1)]
  · have hkey : a * (x1 / R1 - y1 / R2) = (a / R2) * ((R2 - R1) * (x1 / R1) + (x1 - y1)) := by
      field_simp; ring
    have haR : |a / R2| ≤ C := by
      rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]; exact ha
    have hxR : |x1 / R1| ≤ 1 := by rw [abs_div, abs_of_pos h1]; exact (div_le_one h1).mpr hx1
    rw [hkey, abs_mul]
    have hin : |(R2 - R1) * (x1 / R1) + (x1 - y1)| ≤ |R1 - R2| + |x1 - y1| := by
      calc |(R2 - R1) * (x1 / R1) + (x1 - y1)| ≤ |(R2 - R1) * (x1 / R1)| + |x1 - y1| :=
            abs_add_le _ _
        _ ≤ |R1 - R2| + |x1 - y1| := by
            rw [abs_mul, abs_sub_comm R2 R1]
            nlinarith only [hxR, abs_nonneg (R1 - R2)]
    exact mul_le_mul haR hin (abs_nonneg _) hC

/-- A point of the ball of radius `r` of the lifted space lifts into `[0, 2r] × [-r, r]`. -/
theorem zoomLiftPoint_fst_mem {r τ : ℝ} {x : Vec 5} (hx : x ∈ closedBall (0 : Vec 5) r) :
    (zoomLiftPoint (x, τ)).1 ∈ Icc 0 (2 * r) ×ˢ Icc (-r) r := by
  rw [mem_closedBall, dist_zero_right] at hx
  have h4 : |x 4| ≤ r := (norm_le_pi_norm x 4).trans hx
  exact ⟨⟨zoomLiftRadius_nonneg x, (zoomLiftRadius_le_two_mul_norm x).trans (by linarith only
    [hx])⟩,
    abs_le.mp h4⟩

/-- `|V_n| ≤ C R` on a rectangle through the axis mapped into the cylinder, at `τ ≤ -1`. -/
theorem abs_zoomV_le_mul {C h lam zc tau : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hC : 0 ≤ C) (htau : tau ≤ -1) {y : ℝ × ℝ}
    (hy0 : 0 ≤ y.1) (hp : zoomPoint lam h zc (y, tau) ∈ unitCylinder) :
    |zoomV lam h zc u (y, tau)| ≤ C * y.1 := by
  rcases eq_or_lt_of_le hy0 with h0 | hpos
  · have hy : y = (0, y.2) := Prod.ext h0.symm rfl
    rw [hy] at hp ⊢
    rw [zoomV_axis lam h zc u haxi hp]; simp
  · have hq := abs_zoomV_div_le hlam hb hu haxi hp hpos.ne' hC htau
    have hr : (-(y, tau).2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by change (1 : ℝ) ≤ -tau; linarith only [htau])
        (by norm_num)
    have hq' : |zoomV lam h zc u (y, tau) / y.1| ≤ C := hq.trans (mul_le_of_le_one_right hC hr)
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hq'
    exact hq'

/-- The lifted drift is Lipschitz with constant `7C` on a ball of the lifted space mapped into the
cylinder at a time `τ ≤ -1`. -/
theorem norm_zoomDrift_sub_le {C h lam zc r tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 (2 * r) ×ˢ Icc (-r) r, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {x y : Vec 5} (hx : x ∈ closedBall (0 : Vec 5) r) (hy : y ∈ closedBall (0 : Vec 5) r) :
    ‖zoomDrift lam h zc u (x, tau) - zoomDrift lam h zc u (y, tau)‖ ≤ 7 * C * ‖x - y‖ := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hxm := zoomLiftPoint_fst_mem (τ := tau) hx
  have hym := zoomLiftPoint_fst_mem (τ := tau) hy
  have hdist : dist (zoomLiftPoint (x, tau)).1 (zoomLiftPoint (y, tau)).1 ≤ 2 * ‖x - y‖ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_le (abs_zoomLiftRadius_sub_le x y) ?_
    have := norm_le_pi_norm (x - y) 4
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    change |x 4 - y 4| ≤ 2 * ‖x - y‖
    linarith only [this, norm_nonneg (x - y)]
  have hVlip := (lipschitzOnWith_zoomV hlam hb hu2 hC hh1 htau hmem).dist_le_mul _ hxm _ hym
  have hWlip := (lipschitzOnWith_zoomW hlam hb hu2 hC hh0 htau hmem).dist_le_mul _ hxm _ hym
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq] at hVlip hWlip
  have hn := norm_nonneg (x - y)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  by_cases hi : i = 4
  · subst hi
    simp only [zoomDrift, ↓reduceIte]
    calc |zoomW lam h zc u (zoomLiftPoint (x, tau)) - zoomW lam h zc u (zoomLiftPoint (y, tau))|
        ≤ 2 * C * dist (zoomLiftPoint (x, tau)).1 (zoomLiftPoint (y, tau)).1 := hWlip
      _ ≤ 2 * C * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ ≤ 7 * C * ‖x - y‖ := by nlinarith only [hC, hn]
  · simp only [zoomDrift, hi, ↓reduceIte]
    set v1 := zoomV lam h zc u (zoomLiftPoint (x, tau))
    set v2 := zoomV lam h zc u (zoomLiftPoint (y, tau))
    have hkey : v1 * (x i / zoomLiftRadius x) - v2 * (y i / zoomLiftRadius y)
        = (v1 - v2) * (x i / zoomLiftRadius x)
          + v2 * (x i / zoomLiftRadius x - y i / zoomLiftRadius y) := by ring
    have h1 : |(v1 - v2) * (x i / zoomLiftRadius x)| ≤ 2 * C * (2 * ‖x - y‖) := by
      rw [abs_mul]
      calc |v1 - v2| * |x i / zoomLiftRadius x| ≤ (2 * C * (2 * ‖x - y‖)) * 1 :=
            mul_le_mul (hVlip.trans (mul_le_mul_of_nonneg_left hdist (by positivity)))
              (abs_div_zoomLiftRadius_le_one x hi) (abs_nonneg _) (by positivity)
        _ = 2 * C * (2 * ‖x - y‖) := mul_one _
    have hv2 : |v2| ≤ C * zoomLiftRadius y :=
      abs_zoomV_le_mul hlam hb hu2 haxi hC htau (zoomLiftRadius_nonneg y) (hmem _ hym)
    have h2 := abs_mul_div_sub_div_le hC (zoomLiftRadius_nonneg x) (zoomLiftRadius_nonneg y) hv2
      (abs_le_zoomLiftRadius x hi) (abs_le_zoomLiftRadius y hi)
    have hxi : |x i - y i| ≤ ‖x - y‖ := by
      have := norm_le_pi_norm (x - y) i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    have hR := abs_zoomLiftRadius_sub_le x y
    rw [hkey]
    calc |(v1 - v2) * (x i / zoomLiftRadius x)
          + v2 * (x i / zoomLiftRadius x - y i / zoomLiftRadius y)|
        ≤ |(v1 - v2) * (x i / zoomLiftRadius x)|
          + |v2 * (x i / zoomLiftRadius x - y i / zoomLiftRadius y)| := abs_add_le _ _
      _ ≤ 2 * C * (2 * ‖x - y‖) + C * (|zoomLiftRadius x - zoomLiftRadius y| + |x i - y i|) :=
          add_le_add h1 h2
      _ ≤ 7 * C * ‖x - y‖ := by nlinarith only [hC, hn, hR, hxi]

/-- The lifted divergence is `2` times the continued quotient `V_n / R`. -/
theorem finDriftDiv_eq_two_mul_zoomVQuot (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (z : Vec 5 × ℝ) : finDriftDiv lam h zc u z = 2 * zoomVQuot lam h zc u (zoomLiftPoint z) := by
  unfold finDriftDiv zoomVQuot
  have e : (zoomLiftPoint z).1.1 = zoomLiftRadius z.1 := rfl
  rw [e]
  split_ifs <;> ring

/-- The lifted divergence is Lipschitz with constant `12C` on a ball mapped into the cylinder. -/
theorem abs_finDriftDiv_sub_le {C h lam zc r tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2)
    (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 (2 * r) ×ˢ Icc (-r) r, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {x y : Vec 5} (hx : x ∈ closedBall (0 : Vec 5) r) (hy : y ∈ closedBall (0 : Vec 5) r) :
    |finDriftDiv lam h zc u (x, tau) - finDriftDiv lam h zc u (y, tau)| ≤ 12 * C * ‖x - y‖ := by
  have hxm := zoomLiftPoint_fst_mem (τ := tau) hx
  have hym := zoomLiftPoint_fst_mem (τ := tau) hy
  have hq := abs_zoomVQuot_sub_le hlam hb hu haxi hC hh1 htau hmem hxm hym
  have hR := abs_zoomLiftRadius_sub_le x y
  have h4 : |x 4 - y 4| ≤ ‖x - y‖ := by
    have := norm_le_pi_norm (x - y) 4
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
  have hn := norm_nonneg (x - y)
  rw [finDriftDiv_eq_two_mul_zoomVQuot, finDriftDiv_eq_two_mul_zoomVQuot, ← mul_sub, abs_mul,
    abs_two]
  have e1 : (zoomLiftPoint (x, tau)) = ((zoomLiftPoint (x, tau)).1, tau) := rfl
  have e2 : (zoomLiftPoint (y, tau)) = ((zoomLiftPoint (y, tau)).1, tau) := rfl
  rw [e1, e2]
  change |zoomVQuot lam h zc u ((zoomLiftPoint (x, tau)).1, tau)
      - zoomVQuot lam h zc u ((zoomLiftPoint (y, tau)).1, tau)|
      ≤ 2 * C * (|zoomLiftRadius x - zoomLiftRadius y| + |x 4 - y 4|) at hq
  nlinarith only [hq, hR, h4, hC, hn]

/-- The pointwise bounds `‖B_n‖ ≤ C` and `|div B_n| ≤ 2C` on the lifted preimage at `τ ≤ -1`. -/
theorem zoomDrift_finDriftDiv_bound {C h lam zc tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (htau : tau ≤ -1)
    {x : Vec 5} (hp : zoomPoint lam h zc (zoomLiftPoint (x, tau)) ∈ unitCylinder) :
    ‖zoomDrift lam h zc u (x, tau)‖ ≤ C ∧ |finDriftDiv lam h zc u (x, tau)| ≤ 2 * C := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hr : (-tau) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [htau]) (by norm_num)
  have hCr : C * (-tau) ^ (-(1 / 2 : ℝ)) ≤ C := mul_le_of_le_one_right hC hr
  refine ⟨(norm_zoomDrift_le hlam hb hp hC hh0 htau).trans hCr, ?_⟩
  unfold finDriftDiv
  split_ifs with h0
  · have := abs_dr_zoomV_le_rpow_neg_half hlam hb hu2 hp hC htau
    rw [abs_mul, abs_two]
    have e : (-(zoomLiftPoint (x, tau)).2) = -tau := rfl
    rw [e] at this
    linarith only [this, hCr]
  · have := abs_zoomV_div_le hlam hb hu2 haxi hp h0 hC htau
    have e : (-(zoomLiftPoint (x, tau)).2) = -tau := rfl
    rw [e] at this
    have heq : 2 * zoomV lam h zc u (zoomLiftPoint (x, tau)) / zoomLiftRadius x
        = 2 * (zoomV lam h zc u (zoomLiftPoint (x, tau)) / (zoomLiftPoint (x, tau)).1.1) := by
      rw [mul_div_assoc]; rfl
    rw [heq, abs_mul, abs_two]
    linarith only [this, hCr]

end CIV
