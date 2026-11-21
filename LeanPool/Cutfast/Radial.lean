/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Tactic.Lemma

/-!
# Radial integrals of Barenblatt type

Exact values, via spherical coordinates and Euler Beta integrals, of
`∫_{ℝᵈ} |x|ᵃ (C + β|x|²)^{-p} dx` and `∫_{ℝᵈ} |x|ᵃ (C - β|x|²)₊ᵖ dx`
(proofs of Lemmas 3.1 and 4.1 of the paper, eqs. (Ba) and (Baporous)).
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace Radial

open Set

/-- Real Euler Beta integral on `(0,1)`. -/
lemma integral_beta {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∫ t in Ioo (0 : ℝ) 1, t ^ (u - 1) * (1 - t) ^ (v - 1) =
      Gamma u * Gamma v / Gamma (u + v) := by
  have h1 := ProbabilityTheory.lintegral_betaPDF_eq_one hu hv
  rw [ProbabilityTheory.lintegral_betaPDF] at h1
  have hB := ProbabilityTheory.beta_pos hu hv
  have h2 : ∫ t in Ioo (0 : ℝ) 1, 1 / ProbabilityTheory.beta u v * (t ^ (u - 1) * (1 - t) ^ (v - 1))
      = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · simp_rw [← mul_assoc]; rw [h1]; simp
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx ↦ ?_)
      have := hx.2
      exact mul_nonneg (by positivity) (mul_nonneg (rpow_nonneg hx.1.le _)
        (rpow_nonneg (by linarith) _))
    · exact Measurable.aestronglyMeasurable (by fun_prop)
  rw [integral_const_mul] at h2
  unfold ProbabilityTheory.beta at h2 hB
  field_simp at h2
  rw [eq_div_iff (Gamma_pos_of_pos (add_pos hu hv)).ne', ← h2, mul_comm]

lemma integrableOn_beta {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t : ℝ ↦ t ^ (u - 1) * (1 - t) ^ (v - 1)) (Ioo 0 1) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_beta hu hv]
  exact (div_pos (mul_pos (Gamma_pos_of_pos hu) (Gamma_pos_of_pos hv))
    (Gamma_pos_of_pos (add_pos hu hv))).ne'


lemma image_div_one_sub : (fun t : ℝ ↦ t / (1 - t)) '' Ioo 0 1 = Ioi 0 := by
  ext u
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact div_pos h0 (by linarith)
  · intro hu
    refine ⟨u / (1 + u), ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩, ?_⟩
    have : (1 + u) ≠ 0 := by linarith
    field_simp
    ring

lemma hasDerivAt_div_one_sub {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t : ℝ ↦ t / (1 - t)) (1 / (1 - t) ^ 2) t := by
  have h : (1 - t) ≠ 0 := by linarith
  have := (hasDerivAt_id' t).div ((hasDerivAt_id' t).const_sub 1) h
  convert this using 1
  field_simp
  ring

lemma injOn_div_one_sub : InjOn (fun t : ℝ ↦ t / (1 - t)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  have h2 : (1 - y) ≠ 0 := by linarith [hy.2]
  simp only at hxy
  field_simp at hxy
  linarith

lemma betaPrime_pointwise {s p t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |1 / (1 - t) ^ 2| • ((t / (1 - t)) ^ (s - 1) * (1 + t / (1 - t)) ^ (-p)) =
      t ^ (s - 1) * (1 - t) ^ ((p - s) - 1) := by
  obtain ⟨h0, h1⟩ := ht
  have hw : 0 < 1 - t := by linarith
  have e1 : 1 + t / (1 - t) = (1 - t)⁻¹ := by field_simp; ring
  have e2 : (p - s) - 1 = (p - (s - 1)) - (2 : ℕ) := by push_cast; ring
  rw [e1, inv_rpow hw.le, rpow_neg hw.le, inv_inv, div_rpow h0.le hw.le, e2,
    rpow_sub hw (p - (s - 1)) ((2 : ℕ):ℝ), rpow_sub hw p (s - 1), rpow_natCast, abs_of_pos
      (by positivity), smul_eq_mul]
  have : 0 < (1 - t) ^ (s - 1) := rpow_pos_of_pos hw _
  field_simp

/-- Beta integral of the second kind. -/
lemma integral_betaPrime {s p : ℝ} (hs : 0 < s) (hsp : s < p) :
    IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (1 + u) ^ (-p)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * (1 + u) ^ (-p) = Gamma s * Gamma (p - s) / Gamma p := by
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ ↦ t / (1 - t)) (1 / (1 - t) ^ 2)
      (Ioo 0 1) t := fun t ht ↦ (hasDerivAt_div_one_sub ht.2).hasDerivWithinAt
  have hps : 0 < p - s := by linarith
  constructor
  · rw [← image_div_one_sub, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      hd injOn_div_one_sub]
    exact (integrableOn_beta hs hps).congr_fun (fun t ht ↦ (betaPrime_pointwise ht).symm)
      measurableSet_Ioo
  · rw [← image_div_one_sub, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      hd injOn_div_one_sub, setIntegral_congr_fun measurableSet_Ioo
      (fun t ht ↦ betaPrime_pointwise ht), integral_beta hs hps, add_sub_cancel]


lemma integrableOn_Ioi_scale_iff (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn g (Ioi 0) ↔ IntegrableOn (fun v ↦ g (k * v)) (Ioi 0) := by
  rw [integrableOn_Ioi_comp_mul_left_iff g 0 hk, mul_zero]

lemma integral_Ioi_scale (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    ∫ u in Ioi (0 : ℝ), g u = k * ∫ v in Ioi (0 : ℝ), g (k * v) := by
  rw [integral_comp_mul_left_Ioi g 0 hk, mul_zero, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hk.ne', one_mul]

lemma scale_pointwise_add {s p C β v : ℝ} (hC : 0 < C) (hβ : 0 < β) (hv : 0 < v) :
    (C / β * v) ^ (s - 1) * (C + β * (C / β * v)) ^ (-p) =
      (C / β) ^ (s - 1) * C ^ (-p) * (v ^ (s - 1) * (1 + v) ^ (-p)) := by
  have e : C + β * (C / β * v) = C * (1 + v) := by field_simp
  rw [e, mul_rpow (by positivity) hv.le, mul_rpow hC.le (by positivity)]
  ring

lemma kpow_eq {s C β : ℝ} (hC : 0 < C) (hβ : 0 < β) :
    C / β * (C / β) ^ (s - 1) = C ^ s * β ^ (-s) := by
  rw [mul_comm, ← rpow_add_one (div_pos hC hβ).ne', sub_add_cancel, div_rpow hC.le hβ.le,
    rpow_neg hβ.le]
  rfl

/-- `∫₀^∞ u^{s-1} (C+βu)^{-p} du = C^{s-p} β^{-s} Γ(s)Γ(p-s)/Γ(p)`. -/
lemma integral_add_rpow_neg {s p C β : ℝ} (hs : 0 < s) (hsp : s < p) (hC : 0 < C)
    (hβ : 0 < β) :
    IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (C + β * u) ^ (-p)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * (C + β * u) ^ (-p) =
      C ^ (s - p) * β ^ (-s) * (Gamma s * Gamma (p - s) / Gamma p) := by
  have hk : 0 < C / β := div_pos hC hβ
  obtain ⟨hI, hJ⟩ := integral_betaPrime hs hsp
  have hpt : EqOn (fun v : ℝ ↦ (C / β * v) ^ (s - 1) * (C + β * (C / β * v)) ^ (-p))
      (fun v ↦ (C / β) ^ (s - 1) * C ^ (-p) * (v ^ (s - 1) * (1 + v) ^ (-p))) (Ioi 0) :=
    fun v hv ↦ scale_pointwise_add hC hβ hv
  constructor
  · rw [integrableOn_Ioi_scale_iff _ hk]
    exact IntegrableOn.congr_fun (hI.const_mul _) hpt.symm measurableSet_Ioi
  · rw [integral_Ioi_scale _ hk, setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_const_mul, hJ, ← mul_assoc, ← mul_assoc, kpow_eq hC hβ, rpow_sub hC,
      rpow_neg hC.le]
    ring

lemma max_one_sub_pointwise {s p C β v : ℝ} (hC : 0 < C) (hβ : 0 < β) (hv : 0 < v) :
    (C / β * v) ^ (s - 1) * (max (C - β * (C / β * v)) 0) ^ p =
      (C / β) ^ (s - 1) * C ^ p * (v ^ (s - 1) * (max (1 - v) 0) ^ p) := by
  have e : max (C - β * (C / β * v)) 0 = C * max (1 - v) 0 := by
    rw [mul_max_of_nonneg _ _ hC.le, mul_zero]; congr 1; field_simp
  rw [e, mul_rpow (by positivity) hv.le, mul_rpow hC.le (le_max_right _ _)]
  ring

lemma integral_max_one_sub {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (max (1 - u) 0) ^ p) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * (max (1 - u) 0) ^ p =
      Gamma s * Gamma (p + 1) / Gamma (p + 1 + s) := by
  have hp1 : 0 < p + 1 := by linarith
  have hpt : EqOn (fun u : ℝ ↦ u ^ (s - 1) * (1 - u) ^ ((p + 1) - 1))
      (fun u : ℝ ↦ u ^ (s - 1) * (max (1 - u) 0) ^ p) (Ioo 0 1) := by
    intro u hu
    simp only [add_sub_cancel_right]
    rw [max_eq_left (by linarith [hu.2])]
  have hzero : ∀ u ∈ Ioi (0 : ℝ) \ Ioo 0 1, u ^ (s - 1) * (max (1 - u) 0) ^ p = 0 := by
    intro u hu
    have : 1 ≤ u := by
      by_contra h
      exact hu.2 ⟨hu.1, lt_of_not_ge h⟩
    rw [max_eq_right (by linarith), zero_rpow hp.ne', mul_zero]
  constructor
  · exact ((integrableOn_beta hs hp1).congr_fun hpt measurableSet_Ioo).of_forall_sdiff_eq_zero
      measurableSet_Ioi hzero
  · rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
      hzero, ← setIntegral_congr_fun measurableSet_Ioo hpt, integral_beta hs hp1]
    ring_nf

/-- `∫₀^∞ u^{s-1} (C-βu)₊^p du = C^{s+p} β^{-s} Γ(s)Γ(p+1)/Γ(p+1+s)`. -/
lemma integral_max_sub_rpow {s p C β : ℝ} (hs : 0 < s) (hp : 0 < p) (hC : 0 < C)
    (hβ : 0 < β) :
    IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (max (C - β * u) 0) ^ p) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * (max (C - β * u) 0) ^ p =
      C ^ (s + p) * β ^ (-s) * (Gamma s * Gamma (p + 1) / Gamma (p + 1 + s)) := by
  have hk : 0 < C / β := div_pos hC hβ
  obtain ⟨hI, hJ⟩ := integral_max_one_sub hs hp
  have hpt : EqOn (fun v : ℝ ↦ (C / β * v) ^ (s - 1) * (max (C - β * (C / β * v)) 0) ^ p)
      (fun v ↦ (C / β) ^ (s - 1) * C ^ p * (v ^ (s - 1) * (max (1 - v) 0) ^ p)) (Ioi 0) :=
    fun v hv ↦ max_one_sub_pointwise hC hβ hv
  constructor
  · rw [integrableOn_Ioi_scale_iff _ hk]
    exact IntegrableOn.congr_fun (hI.const_mul _) hpt.symm measurableSet_Ioi
  · rw [integral_Ioi_scale _ hk, setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_const_mul, hJ, ← mul_assoc, ← mul_assoc, kpow_eq hC hβ, rpow_add hC]
    ring


lemma nontrivial_E {d : ℕ} (hd : 1 ≤ d) : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

lemma polar_pointwise {d : ℕ} (hd : 1 ≤ d) (F : ℝ → ℝ) (a : ℝ) {y : ℝ} (hy : 0 < y) :
    y ^ (d - 1) • (y ^ a * F (y ^ 2)) =
      y ^ ((2 : ℝ) - 1) • ((y ^ (2 : ℝ)) ^ ((d + a) / 2 - 1) * F (y ^ (2 : ℝ))) := by
  rw [← rpow_mul hy.le, rpow_two, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_assoc, ← rpow_natCast, ← rpow_add hy, ← rpow_add hy, Nat.cast_sub hd]
  congr 2
  push_cast
  ring

lemma real_vol_ball {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      2 * (π ^ ((d : ℝ) / 2) / Gamma (d / 2)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hd0 : (d : ℝ) / 2 ≠ 0 := by positivity
  rw [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity), Gamma_add_one hd0, sqrt_eq_rpow,
    ← rpow_natCast, ← rpow_mul pi_pos.le]
  field_simp

/-- Polar coordinates for functions of `‖x‖²` weighted by `‖x‖ᵃ`. -/
lemma radial {d : ℕ} (hd : 1 ≤ d) (F : ℝ → ℝ) (a : ℝ) :
    (Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ a * F (‖x‖ ^ 2)) ↔
      IntegrableOn (fun u ↦ u ^ ((d + a) / 2 - 1) * F u) (Ioi 0)) ∧
    ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ a * F (‖x‖ ^ 2) =
      π ^ ((d : ℝ) / 2) / Gamma (d / 2) * ∫ u in Ioi (0 : ℝ), u ^ ((d + a) / 2 - 1) * F u := by
  have := nontrivial_E hd
  have hpt : EqOn (fun y : ℝ ↦ y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) •
      (y ^ a * F (y ^ 2))) (fun y ↦ y ^ ((2 : ℝ) - 1) •
        ((fun u ↦ u ^ ((d + a) / 2 - 1) * F u) (y ^ (2 : ℝ)))) (Ioi 0) := by
    intro y hy
    simp only [finrank_euclideanSpace_fin]
    exact polar_pointwise hd F a hy
  constructor
  · rw [integrable_fun_norm_addHaar volume (f := fun r ↦ r ^ a * F (r ^ 2)),
      integrableOn_congr_fun hpt measurableSet_Ioi]
    exact integrableOn_Ioi_comp_rpow_iff' (fun u ↦ u ^ ((d + a) / 2 - 1) * F u) two_ne_zero
  · rw [integral_fun_norm_addHaar volume (fun r ↦ r ^ a * F (r ^ 2)),
      setIntegral_congr_fun measurableSet_Ioi hpt,
      ← integral_comp_rpow_Ioi (fun u ↦ u ^ ((d + a) / 2 - 1) * F u) two_ne_zero]
    simp_rw [mul_smul, abs_two, integral_smul, smul_eq_mul, nsmul_eq_mul,
      finrank_euclideanSpace_fin]
    rw [← mul_assoc, real_vol_ball hd]
    ring

end Radial

open Radial

/-- Eq. (Ba): `∫ |x|ᵃ (C + β|x|²)^{-p} dx
= C^{(d+a)/2-p} β^{-(d+a)/2} π^{d/2} Γ((d+a)/2) Γ(p-(d+a)/2) / (Γ(d/2) Γ(p))`,
for `-d < a < 2p - d`. -/
theorem integrable_rpow_norm_mul_add_sq_rpow_neg {d : ℕ} (hd : 1 ≤ d) {a p C β : ℝ}
    (ha : -(d : ℝ) < a) (hap : a + d < 2 * p) (hC : 0 < C) (hβ : 0 < β) :
    Integrable (fun x : E d => ‖x‖ ^ a * (C + β * ‖x‖ ^ 2) ^ (-p)) :=
  (radial hd (fun u ↦ (C + β * u) ^ (-p)) a).1.2
    (integral_add_rpow_neg (by linarith) (by linarith) hC hβ).1

theorem integral_rpow_norm_mul_add_sq_rpow_neg {d : ℕ} (hd : 1 ≤ d) {a p C β : ℝ}
    (ha : -(d : ℝ) < a) (hap : a + d < 2 * p) (hC : 0 < C) (hβ : 0 < β) :
    ∫ x : E d, ‖x‖ ^ a * (C + β * ‖x‖ ^ 2) ^ (-p) =
      C ^ ((d + a) / 2 - p) * β ^ (-((d + a) / 2)) *
        (π ^ ((d : ℝ) / 2) * Gamma ((d + a) / 2) * Gamma (p - (d + a) / 2) /
          (Gamma (d / 2) * Gamma p)) := by
  rw [(radial hd (fun u ↦ (C + β * u) ^ (-p)) a).2,
    (integral_add_rpow_neg (by linarith) (by linarith) hC hβ).2]
  ring

/-- Eq. (Baporous): `∫ |x|ᵃ (C - β|x|²)₊ᵖ dx
= C^{(d+a)/2+p} β^{-(d+a)/2} π^{d/2} Γ((d+a)/2) Γ(p+1) / (Γ(d/2) Γ(p+1+(d+a)/2))`,
for `a > -d` and `p > 0`. -/
theorem integrable_rpow_norm_mul_sub_sq_rpow {d : ℕ} (hd : 1 ≤ d) {a p C β : ℝ}
    (ha : -(d : ℝ) < a) (hp : 0 < p) (hC : 0 < C) (hβ : 0 < β) :
    Integrable (fun x : E d => ‖x‖ ^ a * (max (C - β * ‖x‖ ^ 2) 0) ^ p) :=
  (radial hd (fun u ↦ (max (C - β * u) 0) ^ p) a).1.2
    (integral_max_sub_rpow (by linarith) hp hC hβ).1

theorem integral_rpow_norm_mul_sub_sq_rpow {d : ℕ} (hd : 1 ≤ d) {a p C β : ℝ}
    (ha : -(d : ℝ) < a) (hp : 0 < p) (hC : 0 < C) (hβ : 0 < β) :
    ∫ x : E d, ‖x‖ ^ a * (max (C - β * ‖x‖ ^ 2) 0) ^ p =
      C ^ ((d + a) / 2 + p) * β ^ (-((d + a) / 2)) *
        (π ^ ((d : ℝ) / 2) * Gamma ((d + a) / 2) * Gamma (p + 1) /
          (Gamma (d / 2) * Gamma (p + 1 + (d + a) / 2))) := by
  rw [(radial hd (fun u ↦ (max (C - β * u) 0) ^ p) a).2,
    (integral_max_sub_rpow (by linarith) hp hC hβ).2]
  ring

end Cutfast
