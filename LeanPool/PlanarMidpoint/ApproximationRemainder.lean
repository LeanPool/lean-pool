/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.JetAlgebra
public import LeanPool.PlanarMidpoint.SpatialTaylor
public import LeanPool.PlanarMidpoint.GeodesicEstimate
public import LeanPool.PlanarMidpoint.GeodesicDefinitions
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Uniform residual bounds for the actual coefficient field. -/

@[expose] public section
noncomputable section
namespace PlanarMidpoint
open Set

theorem approx_actual_residual_bound (C : E → Coeff) (p : E)
    (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian) (h : E)
    (η B T ε t : ℝ) (hη : 0 ≤ η) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hd : ‖approxDisplacement c J H h ε t‖ ≤ B * ε)
    (hv : ‖approxVelocity c J H h ε t‖ ≤ B * ε)
    (htail : ‖approxResidualTail c J H h ε t‖ ≤ T)
    (hcoeff : let d := approxDisplacement c J H h ε t
      ‖C (p + d) - c - J d - (1 / 2 : ℝ) • H d d‖ ≤ η * ‖d‖ ^ 2) :
    ‖approxAcceleration c J H h ε t + K (C (p + approxDisplacement c J H h ε t))
        (approxVelocity c J H h ε t) (approxVelocity c J H h ε t)‖ ≤
      (8 * η * B ^ 4 + T * ε) * ε ^ 4 := by
  let d := approxDisplacement c J H h ε t
  let v := approxVelocity c J H h ε t
  let a := approxAcceleration c J H h ε t
  let cTaylor := c + J d + (1 / 2 : ℝ) • H d d
  have hcoeff' : ‖C (p + d) - cTaylor‖ ≤ η * ‖d‖ ^ 2 := by
    convert hcoeff using 1; congr 1; dsimp [cTaylor]; module
  have hforce := force_taylor_error_bound (C (p + d)) cTaylor d v η B ε
    hη hB hε hcoeff' hd hv
  have hpoly : a + K cTaylor v v = ε ^ 5 • approxResidualTail c J H h ε t :=
    approx_residual_exact c J H h ε t
  change ‖a + K (C (p + d)) v v‖ ≤ _
  calc
    ‖a + K (C (p + d)) v v‖ = ‖(a + K cTaylor v v) + (K (C (p + d)) v v - K cTaylor v v)‖ := by
        congr 1; module
    _ ≤ ‖a + K cTaylor v v‖ + ‖K (C (p + d)) v v - K cTaylor v v‖ := norm_add_le _ _
    _ ≤ T * ε ^ 5 + 8 * η * B ^ 4 * ε ^ 4 := by
      apply add_le_add _ hforce
      rw [hpoly, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε 5)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left htail (pow_nonneg hε 5)
    _ = _ := by ring

/-- A short actual geodesic has the quartic midpoint polynomial as a uniform
approximation. All hypotheses on the approximate trajectory are explicit
polynomial bounds, while the actual curve is constrained only by the ODE. -/
theorem short_geodesic_approximation
    (C : E → Coeff) (p : E) (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian) (h : E)
    (r M L η B T ε ρ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 < r) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hbound : ∀ x ∈ Metric.ball p r, ‖C x‖ ≤ M)
    (hLip : ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      ‖C x - C y‖ ≤ L * ‖x - y‖)
    (hsmall : 8 * L * r ^ 2 + 16 * M * r < 1 / 2)
    (hcoeff : ∀ d : E, ‖d‖ < ρ →
      ‖C (p + d) - c - J d - (1 / 2 : ℝ) • H d d‖ ≤ η * ‖d‖ ^ 2)
    (hsize : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖approxDisplacement c J H h ε t‖ ≤ B * ε ∧
      ‖approxVelocity c J H h ε t‖ ≤ B * ε ∧
      ‖approxResidualTail c J H h ε t‖ ≤ T)
    (hεr : B * ε < r) (hερ : B * ε < ρ)
    (γ v : ℝ → E)
    (hγ : IsShortGeodesic C 1 p r (p - (ε / 2) • h) (p + (ε / 2) • h) γ v) :
    ‖γ (1 / 2) - (p + approxDisplacement c J H h ε (1 / 2))‖ ≤
      2 * (8 * η * B ^ 4 + T * ε) * ε ^ 4 := by
  let y : ℝ → E := fun t ↦ p + approxDisplacement c J H h ε t
  let w := approxVelocity c J H h ε
  let b := approxAcceleration c J H h ε
  have hy (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt y (w t) t := by
    simpa only [y, w, zero_add] using
      (hasDerivAt_const t p).fun_add (hasDerivAt_approxDisplacement c J H h ε t)
  have hw (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt w (b t) t :=
    hasDerivAt_approxVelocity c J H h ε t
  have hyS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : y t ∈ Metric.ball p r := by
    change ‖p + approxDisplacement c J H h ε t - p‖ < r
    simpa only [add_sub_cancel_left] using ((hsize t ht).1.trans_lt hεr)
  have hres (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖b t + K (C (y t)) (w t) (w t)‖ ≤ (8 * η * B ^ 4 + T * ε) * ε ^ 4 :=
    approx_actual_residual_bound C p c J H h η B T ε t hη hB hε
      (hsize t ht).1 (hsize t ht).2.1 (hsize t ht).2.2
      (hcoeff _ ((hsize t ht).1.trans_lt hερ))
  have hcmp := geodesic_polynomial_comparison C (Metric.ball p r) M L r
    ((8 * η * B ^ 4 + T * ε) * ε ^ 4) hM hL hr.le hbound hLip (by linarith)
    γ v y w b hγ.1.1 (by simpa using hγ.1.2) hy hw
    (by simpa [y, approxDisplacement_zero, sub_eq_add_neg, neg_div, neg_smul] using hγ.2.1)
    (by simpa [y, approxDisplacement_one] using hγ.2.2.1)
    (fun t ht ↦ hγ.2.2.2 t ht |>.1) hyS
    (fun t ht ↦ (hγ.2.2.2 t ht).2.le)
    (fun t ht ↦ (hsize t ht).2.1.trans hεr.le) hres (1 / 2) (by norm_num)
  have hden : 0 < 1 - 8 * L * r ^ 2 - 16 * M * r := by linarith
  have hR : 0 ≤ (8 * η * B ^ 4 + T * ε) * ε ^ 4 := by positivity
  refine hcmp.1.trans ?_
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Uniform fourth-order approximation, expressed without any differentiability
of the endpoint-to-geodesic choice. -/
theorem exists_short_geodesic_approximation
    (C : E → Coeff) (p : E) (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian) (h : E)
    (r M L : ℝ) (hr : 0 < r) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ Metric.ball p r, ‖C x‖ ≤ M)
    (hLip : ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      ‖C x - C y‖ ≤ L * ‖x - y‖)
    (hsmall : 8 * L * r ^ 2 + 16 * M * r < 1 / 2)
    (hTaylor : ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ d : E, ‖d‖ < ρ →
      ‖C (p + d) - c - J d - (1 / 2 : ℝ) • H d d‖ ≤ η * ‖d‖ ^ 2)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ > (0 : ℝ), ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ γ v : ℝ → E,
      IsShortGeodesic C 1 p r (p - (ε / 2) • h) (p + (ε / 2) • h) γ v →
      ‖γ (1 / 2) - (p + approxDisplacement c J H h ε (1 / 2))‖ ≤ κ * ε ^ 4 := by
  obtain ⟨B, hB, T, hT, hsize⟩ := approx_uniform_bounds c J H h
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let η := κ / (32 * B ^ 4)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ρ, hρ, hcoeff⟩ := hTaylor η hη
  let δ := min 1 (min (r / B) (min (ρ / B) (κ / (4 * (T + 1)))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ γ v hγ
  have hε1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεr : ε < r / B := lt_of_lt_of_le hεδ
    ((min_le_left _ _).trans' (min_le_right _ _))
  have hερ : ε < ρ / B := lt_of_lt_of_le hεδ
    ((min_le_left _ _).trans' ((min_le_right _ _).trans' (min_le_right _ _)))
  have hεT : ε < κ / (4 * (T + 1)) := lt_of_lt_of_le hεδ
    ((min_le_right _ _).trans' ((min_le_right _ _).trans' (min_le_right _ _)))
  have hBr : B * ε < r := by nlinarith [(lt_div_iff₀ hBpos).mp hεr]
  have hBρ : B * ε < ρ := by nlinarith [(lt_div_iff₀ hBpos).mp hερ]
  have hεabs : |ε| ≤ 1 := by simpa only [abs_of_nonneg hε] using hε1.le
  have hsizeε : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖approxDisplacement c J H h ε t‖ ≤ B * ε ∧
      ‖approxVelocity c J H h ε t‖ ≤ B * ε ∧
      ‖approxResidualTail c J H h ε t‖ ≤ T := by
    intro t ht
    simpa only [abs_of_nonneg hε] using (hsize ε t hεabs ht)
  have happrox := short_geodesic_approximation C p c J H h r M L η B T ε ρ
    hM hL hr hη.le hBpos.le hT hε hbound hLip hsmall hcoeff
    hsizeε
    hBr hBρ γ v hγ
  have hηeq : 16 * η * B ^ 4 = κ / 2 := by
    dsimp [η]
    field_simp [ne_of_gt hBpos]
    ring
  have hTε : 4 * T * ε ≤ κ := by
    have := (lt_div_iff₀ (show 0 < 4 * (T + 1) by positivity)).mp hεT
    nlinarith
  refine happrox.trans ?_
  have hc : 2 * (8 * η * B ^ 4 + T * ε) ≤ κ := by nlinarith
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg hε 4)

end PlanarMidpoint
