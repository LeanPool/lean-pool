/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_VeluPointMap2

import Mathlib.RingTheory.SimpleRing.Principal


/-!
# Vélu sends curve intersections with a line to another line

Use coordinates d = x - x₀ and e = y - y₀ centred at the order-two kernel point.
The curve equation becomes e² + a₁de = d³ + cd² + td, where c = a₂ + 3x₀ and
t = veluGx(x₀, y₀). If e = l d + b with b nonzero, the Vélu images lie on the
line of slope l - t / b and intercept b + t (l² + a₁l - c) / b.

The formula applies equally to chords and tangents. All polynomial calculations keep the
slope and intercept as independent quantities instead of expanding the rational slope.
-/

section privateSection

namespace VeluLineFactored

theorem shifted_curve {R : Type*} [CommRing R] {W : WeierstrassCurve R}
    {x₀ y₀ x y : R} (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (y - y₀) ^ 2 + W.a₁ * (x - x₀) * (y - y₀) - (x - x₀) * W.veluGx x₀ y₀
        - (W.a₂ + 3 * x₀) * (x - x₀) ^ 2 - (x - x₀) ^ 3 = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  simp only [WeierstrassCurve.veluGx]
  linear_combination hP - hQ - (y - y₀) * hord

/-- A small certificate for the transformed line equation. -/
theorem line_image {F : Type*} [Field F] (a c t d e l b : F)
    (hd : d ≠ 0) (hb : b ≠ 0)
    (hcurve : e ^ 2 + a * d * e - d * t - c * d ^ 2 - d ^ 3 = 0)
    (hline : e = l * d + b) :
    e - t * (a * d + e) / d ^ 2 =
      (l - t / b) * (d + t / d) + b + t * (l ^ 2 + a * l - c) / b := by
  rw [hline] at hcurve ⊢
  field_simp
  linear_combination -t * hcurve

/-- Vieta's formula gives the sum of the transformed abscissae. -/
theorem root_sum {F : Type*} [Field F] (a c t l b d₁ d₂ d₃ : F)
    (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0) (hb : b ≠ 0)
    (hsum : d₁ + d₂ + d₃ = l ^ 2 + a * l - c)
    (hpair : d₁ * d₂ + d₁ * d₃ + d₂ * d₃ = t - (2 * l + a) * b)
    (hprod : d₁ * d₂ * d₃ = b ^ 2) :
    (d₁ + t / d₁) + (d₂ + t / d₂) + (d₃ + t / d₃) =
      (l - t / b) ^ 2 + a * (l - t / b) - c := by
  have hinv : d₁⁻¹ + d₂⁻¹ + d₃⁻¹ =
      (d₁ * d₂ + d₁ * d₃ + d₂ * d₃) / (d₁ * d₂ * d₃) := by
    field_simp
    ring
  rw [hpair, hprod] at hinv
  calc
    (d₁ + t / d₁) + (d₂ + t / d₂) + (d₃ + t / d₃) =
        (d₁ + d₂ + d₃) + t * (d₁⁻¹ + d₂⁻¹ + d₃⁻¹) := by ring
    _ = (l ^ 2 + a * l - c) + t * ((t - (2 * l + a) * b) / b ^ 2) := by
      rw [hsum, hinv]
    _ = (l - t / b) ^ 2 + a * (l - t / b) - c := by
      field_simp
      ring

/-- The third intersection of a secant, including the two remaining Vieta relations. -/
theorem secant_vieta {F : Type*} [Field F] (a c t l b d₁ d₂ A : F)
    (hne : d₁ ≠ d₂) (hA : A = l ^ 2 + a * l - c - d₁ - d₂)
    (h₁ : (l * d₁ + b) ^ 2 + a * d₁ * (l * d₁ + b)
      - d₁ * t - c * d₁ ^ 2 - d₁ ^ 3 = 0)
    (h₂ : (l * d₂ + b) ^ 2 + a * d₂ * (l * d₂ + b)
      - d₂ * t - c * d₂ ^ 2 - d₂ ^ 3 = 0) :
    (d₁ * d₂ + d₁ * A + d₂ * A = t - (2 * l + a) * b) ∧
    (d₁ * d₂ * A = b ^ 2) ∧
    ((l * A + b) ^ 2 + a * A * (l * A + b) - A * t - c * A ^ 2 - A ^ 3 = 0) := by
  have hpair : d₁ * d₂ + d₁ * A + d₂ * A = t - (2 * l + a) * b := by
    apply sub_eq_zero.mp
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
    rw [mul_zero, hA]
    linear_combination h₁ - h₂
  have hprod : d₁ * d₂ * A = b ^ 2 := by
    rw [hA] at hpair ⊢
    linear_combination -h₁ + d₁ * hpair
  refine ⟨hpair, hprod, ?_⟩
  rw [hA] at hpair hprod ⊢
  linear_combination (l ^ 2 + a * l - c - d₁ - d₂) * hpair - hprod

/-- Repeated-root Vieta identities for a tangent. -/
theorem tangent_vieta {F : Type*} [Field F] (a c t l d e A : F)
    (hA : A = l ^ 2 + a * l - c - 2 * d)
    (hC : e ^ 2 + a * d * e - d * t - c * d ^ 2 - d ^ 3 = 0)
    (hL : l * (2 * e + a * d) - t - 2 * c * d - 3 * d ^ 2 + a * e = 0) :
    (d * d + d * A + d * A = t - (2 * l + a) * (e - l * d)) ∧
    (d * d * A = (e - l * d) ^ 2) ∧
    ((l * A + (e - l * d)) ^ 2 + a * A * (l * A + (e - l * d))
      - A * t - c * A ^ 2 - A ^ 3 = 0) := by
  have hpair : d * d + d * A + d * A = t - (2 * l + a) * (e - l * d) := by
    rw [hA]
    linear_combination hL
  have hprod : d * d * A = (e - l * d) ^ 2 := by
    rw [hA]
    linear_combination d * hL - hC
  refine ⟨hpair, hprod, ?_⟩
  rw [hA] at hpair hprod ⊢
  linear_combination (l ^ 2 + a * l - c - 2 * d) * hpair - hprod

/-- The transformed tangent direction, without expanding the rational slope. -/
theorem tangent_image {F : Type*} [Field F] (a c t l d e : F)
    (hd : d ≠ 0) (hb : e - l * d ≠ 0)
    (hC : e ^ 2 + a * d * e - d * t - c * d ^ 2 - d ^ 3 = 0)
    (hL : l * (2 * e + a * d) - t - 2 * c * d - 3 * d ^ 2 + a * e = 0) :
    (l - t / (e - l * d)) *
        (2 * (e - t * (a * d + e) / d ^ 2) + a * (d + t / d)) =
      3 * (d + t / d) ^ 2 + 2 * c * (d + t / d) - 4 * t
        - a * (e - t * (a * d + e) / d ^ 2) := by
  field_simp
  linear_combination
    ((e - l * d) * d ^ 2 + t * (e + (l + a) * d)) * hL - t * (4 * l + 2 * a) * hC

/-- The original tangent-slope equation with just its own denominator cleared. -/
theorem shifted_tangent {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.slope x x y y * (2 * (y - y₀) + W.a₁ * (x - x₀))
        - W.veluGx x₀ y₀ - 2 * (W.a₂ + 3 * x₀) * (x - x₀)
        - 3 * (x - x₀) ^ 2 + W.a₁ * (y - y₀) = 0 := by
  have hden : 2 * (y - y₀) + W.a₁ * (x - x₀) = y - W.toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination -hord
  have hs : W.toAffine.slope x x y y * (y - W.toAffine.negY x y)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hy)
  rw [hden, hs]
  simp only [WeierstrassCurve.veluGx]
  ring

end VeluLineFactored

/-- A chord or tangent of nonzero intercept transforms to a line with slope l - t / b. -/
theorem WeierstrassCurve.velu2_line_image_factored
    {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hx : x ≠ x₀) (l b : F) (hb : b ≠ 0) (hline : y - y₀ = l * (x - x₀) + b) :
    W.velu2Y x₀ y₀ x y - y₀ =
      (l - W.veluGx x₀ y₀ / b) * (W.velu2X x₀ y₀ x - x₀)
        + b + W.veluGx x₀ y₀ * (l ^ 2 + W.a₁ * l - (W.a₂ + 3 * x₀)) / b := by
  have h := VeluLineFactored.line_image W.a₁ (W.a₂ + 3 * x₀) (W.veluGx x₀ y₀)
    (x - x₀) (y - y₀) l b (sub_ne_zero.mpr hx) hb
    (VeluLineFactored.shifted_curve hP hQ hord) hline
  simp only [WeierstrassCurve.velu2X, WeierstrassCurve.velu2Y]
  convert h using 1 <;> ring

end privateSection

public section publicSection

/-- Both secant coordinate identities from the transformed line and Vieta's formula. -/
theorem WeierstrassCurve.velu2_secant_align_factored
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    {x₀ y₀ x₁ y₁ x₂ y₂ : F}
    (hP₁ : W.toAffine.Equation x₁ y₁) (hP₂ : W.toAffine.Equation x₂ y₂)
    (hQ : W.toAffine.Equation x₀ y₀) (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    (W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) =
      (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x₁)
        (W.velu2X x₀ y₀ x₂)
        ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁)
          (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))) ∧
    (W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) =
      (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x₁)
        (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁)
        ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁)
          (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))) := by
  let a := W.a₁
  let c := W.a₂ + 3 * x₀
  let t := W.veluGx x₀ y₀
  let l := W.toAffine.slope x₁ x₂ y₁ y₂
  let d₁ := x₁ - x₀
  let d₂ := x₂ - x₀
  let e₁ := y₁ - y₀
  let e₂ := y₂ - y₀
  let b := e₁ - l * d₁
  let xA := W.toAffine.addX x₁ x₂ l
  let yA := W.toAffine.negAddY x₁ x₂ y₁ l
  let A := xA - x₀
  have hd₁ : d₁ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : d₂ ≠ 0 := sub_ne_zero.mpr hx₂
  have hdA : A ≠ 0 := sub_ne_zero.mpr hsp
  have hne : d₁ ≠ d₂ := by
    dsimp only [d₁, d₂]
    intro h
    apply hx12
    linear_combination h
  have hsec : l * (d₁ - d₂) = e₁ - e₂ := by
    dsimp only [l, d₁, d₂, e₁, e₂]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx12]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
    field_simp
    ring
  have hline₁ : e₁ = l * d₁ + b := by dsimp only [b]; ring
  have hline₂ : e₂ = l * d₂ + b := by
    dsimp only [b]
    linear_combination hsec
  have hA : A = l ^ 2 + a * l - c - d₁ - d₂ := by
    dsimp only [A, xA, a, c, d₁, d₂]
    rw [WeierstrassCurve.Affine.addX]
    ring
  have hcurve₁ := VeluLineFactored.shifted_curve hP₁ hQ hord
  have hcurve₂ := VeluLineFactored.shifted_curve hP₂ hQ hord
  change e₁ ^ 2 + a * d₁ * e₁ - d₁ * t - c * d₁ ^ 2 - d₁ ^ 3 = 0 at hcurve₁
  change e₂ ^ 2 + a * d₂ * e₂ - d₂ * t - c * d₂ ^ 2 - d₂ ^ 3 = 0 at hcurve₂
  rw [hline₁] at hcurve₁
  rw [hline₂] at hcurve₂
  obtain ⟨hpair, hprod, hcurveA⟩ :=
    VeluLineFactored.secant_vieta a c t l b d₁ d₂ A hne hA hcurve₁ hcurve₂
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, zero_pow (by decide)] at hprod
    exact mul_ne_zero (mul_ne_zero hd₁ hd₂) hdA hprod
  have hlineA : yA - y₀ = l * A + b := by
    dsimp only [yA, A, xA, b, e₁, d₁]
    rw [WeierstrassCurve.Affine.negAddY]
    ring
  have hPA : W.toAffine.Equation xA yA := by
    rw [← hlineA] at hcurveA
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [WeierstrassCurve.Affine.equation_iff] at hQ
    dsimp only [a, c, t, A] at hcurveA
    simp only [WeierstrassCurve.veluGx] at hcurveA
    linear_combination hcurveA + hQ + (yA - y₀) * hord
  let m := l - t / b
  let B := b + t * (l ^ 2 + a * l - c) / b
  have hI₁ := WeierstrassCurve.velu2_line_image_factored hP₁ hQ hord hx₁ l b hb hline₁
  have hI₂ := WeierstrassCurve.velu2_line_image_factored hP₂ hQ hord hx₂ l b hb hline₂
  have hIA := WeierstrassCurve.velu2_line_image_factored hPA hQ hord hsp l b hb hlineA
  simp only [add_assoc] at hI₁ hI₂ hIA
  change W.velu2Y x₀ y₀ x₁ y₁ - y₀ = m * (W.velu2X x₀ y₀ x₁ - x₀) + B at hI₁
  change W.velu2Y x₀ y₀ x₂ y₂ - y₀ = m * (W.velu2X x₀ y₀ x₂ - x₀) + B at hI₂
  change W.velu2Y x₀ y₀ xA yA - y₀ = m * (W.velu2X x₀ y₀ xA - x₀) + B at hIA
  have hquotSlope : (W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁)
      (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂) = m := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX12]
    apply (div_eq_iff (sub_ne_zero.mpr hX12)).mpr
    linear_combination hI₁ - hI₂
  have hsum : d₁ + d₂ + A = l ^ 2 + a * l - c := by linear_combination hA
  have hroot := VeluLineFactored.root_sum a c t l b d₁ d₂ A hd₁ hd₂ hdA hb
    hsum hpair hprod
  have hsumQ : (W.velu2X x₀ y₀ x₁ - x₀) + (W.velu2X x₀ y₀ x₂ - x₀)
      + (W.velu2X x₀ y₀ xA - x₀) = m ^ 2 + a * m - c := by
    simp only [WeierstrassCurve.velu2X]
    convert hroot using 1
    dsimp only [d₁, d₂, A, t]
    ring
  have hX : W.velu2X x₀ y₀ xA = (W.veluQuotient2 x₀ y₀).toAffine.addX
      (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂) m := by
    rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.veluQuotient2_a₁,
      WeierstrassCurve.veluQuotient2_a₂]
    dsimp only [a, c] at hsumQ
    linear_combination hsumQ
  refine ⟨?_, ?_⟩
  · rw [hquotSlope]
    exact hX
  · rw [hquotSlope]
    conv_rhs => rw [WeierstrassCurve.Affine.negAddY, ← hX]
    linear_combination hIA - hI₁

/-- Both tangent coordinate identities from the transformed line and repeated-root Vieta. -/
theorem WeierstrassCurve.velu2_tangent_align_factored
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y ≠
      (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    (W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y)) =
      (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
        ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))) ∧
    (W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.negAddY x x y (W.toAffine.slope x x y y)) =
      (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
        (W.velu2Y x₀ y₀ x y)
        ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    simpa only [WeierstrassCurve.veluGy, neg_eq_zero] using hgy
  let a := W.a₁
  let c := W.a₂ + 3 * x₀
  let t := W.veluGx x₀ y₀
  let l := W.toAffine.slope x x y y
  let d := x - x₀
  let e := y - y₀
  let b := e - l * d
  let xA := W.toAffine.addX x x l
  let yA := W.toAffine.negAddY x x y l
  let A := xA - x₀
  have hd : d ≠ 0 := sub_ne_zero.mpr hx
  have hdA : A ≠ 0 := sub_ne_zero.mpr hx2
  have hA : A = l ^ 2 + a * l - c - 2 * d := by
    dsimp only [A, xA, a, c, d]
    rw [WeierstrassCurve.Affine.addX]
    ring
  have hC : e ^ 2 + a * d * e - d * t - c * d ^ 2 - d ^ 3 = 0 :=
    VeluLineFactored.shifted_curve hP hQ hord
  have hL : l * (2 * e + a * d) - t - 2 * c * d - 3 * d ^ 2 + a * e = 0 :=
    VeluLineFactored.shifted_tangent hord hy
  obtain ⟨hpair, hprod, hcurveA⟩ := VeluLineFactored.tangent_vieta a c t l d e A hA hC hL
  have hb : b ≠ 0 := by
    intro hb
    change d * d * A = b ^ 2 at hprod
    rw [hb, zero_pow (by decide)] at hprod
    exact mul_ne_zero (mul_ne_zero hd hd) hdA hprod
  have hline : e = l * d + b := by dsimp only [b]; ring
  have hlineA : yA - y₀ = l * A + b := by
    dsimp only [yA, A, xA, b, e, d]
    rw [WeierstrassCurve.Affine.negAddY]
    ring
  have hPA : W.toAffine.Equation xA yA := by
    change (l * A + b) ^ 2 + a * A * (l * A + b)
      - A * t - c * A ^ 2 - A ^ 3 = 0 at hcurveA
    rw [← hlineA] at hcurveA
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [WeierstrassCurve.Affine.equation_iff] at hQ
    dsimp only [a, c, t, A] at hcurveA
    simp only [WeierstrassCurve.veluGx] at hcurveA
    linear_combination hcurveA + hQ + (yA - y₀) * hord
  let m := l - t / b
  let B := b + t * (l ^ 2 + a * l - c) / b
  let X := W.velu2X x₀ y₀ x
  let Y := W.velu2Y x₀ y₀ x y
  have himage := VeluLineFactored.tangent_image a c t l d e hd hb hC hL
  have hSlopeEq : m * (2 * (Y - y₀) + a * (X - x₀)) =
      3 * (X - x₀) ^ 2 + 2 * c * (X - x₀) - 4 * t - a * (Y - y₀) := by
    dsimp only [X, Y]
    simp only [WeierstrassCurve.velu2X, WeierstrassCurve.velu2Y]
    convert himage using 1 <;> dsimp only [d, e, t] <;> ring
  have hD : Y - (W.veluQuotient2 x₀ y₀).toAffine.negY X Y =
      2 * (Y - y₀) + a * (X - x₀) := by
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.veluQuotient2_a₁,
      WeierstrassCurve.veluQuotient2_a₃]
    dsimp only [a]
    linear_combination hord
  have hN : 3 * X ^ 2 + 2 * (W.veluQuotient2 x₀ y₀).a₂ * X
      + (W.veluQuotient2 x₀ y₀).a₄ - (W.veluQuotient2 x₀ y₀).a₁ * Y =
      3 * (X - x₀) ^ 2 + 2 * c * (X - x₀) - 4 * t - a * (Y - y₀) := by
    rw [WeierstrassCurve.veluQuotient2_a₁, WeierstrassCurve.veluQuotient2_a₂,
      WeierstrassCurve.veluQuotient2_a₄]
    dsimp only [a, c, t]
    simp only [WeierstrassCurve.veluGx]
    ring
  have hquotSlope : (W.veluQuotient2 x₀ y₀).toAffine.slope X X Y Y = m := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hY]
    apply (div_eq_iff (sub_ne_zero.mpr hY)).mpr
    rw [hN, hD]
    exact hSlopeEq.symm
  have hI := WeierstrassCurve.velu2_line_image_factored hP hQ hord hx l b hb hline
  have hIA := WeierstrassCurve.velu2_line_image_factored hPA hQ hord hx2 l b hb hlineA
  simp only [add_assoc] at hI hIA
  change Y - y₀ = m * (X - x₀) + B at hI
  change W.velu2Y x₀ y₀ xA yA - y₀ = m * (W.velu2X x₀ y₀ xA - x₀) + B at hIA
  have hsum : d + d + A = l ^ 2 + a * l - c := by linear_combination hA
  have hroot := VeluLineFactored.root_sum a c t l b d d A hd hd hdA hb hsum hpair hprod
  have hsumQ : (X - x₀) + (X - x₀) + (W.velu2X x₀ y₀ xA - x₀) =
      m ^ 2 + a * m - c := by
    dsimp only [X]
    simp only [WeierstrassCurve.velu2X]
    convert hroot using 1
    dsimp only [d, A, t]
    ring
  have hX : W.velu2X x₀ y₀ xA = (W.veluQuotient2 x₀ y₀).toAffine.addX X X m := by
    rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.veluQuotient2_a₁,
      WeierstrassCurve.veluQuotient2_a₂]
    dsimp only [a, c] at hsumQ
    linear_combination hsumQ
  refine ⟨?_, ?_⟩
  · rw [hquotSlope]
    exact hX
  · rw [hquotSlope]
    conv_rhs => rw [WeierstrassCurve.Affine.negAddY, ← hX]
    linear_combination hIA - hI

end publicSection
