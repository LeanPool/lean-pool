/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_Velu

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A factored proof of the tangent identity for Vélu's order-two map

Translate the kernel point to the origin and retain the tangent slope as an independent
quantity. The target factors into a combination of the translated curve equation and the
tangent equation. Only the latter uses division, so no large denominator-cleared polynomial
certificate is needed. This file does not import the original tangent-identity theorem.
-/

section privateSection

namespace VeluTangentFactored

/-- The polynomial certificate, before substituting the rational tangent slope. -/
theorem certificate {R : Type*} [CommRing R] (a c d e l t A B : R)
    (hA : A = l ^ 2 + a * l - c - 2 * d) (hB : B = l * (A - d) + e) :
    d * A * (d - A) * e - d * ((a * d + e) * A ^ 2 - (a * A + B) * d ^ 2)
        + t * (A * e - d * B)
      = (A - d) *
          ((2 * l + a) * (e ^ 2 + a * d * e - d * t - c * d ^ 2 - d ^ 3)
            - (e + (l + a) * d) * (l * (2 * e + a * d) - t - 2 * c * d
                - 3 * d ^ 2 + a * e)) := by
  rw [hB, hA]
  ring

/-- Subtract the equations of the two points and use the order-two relation. -/
theorem shifted_curve {R : Type*} [CommRing R] {W : WeierstrassCurve R}
    {x₀ y₀ x y : R} (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (y - y₀) ^ 2 + W.a₁ * (x - x₀) * (y - y₀) - (x - x₀) * W.veluGx x₀ y₀
        - (W.a₂ + 3 * x₀) * (x - x₀) ^ 2 - (x - x₀) ^ 3 = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  simp only [WeierstrassCurve.veluGx]
  linear_combination hP - hQ - (y - y₀) * hord

/-- Clear just the single denominator in the tangent-slope equation. -/
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

end VeluTangentFactored

end privateSection

public section publicSection

/-- The tangent identity, proved with a small factored polynomial certificate. -/
theorem WeierstrassCurve.velu2_tangent_negAddY_cleared_identity_factored
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hy : y ≠ W.toAffine.negY x y) :
    (x - x₀) * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
          * (x - W.toAffine.addX x x (W.toAffine.slope x x y y)) * (y - y₀)
        - (x - x₀)
          * ((W.a₁ * (x - x₀) + y - y₀)
                * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
                    + W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀)
                * (x - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - y₀)
              - (x - x₀) * (W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀))
      = 0 := by
  let d := x - x₀
  let e := y - y₀
  let c := W.a₂ + 3 * x₀
  let t := W.veluGx x₀ y₀
  let l := W.toAffine.slope x x y y
  let A := W.toAffine.addX x x l - x₀
  let B := W.toAffine.negAddY x x y l - y₀
  have hA : A = l ^ 2 + W.a₁ * l - c - 2 * d := by
    dsimp only [A, c, d]
    rw [WeierstrassCurve.Affine.addX]
    ring
  have hB : B = l * (A - d) + e := by
    dsimp only [B, A, d, e]
    rw [WeierstrassCurve.Affine.negAddY]
    ring
  have hC : e ^ 2 + W.a₁ * d * e - d * t - c * d ^ 2 - d ^ 3 = 0 :=
    VeluTangentFactored.shifted_curve hP hQ hord
  have hL : l * (2 * e + W.a₁ * d) - t - 2 * c * d - 3 * d ^ 2 + W.a₁ * e = 0 :=
    VeluTangentFactored.shifted_tangent hord hy
  have hcertificate := VeluTangentFactored.certificate W.a₁ c d e l t A B hA hB
  rw [hC, hL, mul_zero, mul_zero, sub_self, mul_zero] at hcertificate
  convert hcertificate using 1
  dsimp only [d, e, A, B, t, l]
  ring

end publicSection
