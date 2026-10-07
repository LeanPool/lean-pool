/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.ExteriorNonanalytic
public import LeanPool.CIVAxisymmetric.Main.InteriorAnalyticity

/-!
# `rem:exterior:nonanalytic` without the interior analyticity hypothesis

`CIV.not_eqOn_zero_of_exteriorVanishing` takes the interior analyticity theorem
`thm:analytic:interior` as its hypothesis `hinterior`. That hypothesis is exactly the statement of
`CIV.Main.interiorAnalyticity`, so applying it gives the remark with no hypothesis beyond the
classical system, the exterior vanishing and the nonzero axial velocity.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


namespace CIV

/-- `rem:exterior:nonanalytic`: a classical solution whose velocity satisfies the exterior
vanishing condition on an open set meeting a ball about the axis, and whose axial velocity is
nonzero at a time `t₀`, cannot have a force vanishing on the cylinder `B(R') × (t₁, t₀)`. -/
theorem exteriorNonanalytic
    {R δ t₀ R' t₁ : ℝ} {E : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo (-δ) 0)))
    (hEopen : IsOpen E)
    (hvanish : ∀ x ∈ E, ∀ t ∈ Ioo (-δ) 0,
      (x 0 * u (x, t) 0 + x 1 * u (x, t) 1) / Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = 0
        ∧ u (x, t) 2 = 0)
    (ht₀ : t₀ ∈ Ioo (-δ) 0) (haxis : u ((0 : Vec3), t₀) 2 ≠ 0)
    (hR' : 0 < R') (hR'R : R' ≤ R) (hmeet : (E ∩ vec3Ball (0 : Vec3) R').Nonempty)
    (ht₁ : t₁ ∈ Ioo (-δ) t₀) :
    ¬ ∀ z ∈ spaceTimeSet (vec3Ball 0 R') (Ioo t₁ t₀), f z = 0 :=
  not_eqOn_zero_of_exteriorVanishing hsol hEopen hvanish ht₀ haxis hR' hR'R hmeet ht₁
    (fun S s₁ s₂ hS hs hsolS hfS => Main.interiorAnalyticity S s₁ s₂ hS hs u p f hsolS hfS)

end CIV
