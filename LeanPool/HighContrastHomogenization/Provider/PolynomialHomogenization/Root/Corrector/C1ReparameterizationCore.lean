/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly
public import LeanPool.HighContrastHomogenization.Support.Ambient.Euclidean

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1ReparameterizationCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-to-limit reparameterization core

The analytic construction of the corrector parameter map is separate from
the two general steps recorded here: a uniform finite-tail estimate passes
to its norm limit, and a linear endomorphism strictly closer than the identity
is bijective in finite dimension.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- A linear endomorphism whose pointwise distance from the identity is
strictly smaller than one is bijective. -/
theorem linearMap_bijective_of_euclideanNorm_sub_identity_lt_one
    {d : ℕ} (P : Vec d →ₗ[ℝ] Vec d) (theta : ℝ)
    (htheta1 : theta < 1)
    (hclose : ∀ e : Vec d,
      euclideanNorm (P e - e) ≤ theta * euclideanNorm e) :
    Function.Bijective P := by
  have hinj : Function.Injective P := by
    intro x y hxy
    let z : Vec d := x - y
    have hPz : P z = 0 := by
      dsimp only [z]
      rw [map_sub, hxy, sub_self]
    have hzbound := hclose z
    rw [hPz, zero_sub, euclideanNorm_neg] at hzbound
    have hznonneg : 0 ≤ euclideanNorm z := euclideanNorm_nonneg z
    have hz : euclideanNorm z = 0 := by
      nlinarith only [hzbound, hznonneg, htheta1]
    exact sub_eq_zero.mp (euclideanNorm_eq_zero_iff.mp hz)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

end

end HighContrast
end HCPolySupport
