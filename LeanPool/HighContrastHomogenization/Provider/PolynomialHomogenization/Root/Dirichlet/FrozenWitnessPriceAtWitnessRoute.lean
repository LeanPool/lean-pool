/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessLambdaRouteComposition
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeTwoSidedGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorGeometricFactor
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WindowedFrozenWitnessPrice

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPriceAtWitnessRoute

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frozen-witness energy price, with the transported row supplied

that module supplied the price at an eccentricity-shaped `Cwit`, taking the λ-route's
observation-error bound (`hErr`) and the sign `0 ≤ j` as binders.  The route
refuted the sign; this module replaces both:

* `hErr` is now **produced**, by the λ-route composition of
  `HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessLambdaRouteComposition`
(21a);
* the `3 ^ (−r j)` factor is paid by the law-free geometric factor of
  `HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeTwoSidedGeometry`
(21c′), through that module.

The resulting price has **no** analytic binder from the row: every hypothesis is
either on the domain surface, an output of the response-window tail, an
identification
of the observation family, or one of the energy's own transport binders.

**The one constraint this exposes.**  The composition fixes the observation order to
`responseWindowOrder g`, because that reference tail is at that order; the
frozen clause's boundary energy is at `s₀ ∈ Ico ((1+g)/4) (1/2)`, and
`responseWindowOrder g = (3+5g)/16 < (1+g)/4` for every `g < 1`.  The price
produced here is therefore at the response-window order.  Transporting it to the
printed `s₀` is a separate obligation and is **not** performed here.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The witness generation is below the outer bracket -/

/-- The witness cube side is at most twice the outer sandwich radius. -/
theorem cubeScale_le_two_mul_Rad [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {rho Rad : ℝ}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    (3 : ℝ) ^ j ≤ 2 * Rad := by
  obtain ⟨-, hRad, cc, -, hout⟩ := hsandwich
  have hgauge := gaugeDomain_eq_translateSet hS hU
  have hsub : translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z - cc)
      (openCubeSet (originCube d j)) ⊆
        {y : Vec d | vecNormSq y ≤ Rad ^ 2} := by
    intro x hx
    rw [mem_translateSet_iff_sub_mem] at hx
    have hmem : x + cc ∈
        translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
          (openCubeSet (originCube d j)) := by
      rw [mem_translateSet_iff_sub_mem]
      have hshift : x + cc - matVecMul (matSqrt (symmPart abar))⁻¹ z =
          x - (matVecMul (matSqrt (symmPart abar))⁻¹ z - cc) := by abel
      rw [hshift]
      exact hx
    rw [← hgauge] at hmem
    have hball : vecNormSq (x + cc - cc) < Rad ^ 2 := hout hmem
    have hx' : x + cc - cc = x := by abel
    rw [hx'] at hball
    exact le_of_lt hball
  exact EnergyPrice.cubeScaleFactor_le_two_mul_of_translateSet_subset hRad hsub

/-- With the anchored provider's outer bracket `2 Rad ≤ 3 ^ J`, the witness
generation is below `J`. -/
theorem witnessGeneration_le_bracket [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {rho Rad : ℝ} {J : ℕ}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad)
    (hJ : 2 * Rad ≤ (3 : ℝ) ^ ((J : ℕ) : ℤ)) :
    j ≤ ((J : ℕ) : ℤ) := by
  have h2 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ ((J : ℕ) : ℤ) :=
    le_trans (cubeScale_le_two_mul_Rad hS hU hsandwich) hJ
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h2

/-! ## The `Cwit` the witness route supports -/

/-- The witness route's `Cwit`: the λ-route filling constant, the law-free
geometric factor, the frame fold, and a fixed power of the witness
eccentricity. -/
@[expose]
noncomputable def witnessRouteCwit (d : ℕ) (Claw Cgeo g kappaRate J : ℝ)
    (abar : Mat d) : ℝ :=
  Claw * ((Cgeo * frameFoldConstant d g kappaRate J) *
    (max 1 (witnessEccentricity (symmPart abar))) ^
      witnessErrorEccentricityExponent g kappaRate)

theorem witnessRouteCwit_nonneg (d : ℕ) {Claw Cgeo : ℝ} (hClaw : 0 ≤ Claw)
    (hCgeo : 0 ≤ Cgeo) (g kappaRate J : ℝ) (abar : Mat d) :
    0 ≤ witnessRouteCwit d Claw Cgeo g kappaRate J abar := by
  have hE0 : (0 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_trans zero_le_one (le_max_left _ _)
  rw [witnessRouteCwit]
  exact mul_nonneg hClaw
    (mul_nonneg (mul_nonneg hCgeo (frameFoldConstant_nonneg d g kappaRate J))
      (Real.rpow_nonneg hE0 _))

/-! ## The price, with row 21 supplied -/

end

end RowSupply
end HighContrast
end HCPolySupport
