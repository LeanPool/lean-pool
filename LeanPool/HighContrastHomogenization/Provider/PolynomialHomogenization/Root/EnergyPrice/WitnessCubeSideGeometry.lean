/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.TranslatedCubeEnergyPrice
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeGoodTail
public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessCubeSideGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gate R2-geo: the gauge cube side is at most `2‖L⁻¹‖`

The bound `ell ≤ 2 * ‖(matSqrt (symmPart abar))⁻¹‖` is not a hypothesis of the
frame bound: it is a consequence of the inner-ellipsoid
normalization premise `U ⊆ ellipsoid abar 1`, because `ellipsoid` is
normalized by `specBound (symmPart abar)⁻¹`:

```
ellipsoid abar r = {x | x · (symmPart abar)⁻¹ x ≤ specBound (symmPart abar)⁻¹ · r²}
```

so the gauge image of `ellipsoid abar 1` lies in the Euclidean ball of radius
`√(specBound (symmPart abar)⁻¹) = ‖(matSqrt (symmPart abar))⁻¹‖`, and a
translated triadic cube inside a ball of radius `r` has side at most `2r`.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Coordinate bounds from the Euclidean square -/

/-- One coordinate square is at most the Euclidean square. -/
theorem sq_le_vecNormSq (x : Vec d) (i : Fin d) : x i ^ 2 ≤ vecNormSq x := by
  have h := Finset.single_le_sum
    (f := fun k : Fin d => x k * x k)
    (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ i)
  simpa only [vecNormSq, vecDot, pow_two] using h

/-- A Euclidean bound gives a coordinate bound. -/
theorem abs_le_of_vecNormSq_le {x : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (h : vecNormSq x ≤ r ^ 2) (i : Fin d) : |x i| ≤ r := by
  have hsq : x i ^ 2 ≤ r ^ 2 := (sq_le_vecNormSq x i).trans h
  calc
    |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hsq
    _ = r := Real.sqrt_sq hr

/-! ## The gauge image of the unit ellipsoid -/

/-- `‖(matSqrt S)⁻¹‖ ^ 2 = specBound S⁻¹`. -/
theorem norm_inv_matSqrt_sq {S : Mat d} (hS : S.PosDef) :
    ‖(matSqrt S)⁻¹‖ ^ 2 = specBound S⁻¹ := by
  rw [← matSqrt_inv hS, norm_matSqrt_eq_sqrt_specBound hS.inv,
    Real.sq_sqrt (specBound_nonneg _)]

/-- **The gauge image of the unit ellipsoid lies in the ball of radius
`‖L⁻¹‖`.** -/
theorem vecNormSq_le_of_mem_matImage_inv_matSqrt_ellipsoid
    {abar : Mat d} (hS : (symmPart abar).PosDef) {y : Vec d}
    (hy : y ∈ matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar 1)) :
    vecNormSq y ≤ ‖(matSqrt (symmPart abar))⁻¹‖ ^ 2 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hu : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hback :
      matVecMul (matSqrt (symmPart abar))
          (matVecMul (matSqrt (symmPart abar))⁻¹ x) = x := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hu, matVecMul_one]
  have hid := vecDot_matVecMul_inv_matSqrt hS
    (matVecMul (matSqrt (symmPart abar))⁻¹ x)
  rw [hback] at hid
  have hmem : vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤
      specBound ((symmPart abar)⁻¹) * 1 ^ 2 := hx
  rw [norm_inv_matSqrt_sq hS]
  calc
    vecNormSq (matVecMul (matSqrt (symmPart abar))⁻¹ x) =
        vecDot x (matVecMul (symmPart abar)⁻¹ x) := hid.symm
    _ ≤ specBound ((symmPart abar)⁻¹) * 1 ^ 2 := hmem
    _ = specBound ((symmPart abar)⁻¹) := by ring

/-! ## A translated cube inside a ball -/

/-- **A translate of a triadic cube contained in a Euclidean ball of radius `r`
has side at most `2r`.** -/
theorem cubeScaleFactor_le_two_mul_of_translateSet_subset [NeZero d]
    {j : ℤ} {w : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hsub : translateSet w (openCubeSet (originCube d j)) ⊆
      {y : Vec d | vecNormSq y ≤ r ^ 2}) :
    (3 : ℝ) ^ j ≤ 2 * r := by
  classical
  have hi : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hhalf : ∀ t : ℝ, 0 < t → t < (1 / 2 : ℝ) * (3 : ℝ) ^ j → t ≤ r := by
    intro t ht htlt
    set e : Vec d := fun k => if k = hi then t else 0 with hedef
    have hecoord : ∀ k, e k = if k = hi then t else 0 := fun k => rfl
    have hehi : e hi = t := by rw [hecoord hi, ite_eq_left rfl]
    have hmem : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
        w + sgn • e ∈ translateSet w (openCubeSet (originCube d j)) := by
      intro sgn hsgn
      rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
      intro k
      have hcoord : (w + sgn • e - w) k = sgn * e k := by
        change w k + sgn * e k - w k = sgn * e k
        ring
      have hek : e k = t ∨ e k = 0 := by
        by_cases hk : k = hi
        · exact Or.inl (by rw [hecoord k, ite_eq_left hk])
        · exact Or.inr (by rw [hecoord k, ite_eq_right hk])
      have hsg : sgn * e k = e k ∨ sgn * e k = -(e k) := by
        rcases hsgn with h | h
        · exact Or.inl (by rw [h, one_mul])
        · exact Or.inr (by rw [h]; ring)
      rw [hcoord]
      constructor
      · rcases hsg with h | h <;> rcases hek with h2 | h2 <;> rw [h, h2] <;>
          linarith only [ht, htlt]
      · rcases hsg with h | h <;> rcases hek with h2 | h2 <;> rw [h, h2] <;>
          linarith only [ht, htlt]
    have hp := abs_le_of_vecNormSq_le hr (hsub (hmem 1 (Or.inl rfl))) hi
    have hm := abs_le_of_vecNormSq_le hr (hsub (hmem (-1) (Or.inr rfl))) hi
    have hpval : (w + (1 : ℝ) • e) hi = w hi + t := by
      change w hi + (1 : ℝ) • e hi = w hi + t
      rw [smul_eq_mul, one_mul, hehi]
    have hmval : (w + (-1 : ℝ) • e) hi = w hi - t := by
      change w hi + (-1 : ℝ) • e hi = w hi - t
      rw [smul_eq_mul, hehi]
      ring
    rw [hpval] at hp
    rw [hmval] at hm
    have h1 : w hi + t ≤ |w hi + t| := le_abs_self _
    have h2 : -(w hi - t) ≤ |w hi - t| := neg_le_abs _
    linarith only [h1, h2, hp, hm]
  by_contra hcon
  push Not at hcon
  set t : ℝ := (r + (1 / 2 : ℝ) * (3 : ℝ) ^ j) / 2 with htdef
  have hpow : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have ht : 0 < t := by
    rw [htdef]; linarith only [hr, hpow]
  have htlt : t < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
    rw [htdef]; linarith only [hcon]
  have hle : t ≤ r := hhalf t ht htlt
  rw [htdef] at hle
  linarith only [hle, hcon]

/-! ## The witness instance -/

/-- **Gate R2-geo, closed.**  At the frozen witness the gauge cube side is at
most `2‖(matSqrt (symmPart abar))⁻¹‖`, from the inner-ellipsoid normalization
premise
alone. -/
theorem witnessCubeSide_le_two_mul_norm_inv_matSqrt [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hinner : U ⊆ ellipsoid abar 1) :
    cubeScaleFactor (originCube d j) ≤
      2 * ‖(matSqrt (symmPart abar))⁻¹‖ := by
  have hu : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hgauge :
      matImage (matSqrt (symmPart abar))⁻¹ U =
        translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
          (openCubeSet (originCube d j)) := by
    rw [hU]
    exact RowSupply.matImage_inv_affineImage hu z _
  have hsub :
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
          (openCubeSet (originCube d j)) ⊆
        {y : Vec d | vecNormSq y ≤ ‖(matSqrt (symmPart abar))⁻¹‖ ^ 2} := by
    rw [← hgauge]
    rintro _ ⟨x, hx, rfl⟩
    exact vecNormSq_le_of_mem_matImage_inv_matSqrt_ellipsoid hS
      (Set.mem_image_of_mem _ (hinner hx))
  have hmain := cubeScaleFactor_le_two_mul_of_translateSet_subset
    (norm_nonneg _) hsub
  simpa only [cubeScaleFactor, originCube] using hmain

end

end EnergyPrice
end HighContrast
end HCPolySupport
