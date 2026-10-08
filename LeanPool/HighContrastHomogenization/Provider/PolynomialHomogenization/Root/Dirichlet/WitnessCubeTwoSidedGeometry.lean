/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessCubeSideGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeTwoSidedGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two-sided witness cube/ball geometry

The sign condition `0 ≤ j` is false in general and is replaced by a *bound*
`3 ^ (−r j) ≤ Cgeo`, with
the law-free `Cgeo` left as a residue: it needs the lower companion of
`witnessCubeSide_le_two_mul_norm_inv_matSqrt`.

In gauge coordinates the frozen witness domain is the translated open triadic
cube of generation `j` (`matImage_inv_affineImage`), and `ellipsoid abar r`
pulls back to the exact Euclidean sublevel set of radius `α r`,
`α = √(specBound (symmPart abar)⁻¹) = ‖(matSqrt (symmPart abar))⁻¹‖`
(`matImage_matSqrt_inv_ellipsoid_eq`).  A ball inside an open cube of side `ℓ`
forces `2 · radius ≤ ℓ` — the antipodal-coordinate argument below — and this is
the exact converse of the energy's cube-inside-ball estimate.

Hence, from surface:

```
2 α / (3 √d)  ≤  3 ^ j  ≤  2 α        (inner-ellipsoid normalization inner premise;
inner-ellipsoid normalization outer premise)
2 ρ           ≤  3 ^ j                (the frozen ball sandwich)
ρ             ≤  α                    (the two combined)
```

and `Cgeo := (ρ / (3 √d)) ^ (−r)` is a function of `(d, ρ, r)` alone, which is
exactly `C₀ s₀ ρ Rad`'s permitted dependence.

**The cube-side convention is the coordinate one**:
`openCubeSet (originCube d j)` is `(−3^j/2, 3^j/2)^d`, so a contained ball of
radius `t` obeys `2 t ≤ 3^j` with no `√d`; the `√d` in `Cgeo` is the one carried
by the printed inner radius `1/(3√d)`, not by the cube.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## A ball inside an open triadic cube -/

/-- **A Euclidean ball inside a translated open triadic cube has diameter at
most the side.**  This is the converse of the energy's
`cubeScaleFactor_le_two_mul_of_translateSet_subset`. -/
theorem two_mul_le_cubeScale_of_antipodal_mem [NeZero d] {j : ℤ} {w cc : Vec d}
    {t : ℝ}
    (hmem : ∀ v : Vec d, vecNormSq v ≤ t ^ 2 →
      cc + v ∈ translateSet w (openCubeSet (originCube d j))) :
    2 * t ≤ (3 : ℝ) ^ j := by
  classical
  let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let e : Vec d := fun i => if i = i0 then t else 0
  have he0 : e i0 = t := by simp only [e, ite_eq_left rfl]
  have hnorm_e : vecNormSq e = t ^ 2 := by
    have hterm : ∀ i : Fin d, e i * e i = if i = i0 then t * t else 0 := by
      intro i
      by_cases hi : i = i0 <;> simp [e, hi]
    calc vecNormSq e = ∑ i, e i * e i := rfl
      _ = ∑ i : Fin d, if i = i0 then t * t else 0 :=
        Finset.sum_congr rfl fun i _ => hterm i
      _ = t * t := by simp
      _ = t ^ 2 := (pow_two t).symm
  have hnorm_neg : vecNormSq (-e) = t ^ 2 := by
    have hflip : vecNormSq (-e) = vecNormSq e := by
      simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]
    rw [hflip, hnorm_e]
  have h1 := hmem e hnorm_e.le
  have h2 := hmem (-e) hnorm_neg.le
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff] at h1 h2
  have hA := h1 i0
  have hB := h2 i0
  have hAval : (cc + e - w) i0 = cc i0 + t - w i0 := by
    change cc i0 + e i0 - w i0 = cc i0 + t - w i0
    rw [he0]
  have hBval : (cc + -e - w) i0 = cc i0 - t - w i0 := by
    change cc i0 + -e i0 - w i0 = cc i0 - t - w i0
    rw [he0]
    ring
  rw [hAval] at hA
  rw [hBval] at hB
  linarith only [hA.2, hB.1]

/-! ## The gauge picture of the frozen witness -/

/-- The gauge domain of the frozen witness is the translated open cube. -/
theorem gaugeDomain_eq_translateSet {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    matImage (matSqrt (symmPart abar))⁻¹ U =
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
        (openCubeSet (originCube d j)) := by
  rw [hU]
  exact matImage_inv_affineImage (isUnit_det_matSqrt hS) z _

/-- The gauge scale `α = ‖(matSqrt (symmPart abar))⁻¹‖` is the square root of the
normalizing spectral bound. -/
theorem norm_inv_matSqrt_eq_sqrt_specBound {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    ‖(matSqrt (symmPart abar))⁻¹‖ =
      Real.sqrt (specBound ((symmPart abar)⁻¹)) := by
  rw [← EnergyPrice.norm_inv_matSqrt_sq hS, Real.sqrt_sq (norm_nonneg _)]

/-! ## The lower companion, from the inner-ellipsoid normalization inner premise -/

/-- **The lower companion of `witnessCubeSide_le_two_mul_norm_inv_matSqrt`.**
The printed inner ellipsoid, pulled to gauge coordinates, is the ball of radius
`α / (3 √d)`, and it sits inside the witness cube. -/
theorem two_mul_gaugeInnerRadius_le_cubeScale [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U) :
    2 * (Real.sqrt (specBound ((symmPart abar)⁻¹)) *
        (1 / (3 * Real.sqrt (d : ℝ)))) ≤ (3 : ℝ) ^ j := by
  have hgauge := gaugeDomain_eq_translateSet hS hU
  have hsq : specBound ((symmPart abar)⁻¹) * (1 / (3 * Real.sqrt (d : ℝ))) ^ 2 =
      (Real.sqrt (specBound ((symmPart abar)⁻¹)) *
        (1 / (3 * Real.sqrt (d : ℝ)))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (specBound_nonneg _)]
  refine two_mul_le_cubeScale_of_antipodal_mem
    (cc := (0 : Vec d))
    (w := matVecMul (matSqrt (symmPart abar))⁻¹ z) (j := j) ?_
  intro v hv
  have hv' : v ∈ matImage (matSqrt (symmPart abar))⁻¹
      (ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ)))) := by
    rw [matImage_matSqrt_inv_ellipsoid_eq hS (1 / (3 * Real.sqrt (d : ℝ)))]
    change vecNormSq v ≤
      specBound ((symmPart abar)⁻¹) * (1 / (3 * Real.sqrt (d : ℝ))) ^ 2
    rw [hsq]
    exact hv
  have hin : v ∈ matImage (matSqrt (symmPart abar))⁻¹ U :=
    Set.image_mono hinner hv'
  rw [hgauge] at hin
  rwa [zero_add]

/-- **The sandwich companion.**  The frozen ball sandwich's inner ball also sits
inside the witness cube, so the cube side is at least `2 ρ`. -/
theorem two_mul_rho_le_cubeScale [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {rho Rad : ℝ}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    2 * rho ≤ (3 : ℝ) ^ j := by
  obtain ⟨hrho, -, cc, hin, -⟩ := hsandwich
  have hgauge := gaugeDomain_eq_translateSet hS hU
  have hpow : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  by_contra hcon
  push Not at hcon
  set t : ℝ := ((3 : ℝ) ^ j / 2 + rho) / 2 with htdef
  have ht0 : 0 ≤ t := by
    rw [htdef]
    linarith only [hpow, hrho]
  have htlt : t < rho := by
    rw [htdef]
    linarith only [hcon]
  have htsq : t ^ 2 < rho ^ 2 := by
    have h := mul_self_lt_mul_self ht0 htlt
    simpa only [pow_two] using h
  have hkey : 2 * t ≤ (3 : ℝ) ^ j := by
    refine two_mul_le_cubeScale_of_antipodal_mem
      (cc := cc) (w := matVecMul (matSqrt (symmPart abar))⁻¹ z) (j := j) ?_
    intro v hv
    have hball : cc + v ∈ euclideanBallAt cc rho := by
      change vecNormSq (cc + v - cc) < rho ^ 2
      have hsimp : cc + v - cc = v := by abel
      rw [hsimp]
      exact lt_of_le_of_lt hv htsq
    have := hin hball
    rwa [hgauge] at this
  rw [htdef] at hkey
  linarith only [hkey, hcon]

/-! ## The two-sided statement and the law-free geometric factor -/

/-- **The two-sided witness cube/ball geometry.**  Both premises of the frozen
inner-ellipsoid normalization pin the witness generation between two multiples of the gauge
scale `α`, and the ball sandwich's inner radius is below `α`. -/
theorem witnessCubeScale_two_sided [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {rho Rad : ℝ}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1)
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    2 * (Real.sqrt (specBound ((symmPart abar)⁻¹)) *
          (1 / (3 * Real.sqrt (d : ℝ)))) ≤ (3 : ℝ) ^ j ∧
      (3 : ℝ) ^ j ≤ 2 * Real.sqrt (specBound ((symmPart abar)⁻¹)) ∧
      rho ≤ Real.sqrt (specBound ((symmPart abar)⁻¹)) := by
  have hlow := two_mul_gaugeInnerRadius_le_cubeScale hS hU hinner
  have hupper : (3 : ℝ) ^ j ≤ 2 * Real.sqrt (specBound ((symmPart abar)⁻¹)) := by
    have h := EnergyPrice.witnessCubeSide_le_two_mul_norm_inv_matSqrt hS hU hUsub
    rw [norm_inv_matSqrt_eq_sqrt_specBound hS] at h
    simpa only [cubeScaleFactor, originCube] using h
  have hrho := two_mul_rho_le_cubeScale hS hU hsandwich
  exact ⟨hlow, hupper, by linarith only [hrho, hupper]⟩

/-- The law-free geometric factor: a function of `(d, ρ, r)` only. -/
@[expose]
noncomputable def witnessGeometricFactor (d : ℕ) (rho r : ℝ) : ℝ :=
  (rho / (3 * Real.sqrt (d : ℝ))) ^ (-r)

/-- **The geometric factor bound.**  The `3 ^ (−r j)` factor of the λ-route is below the
law-free `Cgeo = (ρ / (3 √d)) ^ (−r)`, from binder surface. -/
theorem rpow_three_neg_order_le_witnessGeometricFactor [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d} {rho Rad r : ℝ} (hr : 0 ≤ r)
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    (3 : ℝ) ^ (-r * (j : ℝ)) ≤ witnessGeometricFactor d rho r := by
  have hrho : 0 < rho := hsandwich.1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsqrtd : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have h := Real.sqrt_le_sqrt hd1
    rwa [Real.sqrt_one] at h
  have hden : (3 : ℝ) ≤ 3 * Real.sqrt (d : ℝ) := by linarith only [hsqrtd]
  have hdenPos : (0 : ℝ) < 3 * Real.sqrt (d : ℝ) := by linarith only [hden]
  have hfracPos : (0 : ℝ) < rho / (3 * Real.sqrt (d : ℝ)) := div_pos hrho hdenPos
  have hinvle : 1 / (3 * Real.sqrt (d : ℝ)) ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hden
    have h3 : (1 : ℝ) / 3 ≤ 2 := by norm_num
    linarith only [h, h3]
  have hfracle : rho / (3 * Real.sqrt (d : ℝ)) ≤ 2 * rho := by
    rw [div_eq_mul_one_div]
    have h := mul_le_mul_of_nonneg_left hinvle hrho.le
    linarith only [h]
  have hlow : rho / (3 * Real.sqrt (d : ℝ)) ≤ (3 : ℝ) ^ j :=
    le_trans hfracle (two_mul_rho_le_cubeScale hS hU hsandwich)
  have hconv : (3 : ℝ) ^ (-r * (j : ℝ)) = ((3 : ℝ) ^ j) ^ (-r) := by
    have hcomm : (-r * (j : ℝ)) = (j : ℝ) * (-r) := by ring
    rw [hcomm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_intCast]
  rw [hconv, witnessGeometricFactor]
  exact Real.rpow_le_rpow_of_nonpos hfracPos hlow (neg_nonpos.mpr hr)

end

end RowSupply
end HighContrast
end HCPolySupport
