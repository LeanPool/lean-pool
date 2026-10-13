/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LinearExitDatum

/-!
# StoppedMomentsDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The linear and quadratic observables of the displacement bounds

The two Dirichlet problems behind Steps 1 and 3 of the superdiffusive displacement bounds are
posed on the origin cube `openCubeSet (originCube d m)` with the boundary data

```text
  ell_e (x) = e ⬝ x ,          quad_e (x) = (e ⬝ x)^2 ,
```

and, for the second one, the right-hand side `-2 sigma`, written as the divergence of the
field `g(x) = -2 sigma (e ⬝ x) e`.  The homogenized solutions are the data themselves: `ell_e`
is harmonic, and `quad_e` satisfies `-sigma * Laplacian quad_e = -2 sigma (e ⬝ e)`, which is
exactly the divergence of `g`.

This file records the calculus these two data need in order to be fed to the renormalization
of the generator, and reads its conclusion at each of them.

* Gradients: `ell_e` has the constant gradient `e`, and `quad_e` has the gradient
  `2 (e ⬝ x) e`.
* Hölder data: a field of the form `x ↦ (c (e ⬝ x)) e` has `1/2`-Hölder seminorm at most
  `|c| ‖e‖ (sum of |e_i|) 3^{m/2}` on a cube of side `3^m`, and is bounded there by
  `|c| ‖e‖ (sum of |e_i|) 3^m / 2`.  The constant gradient `e` has vanishing seminorm and is
  bounded by `‖e‖`.
* Homogenized solutions: the two data solve the constant-coefficient problems with the stated
  forcings.  For the linear datum this is one integration by parts against a zero-trace test
  function; for the quadratic datum the two sides of the weak equation agree pointwise.

Reading the renormalization estimate at these data then gives, on the cube of side `3^m`,

```text
  |u - ell_e| <= 3^m * EB * ‖e‖ ,
  |u - quad_e| <= (3^m)^2 * 5 * EB * ‖e‖ * (sum of |e_i|) ,
```

almost everywhere, the two displays `e.u.minus.v.mean` and `e.u.minus.v.second` of the source.
The effective diffusivity cancels in the second: the field `g` carries the factor `2 sigma`
and the estimate divides by `sigma`.

## Main definitions

* `affineObservable`, `affineGradient` — `e ⬝ x` and its gradient.
* `quadraticObservable`, `quadraticGradient` — `(e ⬝ x)^2` and its gradient.
* `quadraticForcing` — the field `-2 sigma (e ⬝ x) e`.
* `vecCoordSum` — the sum of the absolute values of the coordinates.

## Main results

* `hasGradientOn_affineObservable`, `hasGradientOn_quadraticObservable`.
* `holderSeminormBoundOn_affineGradient`, `holderSeminormBoundOn_smulAffineField`.
* `isDirichletSolutionOn_homogenized_affine`,
  `isDirichletSolutionOn_homogenized_quadratic`.
* `ae_abs_sub_affineObservable_le`, `ae_abs_sub_quadraticObservable_le`.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The observables -/

/-- The linear observable `x ↦ e ⬝ x`. -/
def affineObservable (e : Vec d) : Vec d → ℝ := fun x => vecDot e x

/-- The gradient of the linear observable: the constant field `e`. -/
def affineGradient (e : Vec d) : Vec d → Vec d := fun _ => e

/-- The quadratic observable `x ↦ (e ⬝ x)^2`. -/
def quadraticObservable (e : Vec d) : Vec d → ℝ := fun x => vecDot e x * vecDot e x

/-- The gradient of the quadratic observable: `x ↦ 2 (e ⬝ x) e`. -/
def quadraticGradient (e : Vec d) : Vec d → Vec d := fun x => (2 * vecDot e x) • e

/-- The field whose divergence is the constant right-hand side of the quadratic problem:
`g(x) = -2 sigma (e ⬝ x) e`. -/
def quadraticForcing (sigma : ℝ) (e : Vec d) : Vec d → Vec d :=
  fun x => (-(2 * sigma) * vecDot e x) • e

/-- The sum of the absolute values of the coordinates of a vector; it is the constant relating
the pairing `e ⬝ x` to the supremum norm of `x`. -/
def vecCoordSum (e : Vec d) : ℝ := ∑ i, |e i|

theorem vecCoordSum_nonneg (e : Vec d) : 0 ≤ vecCoordSum e :=
  Finset.sum_nonneg fun i _ ↦ abs_nonneg (e i)

/-- The pairing against a fixed vector is bounded by the coordinate sum times the supremum
norm. -/
theorem abs_vecDot_le_vecCoordSum_mul (e x : Vec d) :
    |vecDot e x| ≤ vecCoordSum e * ‖x‖ := by
  calc |vecDot e x| ≤ ∑ i, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |e i| * ‖x‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = vecCoordSum e * ‖x‖ := by rw [vecCoordSum, Finset.sum_mul]

/-! ## 2. The gradients -/

private theorem slopeCLM_smul (c : ℝ) (A : Vec d) :
    slopeCLM (c • A) = c • slopeCLM A := by
  ext v
  simp only [slopeCLM_apply, smul_apply, smul_eq_mul, vecDot_smul_left]

/-- **The gradient of the linear observable.** -/
theorem hasGradientOn_affineObservable (W : Set (Vec d)) (e : Vec d) :
    HasGradientOn W (affineObservable e) (affineGradient e) := by
  intro y _
  have hL : HasFDerivAt (fun x : Vec d ↦ (slopeCLM e) x) (slopeCLM e) y :=
    (slopeCLM e).hasFDerivAt
  have hshape : (fun x : Vec d ↦ (slopeCLM e) x) = affineObservable e := by
    funext x
    simp only [slopeCLM_apply, affineObservable]
  rw [hshape] at hL
  exact hL.hasFDerivWithinAt

/-- **The gradient of the quadratic observable.** -/
theorem hasGradientOn_quadraticObservable (W : Set (Vec d)) (e : Vec d) :
    HasGradientOn W (quadraticObservable e) (quadraticGradient e) := by
  intro y _
  have hL : HasFDerivAt (fun x : Vec d ↦ (slopeCLM e) x) (slopeCLM e) y :=
    (slopeCLM e).hasFDerivAt
  have hprod := hL.mul hL
  have hshape : ((fun x : Vec d ↦ (slopeCLM e) x) * fun x : Vec d ↦ (slopeCLM e) x) =
      quadraticObservable e := by
    funext x
    simp only [Pi.mul_apply, slopeCLM_apply, quadraticObservable]
  rw [hshape] at hprod
  have hder : (slopeCLM e) y • slopeCLM e + (slopeCLM e) y • slopeCLM e =
      slopeCLM (quadraticGradient e y) := by
    rw [show quadraticGradient e y = (2 * vecDot e y) • e from rfl, slopeCLM_smul]
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul,
      slopeCLM_apply]
    ring
  rw [hder] at hprod
  exact hprod.hasFDerivWithinAt

/-! ## 3. The geometry of the origin cube -/

/-- The supremum norm on the origin cube of scale `m` is below half the side length. -/
theorem norm_lt_of_mem_openCubeSet_originCube {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) : ‖x‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  rw [mem_openCubeSet_originCube_iff] at hx
  refine (pi_norm_lt_iff (by positivity)).2 fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_lt]
  have h1 := (hx i).1
  have h2 := (hx i).2
  constructor
  · linarith only [h1]
  · linarith only [h2]

/-- The diameter of the origin cube of scale `m` in the supremum norm. -/
theorem norm_sub_le_of_mem_openCubeSet_originCube {m : ℤ} {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hz : z ∈ openCubeSet (originCube d m)) :
    ‖x - z‖ ≤ (3 : ℝ) ^ m := by
  have hxb := norm_lt_of_mem_openCubeSet_originCube hx
  have hzb := norm_lt_of_mem_openCubeSet_originCube hz
  calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ (3 : ℝ) ^ m := by linarith only [hxb, hzb]

private theorem three_zpow_rpow_half (m : ℤ) :
    ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) = Real.rpow 3 ((m : ℝ) / 2) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) m, ← Real.rpow_mul h3.le, mul_one_div]
  rfl

/-! ## 4. The Hölder data -/

/-- **The constant gradient has vanishing Hölder seminorm.** -/
theorem holderSeminormBoundOn_affineGradient (W : Set (Vec d)) (e : Vec d) :
    HolderSeminormBoundOn W (1 / 2) 0 (affineGradient e) := by
  intro x _ z _
  simp only [affineGradient, sub_self, norm_zero, zero_mul, le_refl]

/-- **The vanishing field has vanishing Hölder seminorm.** -/
theorem holderSeminormBoundOn_zero_field (W : Set (Vec d)) :
    HolderSeminormBoundOn W (1 / 2) 0 (fun _ : Vec d ↦ (0 : Vec d)) := by
  intro x _ z _
  simp only [sub_self, norm_zero, zero_mul, le_refl]

/-- **The Hölder seminorm of a field proportional to `(e ⬝ x) e` on the origin cube.** -/
theorem holderSeminormBoundOn_smulAffineField (m : ℤ) (c : ℝ) (e : Vec d) :
    HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
      (|c| * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2))
      (fun x ↦ (c * vecDot e x) • e) := by
  intro x hx z hz
  have hdist : ‖x - z‖ ≤ (3 : ℝ) ^ m := norm_sub_le_of_mem_openCubeSet_originCube hx hz
  have hbase : ‖(c * vecDot e x) • e - (c * vecDot e z) • e‖ ≤
      |c| * (‖e‖ * vecCoordSum e) * ‖x - z‖ := by
    have hdotsub : vecDot e (x - z) = vecDot e x - vecDot e z := by
      simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have hsub : (c * vecDot e x) • e - (c * vecDot e z) • e = (c * vecDot e (x - z)) • e := by
      rw [← sub_smul, hdotsub]
      congr 1
      ring
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_mul]
    have hdot : |vecDot e (x - z)| ≤ vecCoordSum e * ‖x - z‖ :=
      abs_vecDot_le_vecCoordSum_mul e (x - z)
    calc |c| * |vecDot e (x - z)| * ‖e‖ ≤ |c| * (vecCoordSum e * ‖x - z‖) * ‖e‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdot (abs_nonneg c)) (norm_nonneg e)
      _ = |c| * (‖e‖ * vecCoordSum e) * ‖x - z‖ := by ring
  have hsplit : ‖x - z‖ ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) = ‖x - z‖ := by
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  have hmono : ‖x - z‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)
  have hcoef : (0 : ℝ) ≤ |c| * (‖e‖ * vecCoordSum e) :=
    mul_nonneg (abs_nonneg c) (mul_nonneg (norm_nonneg e) (vecCoordSum_nonneg e))
  calc ‖(c * vecDot e x) • e - (c * vecDot e z) • e‖
      ≤ |c| * (‖e‖ * vecCoordSum e) * ‖x - z‖ := hbase
    _ = |c| * (‖e‖ * vecCoordSum e) *
          (‖x - z‖ ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ)) := by rw [hsplit]
    _ ≤ |c| * (‖e‖ * vecCoordSum e) *
          (((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) _)
    _ = |c| * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
        rw [three_zpow_rpow_half]
        ring

/-- **The uniform bound for a field proportional to `(e ⬝ x) e` on the origin cube.** -/
theorem norm_smulAffineField_le (m : ℤ) (c : ℝ) (e : Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    ‖(c * vecDot e x) • e‖ ≤ |c| * (‖e‖ * vecCoordSum e) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have hdot : |vecDot e x| ≤ vecCoordSum e * ‖x‖ := abs_vecDot_le_vecCoordSum_mul e x
  have hnorm : ‖x‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    (norm_lt_of_mem_openCubeSet_originCube hx).le
  have hstep : |vecDot e x| ≤ vecCoordSum e * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) :=
    hdot.trans (mul_le_mul_of_nonneg_left hnorm (vecCoordSum_nonneg e))
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  calc |c| * |vecDot e x| * ‖e‖
      ≤ |c| * (vecCoordSum e * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) * ‖e‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep (abs_nonneg c)) (norm_nonneg e)
    _ = |c| * (‖e‖ * vecCoordSum e) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by ring

/-! ## 5. The homogenized solutions -/

private theorem vecDot_matVecMul_smul_one (c : ℝ) (x z : Vec d) :
    vecDot (matVecMul (c • (1 : Mat d)) x) z = c * vecDot x z := by
  have h : matVecMul (c • (1 : Mat d)) x = c • x := by
    funext j
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [h, vecDot_smul_left]

private theorem hasZeroTraceDifferenceOn_self {U : Set (Vec d)} (v : H1Function U) :
    HasZeroTraceDifferenceOn U v v := by
  refine ⟨0, fun x ↦ ?_, fun x ↦ ?_⟩
  · show v.toFun x = v.toFun x + (0 : H1Function U).toFun x
    simp
  · show v.grad x = v.grad x + (0 : H1Function U).grad x
    simp

/-- **The linear observable solves the homogenized problem with vanishing forcing.**  The
constant-coefficient equation for a constant gradient tests to zero against any zero-trace
function, by one integration by parts. -/
theorem isDirichletSolutionOn_homogenized_affine (sigma : ℝ) (m : ℤ) (e : Vec d)
    (v : H1Function (openCubeSet (originCube d m)))
    (hvgrad : ∀ x, v.grad x = affineGradient e x) :
    IsDirichletSolutionOn (fun _ : Vec d ↦ sigma • (1 : Mat d)) (originCube d m) v v
      (fun _ ↦ (0 : Vec d)) := by
  refine ⟨hasZeroTraceDifferenceOn_self v, fun phi ↦ ?_⟩
  have hzero : (∫ x in openCubeSet (originCube d m),
      vecDot ((fun _ : Vec d ↦ (0 : Vec d)) x) (phi.toH1Function.grad x) ∂volume) = 0 := by
    simp only [vecDot_zero_left, integral_zero]
  rw [hzero, neg_zero]
  have hdomain := isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hconst := integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul
    (U := openCubeSet (originCube d m)) hdomain.isOpen.measurableSet hdomain.isBoundedDomain
    (F := fun _ : Vec d ↦ e) (fun _ ↦ contDiff_const) phi
  have hdiv : ∀ x : Vec d, vecFieldDiv (fun _ : Vec d ↦ e) x = 0 := by
    intro x
    rw [vecFieldDiv_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp
  simp only [hdiv, zero_mul, integral_zero, neg_zero] at hconst
  calc (∫ x in openCubeSet (originCube d m),
        vecDot (matVecMul (sigma • (1 : Mat d)) (v.grad x)) (phi.toH1Function.grad x) ∂volume)
      = ∫ x in openCubeSet (originCube d m),
          sigma * vecDot e (phi.toH1Function.grad x) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        show vecDot (matVecMul (sigma • (1 : Mat d)) (v.grad x)) (phi.toH1Function.grad x) =
          sigma * vecDot e (phi.toH1Function.grad x)
        rw [hvgrad x, vecDot_matVecMul_smul_one]
        rfl
    _ = sigma * ∫ x in openCubeSet (originCube d m),
          vecDot e (phi.toH1Function.grad x) ∂volume := integral_const_mul _ _
    _ = 0 := by rw [hconst, mul_zero]

/-- **The quadratic observable solves the homogenized problem with the stated forcing.**  Here
the two sides of the weak equation agree pointwise: the forcing field is exactly minus the
effective diffusivity times the gradient of the observable. -/
theorem isDirichletSolutionOn_homogenized_quadratic (sigma : ℝ) (m : ℤ) (e : Vec d)
    (v : H1Function (openCubeSet (originCube d m)))
    (hvgrad : ∀ x, v.grad x = quadraticGradient e x) :
    IsDirichletSolutionOn (fun _ : Vec d ↦ sigma • (1 : Mat d)) (originCube d m) v v
      (quadraticForcing sigma e) := by
  refine ⟨hasZeroTraceDifferenceOn_self v, fun phi ↦ ?_⟩
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  show vecDot (matVecMul (sigma • (1 : Mat d)) (v.grad x)) (phi.toH1Function.grad x) =
    -vecDot (quadraticForcing sigma e x) (phi.toH1Function.grad x)
  rw [hvgrad x, show quadraticGradient e x = (2 * vecDot e x) • e from rfl,
    vecDot_matVecMul_smul_one, vecDot_smul_left,
    show quadraticForcing sigma e x = (-(2 * sigma) * vecDot e x) • e from rfl,
    vecDot_smul_left]
  ring

/-! ## 6. Reading the renormalization estimate at the two data -/

private theorem three_rpow_neg_eq (m : ℤ) : Real.rpow 3 (-(m : ℝ)) = ((3 : ℝ) ^ m)⁻¹ := by
  show (3 : ℝ) ^ (-(m : ℝ)) = ((3 : ℝ) ^ m)⁻¹
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  exact Real.rpow_intCast 3 m

private theorem three_rpow_half_mul_self (m : ℤ) :
    Real.rpow 3 ((m : ℝ) / 2) * Real.rpow 3 ((m : ℝ) / 2) = (3 : ℝ) ^ m := by
  show (3 : ℝ) ^ ((m : ℝ) / 2) * (3 : ℝ) ^ ((m : ℝ) / 2) = (3 : ℝ) ^ m
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    show (m : ℝ) / 2 + (m : ℝ) / 2 = ((m : ℤ) : ℝ) by ring, Real.rpow_intCast]

/-- **The renormalization estimate at the linear datum.**  With vanishing forcing, vanishing
Hölder seminorm of the constant gradient, and the uniform gradient bound `‖e‖`, the estimate
reads `|u - ell_e| <= 3^m EB ‖e‖`. -/
theorem ae_abs_sub_affineObservable_le {a : CoeffField d} {m : ℤ} {sigmaBarM EB : ℝ}
    (hren : ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn a (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ : Vec d ↦ sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
        Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
          EB * ((sigmaBarM)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
            (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    {e : Vec d} {u h : H1Function (openCubeSet (originCube d m))}
    (hhval : ∀ x, h.toFun x = affineObservable e x)
    (hhgrad : ∀ x, h.grad x = affineGradient e x)
    (hu : IsDirichletSolutionOn a (originCube d m) u h (fun _ ↦ (0 : Vec d))) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |u.toFun x - affineObservable e x| ≤ (3 : ℝ) ^ m * (EB * ‖e‖) := by
  have hgradshape : h.grad = affineGradient e := funext hhgrad
  have hvalshape : h.toFun = affineObservable e := funext hhval
  have hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) 0 h.grad := by
    rw [hgradshape]
    exact holderSeminormBoundOn_affineGradient _ e
  have hKhInf : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ ‖e‖ := by
    intro x _
    rw [hgradshape]
    exact le_rfl
  have hgrad : HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad := by
    rw [hgradshape, hvalshape]
    exact hasGradientOn_affineObservable _ e
  have hv := isDirichletSolutionOn_homogenized_affine sigmaBarM m e h hhgrad
  have hmain := hren u h h (fun _ ↦ (0 : Vec d)) 0 0 ‖e‖ hu hv
    (holderSeminormBoundOn_zero_field _) hKh hKhInf hgrad
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  filter_upwards [hmain] with x hx
  rw [three_rpow_neg_eq] at hx
  simp only [mul_zero, zero_add, add_zero] at hx
  rw [inv_mul_le_iff₀ h3] at hx
  rw [← hhval x]
  exact hx

/-- **The renormalization estimate at the quadratic datum.**  The effective diffusivity
cancels: the forcing field carries the factor `2 sigma` and the estimate divides by `sigma`.
The estimate reads `|u - quad_e| <= 5 (3^m)^2 EB ‖e‖ (sum of |e_i|)`. -/
theorem ae_abs_sub_quadraticObservable_le {a : CoeffField d} {m : ℤ} {sigmaBarM EB : ℝ}
    (hsigma : 0 < sigmaBarM)
    (hren : ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn a (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ : Vec d ↦ sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
        Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
          EB * ((sigmaBarM)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
            (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    {e : Vec d} {u h : H1Function (openCubeSet (originCube d m))}
    (hhval : ∀ x, h.toFun x = quadraticObservable e x)
    (hhgrad : ∀ x, h.grad x = quadraticGradient e x)
    (hu : IsDirichletSolutionOn a (originCube d m) u h (quadraticForcing sigmaBarM e)) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |u.toFun x - quadraticObservable e x| ≤
        ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EB * (‖e‖ * vecCoordSum e)) := by
  have hgradshape : h.grad = quadraticGradient e := funext hhgrad
  have hvalshape : h.toFun = quadraticObservable e := funext hhval
  have hne : sigmaBarM ≠ 0 := ne_of_gt hsigma
  have hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
      (2 * sigmaBarM * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2))
      (quadraticForcing sigmaBarM e) := by
    have hbase := holderSeminormBoundOn_smulAffineField m (-(2 * sigmaBarM)) e
    rw [abs_neg, abs_of_nonneg (by linarith only [hsigma] : (0 : ℝ) ≤ 2 * sigmaBarM)] at hbase
    exact hbase
  have hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
      (2 * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2)) h.grad := by
    have hbase := holderSeminormBoundOn_smulAffineField m 2 e
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hbase
    rw [hgradshape]
    exact hbase
  have hKhInf : ∀ x ∈ openCubeSet (originCube d m),
      ‖h.grad x‖ ≤ ‖e‖ * vecCoordSum e * (3 : ℝ) ^ m := by
    intro x hx
    have hstep := norm_smulAffineField_le m 2 e hx
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hstep
    rw [hgradshape]
    calc ‖quadraticGradient e x‖
        ≤ 2 * (‖e‖ * vecCoordSum e) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := hstep
      _ = ‖e‖ * vecCoordSum e * (3 : ℝ) ^ m := by ring
  have hgrad : HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad := by
    rw [hgradshape, hvalshape]
    exact hasGradientOn_quadraticObservable _ e
  have hv := isDirichletSolutionOn_homogenized_quadratic sigmaBarM m e h hhgrad
  have hmain := hren u h h (quadraticForcing sigmaBarM e)
    (2 * sigmaBarM * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2))
    (2 * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2))
    (‖e‖ * vecCoordSum e * (3 : ℝ) ^ m) hu hv hKg hKh hKhInf hgrad
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hrr := three_rpow_half_mul_self m
  have hbudget : (sigmaBarM)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) *
        (2 * sigmaBarM * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2)) +
      (‖e‖ * vecCoordSum e * (3 : ℝ) ^ m +
        Real.rpow 3 ((m : ℝ) / 2) * (2 * (‖e‖ * vecCoordSum e) * Real.rpow 3 ((m : ℝ) / 2))) =
      5 * (‖e‖ * vecCoordSum e * (3 : ℝ) ^ m) := by
    rw [← hrr]
    field_simp
    ring
  filter_upwards [hmain] with x hx
  rw [hbudget, three_rpow_neg_eq, inv_mul_le_iff₀ h3] at hx
  rw [← hhval x]
  calc |u.toFun x - h.toFun x|
      ≤ (3 : ℝ) ^ m * (EB * (5 * (‖e‖ * vecCoordSum e * (3 : ℝ) ^ m))) := hx
    _ = ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EB * (‖e‖ * vecCoordSum e)) := by ring

end

end Algsuperdiff.Section5.Provider
