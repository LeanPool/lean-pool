/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionMeasurable

/-!
# LocalizedMeasurable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The data-side energy estimate, and measurability of the events from that of `E` and `X`

Two things.

*The data-side estimate.*  For a fixed coefficient field the solution depends on
the forcing field Lipschitz-continuously in the energy norm: subtracting the two
weak equations and testing with the difference gives

```text
  ‖∇(u_g − u_{g'})‖_{L²} ≤ lam⁻¹ d ‖g − g'‖_{L²} .
```

This is the linearity input of the countable-subclass reduction.

*The events.*  The good cube event, the event `Q` and the percolation scale are
measurable as soon as the localized error and the localized regularity are
measurable functions of the sample.  This isolates the one remaining input: the
reduction of the suprema over the normalized forcing class to a countable
subclass.

## Main results

* `sqrt_energy_grad_sub_le_data`.
* `measurableSet_goodCubeEvent_of_measurable`,
  `measurableSet_qEvent_of_measurable`,
  `measurable_percolationScaleTotal_of_measurable`.

## References

* ABK26, the localized quantities and the chains of good cubes of Section 5.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The data-side energy estimate -/

private theorem h10Sub_toH1Function'' {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-- **The solution depends on the forcing field Lipschitz-continuously in the
energy norm**, with the dimensional factor of the supremum-norm carrier. -/
theorem sqrt_energy_grad_sub_le_data {y : Vec d} {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {u u' : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (hgL2 : MemVectorL2 (cubeSetAt y n) g) (hg'L2 : MemVectorL2 (cubeSetAt y n) g')
    (hu : IsDirichletSolutionAt a y n u g) (hu' : IsDirichletSolutionAt a y n u' g') :
    Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x - u'.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      lam⁻¹ * (d : ℝ) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖g x - g' x‖ ^ (2 : ℕ) ∂volume) := by
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  obtain ⟨w, hwf, hwg⟩ :
      ∃ w : H10Function (cubeSetAt y n),
        (∀ x, w.toH1Function.toFun x = u.toFun x - u'.toFun x) ∧
          (∀ x, w.toH1Function.grad x = u.grad x - u'.grad x) := by
    obtain ⟨w1, h1f, h1g⟩ := hu.1
    obtain ⟨w2, h2f, h2g⟩ := hu'.1
    refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
    · rw [h1f x, h2f x, h10Sub_toH1Function'']
      simp only [H1Function.sub_toFun]
    · rw [h1g x, h2g x, h10Sub_toH1Function'']
      simp only [H1Function.sub_grad]
  have hwL2 : MemVectorL2 (cubeSetAt y n) w.toH1Function.grad :=
    w.toH1Function.grad_memVectorL2
  have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hAu' : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u'.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u'.grad_memVectorL2
  have hsplitW : ∀ x, matVecMul (a x) (w.toH1Function.grad x) =
      matVecMul (a x) (u.grad x) - matVecMul (a x) (u'.grad x) := by
    intro x
    rw [hwg x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  have hkey : ∫ x in cubeSetAt y n,
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) ∂volume =
      -∫ x in cubeSetAt y n,
        vecDot (g x - g' x) (w.toH1Function.grad x) ∂volume := by
    rw [Section4.Provider.Schauder.integral_vecDot_sub_split hAu hAu' hsplitW w,
      Section4.Provider.Schauder.integral_vecDot_sub_split hgL2 hg'L2
        (fun _ => rfl) w, hu.2 w, hu'.2 w]
    ring
  have hupper := abs_setIntegral_vecDot_le (cubeSetAt y n) (hgL2.sub hg'L2) hwL2
  have hbound : lam * Real.sqrt (∫ x in cubeSetAt y n,
      ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      (d : ℝ) * Real.sqrt (∫ x in cubeSetAt y n, ‖g x - g' x‖ ^ (2 : ℕ) ∂volume) := by
    apply sqrt_setIntegral_sq_norm_le_of_energy_bound hlam.le (by positivity) hEll hwL2
    rw [hkey]
    exact (neg_le_abs _).trans (by simpa only [mul_assoc, Pi.sub_apply] using! hupper)
  have hgrad : (∫ x in cubeSetAt y n, ‖u.grad x - u'.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ‖u.grad x - u'.grad x‖ ^ (2 : ℕ) = ‖w.toH1Function.grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  rw [hgrad, mul_assoc, inv_mul_eq_div, le_div_iff₀ hlam]
  linarith only [hbound]

/-! ## 2. The events, from the measurability of the localized quantities -/

theorem measurableSet_goodCubeEvent_of_measurable (M : ABKModel d) (Creg : ℝ) (n : ℤ)
    (y : Vec d) (ep : ℝ) (hE : Measurable (localizedError M n y))
    (hX : Measurable (localizedRegularity M n y)) :
    MeasurableSet (goodCubeEvent M Creg n y ep) :=
  (measurableSet_le hE measurable_const).inter (measurableSet_le hX measurable_const)

theorem measurableSet_qEvent_of_measurable (M : ABKModel d) (Creg Cinj : ℝ) (n : ℤ)
    (z : Vec d) (ep : ℝ) (hE : Measurable (localizedError M n z))
    (hX : Measurable (localizedRegularity M n z)) :
    MeasurableSet (qEvent M Creg Cinj n z ep) :=
  (measurableSet_goodCubeEvent_of_measurable M Creg n z ep hE hX).inter
    (measurableSet_largeScaleEvent M n z _)

/-- **The percolation scale is measurable as soon as the localized quantities
are.**  This replaces the event-level hypothesis by the structural one. -/
theorem measurable_percolationScaleTotal_of_measurable (M : ABKModel d) (Creg Cinj : ℝ)
    (m : ℤ) (ep : ℝ)
    (hE : ∀ (n : ℤ) (z : Vec d), Measurable (localizedError M n z))
    (hX : ∀ (n : ℤ) (z : Vec d), Measurable (localizedRegularity M n z)) :
    Measurable (percolationScaleTotal M Creg Cinj m ep) :=
  measurable_percolationScaleTotal M Creg Cinj m ep
    fun n z => measurableSet_qEvent_of_measurable M Creg Cinj n z ep (hE n z) (hX n z)

end

end Algsuperdiff.Section5.Support
