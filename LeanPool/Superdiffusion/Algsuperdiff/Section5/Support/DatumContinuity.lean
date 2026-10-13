/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderL2Interpolation
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionLinearity

/-!
# DatumContinuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The difference of two solutions of the same localized problem

For a fixed elliptic coefficient field on `y + □_n` the difference of the
solutions of two Dirichlet problems with the same zero boundary condition is
itself a zero-trace function on the cube, and a uniform bound on the difference
of the two data is an `L²` bound on the cube.

Those are the two steps a continuity estimate in the datum starts from: the
energy estimate carries the `L²` size of the datum difference to the gradient of
the difference of the solutions, and the zero-trace Poincaré inequality carries
it back to the `L²` size of the difference itself.

## Main results

* `exists_h10Function_sub` — the zero-trace witness of a difference of
  solutions.
* `setIntegral_sq_le_of_forall_norm_le` — a uniform bound gives an `L²` bound.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero-trace witness of a difference of solutions -/

/-- **The difference of two solutions of the same localized problem has a
zero-trace witness**, whatever the two forcing fields are. -/
theorem exists_h10Function_sub {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u u' : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (hu : IsDirichletSolutionAt a y n u g) (hu' : IsDirichletSolutionAt a y n u' g') :
    ∃ w : H10Function (cubeSetAt y n),
      (∀ x, w.toH1Function.toFun x = u.toFun x - u'.toFun x) ∧
        (∀ x, w.toH1Function.grad x = u.grad x - u'.grad x) := by
  obtain ⟨w1, h1f, h1g⟩ := hu.1
  obtain ⟨w2, h2f, h2g⟩ := hu'.1
  refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
  · rw [h1f x, h2f x]
    show (w1.toH1Function - w2.toH1Function).toFun x = _
    simp only [H1Function.sub_toFun]
  · rw [h1g x, h2g x]
    show (w1.toH1Function - w2.toH1Function).grad x = _
    simp only [H1Function.sub_grad]

/-! ## 2. A uniform bound on the cube is an `L²` bound -/

/-- **A uniformly small field on the cube is small in `L²` there.** -/
theorem setIntegral_sq_le_of_forall_norm_le {y : Vec d} {n : ℤ} {f : Vec d → Vec d}
    {eta : ℝ} (hf : ∀ x ∈ cubeSetAt y n, ‖f x‖ ≤ eta) :
    ∫ x in cubeSetAt y n, ‖f x‖ ^ (2 : ℕ) ∂volume ≤
      volume.real (cubeSetAt y n) * eta ^ (2 : ℕ) := by
  have hcubefin : volume (cubeSetAt y n) ≠ ⊤ :=
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
  have hconstInt : IntegrableOn (fun _ : Vec d => eta ^ (2 : ℕ)) (cubeSetAt y n) volume :=
    integrableOn_const hcubefin
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => by positivity) hconstInt
    ((ae_restrict_iff' (measurableSet_cubeSetAt y n)).2
      (Filter.Eventually.of_forall fun x hx =>
        pow_le_pow_left₀ (norm_nonneg _) (hf x hx) 2))
  rwa [setIntegral_const, smul_eq_mul] at hmono

end

end Algsuperdiff.Section5.Support
