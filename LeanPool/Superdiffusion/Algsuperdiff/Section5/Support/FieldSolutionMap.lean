/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CoefficientMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.EnergyPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionSelector

/-!
# FieldSolutionMap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The solution as a function of a continuous coefficient field on the closed cube

The measurability of the localized quantities factors the sample out of the
solution: the sample enters only through the continuous matrix field
`a_m(ω)` restricted to the closed cube, and the solution depends on that field
alone.  This module builds the parameter space and the solution map on it.

The parameter space is the set of continuous matrix fields on `closedCubeAt y n`
whose symmetric part is `ν I`.  It is **closed**, hence measurable — the
skew-symmetry of the shells makes this the exact condition the cutoff
coefficient satisfies — and on a compact carrier every such field is bounded, so
each of them is elliptic on the cube with a lower constant `ν` and an upper
constant of its own.  No ellipticity constant is fixed across the parameter
space, and no fallback branch is used: the field off the closed cube is the
value at the coordinatewise retraction, which is the identity on the cube.

## Main definitions

* `extendCoeff y n A` — the coefficient field of a continuous matrix field on
  the closed cube.
* `ellipticCube nu y n` — the parameter space.
* `solutionOfField` — the solution attached to a parameter.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## 1. The coefficient field of a continuous matrix field -/

/-- The coefficient field determined by a continuous matrix field on the closed
cube: off the cube it is the value at the coordinatewise retraction. -/
def extendCoeff (y : Vec d) (n : ℤ) (A : C(closedCubeAt y n, Mat d)) : CoeffField d :=
  fun x => A ⟨clampTo y n x, clampTo_mem y n x⟩

theorem continuous_extendCoeff (y : Vec d) (n : ℤ) (A : C(closedCubeAt y n, Mat d)) :
    Continuous (extendCoeff y n A) :=
  A.continuous.comp ((continuous_clampTo y n).subtype_mk _)

theorem extendCoeff_apply_of_mem {y : Vec d} {n : ℤ} (A : C(closedCubeAt y n, Mat d))
    {x : Vec d} (hx : x ∈ closedCubeAt y n) : extendCoeff y n A x = A ⟨x, hx⟩ := by
  simp only [extendCoeff]
  congr 1
  exact Subtype.ext (clampTo_eq_self hx)

/-! ## 2. The equation only sees the coefficient on the cube -/

theorem isDivFormWeakSolutionOn_congr_coeff {W : Set (Vec d)} (hW : MeasurableSet W)
    {a b : CoeffField d} (hab : ∀ x ∈ W, a x = b x) {u : H1Function W}
    {g : Vec d → Vec d} (h : IsDivFormWeakSolutionOn a W u g) :
    IsDivFormWeakSolutionOn b W u g := by
  intro phi
  rw [← h phi]
  refine setIntegral_congr_fun hW fun x hx => ?_
  rw [hab x hx]

theorem isDirichletSolutionAt_congr_coeff {y : Vec d} {n : ℤ} {a b : CoeffField d}
    (hab : ∀ x ∈ cubeSetAt y n, a x = b x) {u : H1Function (cubeSetAt y n)}
    {g : Vec d → Vec d} (h : IsDirichletSolutionAt a y n u g) :
    IsDirichletSolutionAt b y n u g :=
  ⟨h.1, isDivFormWeakSolutionOn_congr_coeff (measurableSet_cubeSetAt y n) hab h.2⟩

/-! ## 3. The parameter space -/

/-- The continuous matrix fields on the closed cube whose symmetric part is
`ν I`. -/
def ellipticCube (nu : ℝ) (y : Vec d) (n : ℤ) : Set C(closedCubeAt y n, Mat d) :=
  {A | ∀ z : closedCubeAt y n, symmPart (A z) = nu • (1 : Mat d)}

theorem coefficientCutoffRestrict_mem_ellipticCube (M : ABKModel d) (m : ℤ) (y : Vec d)
    (n : ℤ) (omega : Cutoff.CutoffSample d) :
    coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega ∈ ellipticCube M.nu y n :=
  fun z => Cutoff.symmPart_coefficientCutoff M.nu m omega (z : Vec d)

/-! ## 4. Ellipticity of the extended field -/

theorem exists_isEllipticFieldOn_extendCoeff {nu : ℝ} (hnu : 0 < nu) (y : Vec d) (n : ℤ)
    {A : C(closedCubeAt y n, Mat d)} (hA : A ∈ ellipticCube nu y n) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (cubeSetAt y n) (extendCoeff y n A) := by
  let _ : Norm C(closedCubeAt y n, Mat d) := ContinuousMap.instNorm
  refine ⟨((d : ℝ) * (d : ℝ) * ‖A‖ ^ 2 + nu ^ 2) / nu, ?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    refine Measurable.ite (measurableSet_cubeSetAt y n) ?_ measurable_const
    exact (((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_extendCoeff y n A))).measurable)
  · intro x hx
    have hxK : x ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hx
    rw [extendCoeff_apply_of_mem A hxK]
    refine Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound hnu (hA _) fun i j => ?_
    calc |A ⟨x, hxK⟩ i j| ≤ ‖A ⟨x, hxK⟩‖ := by
          simpa [Real.norm_eq_abs] using
            Matrix.norm_entry_le_entrywise_sup_norm (A := A ⟨x, hxK⟩) (i := i) (j := j)
      _ ≤ ‖A‖ := A.norm_coe_le_norm _

/-! ## 5. The solution attached to a parameter -/

theorem exists_isDirichletSolutionAt_extendCoeff (M : ABKModel d) (y : Vec d) (n : ℤ)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    (A : ellipticCube M.nu y n) :
    ∃ u : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt (extendCoeff y n A.1) y n u g := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_extendCoeff M.nu_pos y n A.2
  exact exists_isDirichletSolutionAt_of_isEllipticFieldOn hEll hKg hg

/-- The solution attached to a parameter. -/
def solutionOfField (M : ABKModel d) (y : Vec d) (n : ℤ) {g : Vec d → Vec d} {Kg : ℝ}
    (hKg : 0 ≤ Kg) (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    (A : ellipticCube M.nu y n) : H1Function (cubeSetAt y n) :=
  (exists_isDirichletSolutionAt_extendCoeff M y n hKg hg A).choose

theorem isDirichletSolutionAt_solutionOfField (M : ABKModel d) (y : Vec d) (n : ℤ)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    (A : ellipticCube M.nu y n) :
    IsDirichletSolutionAt (extendCoeff y n A.1) y n (solutionOfField M y n hKg hg A) g :=
  (exists_isDirichletSolutionAt_extendCoeff M y n hKg hg A).choose_spec

/-- **At the sample's own parameter the two solutions agree.**  The extended
field and the cutoff field coincide on the cube, so the parameter solution
solves the sample's problem. -/
theorem isDirichletSolutionAt_solutionOfField_cutoff (M : ABKModel d) (m : ℤ) (y : Vec d)
    (n : ℤ) (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n
      (solutionOfField M y n hKg hg
        ⟨coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M m y n omega⟩) g := by
  refine isDirichletSolutionAt_congr_coeff (fun x hx => ?_)
    (isDirichletSolutionAt_solutionOfField M y n hKg hg _)
  rw [extendCoeff_apply_of_mem _ (cubeSetAt_subset_closedCubeAt y n hx)]
  rfl

end

end Algsuperdiff.Section5.Support
