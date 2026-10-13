/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# HarmonicGreen

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Green's second identity for the coordinate Laplacian on `Vec d`

Mathlib's harmonic-function layer (`Analysis/InnerProductSpace/Harmonic/*`) is
stated for `InnerProductSpace, which the sup-normed carrier `Vec d` does
**not** satisfy; and Mathlib's only divergence theorem is the box form on `Fin
(n+1) -> R`.  CoarseGraining, however, already carries a *coordinate* Laplacian
on `Vec d` -- `euclideanCoordLaplacian u x = sum_i d_i d_i u x`, built from
`euclideanCoordDeriv i u x = fderiv R u x (basisVec i)` in
`Sobolev/Foundations/EuclideanL2 -- and Mathlib carries a *global*
integration-by-parts identity valid on any finite-dimensional real normed space
with an additive Haar measure, in particular on `Vec d` with Lebesgue measure.

Iterating that identity twice in each coordinate direction and summing gives
Green's second identity for the coordinate Laplacian, with no `EuclideanSpace`
transfer and no boundary term.  This is the pairing that defines the weak
(distributional) formulation of `Delta u = 0`.

## Contents

* `contDiff_euclideanCoordDeriv_of_contDiff_succ` and
  `continuous_euclideanCoordLaplacian_of_contDiff_two` -- the finite-regularity
  companions of CoarseGraining's `C^infty`-only smoothness lemmas.
* `integral_mul_euclideanCoordDeriv_eq_neg_of_contDiff_one` --
  one integration by parts, `int u d_i psi = - int (d_i u) psi`.
* `integral_mul_euclideanCoordSecondDeriv_eq` -- two integrations by parts,
  `int u d_i d_i psi = int (d_i d_i u) psi`.
* `integral_mul_euclideanCoordLaplacian_eq_integral_euclideanCoordLaplacian_mul`
  -- **Green's second identity** `int u (Delta psi) = int (Delta u) psi` for a
  `C^2` function `u` and a compactly supported `C^2` test function `psi`.
* `integral_mul_euclideanCoordLaplacian_eq_zero_of_forall_mem` -- the
  consequence used to feed the weak formulation: if the coordinate Laplacian of
  `u` vanishes on an set containing `tsupport psi`, then the pairing
  `int u (Delta psi)` vanishes.

Every hypothesis is a genuine regularity or support hypothesis on the two
functions; there is no boundary term because the test function has compact
support and the identity is taken over the whole space.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- **Coordinate differentiation at finite regularity.**

CoarseGraining proves `contDiff_euclideanCoordDeriv` only at `C^infty`; the
two-fold integration by parts below needs the finite-level statement that a
coordinate derivative of a `C^{n+1}` function is `C^n`. -/
theorem contDiff_euclideanCoordDeriv_of_contDiff_succ {ψ : Vec d → ℝ} {n : ℕ}
    (hψ : ContDiff ℝ (n + 1 : ℕ) ψ) (i : Fin d) :
    ContDiff ℝ (n : ℕ) (euclideanCoordDeriv i ψ) := by
  have hfd : ContDiff ℝ (n : ℕ) (fderiv ℝ ψ) := by
    refine hψ.fderiv_right ?_
    norm_cast
  exact hfd.clm_apply contDiff_const

/-- Products in which one factor is continuous with compact support and the
other is continuous are integrable. -/
private theorem integrable_mul_of_hasCompactSupport_right {f g : Vec d → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume :=
  (hf.mul hg).integrable_of_hasCompactSupport (hgc.mul_left)

/-- **One integration by parts in a coordinate direction.**

`int u * (d_i psi) = - int (d_i u) * psi`, with no boundary term because `psi`
has compact support.  This is Mathlib's global Haar-measure integration by parts
specialized to the direction `basisVec i` on `Vec d`. -/
theorem integral_mul_euclideanCoordDeriv_eq_neg_of_contDiff_one
    {u ψ : Vec d → ℝ} (hu : ContDiff ℝ (1 : ℕ) u) (hψ : ContDiff ℝ (1 : ℕ) ψ)
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    ∫ x, u x * euclideanCoordDeriv i ψ x ∂volume =
      -∫ x, euclideanCoordDeriv i u x * ψ x ∂volume := by
  have hucont : Continuous u := hu.continuous
  have hψcont : Continuous ψ := hψ.continuous
  have hduc : Continuous (euclideanCoordDeriv i u) :=
    (contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 0) (by exact_mod_cast hu) i).continuous
  have hdψc : Continuous (euclideanCoordDeriv i ψ) :=
    (contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 0) (by exact_mod_cast hψ) i).continuous
  have hdψsupp : HasCompactSupport (euclideanCoordDeriv i ψ) :=
    hasCompactSupport_euclideanCoordDeriv hψc i
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_hasCompactSupport_right hduc hψcont hψc)
    (integrable_mul_of_hasCompactSupport_right hucont hdψc hdψsupp)
    (integrable_mul_of_hasCompactSupport_right hucont hψcont hψc)
    (fun x _ => (hu.differentiable (by simp)).differentiableAt)
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)

/-- **Two integrations by parts in the same coordinate direction.**

`int u * (d_i d_i psi) = int (d_i d_i u) * psi`.  The two sign changes cancel. -/
theorem integral_mul_euclideanCoordSecondDeriv_eq
    {u ψ : Vec d → ℝ} (hu : ContDiff ℝ (2 : ℕ) u) (hψ : ContDiff ℝ (2 : ℕ) ψ)
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    ∫ x, u x * euclideanCoordSecondDeriv i i ψ x ∂volume =
      ∫ x, euclideanCoordSecondDeriv i i u x * ψ x ∂volume := by
  have hu1 : ContDiff ℝ (1 : ℕ) u := hu.of_le (by norm_cast)
  have hψ1 : ContDiff ℝ (1 : ℕ) ψ := hψ.of_le (by norm_cast)
  have hdu : ContDiff ℝ (1 : ℕ) (euclideanCoordDeriv i u) :=
    contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 1) (by exact_mod_cast hu) i
  have hdψ : ContDiff ℝ (1 : ℕ) (euclideanCoordDeriv i ψ) :=
    contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 1) (by exact_mod_cast hψ) i
  have hstep₁ :
      ∫ x, u x * euclideanCoordDeriv i (euclideanCoordDeriv i ψ) x ∂volume =
        -∫ x, euclideanCoordDeriv i u x * euclideanCoordDeriv i ψ x ∂volume :=
    integral_mul_euclideanCoordDeriv_eq_neg_of_contDiff_one
      hu1 hdψ (hasCompactSupport_euclideanCoordDeriv hψc i) i
  have hstep₂ :
      ∫ x, euclideanCoordDeriv i u x * euclideanCoordDeriv i ψ x ∂volume =
        -∫ x, euclideanCoordDeriv i (euclideanCoordDeriv i u) x * ψ x ∂volume :=
    integral_mul_euclideanCoordDeriv_eq_neg_of_contDiff_one
      hdu hψ1 hψc i
  show ∫ x, u x * euclideanCoordDeriv i (euclideanCoordDeriv i ψ) x ∂volume =
    ∫ x, euclideanCoordDeriv i (euclideanCoordDeriv i u) x * ψ x ∂volume
  rw [hstep₁, hstep₂, neg_neg]

/-- The coordinate Laplacian of a `C^2` function is continuous.  CoarseGraining
proves `contDiff_euclideanCoordLaplacian` only at `C^infty`. -/
theorem continuous_euclideanCoordLaplacian_of_contDiff_two {u : Vec d → ℝ}
    (hu : ContDiff ℝ (2 : ℕ) u) : Continuous (euclideanCoordLaplacian u) := by
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  have hdu : ContDiff ℝ (1 : ℕ) (euclideanCoordDeriv i u) :=
    contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 1) (by exact_mod_cast hu) i
  exact (contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 0)
    (by exact_mod_cast hdu) i).continuous

/-- **Green's second identity for the coordinate Laplacian.**

`int u * (Delta psi) = int (Delta u) * psi` for `u` of class `C^2` and a
compactly supported `C^2` test function `psi`.  Summing the two-fold coordinate
integration by parts over the `d` directions. -/
theorem integral_mul_euclideanCoordLaplacian_eq_integral_euclideanCoordLaplacian_mul
    {u ψ : Vec d → ℝ} (hu : ContDiff ℝ (2 : ℕ) u) (hψ : ContDiff ℝ (2 : ℕ) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, u x * euclideanCoordLaplacian ψ x ∂volume =
      ∫ x, euclideanCoordLaplacian u x * ψ x ∂volume := by
  have hucont : Continuous u := hu.continuous
  have hψcont : Continuous ψ := hψ.continuous
  have hdd : ∀ (v : Vec d → ℝ), ContDiff ℝ (2 : ℕ) v → ∀ i : Fin d,
      Continuous (euclideanCoordSecondDeriv i i v) := by
    intro v hv i
    have hdv : ContDiff ℝ (1 : ℕ) (euclideanCoordDeriv i v) :=
      contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 1) (by exact_mod_cast hv) i
    exact (contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 0) (by exact_mod_cast hdv) i).continuous
  have hddsupp : ∀ i : Fin d, HasCompactSupport (euclideanCoordSecondDeriv i i ψ) :=
    fun i =>
      hasCompactSupport_euclideanCoordDeriv
        (hasCompactSupport_euclideanCoordDeriv hψc i) i
  have hleft :
      ∫ x, u x * euclideanCoordLaplacian ψ x ∂volume =
        ∑ i : Fin d, ∫ x, u x * euclideanCoordSecondDeriv i i ψ x ∂volume := by
    have hsum : ∀ x : Vec d,
        u x * euclideanCoordLaplacian ψ x =
          ∑ i : Fin d, u x * euclideanCoordSecondDeriv i i ψ x := by
      intro x
      rw [euclideanCoordLaplacian, Finset.mul_sum]
    simp only [hsum]
    exact integral_finsetSum Finset.univ fun i _ =>
      integrable_mul_of_hasCompactSupport_right hucont (hdd ψ hψ i) (hddsupp i)
  have hright :
      ∫ x, euclideanCoordLaplacian u x * ψ x ∂volume =
        ∑ i : Fin d, ∫ x, euclideanCoordSecondDeriv i i u x * ψ x ∂volume := by
    have hsum : ∀ x : Vec d,
        euclideanCoordLaplacian u x * ψ x =
          ∑ i : Fin d, euclideanCoordSecondDeriv i i u x * ψ x := by
      intro x
      rw [euclideanCoordLaplacian, Finset.sum_mul]
    simp only [hsum]
    exact integral_finsetSum Finset.univ fun i _ =>
      integrable_mul_of_hasCompactSupport_right (hdd u hu i) hψcont hψc
  rw [hleft, hright]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_euclideanCoordSecondDeriv_eq hu hψ hψc i

/-- **The vanishing pairing.**

If the coordinate Laplacian of a `C^2` function `u` vanishes at every point of a
set containing the support of the test function, then the Green pairing
`int u (Delta psi)` vanishes.  This is the statement that a classically harmonic
function is harmonic in the distributional sense. -/
theorem integral_mul_euclideanCoordLaplacian_eq_zero_of_forall_mem
    {U : Set (Vec d)} {u ψ : Vec d → ℝ} (hu : ContDiff ℝ (2 : ℕ) u)
    (hψ : ContDiff ℝ (2 : ℕ) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ U)
    (hzero : ∀ x ∈ U, euclideanCoordLaplacian u x = 0) :
    ∫ x, u x * euclideanCoordLaplacian ψ x ∂volume = 0 := by
  rw [integral_mul_euclideanCoordLaplacian_eq_integral_euclideanCoordLaplacian_mul
    hu hψ hψc]
  have hpt : ∀ x : Vec d, euclideanCoordLaplacian u x * ψ x = 0 := by
    intro x
    by_cases hx : ψ x = 0
    · rw [hx, mul_zero]
    · have hmem : x ∈ U := hsupp (subset_tsupport ψ hx)
      rw [hzero x hmem, zero_mul]
  simp only [hpt, integral_zero]

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
