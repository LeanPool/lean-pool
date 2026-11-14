/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicGreen
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# HarmonicWeak

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak (distributional) harmonicity on `Vec d`

Mathlib's `InnerProductSpace.HarmonicAt` is a `C^2`-strong notion on an inner
product space, so it is unavailable on the sup-normed carrier `Vec d` and it
cannot express harmonicity of a merely locally integrable function.
CoarseGraining carries the *variational* notion (`IsAHarmonicGradient`, phrased
through `H1Function` and `IsSolenoidalOn`) but no distributional one.

This module fixes the distributional predicate directly on `Vec d`, using
CoarseGraining's coordinate Laplacian and the Green pairing of `HarmonicGreen`:

```
  IsWeaklyHarmonicOn U u  <->  int_U u * (Delta psi) = 0
      for every  psi in C_c^infty  with  tsupport psi subset U .
```

and proves one half of its consistency with the classical notion: a `C^2`
function that is weakly harmonic on an open set has vanishing coordinate
Laplacian there.  Green's identity turns the defining pairing into
`int (Delta u) psi = 0` for every test function supported in `U`; the
fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) then gives
`Delta u = 0` almost everywhere on `U`, and continuity upgrades that from
"almost everywhere on `U`" to "everywhere on `U`".

Only that half and the elementary stability properties are proved
here.  The two substantial theorems about the predicate -- the mean value
property and Weyl's lemma (a weakly harmonic function agrees a.e. with a smooth
one) -- are **not** proved here and are not assumed anywhere below.

## Contents

* `IsWeaklyHarmonicOn` -- the predicate.
* `setIntegral_mul_euclideanCoordLaplacian_eq_integral` -- the Green pairing over
  `U` agrees with the pairing over the whole space, because the test function is
  supported in `U`.
* `IsWeaklyHarmonicOn.euclideanCoordLaplacian_eq_zero` -- weak plus `C^2` implies
  classical, on an open set.
* `IsWeaklyHarmonicOn.mono`, `IsWeaklyHarmonicOn.const_mul` -- stability under
  shrinking the set and under scalar multiples.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- **Weak (distributional) harmonicity on an open set.**

`u` is weakly harmonic on `U` when its Green pairing against the coordinate
Laplacian of every compactly supported smooth test function supported in `U`
vanishes.  The test-function class and the `int_U` convention are those of
CoarseGraining's `HasWeakPartialDerivOn`, so the predicate composes with
CoarseGraining's weak-derivative layer without translation. -/
def IsWeaklyHarmonicOn (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ U → ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume = 0

/-- The Green pairing over `U` is the Green pairing over the whole space: the
integrand vanishes off `tsupport psi`, which is contained in `U`. -/
theorem setIntegral_mul_euclideanCoordLaplacian_eq_integral {U : Set (Vec d)}
    (u : Vec d → ℝ) {ψ : Vec d → ℝ} (hsupp : tsupport ψ ⊆ U) :
    ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume =
      ∫ x, u x * euclideanCoordLaplacian ψ x ∂volume := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro x hx
  have hxs : x ∉ tsupport ψ := fun hmem => hx (hsupp hmem)
  have hzero : euclideanCoordLaplacian ψ x = 0 := by
    by_contra hne
    exact hxs (support_euclideanCoordLaplacian_subset_tsupport ψ
      (Function.mem_support.mpr hne))
  rw [hzero, mul_zero]

/-- Weak harmonicity restricts to subsets. -/
theorem IsWeaklyHarmonicOn.mono {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hu : IsWeaklyHarmonicOn U u) (hVU : V ⊆ U) : IsWeaklyHarmonicOn V u := by
  intro ψ hψ hψc hsupp
  rw [setIntegral_mul_euclideanCoordLaplacian_eq_integral u hsupp,
    ← setIntegral_mul_euclideanCoordLaplacian_eq_integral u (hsupp.trans hVU)]
  exact hu ψ hψ hψc (hsupp.trans hVU)

/-- **Weak plus `C^2` implies classical.**

If `u` is of class `C^2` and weakly harmonic on an open set `U`, then its
coordinate Laplacian vanishes at every point of `U`.  Green's identity turns the
defining pairing into `int (Delta u) psi = 0` for every test function supported
in `U`; the fundamental lemma of the calculus of variations then gives
`Delta u = 0` almost everywhere on `U`, and continuity of `Delta u` upgrades
this to every point of the open set `U`. -/
theorem IsWeaklyHarmonicOn.euclideanCoordLaplacian_eq_zero {U : Set (Vec d)}
    (hU : IsOpen U) {u : Vec d → ℝ} (hu : ContDiff ℝ (2 : ℕ) u)
    (hw : IsWeaklyHarmonicOn U u) :
    ∀ x ∈ U, euclideanCoordLaplacian u x = 0 := by
  have hcont : Continuous (euclideanCoordLaplacian u) :=
    continuous_euclideanCoordLaplacian_of_contDiff_two hu
  have hloc : LocallyIntegrableOn (euclideanCoordLaplacian u) U volume :=
    hcont.locallyIntegrable.locallyIntegrableOn U
  have hae : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ U → euclideanCoordLaplacian u x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro ψ hψ hψc hsupp
    have hzero := hw ψ hψ hψc hsupp
    rw [setIntegral_mul_euclideanCoordLaplacian_eq_integral u hsupp,
      integral_mul_euclideanCoordLaplacian_eq_integral_euclideanCoordLaplacian_mul
        hu (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hψc] at hzero
    calc ∫ x, ψ x • euclideanCoordLaplacian u x ∂volume
        = ∫ x, euclideanCoordLaplacian u x * ψ x ∂volume := by
          simp only [smul_eq_mul, mul_comm]
      _ = 0 := hzero
  intro x hx
  by_contra hne
  have hVopen : IsOpen (U ∩ (euclideanCoordLaplacian u) ⁻¹' ({0}ᶜ)) :=
    hU.inter (isOpen_compl_singleton.preimage hcont)
  have hxV : x ∈ U ∩ (euclideanCoordLaplacian u) ⁻¹' ({0}ᶜ) := ⟨hx, hne⟩
  have hVpos : 0 < volume (U ∩ (euclideanCoordLaplacian u) ⁻¹' ({0}ᶜ)) :=
    hVopen.measure_pos volume ⟨x, hxV⟩
  have hsub : U ∩ (euclideanCoordLaplacian u) ⁻¹' ({0}ᶜ) ⊆
      {y : Vec d | ¬(y ∈ U → euclideanCoordLaplacian u y = 0)} := by
    rintro y ⟨hyU, hyne⟩
    exact fun himp => hyne (himp hyU)
  exact absurd (measure_mono_null hsub (ae_iff.mp hae)) hVpos.ne'

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
