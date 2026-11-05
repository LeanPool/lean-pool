/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationApproxForcing

/-!
# HarmonicReplaceForcing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The birth-scale size of the harmonic replacement defect

`HarmonicReplaceExistence` bounds the normalized mean square of the correction
`grad phi = grad w - grad h` by the normalized mean-square deviation of the
forcing field `G` from an **arbitrary** constant.  `OscillationApproxForcing`
bounds the normalized mean-square *oscillation* of a Lipschitz forcing field on a
cube of scale `m` by `sqrt d * M * 3^m`, where `M` bounds the differentials of the
coordinates of `G`.

Choosing the arbitrary constant to be the cube average of `G` joins the two: the
deviation becomes the oscillation, and the harmonic replacement defect inherits
the birth-scale size `3^m`.  That is exactly the hypothesis `hE` of
`OscillationTelescope.le_zpow_mul_add_nsmul_of_nested_decomposition`, whose
cancellation against the arbitrary-gap factor `3^{-j}` is what makes the forcing
in `e.nablaw.oscillations` accumulate linearly in the number of scales.

## Contents

* `memVectorL2_of_differentiable_coord_openCubeAtScale` -- a coordinatewise
  differentiable field is `L^2` on a cube.
* `exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le` -- **the birth-scale atom in
  replacement form**: the harmonic replacement exists and its gradient defect has
  normalized `L^2` size at most `sqrt d * M * 3^m`.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic/oscillation layer of this same
directory.  It mentions no object of the manuscript: no model, no cutoff, no
shell, no corrector, no `sigmaBar`.  The manuscript's factor `sigmaBar^{-1}`
enters only when the abstract forcing `G` of this file is instantiated by the
physical forcing, which happens nowhere here.  It is intended to be portable
into CoarseGraining by a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- A field whose coordinates are differentiable is square integrable on every
cube: it is continuous, hence bounded on the compact closure. -/
theorem memVectorL2_of_differentiable_coord_openCubeAtScale {G : Vec d → Vec d}
    (hG : ∀ i : Fin d, Differentiable ℝ fun y => G y i) (z : Vec d) (m : ℤ) :
    MemVectorL2 (openCubeAtScale z m) G := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z m)) :=
    (isOpenBoundedConvexDomain_openCubeAtScale z m).isFiniteMeasure_restrict_volume
  have hGcont : Continuous G := continuous_pi fun i => (hG i).continuous
  have hcl : IsCompact (closure (openCubeAtScale z m)) :=
    (isOpenBoundedConvexDomain_openCubeAtScale z m).isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ := hcl.exists_bound_of_continuousOn hGcont.continuousOn
  refine MemLp.of_bound hGcont.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (measurableSet_openCubeAtScale z m)]
  exact Filter.Eventually.of_forall fun x hx => hC x (subset_closure hx)

/-- **The birth-scale atom in harmonic-replacement form.**

Let `w` be an `H^1` function on the cube `z + cu_m` which weakly solves
`- Delta w = div G` there, and suppose the differential of every coordinate of the
forcing `G` has operator norm at most `M` on the cube.  Then `w` admits a harmonic
replacement `w - phi` on the cube whose gradient defect obeys

```
  || grad phi ||_{L2bar (z + cu_m)} <= sqrt d * M * 3^m .
```

The proof runs the harmonic replacement of `HarmonicReplaceExistence` with the
recentring constant chosen to be the cube average of `G`, so that the energy bound
is stated against the mean-square *oscillation* of `G`, and then applies the
mean-value forcing atom of `OscillationApproxForcing`. -/
theorem exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le [NeZero d]
    (z : Vec d) (m : ℤ) (w : H1Function (openCubeAtScale z m))
    {G : Vec d → Vec d} {M : ℝ} (hM : 0 ≤ M)
    (hGdiff : ∀ i : Fin d, Differentiable ℝ fun y => G y i)
    (hGbound : ∀ x ∈ openCubeAtScale z m, ∀ i : Fin d,
      ‖fderiv ℝ (fun y => G y i) x‖ ≤ M)
    (hw : ∀ ψ : H10Function (openCubeAtScale z m),
      ∫ x in openCubeAtScale z m, vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeAtScale z m, vecDot (G x) (ψ.toH1Function.grad x) ∂volume) :
    ∃ φ : H10Function (openCubeAtScale z m),
      IsWeaklyHarmonicOn (openCubeAtScale z m) (w - φ.toH1Function).toFun ∧
      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m)
          φ.toH1Function.grad 0) ≤ Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m := by
  have hGL2 : MemVectorL2 (openCubeAtScale z m) G :=
    memVectorL2_of_differentiable_coord_openCubeAtScale hGdiff z m
  obtain ⟨φ, hharm, henergy⟩ :=
    exists_h10Function_isWeaklyHarmonicOn_sub_openCubeAtScale z m w hGL2 hw
      (volumeAverageVec (openCubeAtScale z m) G)
  refine ⟨φ, hharm, ?_⟩
  have hosc : Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m)
      φ.toH1Function.grad 0 ≤
      Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z m) G := henergy
  exact le_trans (Real.sqrt_le_sqrt hosc)
    (sqrt_meanSquareOscillationVecOn_le_of_norm_fderiv_le hM hGdiff z m hGbound)

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
