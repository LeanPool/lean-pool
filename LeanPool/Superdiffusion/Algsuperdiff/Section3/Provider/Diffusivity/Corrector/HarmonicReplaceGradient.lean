/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayWeak
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationMeanSquare
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas

/-!
# HarmonicReplaceGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Identifying the Weyl representative's gradient with the weak gradient

`OscillationDecayWeak` states the per-scale decay for the *smooth interior
representative* `v` of a weakly harmonic function, because the pointwise `fderiv`
of a merely `H^1` function carries no information.  The telescope, however,
accumulates the mean-square oscillations of the **weak gradient** of the harmonic
replacement, since that is the object the energy estimate controls.  This module
closes the gap.

The mechanism is uniqueness of weak derivatives.  On the open set `V` where `v
= h` almost everywhere, both `euclideanGradient v` (because `v` is smooth) and
`grad h` (by restriction from the larger set) are weak gradients of the *same*
function -- the weak-derivative identity only sees its argument through an
integral, so an almost-everywhere change of representative leaves it intact.
CoarseGraining's `HasWeakPartialDerivOn.ae_eq` then identifies them almost
everywhere on `V`, and every mean-square functional in the estimate is an
integral, hence blind to the difference.

A second, smaller mismatch is handled here too.  The interior Weyl lemma needs a
**globally** locally integrable representative, which an `H^1(U)` function is not:
its values off `U` are unconstrained.  Replacing it by its extension by zero
`U.indicator h` removes the mismatch without changing anything: the
weak-harmonicity pairing is an integral over `U` only.

## Contents

* `IsWeaklyHarmonicOn.congr_on` -- weak harmonicity depends only on the values on
  the set.
* `integrable_indicator_of_memL2On` -- the extension by zero of an `L^2` function
  on a finite-measure set is globally integrable.
* `HasWeakPartialDerivOn.congr_ae` -- the weak-derivative identity is stable
  under an almost-everywhere change of the differentiated function.
* `ae_eq_euclideanGradient_of_ae_eq_of_contDiff` -- **the identification**.
* `meanSquareDeviationVecOn_congr_ae`, `volumeAverageVec_congr_ae`,
  `meanSquareOscillationVecOn_congr_ae` -- the mean-square functionals are blind
  to null sets.
* `exists_gradient_oscillation_gap_decay_weakGradient` -- **the payload**: the
  arbitrary-gap decay, stated for the weak gradient of an `H^1` weakly harmonic
  function, which is the form the telescope consumes.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic/oscillation layer of this same
directory.  It mentions no object of the manuscript: no model, no cutoff, no
shell, no corrector, no `sigmaBar`.  It is intended to be portable into
CoarseGraining by a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- Weak harmonicity on `U` depends only on the values of the function on `U`:
the defining pairing is an integral over `U`. -/
theorem IsWeaklyHarmonicOn.congr_on {U : Set (Vec d)} {u u' : Vec d → ℝ}
    (hu : IsWeaklyHarmonicOn U u) (hU : MeasurableSet U)
    (heq : ∀ x ∈ U, u' x = u x) :
    IsWeaklyHarmonicOn U u' := by
  intro ψ hψ hψc hsupp
  have hcongr : ∫ x in U, u' x * euclideanCoordLaplacian ψ x ∂volume =
      ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume := by
    refine setIntegral_congr_fun hU ?_
    intro x hx
    change u' x * euclideanCoordLaplacian ψ x = u x * euclideanCoordLaplacian ψ x
    rw [heq x hx]
  rw [hcongr]
  exact hu ψ hψ hψc hsupp

/-- The extension by zero of an `L^2` function on a finite-measure measurable set
is globally integrable, hence globally locally integrable: exactly the hypothesis
the interior Weyl lemma imposes on its input. -/
theorem integrable_indicator_of_memL2On {U : Set (Vec d)} (hU : MeasurableSet U)
    [IsFiniteMeasure (volumeMeasureOn U)] {u : Vec d → ℝ} (hu : MemL2On U u) :
    Integrable (U.indicator u) volume := by
  rw [integrable_indicator_iff hU]
  exact hu.integrable (by norm_num)

/-- The weak-derivative identity is stable under an almost-everywhere change of
the differentiated function: it sees that function only through an integral. -/
theorem HasWeakPartialDerivOn.congr_ae {U : Set (Vec d)} {i : Fin d}
    {u u' gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)
    (hae : u' =ᵐ[volume.restrict U] u) :
    HasWeakPartialDerivOn U i u' gi := by
  intro φ hφ hφc hsupp
  have hcongr : ∫ x in U, u' x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hcongr]
  exact h φ hφ hφc hsupp

/-- **Identification of the two gradients.**

If a `C^1` function `v` agrees almost everywhere on an open subset `V` of `U`
with an `H^1(U)` function `h`, then the pointwise Euclidean gradient of `v`
agrees almost everywhere on `V` with the weak gradient of `h`.

Both fields are weak gradients of the same function on `V` -- the first because
`v` is `C^1`, the second by restriction from `U` followed by the
almost-everywhere transport above -- and weak gradients are almost everywhere
unique on open sets. -/
theorem ae_eq_euclideanGradient_of_ae_eq_of_contDiff {U V : Set (Vec d)}
    (hV : IsOpen V) (hVU : V ⊆ U) [IsFiniteMeasure (volumeMeasureOn V)]
    (h : H1Function U) {v : Vec d → ℝ} (hv : ContDiff ℝ 1 v)
    (hae : v =ᵐ[volume.restrict V] h.toFun) :
    euclideanGradient v =ᵐ[volume.restrict V] h.grad := by
  have hgv : HasWeakGradientOn V v (euclideanGradient v) :=
    HasWeakGradientOn.of_contDiff hv
  have hgh : ∀ i : Fin d,
      HasWeakPartialDerivOn V i v (fun x => h.grad x i) := fun i =>
    HasWeakPartialDerivOn.congr_ae
      (HasWeakPartialDerivOn.restrict hV hVU (h.hasWeakGradient i)) hae
  have hlocv : ∀ i : Fin d,
      LocallyIntegrableOn (fun x => euclideanGradient v x i) V volume := by
    intro i
    have hcont : Continuous (fun x => euclideanGradient v x i) := by
      simpa [euclideanGradient, euclideanCoordDeriv] using
        (hv.continuous_fderiv (by simp)).clm_apply (continuous_const (y := basisVec i))
    exact hcont.locallyIntegrable.locallyIntegrableOn V
  have hloch : ∀ i : Fin d,
      LocallyIntegrableOn (fun x => h.grad x i) V volume := by
    intro i
    have hL2 : MemL2On V (fun x => h.grad x i) := memL2On_mono hVU (h.grad_memL2 i)
    have hint : IntegrableOn (fun x => h.grad x i) V volume :=
      hL2.integrable (by norm_num)
    exact hint.locallyIntegrableOn
  have hcoord : ∀ i : Fin d,
      (fun x => euclideanGradient v x i) =ᵐ[volume.restrict V] fun x => h.grad x i :=
    fun i => HasWeakPartialDerivOn.ae_eq hV (hlocv i) (hloch i) (hgv i) (hgh i)
  have hall : ∀ᵐ x ∂(volume.restrict V), ∀ i : Fin d,
      euclideanGradient v x i = h.grad x i := ae_all_iff.2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- Mean-square deviation of a vector field is blind to null sets. -/
theorem meanSquareDeviationVecOn_congr_ae {V : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volume.restrict V] g) (c : Vec d) :
    Book.Ch01.meanSquareDeviationVecOn V f c =
      Book.Ch01.meanSquareDeviationVecOn V g c := by
  refine Finset.sum_congr rfl fun k _ => ?_
  change volumeAverage V (fun y => (f y k - c k) ^ 2) =
    volumeAverage V (fun y => (g y k - c k) ^ 2)
  unfold volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The volume average of a vector field is blind to null sets. -/
theorem volumeAverageVec_congr_ae {V : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volume.restrict V] g) :
    volumeAverageVec V f = volumeAverageVec V g := by
  funext i
  change volumeAverage V (fun x => f x i) = volumeAverage V (fun x => g x i)
  unfold volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [hx]

/-- Mean-square oscillation of a vector field is blind to null sets. -/
theorem meanSquareOscillationVecOn_congr_ae {V : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volume.restrict V] g) :
    Book.Ch01.meanSquareOscillationVecOn V f =
      Book.Ch01.meanSquareOscillationVecOn V g := by
  change Book.Ch01.meanSquareDeviationVecOn V f (volumeAverageVec V f) =
    Book.Ch01.meanSquareDeviationVecOn V g (volumeAverageVec V g)
  rw [volumeAverageVec_congr_ae hfg]
  exact meanSquareDeviationVecOn_congr_ae hfg _

/-- **The arbitrary-gap oscillation decay for the weak gradient.**

For an `H^1` function on the cube `z + cu_{n+k}` which is weakly harmonic there,
the normalized mean-square oscillation of its **weak gradient** on `z + cu_n`
decays like `3^{-k}` relative to the deviation of the same weak gradient on
`z + cu_{n+k-1}`, for every gap `k >= d + 3` and every constant `c`.

This is `OscillationDecayWeak`'s estimate with the smooth interior representative
eliminated: the extension by zero supplies the global local integrability that the
interior Weyl lemma needs, and the gradient identification above replaces
`euclideanGradient v` by `grad h` inside both mean-square functionals. -/
theorem exists_gradient_oscillation_gap_decay_weakGradient (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (n : ℤ) (k : ℕ), d + 3 ≤ k →
      ∀ h : H1Function (openCubeAtScale z (n + (k : ℤ))),
        IsWeaklyHarmonicOn (openCubeAtScale z (n + (k : ℤ))) h.toFun →
        ∀ c : Vec d,
          Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) h.grad)
            ≤ C * (3 : ℝ) ^ (-(k : ℤ)) *
              Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                (openCubeAtScale z (n + (k : ℤ) - 1)) h.grad c) := by
  obtain ⟨C, hCnn, hdec⟩ := exists_gradient_oscillation_gap_decay_of_isWeaklyHarmonicOn hd
  refine ⟨C, hCnn, ?_⟩
  intro z n k hk h hw c
  have hUfin : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z (n + (k : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_openCubeAtScale_ne_top z (n + (k : ℤ)))
  have hVfin : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z (n + (k : ℤ) - 1))) :=
    isFiniteMeasure_restrict.mpr (volume_openCubeAtScale_ne_top z (n + (k : ℤ) - 1))
  have hVU : openCubeAtScale z (n + (k : ℤ) - 1) ⊆ openCubeAtScale z (n + (k : ℤ)) :=
    openCubeAtScale_subset_of_le z (by omega)
  have hnV : openCubeAtScale z n ⊆ openCubeAtScale z (n + (k : ℤ) - 1) :=
    openCubeAtScale_subset_of_le z (by omega)
  have hueq : ∀ x ∈ openCubeAtScale z (n + (k : ℤ)),
      (openCubeAtScale z (n + (k : ℤ))).indicator h.toFun x = h.toFun x :=
    fun x hx => Set.indicator_of_mem hx _
  have huw : IsWeaklyHarmonicOn (openCubeAtScale z (n + (k : ℤ)))
      ((openCubeAtScale z (n + (k : ℤ))).indicator h.toFun) :=
    hw.congr_on (measurableSet_openCubeAtScale z (n + (k : ℤ))) hueq
  have huloc : LocallyIntegrable
      ((openCubeAtScale z (n + (k : ℤ))).indicator h.toFun) volume :=
    (integrable_indicator_of_memL2On
      (measurableSet_openCubeAtScale z (n + (k : ℤ))) h.memL2).locallyIntegrable
  obtain ⟨v, hvs, hvae, hbound⟩ := hdec _ huloc z n k hk huw
  have hvh : v =ᵐ[volume.restrict (openCubeAtScale z (n + (k : ℤ) - 1))] h.toFun := by
    rw [Filter.EventuallyEq, ae_restrict_iff'
      (measurableSet_openCubeAtScale z (n + (k : ℤ) - 1))]
    filter_upwards [hvae] with x hx
    intro hxV
    rw [hx hxV, hueq x (hVU hxV)]
  have hgrad : euclideanGradient v =ᵐ[volume.restrict
      (openCubeAtScale z (n + (k : ℤ) - 1))] h.grad :=
    ae_eq_euclideanGradient_of_ae_eq_of_contDiff
      (isOpen_openCubeAtScale z (n + (k : ℤ) - 1)) hVU h (hvs.of_le (by simp)) hvh
  have hgradn : euclideanGradient v =ᵐ[volume.restrict (openCubeAtScale z n)] h.grad :=
    ae_restrict_of_ae_restrict_of_subset hnV hgrad
  have hbnd := hbound c
  rw [meanSquareOscillationVecOn_congr_ae hgradn,
    meanSquareDeviationVecOn_congr_ae hgrad c] at hbnd
  exact hbnd

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
