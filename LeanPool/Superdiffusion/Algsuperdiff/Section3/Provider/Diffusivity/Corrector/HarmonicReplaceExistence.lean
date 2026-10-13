/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationCubeFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceDirichlet
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# HarmonicReplaceExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Harmonic replacement, and the energy minimality of the correction

Let `w` be an `H^1` function on a bounded open convex domain `U` which solves, in
the weak sense against `H^1_0 (U)` competitors, a Laplace equation with
divergence-form right-hand side,

```
  int_U <grad w, grad psi> = int_U <G, grad psi>   for every  psi in H^1_0 (U) .
```

Subtracting from `w` the `H^1_0` potential `phi` of the *recentred* forcing
`G - c` produces `h := w - phi`, and the two weak formulations cancel exactly:
the residual pairing is `int_U <c, grad psi>`, which vanishes because the mean
gradient of a zero-trace function is zero.  Thus `h` is variationally harmonic,
hence -- through `HarmonicReplaceBridge` -- weakly harmonic in the distributional
sense that the interior Weyl lemma and the oscillation decay consume.

The same solve is energy-minimal: testing the equation for `phi` against `phi`
itself gives `int |grad phi|^2 = int <G - c, grad phi>`, and expanding the
nonnegative square `int |(G - c) - grad phi|^2 >= 0` turns that identity into

```
  int_U |grad w - grad h|^2 = int_U |grad phi|^2 <= int_U |G - c|^2 ,
```

for **every** constant `c`.  Dividing by `|U|` states it as a comparison of
normalized mean squares, which is the shape the oscillation telescope consumes:
the deviation of the correction is bounded by the deviation of the forcing from
an arbitrary constant, in particular from its own average.

No Cauchy-Schwarz inequality and no Poincare inequality is used; the argument is
the completed square only.

## Contents

* `vecDot_sub_left'`, `vecNormSq_sub_eq` -- the pointwise algebra of the
  completed square in the coordinate inner product.
* `isOpenBoundedConvexDomain_openCubeAtScale` -- the concentric cubes of the
  oscillation family belong to the domain class of the solve.
* `exists_h10Function_isWeaklyHarmonicOn_sub` -- **the harmonic replacement**,
  with the energy bound, on an abstract bounded open convex domain.
* `exists_h10Function_isWeaklyHarmonicOn_sub_openCubeAtScale` -- the same on a
  concentric cube, with the energy bound in normalized mean-square form.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- Left additivity of the coordinate inner product in subtracted form. -/
theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  show ∑ i : Fin d, (x - y) i * z i =
    (∑ i : Fin d, x i * z i) - ∑ i : Fin d, y i * z i
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (x - y) i = x i - y i := rfl
  rw [hsub]
  ring

/-- The completed square in the coordinate inner product. -/
theorem vecNormSq_sub_eq (a b : Vec d) :
    vecNormSq (a - b) = vecNormSq a - 2 * vecDot a b + vecNormSq b := by
  have hexp : ∀ v : Vec d, vecNormSq v = ∑ i : Fin d, v i * v i := fun _ => rfl
  have hdot : vecDot a b = ∑ i : Fin d, a i * b i := rfl
  rw [hexp, hexp, hexp, hdot, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (a - b) i = a i - b i := rfl
  rw [hsub]
  ring

/-- The concentric cube `z + cu_m` is a bounded open convex domain, hence a legal
domain for the Laplace-Dirichlet solve. -/
theorem isOpenBoundedConvexDomain_openCubeAtScale (z : Vec d) (m : ℤ) :
    IsOpenBoundedConvexDomain (openCubeAtScale z m) := by
  refine ⟨isOpen_openCubeAtScale z m, ⟨‖z‖ + (3 : ℝ) ^ m, ?_, ?_⟩,
    convex_openCubeAtScale z m⟩
  · have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    linarith
  · intro x hx i
    have hxi : |x i - z i| < (3 : ℝ) ^ m / 2 := (mem_openCubeAtScale_iff z m x).mp hx i
    have hzi : |z i| ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
    have htri : |x i| ≤ |x i - z i| + |z i| := by
      have hxeq : x i = (x i - z i) + z i := by ring
      calc |x i| = |(x i - z i) + z i| := by rw [← hxeq]
        _ ≤ |x i - z i| + |z i| := abs_add_le _ _
    have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
    linarith

/-- **Harmonic replacement with energy minimality.**

Let `w` be an `H^1` function on a nonempty bounded open convex domain `U` which
weakly solves `- Delta w = div G` against `H^1_0 (U)` competitors, and let `c` be
an arbitrary constant vector.  Then there is `phi in H^1_0 (U)` such that

* `w - phi` is weakly harmonic on `U` in the distributional sense of
  `HarmonicWeak`, and
* `int_U |grad phi|^2 <= int_U |G - c|^2`.

The first conclusion is the cancellation of the two weak formulations, using that
a constant pairs to zero with the gradient of a zero-trace function; the second is
the completed square. -/
theorem exists_h10Function_isWeaklyHarmonicOn_sub [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (w : H1Function U)
    {G : Vec d → Vec d} (hG : MemVectorL2 U G)
    (hw : ∀ ψ : H10Function U,
      ∫ x in U, vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (ψ.toH1Function.grad x) ∂volume)
    (c : Vec d) :
    ∃ φ : H10Function U,
      IsWeaklyHarmonicOn U (w - φ.toH1Function).toFun ∧
      ∫ x in U, vecNormSq (φ.toH1Function.grad x) ∂volume ≤
        ∫ x in U, vecNormSq (G x - c) ∂volume := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hGc : MemVectorL2 U (fun x => G x - c) := hG.sub (memVectorL2_const c)
  obtain ⟨φ, hφ⟩ := exists_h10Function_integral_vecDot_grad_eq hU hne hGc
  refine ⟨φ, ?_, ?_⟩
  · -- variational harmonicity of `w - phi`, then the bridge
    refine isWeaklyHarmonicOn_of_forall_h10Function_integral_vecDot_grad_eq_zero
      hU.isOpen (w - φ.toH1Function) ?_
    intro ψ
    have hsplit : (fun x => vecDot ((w - φ.toH1Function).grad x) (ψ.toH1Function.grad x)) =
        fun x => vecDot (w.grad x) (ψ.toH1Function.grad x) -
          vecDot (φ.toH1Function.grad x) (ψ.toH1Function.grad x) := by
      funext x
      rw [H1Function.sub_grad]
      exact vecDot_sub_left' _ _ _
    have hint₁ : IntegrableOn
        (fun x => vecDot (w.grad x) (ψ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2
    have hint₂ : IntegrableOn
        (fun x => vecDot (φ.toH1Function.grad x) (ψ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 φ.toH1Function.grad_memVectorL2
        ψ.toH1Function.grad_memVectorL2
    rw [hsplit, integral_sub hint₁ hint₂, hw ψ, hφ ψ,
      integral_vecDot_sub_const_zeroTraceGrad_eq hG ψ c, sub_self]
  · -- the completed square
    have hAmem : MemVectorL2 U φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
    have hAA : IntegrableOn
        (fun x => vecNormSq (φ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hAmem hAmem
    have hBB : IntegrableOn (fun x => vecNormSq (G x - c)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hGc hGc
    have hBA : IntegrableOn
        (fun x => vecDot (G x - c) (φ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hGc hAmem
    have hAB : ∫ x in U, vecNormSq (φ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x - c) (φ.toH1Function.grad x) ∂volume := hφ φ
    have hnn : 0 ≤ ∫ x in U, vecNormSq ((G x - c) - φ.toH1Function.grad x) ∂volume :=
      integral_nonneg fun x => vecNormSq_nonneg _
    have hexpand : ∫ x in U, vecNormSq ((G x - c) - φ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecNormSq (G x - c) ∂volume -
          2 * ∫ x in U, vecDot (G x - c) (φ.toH1Function.grad x) ∂volume +
          ∫ x in U, vecNormSq (φ.toH1Function.grad x) ∂volume := by
      have hpt : ∀ x : Vec d, vecNormSq ((G x - c) - φ.toH1Function.grad x) =
          vecNormSq (G x - c) - 2 * vecDot (G x - c) (φ.toH1Function.grad x) +
            vecNormSq (φ.toH1Function.grad x) := fun x => vecNormSq_sub_eq _ _
      have hmul2 : IntegrableOn
          (fun x => 2 * vecDot (G x - c) (φ.toH1Function.grad x)) U volume :=
        hBA.const_mul 2
      have hsubint : IntegrableOn
          (fun x => vecNormSq (G x - c) -
            2 * vecDot (G x - c) (φ.toH1Function.grad x)) U volume :=
        hBB.sub hmul2
      have h1 : ∫ x in U, (vecNormSq (G x - c) -
            2 * vecDot (G x - c) (φ.toH1Function.grad x) +
            vecNormSq (φ.toH1Function.grad x)) ∂volume =
          (∫ x in U, (vecNormSq (G x - c) -
            2 * vecDot (G x - c) (φ.toH1Function.grad x)) ∂volume) +
            ∫ x in U, vecNormSq (φ.toH1Function.grad x) ∂volume :=
        integral_add hsubint hAA
      have h2 : ∫ x in U, (vecNormSq (G x - c) -
            2 * vecDot (G x - c) (φ.toH1Function.grad x)) ∂volume =
          (∫ x in U, vecNormSq (G x - c) ∂volume) -
            ∫ x in U, 2 * vecDot (G x - c) (φ.toH1Function.grad x) ∂volume :=
        integral_sub hBB hmul2
      have h3 : ∫ x in U, 2 * vecDot (G x - c) (φ.toH1Function.grad x) ∂volume =
          2 * ∫ x in U, vecDot (G x - c) (φ.toH1Function.grad x) ∂volume :=
        integral_const_mul 2 _
      simp only [hpt]
      rw [h1, h2, h3]
    linarith

/-- **Harmonic replacement on a concentric cube, in normalized mean-square form.**

The specialization of the previous theorem to `U = z + cu_m`, with the energy
bound divided by the volume of the cube so that both sides are the normalized
mean squares that the oscillation telescope compares.  Taking `c` to be the
average of `G` on the cube turns the right-hand side into
`meanSquareOscillationVecOn (z + cu_m) G`, which is the quantity the birth-scale
forcing atom of `OscillationApproxForcing` bounds. -/
theorem exists_h10Function_isWeaklyHarmonicOn_sub_openCubeAtScale [NeZero d]
    (z : Vec d) (m : ℤ) (w : H1Function (openCubeAtScale z m))
    {G : Vec d → Vec d} (hG : MemVectorL2 (openCubeAtScale z m) G)
    (hw : ∀ ψ : H10Function (openCubeAtScale z m),
      ∫ x in openCubeAtScale z m, vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeAtScale z m, vecDot (G x) (ψ.toH1Function.grad x) ∂volume)
    (c : Vec d) :
    ∃ φ : H10Function (openCubeAtScale z m),
      IsWeaklyHarmonicOn (openCubeAtScale z m) (w - φ.toH1Function).toFun ∧
      Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m)
          φ.toH1Function.grad 0 ≤
        Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m) G c := by
  have hU := isOpenBoundedConvexDomain_openCubeAtScale z m
  have : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z m)) :=
    hU.isFiniteMeasure_restrict_volume
  have hne : (openCubeAtScale z m).Nonempty := by
    refine ⟨z, ?_⟩
    rw [mem_openCubeAtScale_iff]
    intro i
    simpa using half_pos (zpow_three_pos m)
  obtain ⟨φ, hharm, henergy⟩ :=
    exists_h10Function_isWeaklyHarmonicOn_sub hU hne w hG hw c
  refine ⟨φ, hharm, ?_⟩
  have hAmem : MemVectorL2 (openCubeAtScale z m) φ.toH1Function.grad :=
    φ.toH1Function.grad_memVectorL2
  rw [Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub_of_memVectorL2
      hAmem 0,
    Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub_of_memVectorL2 hG c]
  have hzero : ∀ x : Vec d, φ.toH1Function.grad x - 0 = φ.toH1Function.grad x :=
    fun x => sub_zero _
  show (volume (openCubeAtScale z m)).toReal⁻¹ *
      ∫ x in openCubeAtScale z m, vecNormSq (φ.toH1Function.grad x - 0) ∂volume ≤
    (volume (openCubeAtScale z m)).toReal⁻¹ *
      ∫ x in openCubeAtScale z m, vecNormSq (G x - c) ∂volume
  simp only [hzero]
  exact mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr ENNReal.toReal_nonneg)

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
