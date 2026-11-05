/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayAverage
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# OscillationApproxForcing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The birth-scale forcing atom on a concentric cube

The second term of `e.nablaw.oscillations` is

```
  C shom_{m-h}^{-1} (m-h-n) 3^n || grad (k_m - k_{m-h}) ||_{L^inf (z + cu_{m-h})} .
```

Its per-scale atom is the normalized `L^2` oscillation of the forcing field on
the cube of that scale, and the factor `3^{scale}` in front of the `L^inf`
gradient is exactly the Poincare constant of the cube in its crudest, sup-norm
form.  That is what this module proves:

```
  || F - (F)_{z + cu_m} ||_{L2bar (z + cu_m)}
      <= sqrt d * 3^m * sup_{z + cu_m} || D F || .
```

The cube is convex (`OscillationCubeFamily.convex_openCubeAtScale`) and has
sup-norm diameter `3^m` (`OscillationDecayAverage.norm_sub_le_of_mem_openCubeAtScale`),
so the convex mean-value inequality gives the pointwise bound at once; the only
further ingredients are the pointwise-to-mean-square step and the mean recentring
of `OscillationDecayAverage`.  No Poincare inequality in Sobolev form and no
capacity argument is needed, because the forcing is controlled in `L^inf`
already.

**This is one half of the harmonic-approximation step, not the whole of it.**
The other half -- solving `-Delta phi = div ((F - c) 1_U)` in `H^1_0 (U)` so that
`w - phi` becomes harmonic on `U`, with the energy estimate
`|| grad w - grad (w - phi) ||_{L2bar (U)} <= || F - (F)_U ||_{L2bar (U)}` -- is
**not** proved here and is not used here.  See the disclosure.

## Contents

* `meanSquareDeviationVecOn_center_le_of_norm_fderiv_le` -- the pointwise
  mean-value step, in mean-square form and centred at the cube centre.
* `sqrt_meanSquareOscillationVecOn_le_of_norm_fderiv_le` -- **the forcing atom**,
  in the norm form `<= sqrt d * M * 3^m` that the accumulation of
  `OscillationTelescope` consumes as its birth-scale hypothesis `hE`.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- **The mean-value step on the convex cube.**

If every coordinate of `F` has differential of operator norm at most `M` on the
cube `z + cu_m`, then the mean-square deviation of `F` from its value at the
centre is at most `d M^2 3^{2m}`. -/
theorem meanSquareDeviationVecOn_center_le_of_norm_fderiv_le
    {F : Vec d → Vec d} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i : Fin d, Differentiable ℝ fun y => F y i) (z : Vec d) (m : ℤ)
    (hbound : ∀ x ∈ openCubeAtScale z m, ∀ i : Fin d,
      ‖fderiv ℝ (fun y => F y i) x‖ ≤ M) :
    Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m) F (F z)
      ≤ (Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m) ^ 2 := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
  have hcoord : ∀ (i : Fin d) (x : Vec d), x ∈ openCubeAtScale z m →
      |F x i - F z i| ≤ M * (3 : ℝ) ^ m := by
    intro i x hx
    have hmvt := (convex_openCubeAtScale z m).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hF i) w) (fun w hw => hbound w hw i) (mem_openCubeAtScale_self z m) hx
    have hnorm : ‖x - z‖ ≤ (3 : ℝ) ^ m :=
      norm_sub_le_of_mem_openCubeAtScale hx (mem_openCubeAtScale_self z m)
    exact le_trans hmvt (mul_le_mul_of_nonneg_left hnorm hM)
  refine meanSquareDeviationVecOn_le_of_forall_vecNormSq_le
    (measurableSet_openCubeAtScale z m) (volume_openCubeAtScale_ne_top z m)
    (volume_openCubeAtScale_toReal_pos z m)
    (fun i => integrableOn_openCubeAtScale_of_continuous
      ((((hF i).continuous.sub continuous_const)).pow 2) z m) ?_
  intro x hx
  have hexpand : vecNormSq (F x - F z) = ∑ i : Fin d, (F x i - F z i) ^ 2 := by
    simp [vecNormSq, vecDot, sq]
  have hterm : ∀ i : Fin d, (F x i - F z i) ^ 2 ≤ (M * (3 : ℝ) ^ m) ^ 2 := by
    intro i
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i x hx) 2
  have hsq : (Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m) ^ 2
      = (d : ℝ) * (M * (3 : ℝ) ^ m) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [hexpand, hsq]
  calc ∑ i : Fin d, (F x i - F z i) ^ 2
      ≤ ∑ _i : Fin d, (M * (3 : ℝ) ^ m) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * (M * (3 : ℝ) ^ m) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The birth-scale forcing atom.**

`|| F - (F)_{z + cu_m} ||_{L2bar (z + cu_m)} <= sqrt d * M * 3^m` whenever the
differential of every coordinate of `F` has operator norm at most `M` on the
cube.  With `m = n + j` this is exactly the birth-scale hypothesis
`E j <= c * 3^{n+j}` of
`OscillationTelescope.le_zpow_mul_add_nsmul_of_nested_decomposition`, with the
scale-independent constant `c = sqrt d * M`; the linear-in-`N` accumulation of
that module is what turns it into the printed `(m-h-n) 3^n` factor. -/
theorem sqrt_meanSquareOscillationVecOn_le_of_norm_fderiv_le
    {F : Vec d → Vec d} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i : Fin d, Differentiable ℝ fun y => F y i) (z : Vec d) (m : ℤ)
    (hbound : ∀ x ∈ openCubeAtScale z m, ∀ i : Fin d,
      ‖fderiv ℝ (fun y => F y i) x‖ ≤ M) :
    Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z m) F)
      ≤ Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
  have hnn : (0 : ℝ) ≤ Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) hpow.le
  have hosc : Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z m) F
      ≤ Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m) F (F z) :=
    meanSquareOscillationVecOn_le_meanSquareDeviationVecOn
      (volume_openCubeAtScale_ne_top z m) (volume_openCubeAtScale_toReal_pos z m) (F z)
      (fun i => integrableOn_openCubeAtScale_of_continuous (hF i).continuous z m)
      (fun i => integrableOn_openCubeAtScale_of_continuous ((hF i).continuous.pow 2) z m)
  have hchain := hosc.trans
    (meanSquareDeviationVecOn_center_le_of_norm_fderiv_le hM hF z m hbound)
  have hroot := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq hnn] at hroot

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
