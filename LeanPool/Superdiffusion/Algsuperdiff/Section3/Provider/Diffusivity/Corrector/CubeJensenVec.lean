/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeJensen
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# CubeJensenVec

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Portable: the vector cube-average Jensen inequality at the fourth power

This file contains **generic mathematics only**.  Apart from the sibling
portable module `CubeJensen` -- itself a Mathlib + `Homogenization.*` file, and
a candidate for relocation into CoarseGraining -- it imports nothing but
Mathlib and `Homogenization.*`, mentions no ABK26 object, no model, no cutoff
law, no scale and no anchor.

## What is here

Two facts are needed whenever a volume-normalized `L^4` quantity built from the
*averaged* value of a vector field on a cube has to be compared with the
volume-normalized `L^8` norm of the field itself:

* `sq_vecNormSq_cubeAverageVec_le_cubeAverage_sq_of_memLp` -- the vector Jensen
  inequality at the fourth power, `|u_Q|^4 <= avg |u|^4`, where `|.|` is the
  Euclidean length `vecNormSq^{1/2}` on `Vec d` and `u_Q = cubeAverageVec Q u`;
* `cubeAverage_norm_pow_four_le_cubeLpNorm_eight_pow_four_of_memLp` -- the
  volume-normalized `L^4 <= L^8` bridge, `avg ‖g‖^4 <= (‖g‖_{L^8(Q)})^4`, for a
  field valued in an arbitrary normed group, and its Euclidean specialization
  `cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp`.

## Why the vector Jensen is not the coordinate one

CoarseGraining proves the `p = 2` vector statement in **sum** form,
`vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp`:

```
  |u_Q|^2 <= sum_i avg (u_i)^2 .
```

Consumers that then need a *fourth* power must either pay a dimensional factor
`d` (Cauchy-Schwarz on the `d`-term sum, the route the proved
`ellipticityBudget_le` takes) or collapse the sum back into a single cube
average.  The second route is taken here, because the display it feeds --
ABK26's fourth-moment display -- is a numerical bound by a dimension-only
constant, and paying an avoidable factor `d` inside a bound whose right-hand
side is a *fourth root* would make the resulting constant `d^{1/4}`-inflected
for no reason.  The collapse is exact, not an estimate: it is the finite
additivity of the cube average, `cubeAverage_finset_sum_of_integrable`, which
CoarseGraining has only in the two-term form `cubeAverage_add_of_integrableOn`
and which is supplied here by rewriting both sides as integrals against the
normalized cube measure.

With the sum collapsed, `|u_Q|^2 <= avg |u|^2` is a genuine scalar cube average
on the right, and the scalar `p = 2` Jensen inequality of CoarseGraining
applies to it a second time, giving `|u_Q|^4 <= (avg |u|^2)^2 <= avg |u|^4`.

## Main results

* `cubeAverage_finset_sum_of_integrable`
* `cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp`
* `sq_vecNormSq_cubeAverageVec_le_cubeAverage_sq_of_memLp`
* `cubeAverage_norm_pow_four_le_cubeLpNorm_eight_pow_four_of_memLp`
* `cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open MeasureTheory
open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Finite additivity of the normalized cube average -/

/-- **Finite additivity of the cube average.**  CoarseGraining supplies the
two-term form `cubeAverage_add_of_integrableOn`; this is the `Finset` form,
obtained by reading both sides as integrals against the (finite) normalized
cube measure. -/
theorem cubeAverage_finset_sum_of_integrable {ι : Type*} (Q : TriadicCube d)
    (s : Finset ι) (f : ι → Vec d → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage Q (f i) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_finsetSum s hf

/-! ## Membership bookkeeping -/

/-- The square of an `L^4` function on the normalized cube lies in `L^2`. -/
private theorem memLp_sq_two_of_memLp_four_vec (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 4 (normalizedCubeMeasure Q)) :
    MemLp (fun x => f x ^ (2 : ℕ)) 2 (normalizedCubeMeasure Q) := by
  have h := (memLp_norm_rpow_iff (μ := normalizedCubeMeasure Q) (f := f)
      (p := (4 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hf.aestronglyMeasurable
      (by norm_num) (by norm_num)).2 hf
  have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  rw [hdiv] at h
  have hfun : (fun x => ‖f x‖ ^ ((2 : ℝ≥0∞).toReal)) = fun x => f x ^ (2 : ℕ) := by
    funext x
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ f x ^ (2 : ℕ))]
  rwa [hfun] at h

/-- Each coordinate of an `L^p` vector field on the normalized cube is `L^p`. -/
private theorem memLp_apply_of_memLp (Q : TriadicCube d) {u : Vec d → Vec d}
    {p : ℝ≥0∞} (hu : MemLp u p (normalizedCubeMeasure Q)) (i : Fin d) :
    MemLp (fun x => u x i) p (normalizedCubeMeasure Q) := by
  simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu

/-- The Euclidean squared length of an `L^4` vector field lies in `L^2`. -/
private theorem memLp_vecNormSq_two_of_memLp_four (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u 4 (normalizedCubeMeasure Q)) :
    MemLp (fun x => vecNormSq (u x)) 2 (normalizedCubeMeasure Q) := by
  have hsum : MemLp (fun x => ∑ i : Fin d, u x i ^ (2 : ℕ)) 2
      (normalizedCubeMeasure Q) :=
    memLp_finsetSum (μ := normalizedCubeMeasure Q) Finset.univ
      (fun i _ => memLp_sq_two_of_memLp_four_vec Q (memLp_apply_of_memLp Q hu i))
  have hfun : (fun x => ∑ i : Fin d, u x i ^ (2 : ℕ)) =
      fun x => vecNormSq (u x) := by
    funext x
    simp [vecNormSq, vecDot, pow_two]
  rwa [hfun] at hsum

/-! ## The cube average of the Euclidean squared length -/

/-- **The sum of CoarseGraining's coordinate averages is a single cube average.**
This is the exact collapse that lets the vector Jensen inequality be iterated
without paying a dimensional factor. -/
theorem cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp (Q : TriadicCube d)
    (u : Vec d → Vec d) (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecNormSq (u x)) =
      ∑ i : Fin d, cubeAverage Q (fun x => u x i ^ (2 : ℕ)) := by
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => u x i ^ (2 : ℕ)) (normalizedCubeMeasure Q) :=
    fun i _ => (memLp_apply_of_memLp Q hu i).integrable_sq
  have hsum := cubeAverage_finset_sum_of_integrable Q (Finset.univ : Finset (Fin d))
    (fun i x => u x i ^ (2 : ℕ)) hint
  have hfun : (fun x => ∑ i : Fin d, u x i ^ (2 : ℕ)) =
      fun x => vecNormSq (u x) := by
    funext x
    simp [vecNormSq, vecDot, pow_two]
  rwa [hfun] at hsum

/-! ## The vector Jensen inequality at the fourth power -/

/-- **Vector cube-average Jensen at the fourth power.**  For a vector field in
`L^4` of the normalized cube measure,

```
  |u_Q|^4 <= avg_Q |u|^4 ,
```

with `|.|` the Euclidean length and `u_Q = cubeAverageVec Q u`.  Written with
`vecNormSq` on both sides, this is
`vecNormSq (cubeAverageVec Q u)^2 <= cubeAverage Q (vecNormSq o u)^2`. -/
theorem sq_vecNormSq_cubeAverageVec_le_cubeAverage_sq_of_memLp (Q : TriadicCube d)
    (u : Vec d → Vec d) (hu : MemLp u 4 (normalizedCubeMeasure Q)) :
    vecNormSq (cubeAverageVec Q u) ^ (2 : ℕ) ≤
      cubeAverage Q (fun x => vecNormSq (u x) ^ (2 : ℕ)) := by
  have hu2 : MemLp u 2 (normalizedCubeMeasure Q) := hu.mono_exponent (by norm_num)
  have hjensen := vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp Q u hu2
  rw [← cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp Q u hu2] at hjensen
  have hg : MemLp (fun x => vecNormSq (u x)) 2 (normalizedCubeMeasure Q) :=
    memLp_vecNormSq_two_of_memLp_four Q hu
  have hsecond := sq_cubeAverage_le_cubeAverage_sq_of_memLp Q
    (fun x => vecNormSq (u x)) hg
  have h0 : (0 : ℝ) ≤ vecNormSq (cubeAverageVec Q u) :=
    vecNormSq_nonneg (cubeAverageVec Q u)
  calc vecNormSq (cubeAverageVec Q u) ^ (2 : ℕ)
      ≤ cubeAverage Q (fun x => vecNormSq (u x)) ^ (2 : ℕ) := by gcongr
    _ ≤ cubeAverage Q (fun x => vecNormSq (u x) ^ (2 : ℕ)) := hsecond

/-! ## The volume-normalized `L^4 <= L^8` bridge -/

/-- **The `L^4 <= L^8` bridge on a cube.**  For a field valued in any normed
group and lying in `L^8` of the normalized cube measure,

```
  avg_Q ‖g‖^4 <= (‖g‖_{L^8(Q)})^4 ,
```

with `‖g‖_{L^8(Q)} = cubeLpNorm Q 8 g` the volume-normalized `L^8` norm.  This
is the scalar `L^4 <= L^8` comparison of `CubeJensen` applied to the pointwise
norm, read back through
`cubeLpNorm_rpow_eq_cubeAverage_norm_rpow`. -/
theorem cubeAverage_norm_pow_four_le_cubeLpNorm_eight_pow_four_of_memLp
    {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (g : Vec d → E)
    (hg : MemLp g 8 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => ‖g x‖ ^ (4 : ℕ)) ≤ cubeLpNorm Q 8 g ^ (4 : ℕ) := by
  have hnorm : MemLp (fun x => ‖g x‖) 8 (normalizedCubeMeasure Q) := hg.norm
  have hjensen := sq_cubeAverage_pow_four_le_cubeAverage_pow_eight_of_memLp Q
    (fun x => ‖g x‖) hnorm
  have hrepr : cubeLpNorm Q 8 g ^ ((8 : ℝ≥0∞).toReal) =
      cubeAverage Q (fun x => ‖g x‖ ^ ((8 : ℝ≥0∞).toReal)) :=
    cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 8 g (by norm_num) (by norm_num) hg
  have htoReal : ((8 : ℝ≥0∞).toReal) = ((8 : ℕ) : ℝ) := by norm_num
  rw [htoReal, Real.rpow_natCast] at hrepr
  have hfun : (fun x => ‖g x‖ ^ (((8 : ℕ) : ℝ))) = fun x => ‖g x‖ ^ (8 : ℕ) := by
    funext x
    rw [Real.rpow_natCast]
  rw [hfun] at hrepr
  have hpow : cubeAverage Q (fun x => ‖g x‖ ^ (4 : ℕ)) ^ (2 : ℕ) ≤
      (cubeLpNorm Q 8 g ^ (4 : ℕ)) ^ (2 : ℕ) := by
    calc cubeAverage Q (fun x => ‖g x‖ ^ (4 : ℕ)) ^ (2 : ℕ)
        ≤ cubeAverage Q (fun x => ‖g x‖ ^ (8 : ℕ)) := hjensen
      _ = cubeLpNorm Q 8 g ^ (8 : ℕ) := hrepr.symm
      _ = (cubeLpNorm Q 8 g ^ (4 : ℕ)) ^ (2 : ℕ) := by ring
  have hrhs : (0 : ℝ) ≤ cubeLpNorm Q 8 g ^ (4 : ℕ) :=
    pow_nonneg (cubeLpNorm_nonneg Q 8 g) 4
  exact le_of_sq_le_sq hpow hrhs

/-- **The Euclidean form of the `L^4 <= L^8` bridge.**  With
`‖u‖_{L^8(Q)} = cubeLpNorm Q 8 (vecNorm o u)` the volume-normalized `L^8` norm
read with the Euclidean pointwise length,

```
  avg_Q |u|^4 <= (‖u‖_{L^8(Q)})^4 .
```
-/
theorem cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp (fun x => Book.Ch02.vecNorm (u x)) 8 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecNormSq (u x) ^ (2 : ℕ)) ≤
      cubeLpNorm Q 8 (fun x => Book.Ch02.vecNorm (u x)) ^ (4 : ℕ) := by
  have hbridge := cubeAverage_norm_pow_four_le_cubeLpNorm_eight_pow_four_of_memLp
    Q (fun x => Book.Ch02.vecNorm (u x)) hu
  have hfun : (fun x => ‖Book.Ch02.vecNorm (u x)‖ ^ (4 : ℕ)) =
      fun x => vecNormSq (u x) ^ (2 : ℕ) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (u x)),
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Book.Ch02.vecNorm_sq_eq_vecNormSq]
  rwa [hfun] at hbridge

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
