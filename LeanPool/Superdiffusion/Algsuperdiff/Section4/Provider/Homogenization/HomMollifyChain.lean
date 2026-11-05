/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyIncrement
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomLiftEndpoint
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# HomMollifyChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the S44-J chain, end to end

## The composed theorem

Two ingredients together close the Step-3c bridge of Theorem B, and this
module performs the composition.

```text
  UniformBoxGaugeBound m s A (∇w)            (the negative-order gradient bound)
      ⟹  [w]_{C^{0,1-s}} ≤ 16 d A            (holderSeminormBoundOn_of_uniformBoxGauge)
      ⟹  3^{-m}‖w‖_{L^∞(□_m)} ≤ 16 d A 3^{-ms}   (ae_linfty_of_uniformBoxGauge_originCube)
```

* the mollifier calculus supplies: `(L)`, `(I)`, `(hLim)` for the family
  `W_n = (w ⋆ ψ)_{· + □_n}` at the common constant `2 d A`.
* the lifting supplies the telescoping estimate (absolute constant `8`) and the
  `L^∞` endpoint (constant exactly `1`).
* The mollifier is then removed: the Hölder bound is *uniform in* `ψ`, and
  `w ⋆ ψ_k → w` pointwise at the continuous representative along any bump
  sequence with shrinking radii (`ContDiffBump.convolution_tendsto_right_of_continuous`),
  so the bound passes to the limit (`HolderSeminormBoundOn.of_tendsto`).

The final constant is `16 · d · A`: the absolute `8`, the common constant `2 d
A`.  The `d` is the sup-norm duality of `HomMollifyLipschitz`; nothing else
dimensional enters.

## What the consumer must supply

Besides the negative-order gauge on `∇w`, the frame items are:

* `HasWeakGradientOn Set.univ w G` with `w` integrable and compactly
  supported and each `G · i` integrable — for `w = u - v ∈ H¹₀(□_m)` this is
  `CoarseGraining`'s `H10Function.hasWeakGradientOn_univ_zeroExtension` applied to the
  zero extension, whose `MemLp` fields give the integrability;
* a *continuous representative* `g =ᵐ w`.  This is the same
  representative-level input the lifting already needs for the boundary hypothesis
  `hzero` (`HomLiftEndpoint`), and it is where the a.e.-defined Sobolev
  object is replaced by a genuine function.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Hölder bounds pass to pointwise limits -/

/-- A Hölder bound valid along a pointwise-convergent sequence passes to the
limit. -/
theorem holderSeminormBoundOn_of_tendsto {U : Set (Vec d)} {alpha K : ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hf : ∀ k, HolderSeminormBoundOn U alpha K (f k))
    (hlim : ∀ x ∈ U, Filter.Tendsto (fun k => f k x) Filter.atTop (nhds (g x))) :
    HolderSeminormBoundOn U alpha K g := by
  intro x hx y hy
  have hconv : Filter.Tendsto (fun k => ‖f k x - f k y‖) Filter.atTop (nhds ‖g x - g y‖) :=
    ((hlim x hx).sub (hlim y hy)).norm
  refine le_of_tendsto hconv (Filter.Eventually.of_forall fun k => ?_)
  exact hf k x hx y hy

/-! ## 2. The Hölder bound for the mollification -/

/-- **The lifting for the mollified function.**

Under the translate-uniform negative gauge of order `-s` on `∇w`, every
mollification `w ⋆ ψ` obeys the Hölder bound of exponent `1 - s` at the
constant `16 d A`, on any set of diameter at most `3^m`.  The constant does
not depend on `ψ`. -/
theorem holderSeminormBoundOn_convolution_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ)
    {U : Set (Vec d)} (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ)) :
    HolderSeminormBoundOn U (1 - s) (16 * (d : ℝ) * A)
      (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := by
  have hP : (0 : ℝ) ≤ (d : ℝ) * A := mul_nonneg (Nat.cast_nonneg d) hgauge.nonneg
  have hA2 : (0 : ℝ) ≤ 2 * (d : ℝ) * A := by linarith only [hP]
  have hbase := holderSeminormBoundOn_of_increments
    (U := U) (w := w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)
    (W := fun n => boxRegularization n ψ w) (m := m) (s := s) (A := 2 * (d : ℝ) * A)
    hs0 hs2 hA2 hdiam
    (by
      intro n hn x _hx y _hy
      refine (abs_boxRegularization_sub_le hw hwI hwc hGI hgauge hψ hn x y).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (three_rpow_nonneg _))
        (norm_nonneg _)
      linarith only [hP])
    (by
      intro n hn x _hx
      exact abs_boxRegularization_sub_pred_le hw hwI hwc hGI hgauge hs2 hψ hn x)
    (by
      intro x _hx n _hn
      exact tendsto_boxRegularization_atTop hwI hψ n x)
  refine hbase.mono_const ?_
  linarith only [hP]

/-! ## 3. Removing the mollifier -/

/-- A shrinking sequence of bump functions on `Vec d`. -/
def mollifyBump (k : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / (2 * ((k : ℝ) + 1))
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) hk]
    linarith only [hk]

theorem mollifyBump_rOut (k : ℕ) : (mollifyBump (d := d) k).rOut = 1 / ((k : ℝ) + 1) := rfl

theorem tendsto_mollifyBump_rOut :
    Filter.Tendsto (fun k : ℕ => (mollifyBump (d := d) k).rOut) Filter.atTop (nhds 0) := by
  simpa only [mollifyBump_rOut] using tendsto_one_div_add_atTop_nhds_zero_nat

/-- The normalized bump is a mollifier density. -/
theorem isMollifierDensity_mollifyBump (k : ℕ) :
    IsMollifierDensity ((mollifyBump (d := d) k).normed volume) where
  smooth := (mollifyBump (d := d) k).contDiff_normed
  compactSupport := (mollifyBump (d := d) k).hasCompactSupport_normed
  nonneg := fun z => (mollifyBump (d := d) k).nonneg_normed z
  integral_eq_one := (mollifyBump (d := d) k).integral_normed

/-! ## 4. The composed lifting -/

/-- **THE S44-J LIFTING, END TO END.**

From the translate-uniform negative gauge of order `-s` on `∇w` — the
manuscript's `‖∇u - ∇v‖_{W^{-s,∞}(□_m)}` bound, at the translate carrier —
the continuous representative `g` of `w` is Hölder continuous of exponent
`1 - s` with constant `16 d A`, on any set of diameter at most `3^m`.

This is the principle that "`W^{-s,∞}` for the gradient is
like `C^{0,1-s}` for the function") made into a theorem. -/
theorem holderSeminormBoundOn_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    {U : Set (Vec d)} (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ)) :
    HolderSeminormBoundOn U (1 - s) (16 * (d : ℝ) * A) g := by
  refine holderSeminormBoundOn_of_tendsto
    (f := fun k => w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((mollifyBump (d := d) k).normed volume)) ?_ ?_
  · intro k
    exact holderSeminormBoundOn_convolution_of_uniformBoxGauge hw hwI hwc hGI hgauge hs0 hs2
      (isMollifierDensity_mollifyBump k) hdiam
  · intro x _hx
    have hrw : ∀ k : ℕ, (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((mollifyBump (d := d) k).normed volume)) x
        = (((mollifyBump (d := d) k).normed volume)
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
      intro k
      rw [convolution_comm_real w ((mollifyBump (d := d) k).normed volume)]
      exact congrFun (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
        (Filter.EventuallyEq.refl _ ((mollifyBump (d := d) k).normed volume)) hgw) x
    simpa only [hrw] using
      ContDiffBump.convolution_tendsto_right_of_continuous
        (μ := (volume : Measure (Vec d))) tendsto_mollifyBump_rOut hgc x

/-! ## 5. The `L^∞` endpoint, in the shape of the frozen root's clause (C3) -/

/-- **The Step-3c display, at the origin cube.**

From the negative-order gauge on `∇w` at the scales `n ≤ m`, together with
the vanishing of the continuous representative on the faces of `□_m` — the
rendering of `u - v ∈ H¹₀(□_m)` — one obtains

```text
  3^{-m} |g(x)| ≤ 16 d A · 3^{-ms}   for a.e. x ∈ □_m,
```

which is exactly the shape of the frozen root's clause (C3),
the introduction's homogenization estimate, with the explicit constant `16 d`. -/
theorem ae_linfty_of_uniformBoxGauge_originCube [NeZero d] (m : ℤ) {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), g y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |g x| ≤ 16 * (d : ℝ) * A * (3 : ℝ) ^ (-(m : ℝ) * s) := by
  have hs1 : s < 1 := by linarith only [hs2]
  have hK : (0 : ℝ) ≤ 16 * (d : ℝ) * A := by
    have hP : (0 : ℝ) ≤ (d : ℝ) * A := mul_nonneg (Nat.cast_nonneg d) hgauge.nonneg
    linarith only [hP]
  have hdiam : ∀ x ∈ closedCubeSet (originCube d m), ∀ y ∈ closedCubeSet (originCube d m),
      ‖x - y‖ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ) := by
    simpa using! norm_sub_le_cubeScaleFactor (originCube d m)
  have hHol : HolderSeminormBoundOn (closedCubeSet (originCube d m)) (1 - s)
      (16 * (d : ℝ) * A) g :=
    holderSeminormBoundOn_of_uniformBoxGauge hw hwI hwc hGI hgauge hs0 hs2 hgc hgw hdiam
  have hres := ae_linfty_of_holder_of_boundary_zero_cube (originCube d m) hs1 hK hHol hzero
  simpa using! hres

end

end Algsuperdiff.Section4.Provider.Homogenization
