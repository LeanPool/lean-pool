/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyPairing
public import LeanPool.HighContrastHomogenization.Support.Sobolev.WeakDerivatives

/-!
# HomMollifySwap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the two swaps of the mollifier calculus

## What this module proves

Two exchange identities carry the whole mollifier calculus.

**(S1) The averaging swap.**  For a mollifier `ψ` and a field `f`,

```text
  (f ⋆ ψ)_{x+□_n}  =  ∫ ψ(z) · (f)_{x-z+□_n} dz.
```

The box average of a mollification is the `ψ`-mixture of the box averages —
i.e. the mollifier commutes with the sliding average.  This is
`boxAverage_convolution_eq_boxMixture`, and it is exactly what turns the
manuscript's cube-average gauge into a bound on the mollified gradient:
combined with the kernel pairing of `HomMollifyPairing` it yields
`norm_boxAverageVec_convolution_le_of_uniformBoxGauge`, this file's working
form of the core estimate.

**(S2) The weak-gradient swap.**  For `w` with weak gradient `G` on the whole
space and a smooth compactly supported kernel `Θ`,

```text
  ∫ w(y) (∂_i Θ)(x - y) dy  =  ∫ G_i(y) Θ(x - y) dy,
```

i.e. `∂_i(Θ ⋆ w) = Θ ⋆ G_i`.  This is
`integral_mul_fderiv_sub_eq_integral_weakGrad`; it is the *only* place where
the Sobolev regularity of `w` is used, and it is a single application of
`HasWeakPartialDerivOn` to the test function `y ↦ Θ(x - y)`.

Together: the gradient of the mollification of `w` at scale `3^n` is the
mixture of the scale-`n` box averages of `∇w`, hence is bounded by
`A · 3^{-ns}` under the translate-uniform gauge.

## The `H¹₀` frame

The hypothesis `HasWeakGradientOn Set.univ w G` is not an extra assumption on
the Step-3 object: for `w = u - v ∈ H¹₀(□_m)` — which is exactly the
manuscript's hypothesis in the paper — `CoarseGraining`'s
`H10Function.hasWeakGradientOn_univ_zeroExtension` supplies it for the
extension of `w` by zero, together with `MemLp` for `w` and `∇w`, whence
their integrability (compact support).

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Commutativity of the scalar convolution -/

/-- The scalar convolution pairing is its own flip. -/
theorem lsmul_flip_eq_lsmul :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm b a

/-- **Scalar convolution is commutative.** -/
theorem convolution_comm_real (f g : Vec d → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure (Vec d))] g
      = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  have h := convolution_flip (f := f) (g := g) (ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (Vec d)))
  rw [lsmul_flip_eq_lsmul] at h
  exact h.symm

/-! ## 2. Associativity for a bounded integrable mollifier -/

/-- **Associativity of the scalar convolution** when the outer factor is
bounded and all three factors are integrable. -/
theorem convolution_assoc_real {f g k : Vec d → ℝ} {C : ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (hk : Integrable k volume)
    (hfb : ∀ t, ‖f t‖ ≤ C) (x₀ : Vec d) :
    ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x₀
      = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x₀ := by
  have hL : ∀ x y z : ℝ,
      (ContinuousLinearMap.lsmul ℝ ℝ) ((ContinuousLinearMap.lsmul ℝ ℝ) x y) z
        = (ContinuousLinearMap.lsmul ℝ ℝ) x ((ContinuousLinearMap.lsmul ℝ ℝ) y z) := by
    intro x y z
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_assoc x y z
  have hgk : Integrable
      ((fun x => ‖g x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖k x‖) volume :=
    hg.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk.norm
  have hfgk : ConvolutionExistsAt (fun x => ‖f x‖)
      ((fun x => ‖g x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖k x‖) x₀
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    have hshift := hgk.comp_sub_left x₀
    have hmeas : AEStronglyMeasurable (fun t : Vec d => ‖f t‖) volume := hf.norm.1
    have hbdd : ∀ᵐ t : Vec d ∂(volume : Measure (Vec d)), ‖‖f t‖‖ ≤ C :=
      Filter.Eventually.of_forall fun t => by
        rw [norm_norm]; exact hfb t
    simpa only [ContinuousLinearMap.mul_apply', ConvolutionExistsAt] using
      hshift.bdd_mul hmeas hbdd
  exact convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ) hL
    hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
    (hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hg)
    (hg.norm.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hk.norm) hfgk

/-! ## 3. (S1) The averaging swap -/

/-- **The averaging swap.**  The scale-`n` box average of the mollification
`f ⋆ ψ` is the `ψ`-mixture of the scale-`n` box averages of `f`:

```text
  (f ⋆ ψ)_{x+□_n} = ∫ ψ(z) (f)_{x-z+□_n} dz.
```

This is the precise sense in which "a mollifier at scale `3^n` is a
superposition of translated scale-`n` box averages", and it is the identity
that lets the manuscript's cube-average gauge control a mollified field. -/
theorem boxAverage_convolution_eq_boxMixture (n : ℤ) {ψ f : Vec d → ℝ} {C : ℝ}
    (hψ : Integrable ψ volume) (hf : Integrable f volume) (hψb : ∀ t, ‖ψ t‖ ≤ C)
    (x : Vec d) :
    boxAverage n x (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) = boxMixture n ψ f x := by
  have hK : Integrable (boxKernel (d := d) n) volume := integrable_boxKernel n
  have hstep : ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel n) x
      = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel n) x :=
    convolution_assoc_real hψ hf hK hψb x
  calc boxAverage n x (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)
      = (boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)) x :=
        (convolution_boxKernel_eq_boxAverage n _ x).symm
    _ = ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel n) x := by
        rw [convolution_comm_real (boxKernel n), convolution_comm_real f ψ]
    _ = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel n) x := hstep
    _ = boxMixture n ψ f x := by
        rw [boxMixture_eq_convolution]
        congr 1
        funext y
        rw [convolution_comm_real f (boxKernel n)]
        exact convolution_boxKernel_eq_boxAverage n f y

/-! ## 4. The pairing in convolution form -/

/-- The coordinatewise mollification of a vector field. -/
def convolutionVec (ψ : Vec d → ℝ) (F : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => (fun y => F y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ <| x

theorem convolutionVec_apply (ψ : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    convolutionVec ψ F x i
      = ((fun y => F y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x := rfl

/-- **THE CORE ESTIMATE IN CONVOLUTION FORM.**

If the vector field `F` obeys the translate-uniform negative gauge of order
`-s` on the scales `≤ m`, then for every scale `n ≤ m`, every probability
density `ψ` that is integrable and bounded, and every point `x`, the
scale-`n` box average of the mollification `F ⋆ ψ` obeys

```text
  ‖(F ⋆ ψ)_{x+□_n}‖ ≤ A · 3^{-ns}.
```

The constant is exactly `1`: the mollification is a mass-one superposition
of translated box averages, each bounded by the gauge. -/
theorem norm_boxAverageVec_convolution_le_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {F : Vec d → Vec d} (h : UniformBoxGaugeBound m s A F) {n : ℤ} (hn : n ≤ m)
    {ψ : Vec d → ℝ} {C : ℝ} (hψ : Integrable ψ volume) (hψb : ∀ t, ‖ψ t‖ ≤ C)
    (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : ∫ z, ψ z = 1)
    (hF : ∀ i : Fin d, Integrable (fun y => F y i) volume) (x : Vec d) :
    ‖boxAverageVec n x (convolutionVec ψ F)‖ ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
  have hswap : boxAverageVec n x (convolutionVec ψ F) = boxMixtureVec n ψ F x := by
    funext i
    rw [boxAverageVec_apply, boxMixtureVec_apply]
    exact boxAverage_convolution_eq_boxMixture n hψ (hF i) hψb x
  rw [hswap]
  exact norm_boxMixtureVec_le_of_uniformBoxGauge h hn hψ0 hψ1 x

/-! ## 5. (S2) The weak-gradient swap -/

/-- **The weak-gradient swap.**  If `w` has weak gradient `G` on the whole
space and `Θ` is a smooth compactly supported kernel, then

```text
  ∫ w(y) (∂_i Θ)(x - y) dy = ∫ G_i(y) Θ(x - y) dy,
```

i.e. differentiating the mollification `Θ ⋆ w` hits the kernel on the left
and the weak gradient on the right.  This is a single application of the
definition of the weak partial derivative to the test function
`y ↦ Θ(x - y)`.

For the Step-3 object `w = u - v ∈ H¹₀(□_m)` the hypothesis is `CoarseGraining`'s
`H10Function.hasWeakGradientOn_univ_zeroExtension`. -/
theorem integral_mul_fderiv_sub_eq_integral_weakGrad {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) {Θ : Vec d → ℝ}
    (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) (hΘc : HasCompactSupport Θ) (i : Fin d) (x : Vec d) :
    ∫ y, w y * (fderiv ℝ Θ (x - y)) (basisVec i) = ∫ y, G y i * Θ (x - y) := by
  classical
  have hsub : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => x - y :=
    contDiff_const.sub contDiff_id
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => Θ (x - y) := hΘ.comp hsub
  have hφc : HasCompactSupport fun y : Vec d => Θ (x - y) := by
    refine HasCompactSupport.intro (K := (fun y : Vec d => x - y) '' tsupport Θ)
      (hΘc.isCompact.image (by fun_prop)) ?_
    intro y hy
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hc
    exact hy ⟨x - y, hc, by show x - (x - y) = y; rw [sub_sub_cancel]⟩
  have hderiv : ∀ y : Vec d,
      (fderiv ℝ (fun z : Vec d => Θ (x - z)) y) (basisVec i)
        = -(fderiv ℝ Θ (x - y)) (basisVec i) := by
    intro y
    have hmap : HasFDerivAt (fun z : Vec d => x - z) (-ContinuousLinearMap.id ℝ (Vec d)) y := by
      have hc : HasFDerivAt (fun _ : Vec d => x) (0 : Vec d →L[ℝ] Vec d) y :=
        hasFDerivAt_const x y
      have hi : HasFDerivAt (fun z : Vec d => z) (ContinuousLinearMap.id ℝ (Vec d)) y :=
        hasFDerivAt_id y
      have h := hc.sub hi
      rwa [zero_sub] at h
    have hΘat : HasFDerivAt Θ (fderiv ℝ Θ (x - y)) (x - y) :=
      (hΘ.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt (fun z : Vec d => Θ (x - z))
        ((fderiv ℝ Θ (x - y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y := hΘat.comp y hmap
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply, map_neg]
  have hweak := hw i (fun y : Vec d => Θ (x - y)) hφ hφc (Set.subset_univ _)
  rw [Measure.restrict_univ] at hweak
  have hleft : ∫ y, w y * (fderiv ℝ (fun z : Vec d => Θ (x - z)) y) (basisVec i)
      = -∫ y, w y * (fderiv ℝ Θ (x - y)) (basisVec i) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show w y * (fderiv ℝ (fun z : Vec d => Θ (x - z)) y) (basisVec i)
      = -(w y * (fderiv ℝ Θ (x - y)) (basisVec i))
    rw [hderiv y]
    ring
  rw [hleft] at hweak
  exact neg_injective hweak

end

end Algsuperdiff.Section4.Provider.Homogenization
