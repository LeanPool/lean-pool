/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifySwap

/-!
# HomMollifyLipschitz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the scale-`n` Lipschitz estimate `(L)`

## What this module proves

The regularization family of this file is

```text
  W_n:= (w ⋆ ψ)_{· + □_n}    (mollify by `ψ`, then slide the scale-`n` box)
```

(`boxRegularization`).  Its gradient is computed twice — once for each
convolution factor — and each computation is one of the swaps of
`HomMollifySwap`:

* `fderiv_convolution_apply_basisVec` — `∂_i(w ⋆ ψ) = (∇w)_i ⋆ ψ`, the weak
  gradient swap `(S2)`;
* `fderiv_boxRegularization_apply` — `∇W_n(x) v = Σ_i v_i ((∇w)_i ⋆ ψ)_{x+□_n}`,
  i.e. the gradient of the sliding average is the sliding average of the
  gradient, by the box-kernel identity of `HomMollifyPairing`.

Feeding the averaging swap `(S1)` and the kernel pairing into the second
display gives the **gradient bound**

```text
  ‖∇W_n(x)‖ ≤ d · A · 3^{-ns}
```

(`norm_fderiv_boxRegularization_le`), and the mean value inequality on the
convex set `Vec d` turns it into the obligation

```text
  (L)   |W_n(x) - W_n(y)| ≤ (d · A) · 3^{-ns} · ‖x - y‖.
```

## Where the dimensional constant comes from

The pairing itself costs nothing (`HomMollifyPairing`, constant `1`).  The
factor `d` is the *only* dimensional loss in the whole chain, and it is the
sup-norm duality: on `Vec d = Fin d → ℝ` with the supremum norm, a linear
functional `v ↦ Σ_i g_i v_i` has operator norm `Σ_i |g_i| ≤ d · max_i |g_i|`,
and the gauge controls the maximum.  So `C(d) = d` exactly, and the
constant `8` composes to `8 d A`.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The mollifier profile -/

/-- A **mollifier density**: a smooth, compactly supported probability density
on `Vec d`.  Convolving with it is the smoothing step of the regularization. -/
structure IsMollifierDensity (ψ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ψ
  compactSupport : HasCompactSupport ψ
  nonneg : ∀ z, 0 ≤ ψ z
  integral_eq_one : ∫ z, ψ z = 1

theorem IsMollifierDensity.continuous {ψ : Vec d → ℝ} (h : IsMollifierDensity ψ) :
    Continuous ψ := h.smooth.continuous

theorem IsMollifierDensity.integrable {ψ : Vec d → ℝ} (h : IsMollifierDensity ψ) :
    Integrable ψ volume :=
  h.continuous.integrable_of_hasCompactSupport h.compactSupport

theorem IsMollifierDensity.exists_bound {ψ : Vec d → ℝ} (h : IsMollifierDensity ψ) :
    ∃ C : ℝ, ∀ t, ‖ψ t‖ ≤ C :=
  h.compactSupport.exists_bound_of_continuous h.continuous

/-! ## 2. The regularization family -/

/-- **The scale-`n` regularization of `w`**: mollify by `ψ`, then take the
sliding scale-`n` box average. -/
def boxRegularization (n : ℤ) (ψ w : Vec d → ℝ) (x : Vec d) : ℝ :=
  boxAverage n x (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)

theorem boxRegularization_def (n : ℤ) (ψ w : Vec d → ℝ) (x : Vec d) :
    boxRegularization n ψ w x = boxAverage n x (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
  rfl

/-- The regularization is the convolution of the box kernel with the
mollification. -/
theorem boxRegularization_eq_convolution (n : ℤ) (ψ w : Vec d → ℝ) :
    boxRegularization n ψ w
      = boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := by
  funext x
  exact (convolution_boxKernel_eq_boxAverage n _ x).symm

/-! ## 3. The gradient of the mollification -/

/-- The mollification of a locally integrable function by a mollifier density
is smooth. -/
theorem contDiff_convolution_mollifier {w ψ : Vec d → ℝ}
    (hwLoc : LocallyIntegrable w volume) (hψ : IsMollifierDensity ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
  hψ.compactSupport.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hwLoc hψ.smooth

/-- The mollification of a compactly supported function has compact
support. -/
theorem hasCompactSupport_convolution_mollifier {w ψ : Vec d → ℝ}
    (hwc : HasCompactSupport w) (hψ : IsMollifierDensity ψ) :
    HasCompactSupport (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hwc hψ.compactSupport

/-- **`∂_i (w ⋆ ψ) = (∇w)_i ⋆ ψ`** — the weak gradient swap in derivative
form. -/
theorem fderiv_convolution_apply_basisVec {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwLoc : LocallyIntegrable w volume)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ) (i : Fin d) (a : Vec d) :
    (fderiv ℝ (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) a) (basisVec i)
      = ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) a := by
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hd := HasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hψ.compactSupport hwLoc (hψ.smooth.of_le hone) a
  have hp := convolution_precompR_apply (f := w) (g := fderiv ℝ ψ)
    (μ := (volume : Measure (Vec d))) (ContinuousLinearMap.lsmul ℝ ℝ) hwLoc
    (HasCompactSupport.fderiv (𝕜 := ℝ) hψ.compactSupport)
    (hψ.smooth.continuous_fderiv (by simp)) a (basisVec i)
  rw [hd.fderiv, hp, convolution_lsmul, convolution_lsmul]
  simp only [smul_eq_mul]
  exact integral_mul_fderiv_sub_eq_integral_weakGrad hw hψ.smooth hψ.compactSupport i a

/-! ## 4. The gradient of the regularization -/

/-- Every vector is the sum of its coordinates times the basis vectors. -/
theorem eq_sum_smul_basisVec (v : Vec d) : v = ∑ i, v i • basisVec i := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j fun x => v x]
  simp

/-- The box average is linear over a finite combination of integrable
functions. -/
theorem boxAverage_finset_sum {n : ℤ} {x : Vec d} (c : Fin d → ℝ) (h : Fin d → Vec d → ℝ)
    (hint : ∀ i, IntegrableOn (h i) (boxSet n x) volume) :
    boxAverage n x (fun a => ∑ i, c i * h i a) = ∑ i, c i * boxAverage n x (h i) := by
  have hsum : ∫ a in boxSet n x, ∑ i, c i * h i a
      = ∑ i, ∫ a in boxSet n x, c i * h i a :=
    integral_finsetSum _ fun i _ => (hint i).const_mul (c i)
  rw [boxAverage_eq_inv_mul_integral, hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, boxAverage_eq_inv_mul_integral]
  ring

/-- **The gradient of the regularization.**  For every direction `v`,

```text
  ∇W_n(x) v = Σ_i v_i · ((∇w)_i ⋆ ψ)_{x+□_n}.
```
-/
theorem fderiv_boxRegularization_apply {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwLoc : LocallyIntegrable w volume)
    (hwc : HasCompactSupport w) (hGloc : ∀ i, LocallyIntegrable (fun y => G y i) volume)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ) (n : ℤ) (x v : Vec d) :
    (fderiv ℝ (boxRegularization n ψ w) x) v
      = ∑ i, v i *
          boxAverage n x ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := by
  classical
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hVsmooth : ContDiff ℝ (⊤ : ℕ∞) (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
    contDiff_convolution_mollifier hwLoc hψ
  have hVc : HasCompactSupport (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
    hasCompactSupport_convolution_mollifier hwc hψ
  have hKloc : LocallyIntegrable (boxKernel (d := d) n) volume := locallyIntegrable_boxKernel n
  have hd := HasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hVc hKloc (hVsmooth.of_le hone) x
  have hp := convolution_precompR_apply (f := boxKernel (d := d) n)
    (g := fderiv ℝ (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ))
    (μ := (volume : Measure (Vec d))) (ContinuousLinearMap.lsmul ℝ ℝ) hKloc
    (HasCompactSupport.fderiv (𝕜 := ℝ) hVc) (hVsmooth.continuous_fderiv (by simp)) x v
  rw [boxRegularization_eq_convolution n ψ w, hd.fderiv, hp,
    convolution_boxKernel_eq_boxAverage]
  have hdir : (fun a => (fderiv ℝ (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) a) v)
      = fun a => ∑ i, v i * ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) a := by
    funext a
    conv_lhs => rw [eq_sum_smul_basisVec v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (fun t => v i * t) (fderiv_convolution_apply_basisVec hw hwLoc hψ i a)
  have hcont : ∀ i : Fin d,
      Continuous ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := fun i =>
    hψ.compactSupport.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hGloc i) hψ.continuous
  rw [hdir]
  exact boxAverage_finset_sum v _ fun i =>
    ContinuousOn.integrableOn_compact (isCompact_boxSet n x) (hcont i).continuousOn

/-- The regularization is differentiable everywhere. -/
theorem differentiable_boxRegularization {w ψ : Vec d → ℝ}
    (hwLoc : LocallyIntegrable w volume) (hwc : HasCompactSupport w)
    (hψ : IsMollifierDensity ψ) (n : ℤ) :
    Differentiable ℝ (boxRegularization n ψ w) := by
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hVsmooth : ContDiff ℝ (⊤ : ℕ∞) (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
    contDiff_convolution_mollifier hwLoc hψ
  have hVc : HasCompactSupport (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
    hasCompactSupport_convolution_mollifier hwc hψ
  have hKloc : LocallyIntegrable (boxKernel (d := d) n) volume := locallyIntegrable_boxKernel n
  intro x
  have hd := HasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hVc hKloc (hVsmooth.of_le hone) x
  rw [boxRegularization_eq_convolution n ψ w]
  exact hd.differentiableAt

/-! ## 5. The gradient bound and `(L)` -/

/-- **The gradient bound.**  Under the translate-uniform gauge of order `-s`
on `∇w`, the scale-`n` regularization has gradient bounded by
`d · A · 3^{-ns}` everywhere.

The dimensional factor `d` is the sup-norm duality on `Vec d` and is the only
dimensional loss in the chain; the pairing itself costs nothing. -/
theorem norm_fderiv_boxRegularization_le {m : ℤ} {s A : ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ) {n : ℤ} (hn : n ≤ m) (x : Vec d) :
    ‖fderiv ℝ (boxRegularization n ψ w) x‖ ≤ (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
  classical
  obtain ⟨C, hC⟩ := hψ.exists_bound
  have hB : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) :=
    mul_nonneg hgauge.nonneg (three_rpow_nonneg _)
  have hbound := norm_boxAverageVec_convolution_le_of_uniformBoxGauge hgauge hn
    hψ.integrable hC hψ.nonneg hψ.integral_eq_one hGI x
  have hcoord : ∀ i : Fin d,
      |boxAverage n x ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)|
        ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
    intro i
    have hle := norm_le_pi_norm (boxAverageVec n x (convolutionVec ψ G)) i
    rw [Real.norm_eq_abs, boxAverageVec_apply] at hle
    exact hle.trans hbound
  have hCnn : (0 : ℝ) ≤ (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hmul := mul_nonneg this hB
    calc (0 : ℝ) ≤ (d : ℝ) * (A * (3 : ℝ) ^ (-((n : ℝ) * s))) := hmul
      _ = (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ hCnn ?_
  intro v
  rw [Real.norm_eq_abs,
    fderiv_boxRegularization_apply hw hwI.locallyIntegrable hwc
      (fun i => (hGI i).locallyIntegrable) hψ n x v]
  have hterm : ∀ i : Fin d,
      |v i * boxAverage n x ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)|
        ≤ (A * (3 : ℝ) ^ (-((n : ℝ) * s))) * ‖v‖ := by
    intro i
    rw [abs_mul]
    have hvi : |v i| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
    calc |v i| * |boxAverage n x ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)|
        ≤ ‖v‖ * (A * (3 : ℝ) ^ (-((n : ℝ) * s))) :=
          mul_le_mul hvi (hcoord i) (abs_nonneg _) (norm_nonneg v)
      _ = (A * (3 : ℝ) ^ (-((n : ℝ) * s))) * ‖v‖ := by ring
  calc |∑ i, v i * boxAverage n x
          ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)|
      ≤ ∑ i : Fin d, |v i * boxAverage n x
          ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (A * (3 : ℝ) ^ (-((n : ℝ) * s))) * ‖v‖ :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **(L), the Lipschitz obligation.**

The scale-`n` regularization of `w` is Lipschitz with constant `d · A ·
3^{-ns}`, exactly the shape
`HomLiftTelescope.holderSeminormBoundOn_of_increments` consumes. -/
theorem abs_boxRegularization_sub_le {m : ℤ} {s A : ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ) {n : ℤ} (hn : n ≤ m) (x y : Vec d) :
    |boxRegularization n ψ w x - boxRegularization n ψ w y|
      ≤ (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) * ‖x - y‖ := by
  have hdiff : Differentiable ℝ (boxRegularization n ψ w) :=
    differentiable_boxRegularization hwI.locallyIntegrable hwc hψ n
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := boxRegularization n ψ w) (s := (Set.univ : Set (Vec d)))
    (C := (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)))
    (fun z _ => hdiff z)
    (fun z _ => norm_fderiv_boxRegularization_le hw hwI hwc hGI hgauge hψ hn z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rwa [Real.norm_eq_abs] at hmv

end

end Algsuperdiff.Section4.Provider.Homogenization
