/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
/-!
# The generator of a diffusion

`diffusionGenerator b σ F x = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]` for drift `b` and noise
columns
`σ_k`, coordinate-free on a normed space; it is invariant under continuous linear changes of
coordinates
(`diffusionGenerator_transport`), which moves a diffusion on a finite-dimensional state space (for
BKL
arXiv:2610.05474v1 (67), the parameter space `E × (E →L[ℝ] E)`) to coordinates `Fin N → ℝ`.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.Diffusion

/-- `𝓛F(x) = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]`. -/
noncomputable def diffusionGenerator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) : ℝ :=
  fderiv ℝ F x (b x) + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ F) x (σ x k) (σ x k)

/--
A diffusion generator with continuous drift and noise maps `C²` functions to continuous functions.
-/
theorem continuous_diffusionGenerator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {b : V → V} {σ : V → Fin d → V} {F : V → ℝ} (hb : Continuous b)
    (hσ : ∀ k, Continuous (fun x => σ x k)) (hF : ContDiff ℝ 2 F) :
    Continuous (diffusionGenerator b σ F) := by
  have hfirst : Continuous (fun x => fderiv ℝ F x (b x)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply hb
  have hsecond (k : Fin d) : Continuous (fun x => fderiv ℝ (fderiv ℝ F) x (σ x k) (σ x k)) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact ((hfd.continuous_fderiv one_ne_zero).clm_apply (hσ k)).clm_apply (hσ k)
  exact hfirst.add (continuous_const.mul (continuous_finsetSum _ (fun k _ => hsecond k)))

section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Coordinates of a finite-dimensional state space (`N = finrank ℝ V` definitionally). -/
noncomputable def stateEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
  (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv

/-- Transported drift / noise. -/
noncomputable def transportDrift {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (Φ : V ≃L[ℝ] V') (b : V → V) : V' → V' := fun y => Φ (b (Φ.symm y))

noncomputable def transportNoise {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (σ : V → Fin d → V) : V' → Fin d → V' :=
  fun y k => Φ (σ (Φ.symm y) k)

/-- The coordinate-free generator is invariant under a continuous linear change of
coordinates (no differentiability hypothesis is needed for a linear equivalence). -/
theorem diffusionGenerator_transport {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
      diffusionGenerator b σ F x := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  let A := Φ.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have he : fderiv ℝ (F ∘ Φ.symm) = A ∘ ((fderiv ℝ F) ∘ Φ.symm) := by
    funext y
    rw [Φ.symm.comp_right_fderiv]
    ext z
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₂ (u : V) :
      fderiv ℝ (fderiv ℝ (F ∘ Φ.symm)) (Φ x) (Φ u) (Φ u) =
        fderiv ℝ (fderiv ℝ F) x u u := by
    rw [he, A.comp_fderiv, Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₁ :
      fderiv ℝ (F ∘ Φ.symm) (Φ x) (Φ (b x)) = fderiv ℝ F x (b x) := by
    rw [Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [diffusionGenerator, transportDrift, transportNoise,
    ContinuousLinearEquiv.symm_apply_apply, h₁, h₂]

end Adapter

end FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

section GeneratorChainRule



/-! Chain rule for the generator, the step (82) of BKL. -/

/--
**Chain rule for the generator** (Itô's formula for a composite, the step (82) of BKL
arXiv:2610.05474v1):
`𝓛(Φ ∘ G) = DΦ[DG·b + ½ Σ_k D²G[σ_k, σ_k]] + ½ Σ_k D²Φ[DG·σ_k, DG·σ_k]`. -/
theorem diffusionGenerator_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V) (Φ : W → ℝ)
    (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x)
          (fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) *
          ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hΦ₂ : ContDiff ℝ (1 + 1) Φ := by convert hΦ using 1; norm_num
  have hG₂ : ContDiff ℝ (1 + 1) G := by convert hG using 1; norm_num
  have hΦf : ContDiff ℝ 1 (fderiv ℝ Φ) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := Φ) (n := 1)).mp hΦ₂ |>.2.2
  have hGf : ContDiff ℝ 1 (fderiv ℝ G) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := G) (n := 1)).mp hG₂ |>.2.2
  have hΦfd : Differentiable ℝ (fderiv ℝ Φ) := hΦf.differentiable_one
  have hGfd : Differentiable ℝ (fderiv ℝ G) := hGf.differentiable_one
  have hfirst : fderiv ℝ (Φ ∘ G) = fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y := by
    funext y
    simpa only [Function.comp_apply] using
      (fderiv_comp y hΦd.differentiableAt hGd.differentiableAt)
  have hfirst_apply (u : V) : fderiv ℝ (Φ ∘ G) x u = fderiv ℝ Φ (G x) (fderiv ℝ G x u) := by
    rw [hfirst]
    simp only [ContinuousLinearMap.comp_apply]
  have hc : DifferentiableAt ℝ (fun y : V => fderiv ℝ Φ (G y)) x := by
    change DifferentiableAt ℝ ((fderiv ℝ Φ) ∘ G) x
    exact (hΦfd.comp hGd).differentiableAt
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x := hGfd.differentiableAt
  have hcderiv :
    fderiv ℝ (fun y : V => fderiv ℝ Φ (G y)) x = fderiv ℝ (fderiv ℝ Φ) (G x) ∘SL fderiv ℝ G x := by
    change fderiv ℝ ((fderiv ℝ Φ) ∘ G) x = _
    exact fderiv_comp x hΦfd.differentiableAt hGd.differentiableAt
  have hdiag (u : V) :
    fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
      fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
        fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) := by
    rw [hfirst, fderiv_clm_comp hc hd, hcderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
  calc
    diffusionGenerator b σ (Φ ∘ G) x =
        fderiv ℝ (Φ ∘ G) x (b x) +
          (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) :=
      rfl
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) +
          (1 / 2 : ℝ) *
            ∑ k,
              (fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
                fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k))) := by
      rw [hfirst_apply]
      exact
        congrArg (fun z : ℝ => fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) + z)
          (congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
            (Finset.sum_congr rfl (fun k hk => hdiag (σ x k))))
    _ =
        fderiv ℝ Φ (G x)
            (fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
          (1 / 2 : ℝ) *
            ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
      rw [map_add, map_smul, map_sum, Finset.sum_add_distrib]
      simp only [smul_eq_mul]
      ring

end GeneratorChainRule

end FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

section LocalGeneratorChainRule



/-! Pointwise chain rule under local `C²` hypotheses. -/

private theorem contDiffAt_fderiv_of_contDiffAt_two {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (h : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (fderiv ℝ f) x := by
  have h₂ : ContDiffAt ℝ ((1 : ℕ) + 1) f x := by
    convert h using 1
    norm_num
  rcases contDiffAt_succ_iff_hasFDerivAt.mp h₂ with ⟨f', hf', hf'cd⟩
  rcases hf' with ⟨u, hu, hfu⟩
  have heq : f' =ᶠ[nhds x] fderiv ℝ f := by
    filter_upwards [hu] with y hy
    exact (hfu y hy).fderiv.symm
  exact hf'cd.congr_of_eventuallyEq heq.symm

section NormedSpace

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem diffusionGenerator_comp_local_second_derivative
    (Φ : W → ℝ) (G : V → W) (x : V)
    (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) (u : V) :
    fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
      fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
        fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) := by
  have hGd : DifferentiableAt ℝ G x :=
    hG.differentiableAt (by norm_num)
  have hΦf : ContDiffAt ℝ 1 (fderiv ℝ Φ) (G x) :=
    contDiffAt_fderiv_of_contDiffAt_two hΦ
  have hGf : ContDiffAt ℝ 1 (fderiv ℝ G) x :=
    contDiffAt_fderiv_of_contDiffAt_two hG
  have hΦfd : DifferentiableAt ℝ (fderiv ℝ Φ) (G x) :=
    hΦf.differentiableAt (by norm_num)
  have hGfd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    hGf.differentiableAt (by norm_num)
  have hΦev : ∀ᶠ z in nhds (G x), ContDiffAt ℝ 2 Φ z :=
    hΦ.eventually (by norm_num)
  have hΦpull : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 Φ (G y) := by
    exact hG.continuousAt.eventually hΦev
  have hfirst_event :
      fderiv ℝ (Φ ∘ G) =ᶠ[nhds x]
        (fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y) := by
    filter_upwards [hG.eventually (by norm_num), hΦpull] with y hyG hyΦ
    simpa only [Function.comp_apply] using
      (fderiv_comp y
        (hyΦ.differentiableAt (by norm_num))
        (hyG.differentiableAt (by norm_num)))
  have hsecond :
      fderiv ℝ (fderiv ℝ (Φ ∘ G)) x =
        fderiv ℝ (fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y) x :=
    hfirst_event.fderiv_eq
  have hc :
      DifferentiableAt ℝ (fun y : V => fderiv ℝ Φ (G y)) x := by
    change DifferentiableAt ℝ ((fderiv ℝ Φ) ∘ G) x
    exact hΦfd.comp x hGd
  have hcderiv :
      fderiv ℝ (fun y : V => fderiv ℝ Φ (G y)) x =
        fderiv ℝ (fderiv ℝ Φ) (G x) ∘SL fderiv ℝ G x := by
    change fderiv ℝ ((fderiv ℝ Φ) ∘ G) x = _
    exact fderiv_comp x hΦfd hGd
  rw [hsecond, fderiv_clm_comp hc hGfd, hcderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/--
**Chain rule for the generator, local form** (Itô's formula for a composite, step (82) of BKL
arXiv:2610.05474v1, at one point): if `Φ` is `C²` near `G x` and `G` is `C²` near `x`, then
`𝓛(Φ ∘ G)(x) = DΦ(G x)[DG·b + ½ Σ_k D²G[σ_k, σ_k]] + ½ Σ_k D²Φ(G x)[DG·σ_k, DG·σ_k]`. -/
theorem diffusionGenerator_comp_of_contDiffAt {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x)
          (fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) *
          ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
  have hΦd : DifferentiableAt ℝ Φ (G x) := hΦ.differentiableAt (by norm_num)
  have hGd : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  have hfirst : fderiv ℝ (Φ ∘ G) x = fderiv ℝ Φ (G x) ∘SL fderiv ℝ G x := by
    simpa only [Function.comp_apply] using (fderiv_comp x hΦd hGd)
  have hdiag (u : V) :
    fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
      fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
        fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) :=
    diffusionGenerator_comp_local_second_derivative Φ G x hΦ hG u
  calc
    diffusionGenerator b σ (Φ ∘ G) x =
        fderiv ℝ (Φ ∘ G) x (b x) +
          (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) :=
      rfl
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) +
          (1 / 2 : ℝ) *
            ∑ k,
              (fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
                fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k))) := by
      have hsum :
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) =
          (1 / 2 : ℝ) *
            ∑ k,
              (fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
                fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k))) := by
        apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
        exact Finset.sum_congr rfl (fun k _hk => hdiag (σ x k))
      rw [hfirst]
      simp only [ContinuousLinearMap.comp_apply]
      exact congrArg (fun z : ℝ => fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) + z) hsum
    _ =
        fderiv ℝ Φ (G x)
            (fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
          (1 / 2 : ℝ) *
            ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
      rw [map_add, map_smul, map_sum, Finset.sum_add_distrib]
      simp only [smul_eq_mul]
      ring

end NormedSpace

end LocalGeneratorChainRule

end FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

/-- **Product rule for the generator** (carré du champ): for `u, v` that are `C²` at `x`,
`𝓛(uv) = u 𝓛v + v 𝓛u + Σ_k Du[σ_k] Dv[σ_k]`. -/
theorem diffusionGenerator_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y * v y) x =
      u x * diffusionGenerator b σ v x + v x * diffusionGenerator b σ u x +
        ∑ k, fderiv ℝ u x (σ x k) * fderiv ℝ v x (σ x k) := by
  have hu' : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x := hv.differentiableAt (by norm_num)
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod :
      (fun y => fderiv ℝ (fun z => u z * v z) y) =ᶠ[nhds x]
        (fun y => u y • fderiv ℝ v y + v y • fderiv ℝ u y) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
    exact fderiv_fun_mul (hyu.differentiableAt (by norm_num))
      (hyv.differentiableAt (by norm_num))
  have hD :
      HasFDerivAt
        (fun y => u y • fderiv ℝ v y + v y • fderiv ℝ u y)
        ((u x • fderiv ℝ (fderiv ℝ v) x +
            (fderiv ℝ u x).smulRight (fderiv ℝ v x)) +
          (v x • fderiv ℝ (fderiv ℝ u) x +
            (fderiv ℝ v x).smulRight (fderiv ℝ u x))) x :=
    (hu'.hasFDerivAt.smul hfv.hasFDerivAt).add
      (hv'.hasFDerivAt.smul hfu.hasFDerivAt)
  have hsecond (a : V) :
      fderiv ℝ (fderiv ℝ (fun y => u y * v y)) x a a =
        u x * fderiv ℝ (fderiv ℝ v) x a a +
          v x * fderiv ℝ (fderiv ℝ u) x a a +
            2 * (fderiv ℝ u x a * fderiv ℝ v x a) := by
    rw [hprod.fderiv_eq, hD.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  unfold diffusionGenerator
  rw [fderiv_fun_mul hu' hv']
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hsecond]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end FunctionalInequalities.Probability.Diffusion
