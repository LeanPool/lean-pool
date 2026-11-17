/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The vector-valued generator

`vectorGenerator b σ G x = DG(x)[b x] + ½ Σ_k D²G(x)[σ_k x, σ_k x]` (the drift of `G(X_t)`), equal
to `diffusionGenerator`
for scalar `G`, and its behaviour under continuous linear maps, products and finite families.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace FunctionalInequalities.Probability.Diffusion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

/--
The vector-valued generator `𝓛G(x) = DG(x)[b x] + ½ Σ_k D²G(x)[σ_k x, σ_k x]` of a `W`-valued
function
(the drift of `G(X_t)` in Itô's formula; BKL arXiv:2610.05474v1, (81)–(82)). -/
def vectorGenerator {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (b : V → V)
    (σ : V → Fin d → V) (G : V → W) (x : V) : W :=
  fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)

/-- For scalar functions the vector generator is the generator. -/
theorem diffusionGenerator_eq_vectorGenerator (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator b σ F x = vectorGenerator b σ F x := by
  simp only [diffusionGenerator, vectorGenerator, smul_eq_mul]

section NormedSpace

variable {W W' : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- The derivative of a continuous linear map applied to a differentiable function. -/
theorem fderiv_clm_comp_apply_vec (ℓ : W →L[ℝ] W') {G : V → W} {x : V}
    (hG : DifferentiableAt ℝ G x) (v : V) :
    fderiv ℝ (fun y => ℓ (G y)) x v = ℓ (fderiv ℝ G x v) := by
  exact congrArg (fun q : V →L[ℝ] W' => q v)
    (ℓ.hasFDerivAt.comp x hG.hasFDerivAt).fderiv

/-- The vector generator commutes with continuous linear maps. -/
theorem vectorGenerator_clm_comp (b : V → V) (σ : V → Fin d → V)
    (ℓ : W →L[ℝ] W') {G : V → W} {x : V} (hG : ContDiffAt ℝ 2 G x) :
    vectorGenerator b σ (fun y => ℓ (G y)) x = ℓ (vectorGenerator b σ G x) := by
  have hG' : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  have htwo : ContDiffWithinAt ℝ ((1 : WithTop ℕ∞) + 1) G Set.univ x := by
    convert hG.contDiffWithinAt using 1
    norm_num
  obtain ⟨u, hu, _, _, f', huf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt'
      (𝕜 := ℝ) (f := G) (s := Set.univ) (x := x)
      (n := (1 : WithTop ℕ∞)) (by norm_num)).mp htwo
  have hu' : u ∈ nhds x := by
    simpa using hu
  have huf_at : ∀ y ∈ u, HasFDerivAt G (f' y) y := by
    intro y hy
    exact hasFDerivWithinAt_univ.mp (huf' y hy)
  have hf'd : DifferentiableAt ℝ f' x :=
    (contDiffWithinAt_univ.mp hf').differentiableAt (by norm_num)
  have hfg : ∀ y ∈ u, fderiv ℝ G y = f' y := by
    intro y hy
    exact (huf_at y hy).fderiv
  let L : (V →L[ℝ] W) →L[ℝ] (V →L[ℝ] W') :=
    ContinuousLinearMap.compL ℝ V W W' ℓ
  have heq : Filter.EventuallyEq (nhds x) (fderiv ℝ G) f' := by
    filter_upwards [hu'] with y hy
    exact hfg y hy
  have heq₁ :
      Filter.EventuallyEq (nhds x)
        (fderiv ℝ (fun y => ℓ (G y))) (fun y => L (f' y)) := by
    filter_upwards [hu'] with y hy
    apply ContinuousLinearMap.ext
    intro z
    calc
      fderiv ℝ (fun t => ℓ (G t)) y z = ℓ (fderiv ℝ G y z) :=
        fderiv_clm_comp_apply_vec ℓ (huf_at y hy).differentiableAt z
      _ = ℓ (f' y z) := by rw [hfg y hy]
      _ = L (f' y) z := rfl
  have hsecond (v w : V) :
      fderiv ℝ (fderiv ℝ (fun y => ℓ (G y))) x v w =
        ℓ (fderiv ℝ (fderiv ℝ G) x v w) := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => ℓ (G y))) x v w =
          fderiv ℝ (fun y => L (f' y)) x v w := by
            rw [heq₁.fderiv_eq]
      _ = L (fderiv ℝ f' x v) w :=
        congrArg (fun q : V →L[ℝ] W' => q w)
          (fderiv_clm_comp_apply_vec L hf'd v)
      _ = ℓ (fderiv ℝ f' x v w) := rfl
      _ = ℓ (fderiv ℝ (fderiv ℝ G) x v w) := by
        rw [heq.fderiv_eq]
  simp only [vectorGenerator]
  rw [fderiv_clm_comp_apply_vec ℓ hG' (b x)]
  simp_rw [hsecond]
  simp only [map_add, map_smul, map_sum]

end NormedSpace

section NormedSpace

variable {W₁ W₂ : Type*}
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- The vector generator of a pair is the pair of vector generators. -/
theorem vectorGenerator_prodMk (b : V → V) (σ : V → Fin d → V)
    {G₁ : V → W₁} {G₂ : V → W₂} {x : V} (h₁ : ContDiffAt ℝ 2 G₁ x) (h₂ : ContDiffAt ℝ 2 G₂ x) :
    vectorGenerator b σ (fun y => (G₁ y, G₂ y)) x =
      (vectorGenerator b σ G₁ x, vectorGenerator b σ G₂ x) := by
  apply Prod.ext
  · exact
      (vectorGenerator_clm_comp b σ
        (ContinuousLinearMap.fst ℝ W₁ W₂) (h₁.prodMk h₂)).symm
  · exact
      (vectorGenerator_clm_comp b σ
        (ContinuousLinearMap.snd ℝ W₁ W₂) (h₁.prodMk h₂)).symm

/-- The vector generator of a finite family is computed componentwise. -/
theorem vectorGenerator_pi {ι : Type*} [Fintype ι] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (b : V → V) (σ : V → Fin d → V) {G : V → ι → W} {x : V}
    (hG : ∀ i, ContDiffAt ℝ 2 (fun y => G y i) x) :
    vectorGenerator b σ G x = fun i => vectorGenerator b σ (fun y => G y i) x := by
  have h : ContDiffAt ℝ 2 G x := contDiffAt_pi.mpr hG
  funext i
  exact (vectorGenerator_clm_comp b σ (ContinuousLinearMap.proj i : (ι → W) →L[ℝ] W) h).symm

/-- The derivative of a pair, applied to a vector. -/
theorem fderiv_prodMk_apply_vec {G₁ : V → W₁} {G₂ : V → W₂} {x : V}
    (h₁ : DifferentiableAt ℝ G₁ x) (h₂ : DifferentiableAt ℝ G₂ x) (v : V) :
    fderiv ℝ (fun y => (G₁ y, G₂ y)) x v = (fderiv ℝ G₁ x v, fderiv ℝ G₂ x v) := by
  exact congrArg (fun q => q v) (h₁.fderiv_prodMk h₂)

end NormedSpace

/-- The derivative of a componentwise differentiable family, applied to a vector. -/
theorem fderiv_pi_apply_vec {ι : Type*} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : V → ι → W} {x : V} (hG : ∀ i, DifferentiableAt ℝ (fun y => G y i) x) (v : V) :
    fderiv ℝ G x v = fun i => fderiv ℝ (fun y => G y i) x v := by
  rw [fderiv_pi hG]
  funext i
  exact ContinuousLinearMap.pi_apply _ _ _

end FunctionalInequalities.Probability.Diffusion
