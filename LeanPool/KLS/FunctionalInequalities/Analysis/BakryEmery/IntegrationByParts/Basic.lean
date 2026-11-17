/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Laplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Weighted integration by parts

Haar integration by parts and its tilted-measure specialization. The pointwise
weighted Laplacian and its regularity are provided by Laplacian.lean; no convexity is used. The
compact-test directional identity `∫ ∂ᵥF · g = −∫ F · ∂ᵥg` for smooth `F`, `g` with either one
compactly
supported derives its integrability from the compact support.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

section CompactTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/--
The three directional Haar integration-by-parts integrands are integrable as soon as one of the two
smooth factors has compact support (normed-space scope; no inner product, no finite dimension). -/
theorem integrable_fderiv_mul_of_hasCompactSupport (m : Measure E) [m.IsAddHaarMeasure]
    {F g : E → ℝ} (hF : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport F ∨ HasCompactSupport g) (v : E) :
    Integrable (fun x => fderiv ℝ F x v * g x) m ∧
      Integrable (fun x => F x * fderiv ℝ g x v) m ∧ Integrable (fun x => F x * g x) m := by
  have hFv : Continuous (fun x => fderiv ℝ F x v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgv : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc1 : HasCompactSupport (fun x => fderiv ℝ F x v * g x) := by
    rcases hc with hf | hg
    · exact (hf.fderiv_apply ℝ v).mul_right
    · exact hg.mul_left
  have hc2 : HasCompactSupport (fun x => F x * fderiv ℝ g x v) := by
    rcases hc with hf | hg
    · exact hf.mul_right
    · exact (hg.fderiv_apply ℝ v).mul_left
  have hc3 : HasCompactSupport (fun x => F x * g x) := by
    rcases hc with hf | hg
    · exact hf.mul_right
    · exact hg.mul_left
  exact
    ⟨(hFv.mul hg.continuous).integrable_of_hasCompactSupport hc1,
      (hF.continuous.mul hgv).integrable_of_hasCompactSupport hc2,
      (hF.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc3⟩

/-- Directional Haar integration by parts with either smooth factor compactly supported:
`∫ ∂ᵥF · g = −∫ F · ∂ᵥg` (normed-space scope, finite dimension). -/
theorem integral_fderiv_mul_eq_neg_of_hasCompactSupport (m : Measure E) [m.IsAddHaarMeasure]
    {F g : E → ℝ} (hF : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport F ∨ HasCompactSupport g) (v : E) :
    (∫ x, fderiv ℝ F x v * g x ∂m) = -∫ x, F x * fderiv ℝ g x v ∂m := by
  obtain ⟨h1, h2, h3⟩ := integrable_fderiv_mul_of_hasCompactSupport m hF hg hc v
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := m) h1 h2 h3
    (fun x _ => hF.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x) (v := v)
  linarith only [h]

end CompactTest

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The gradient of the normalised tilted weight `exp (-U) / Z` is `-(exp (-U) / Z) ∇U`. -/
theorem inner_gradient_tilted_weight {U : E → ℝ} (hU : ContDiff ℝ 1 U) (Z : ℝ) (x y : E) :
    ⟪gradient (fun z => Real.exp ((-U) z) / Z) x, y⟫ =
      -(Real.exp ((-U) x) / Z) * ⟪gradient U x, y⟫ := by
  have hd : HasFDerivAt (fun z => Real.exp ((-U) z) / Z)
      (Z⁻¹ • (Real.exp ((-U) x) • -fderiv ℝ U x)) x := by
    have h1 : HasFDerivAt (fun z => Real.exp ((-U) z)) (Real.exp ((-U) x) • -fderiv ℝ U x) x :=
      ((hU.differentiable one_ne_zero x).hasFDerivAt.neg).exp
    have hfun : (fun z => Real.exp ((-U) z) / Z) = fun z => Real.exp ((-U) z) * Z⁻¹ :=
      funext fun z => div_eq_mul_inv _ _
    rw [hfun]
    exact h1.mul_const Z⁻¹
  rw [inner_gradient_left, hd.fderiv, inner_gradient_left]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

section Haar

variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]

omit [CompleteSpace E] in
/-- One-directional weighted integration by parts against a Haar measure: for a `C¹` weight `w`, a
`C²` compactly supported `f` and a `C¹` function `g`,
`∫ w ∂ᵥf ∂ᵥg = -∫ (w ∂ᵥ∂ᵥf + ∂ᵥw ∂ᵥf) g`. -/
theorem integral_mul_fderiv_mul_fderiv {w f g : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (v : E) :
    ∫ x, w x * (fderiv ℝ f x v * fderiv ℝ g x v) ∂m =
      -∫ x, (w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v) * g x ∂m := by
  set F : E → ℝ := fun x => w x * fderiv ℝ f x v with hF
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hF1 : ContDiff ℝ 1 F := hw.mul (hf1.clm_apply contDiff_const)
  have hFc : HasCompactSupport F := (hfc.fderiv_apply ℝ v).mul_left
  have hFd : ∀ x, HasFDerivAt F
      (w x • ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip v) +
        fderiv ℝ f x v • fderiv ℝ w x) x := fun x =>
    (hw.differentiable one_ne_zero x).hasFDerivAt.mul
      ((hf1.differentiable one_ne_zero x).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have hFderiv : ∀ x, fderiv ℝ F x v =
      w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v := by
    intro x
    rw [(hFd x).fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_zero, ContinuousLinearMap.flip_apply,
      smul_eq_mul, zero_add]
    ring
  have hFcont : Continuous F := hF1.continuous
  have hgcont : Continuous g := hg.continuous
  have hg'cont : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF'cont : Continuous fun x => fderiv ℝ F x v :=
    (hF1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ F x v * g x) m :=
    (hF'cont.mul hgcont).integrable_of_hasCompactSupport (hFc.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun x => F x * fderiv ℝ g x v) m :=
    (hFcont.mul hg'cont).integrable_of_hasCompactSupport hFc.mul_right
  have h3 : Integrable (fun x => F x * g x) m :=
    (hFcont.mul hgcont).integrable_of_hasCompactSupport hFc.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := m) h1 h2 h3
    (fun x _ => (hFd x).differentiableAt) (fun x _ => hg.differentiable one_ne_zero x)
  calc ∫ x, w x * (fderiv ℝ f x v * fderiv ℝ g x v) ∂m
      = ∫ x, F x * fderiv ℝ g x v ∂m := by
        congr 1
        funext x
        simp only [hF]
        ring
    _ = -∫ x, fderiv ℝ F x v * g x ∂m := key
    _ = -∫ x, (w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v) * g x ∂m := by
        congr 2
        funext x
        rw [hFderiv x]

/-- **Weighted integration by parts** against a Haar measure: for a `C¹` weight `w`, a `C²`
compactly supported `f` and a `C¹` function `g`,
`∫ w ⟪∇f, ∇g⟫ dm = -∫ (w Δf + ⟪∇w, ∇f⟫) g dm`, i.e. `∫ ⟪w∇f, ∇g⟫ = -∫ div(w∇f) g`. -/
theorem integral_mul_inner_gradient_eq_neg {w f g : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, w x * ⟪gradient f x, gradient g x⟫ ∂m =
      -∫ x, (w x * Laplacian.laplacian f x + ⟪gradient w x, gradient f x⟫) * g x ∂m := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hf' : Continuous (fderiv ℝ f) := hf1.continuous
  have hf'' : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv one_ne_zero
  have hw' : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hint : ∀ i, Integrable (fun x => w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i))) m := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact
        hw.continuous.mul
          ((hf'.clm_apply continuous_const).mul (hg'.clm_apply continuous_const))
    · exact ((hfc.fderiv_apply ℝ (b i)).mul_right).mul_left
  have hint' :
    ∀ i,
      Integrable
        (fun x =>
          (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) +
              fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) *
            g x)
        m := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact
        ((hw.continuous.mul ((hf''.clm_apply continuous_const).clm_apply continuous_const)).add
              ((hw'.clm_apply continuous_const).mul (hf'.clm_apply continuous_const))).mul
          hg.continuous
    · refine HasCompactSupport.mul_right ?_
      exact
        ((((hfc.fderiv (𝕜 := ℝ)).fderiv_apply ℝ (b i)).comp_left (g := fun A : E →L[ℝ] ℝ =>
                A (b i)) (by simp)).mul_left).add
          ((hfc.fderiv_apply ℝ (b i)).mul_left)
  calc
    ∫ x, w x * ⟪gradient f x, gradient g x⟫ ∂m =
        ∫ x, ∑ i, w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i)) ∂m := by
      congr 1
      funext x
      rw [inner_gradient_eq_sum_fderiv_mul_fderiv, Finset.mul_sum]
    _ = ∑ i, ∫ x, w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i)) ∂m :=
      integral_finsetSum _ fun i _ => hint i
    _ =
        ∑ i,
          -∫ x,
              (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) +
                  fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) *
                g x ∂m :=
      Finset.sum_congr rfl fun i _ => integral_mul_fderiv_mul_fderiv m hw hf hfc hg (b i)
    _ =
        -∫ x,
            ∑ i,
              (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) +
                  fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) *
                g x ∂m := by
      rw [integral_finsetSum _ fun i _ => hint' i, Finset.sum_neg_distrib]
    _ = -∫ x, (w x * Laplacian.laplacian f x + ⟪gradient w x, gradient f x⟫) * g x ∂m := by
      congr 2
      funext x
      rw [laplacian_eq_sum_fderiv_fderiv, inner_gradient_eq_sum_fderiv_mul_fderiv, ←
        Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

end Haar

section Tilted

variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]

/--
**Weighted integration by parts for a tilted Haar measure** (property weighted integration by
parts): with
`μ = m.tilted (-U)` the normalised law of density `exp (-U)`, a `C¹` potential `U`, a `C²`
compactly supported `f` and a `C¹` function `g`,
`∫ ⟪∇f, ∇g⟫ dμ = ∫ (-ℒf) g dμ` where `ℒf = Δf - ⟪∇U, ∇f⟫`. -/
theorem integral_inner_gradient_tilted {U f g : E → ℝ} (hU : ContDiff ℝ 1 U)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-U)) =
      ∫ x, -weightedLaplacian U f x * g x ∂(m.tilted (-U)) := by
  rw [integral_tilted, integral_tilted]
  set Z : ℝ := ∫ x, Real.exp ((-U) x) ∂m with hZ
  have hw : ContDiff ℝ 1 fun z => Real.exp ((-U) z) / Z := by
    have : (fun z => Real.exp ((-U) z) / Z) = fun z => Real.exp ((-U) z) * Z⁻¹ :=
      funext fun z => div_eq_mul_inv _ _
    rw [this]
    exact (hU.neg.exp).mul contDiff_const
  have key := integral_mul_inner_gradient_eq_neg m hw hf hfc hg
  simp only [smul_eq_mul]
  rw [key, ← integral_neg]
  congr 1
  funext x
  rw [inner_gradient_tilted_weight hU Z, weightedLaplacian_apply]
  ring

/-- **Symmetry of the weighted Laplacian on compactly supported `C²` functions.** For
`μ = m.tilted (-U)` and a `C¹` potential `U`, `∫ (ℒf) g dμ = ∫ f (ℒg) dμ`. Both functions must be
`C²` with compact support; no convexity and no `L²` theory is used. This is the classical
self-adjointness of `ℒ` on the smooth compactly supported class, in integrated form. -/
theorem integral_weightedLaplacian_mul_comm {U f g : E → ℝ} (hU : ContDiff ℝ 1 U)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∫ x, weightedLaplacian U f x * g x ∂(m.tilted (-U)) =
      ∫ x, f x * weightedLaplacian U g x ∂(m.tilted (-U)) := by
  have h1 := integral_inner_gradient_tilted m hU hf hfc (hg.of_le (by norm_num))
  have h2 := integral_inner_gradient_tilted m hU hg hgc (hf.of_le (by norm_num))
  have hcomm : ∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-U)) =
      ∫ x, ⟪gradient g x, gradient f x⟫ ∂(m.tilted (-U)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
  have e1 : ∫ x, weightedLaplacian U f x * g x ∂(m.tilted (-U)) =
      -∫ x, -weightedLaplacian U f x * g x ∂(m.tilted (-U)) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, f x * weightedLaplacian U g x ∂(m.tilted (-U)) =
      -∫ x, -weightedLaplacian U g x * f x ∂(m.tilted (-U)) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1, e2, ← h1, ← h2, hcomm]

end Tilted

section Directional

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
**Weighted directional integration by parts** (Letwin arXiv:2607.24164v1, Lemma A.3, pp. 16–17):
for smooth `φ, f, g` with `∫ e^{-φ} dm = 1` and the four integrands `(∂_v f) g`, `f ∂_v g`, `f g ∂_v
φ`,
`f g` integrable under `ν = e^{-φ} m`,
`∫ (∂_v f) g dν = ∫ f ((∂_v φ) g − ∂_v g) dν`.
-/
theorem integral_fderiv_mul_tilted_eq [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure] (φ f g : E → ℝ)
    (v : E) (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hφexp : Integrable (fun x => Real.exp (-φ x)) m) (hφnorm : ∫ x, Real.exp (-φ x) ∂m = 1)
    (hdfg : Integrable (fun x => fderiv ℝ f x v * g x) (m.tilted (-φ)))
    (hfdg : Integrable (fun x => f x * fderiv ℝ g x v) (m.tilted (-φ)))
    (hfgdφ : Integrable (fun x => f x * g x * fderiv ℝ φ x v) (m.tilted (-φ)))
    (hfg : Integrable (fun x => f x * g x) (m.tilted (-φ))) :
    (∫ x, fderiv ℝ f x v * g x ∂(m.tilted (-φ))) =
      ∫ x, f x * (fderiv ℝ φ x v * g x - fderiv ℝ g x v) ∂(m.tilted (-φ)) := by
  let w : E → ℝ := fun x => Real.exp (-φ x)
  let G : E → ℝ := fun x => g x * w x
  have hfd : ∀ x, DifferentiableAt ℝ f x := fun x => hf.differentiable (by simp) x
  have hgd : ∀ x, DifferentiableAt ℝ g x := fun x => hg.differentiable (by simp) x
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable (by simp) x
  have hGd : ∀ x, HasFDerivAt G (g x • (w x • -fderiv ℝ φ x) + w x • fderiv ℝ g x) x := by
    intro x
    exact (hgd x).hasFDerivAt.mul ((hφd x).hasFDerivAt.neg.exp)
  have hGv : ∀ x, fderiv ℝ G x v = w x * fderiv ℝ g x v - w x * g x * fderiv ℝ φ x v := by
    intro x
    rw [(hGd x).fderiv]
    simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
    ring
  have hL1 : Integrable (fun x => w x * (fderiv ℝ f x v * g x)) m := by
    simpa only [Pi.neg_apply, smul_eq_mul] using (integrable_tilted_iff hφexp _).mp hdfg
  have hD1 : Integrable (fun x => w x * (f x * fderiv ℝ g x v)) m := by
    simpa only [Pi.neg_apply, smul_eq_mul] using (integrable_tilted_iff hφexp _).mp hfdg
  have hD2 : Integrable (fun x => w x * (f x * g x * fderiv ℝ φ x v)) m := by
    simpa only [Pi.neg_apply, smul_eq_mul] using (integrable_tilted_iff hφexp _).mp hfgdφ
  have hF1 : Integrable (fun x => fderiv ℝ f x v * G x) m := by
    convert hL1 using 1
    funext x
    dsimp [G]
    ring
  have hF2 : Integrable (fun x => f x * fderiv ℝ G x v) m := by
    convert hD1.sub hD2 using 1
    funext x
    simp only [hGv, Pi.sub_apply]
    ring
  have hF3 : Integrable (fun x => f x * G x) m := by
    have hh := (integrable_tilted_iff hφexp _).mp hfg
    convert hh using 1
    funext x
    simp only [G, w, smul_eq_mul]
    ring
  have hkey :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := m) hF1 hF2 hF3 (fun x _ => hfd x)
      (fun x _ => (hGd x).differentiableAt)
  rw [integral_tilted, integral_tilted]
  simp only [Pi.neg_apply, hφnorm, div_one, smul_eq_mul]
  calc
    _ = ∫ x, fderiv ℝ f x v * G x ∂m := by
      congr 1
      funext x
      dsimp [G, w]
      ring
    _ = -∫ x, f x * fderiv ℝ G x v ∂m := by linarith only [hkey]
    _ = ∫ x, -(f x * fderiv ℝ G x v) ∂m := (integral_neg _).symm
    _ = _ := by
      congr 1
      funext x
      rw [hGv]
      dsimp [w]
      ring

/--
**Mean Hessian equals the gradient second moment** under `e^{-φ}m` (Letwin Lemma 2.3, step 1): the
directional integration by parts applied to `∂_u φ` and
`g = 1`. -/
theorem integral_fderiv_fderiv_tilted_eq_integral_mul [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure] (φ : E → ℝ)
    (u v : E) (hφ : ContDiff ℝ ∞ φ) (hφexp : Integrable (fun x => Real.exp (-φ x)) m)
    (hφnorm : ∫ x, Real.exp (-φ x) ∂m = 1)
    (hdd : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y u) x v) (m.tilted (-φ)))
    (hdd' : Integrable (fun x => fderiv ℝ φ x u * fderiv ℝ φ x v) (m.tilted (-φ)))
    (hd : Integrable (fun x => fderiv ℝ φ x u) (m.tilted (-φ))) :
    (∫ x, fderiv ℝ (fun y => fderiv ℝ φ y u) x v ∂(m.tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(m.tilted (-φ)) := by
  have hF : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y u) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdfg :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y u) x v * (1 : ℝ)) (m.tilted (-φ)) := by
    simpa only [mul_one] using hdd
  have hfdg :
    Integrable (fun x => fderiv ℝ φ x u * fderiv ℝ (fun _ : E => (1 : ℝ)) x v)
      (m.tilted (-φ)) := by
    have hz : Integrable (0 : E → ℝ) (m.tilted (-φ)) := integrable_zero E ℝ (m.tilted (-φ))
    refine hz.congr (Filter.Eventually.of_forall ?_)
    intro x
    simp
  have hfgdφ :
    Integrable (fun x => fderiv ℝ φ x u * (1 : ℝ) * fderiv ℝ φ x v) (m.tilted (-φ)) := by
    simpa only [mul_one] using hdd'
  have hfg : Integrable (fun x => fderiv ℝ φ x u * (1 : ℝ)) (m.tilted (-φ)) := by
    simpa only [mul_one] using hd
  have h :=
    integral_fderiv_mul_tilted_eq (m := m) (φ := φ) (f := fun y => fderiv ℝ φ y u) (g :=
      fun _ : E => (1 : ℝ)) (v := v) (hφ := hφ) (hf := hF) (hg := contDiff_const) (hφexp :=
      hφexp) (hφnorm := hφnorm) (hdfg := hdfg) (hfdg := hfdg) (hfgdφ := hfgdφ) (hfg := hfg)
  simp only [mul_one] at h
  rw [h]
  congr 1
  funext x
  simp

end InnerProduct

end Directional

end FunctionalInequalities.Analysis.BakryEmery
