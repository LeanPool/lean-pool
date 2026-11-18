/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Hessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator

/-!
# Bochner's identity at `C^{1,1}`

`∫ (ℒf)² dν = ∫ (‖∇²f‖² + ⟪D∇U ∇f, ∇f⟫) dν` for compactly supported smooth `f` and a Lipschitz `C¹`
potential `U` with
Lipschitz gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

private lemma compact_norm_bound
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {g : X → F} (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hg).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (g x) ⟨x, rfl⟩).trans (le_max_left _ _)

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]

section HessianSquares

omit [CompleteSpace E]
private lemma continuous_hessian_square {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (hessianSqStdBasis f) := by
  classical
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun _ _ =>
      (((hf.fderiv_right (m := 1) (by decide)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const |>.clm_apply continuous_const).pow 2

private lemma compact_hessian_square {f : E → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (hessianSqStdBasis f) := by
  classical
  refine ((hc.fderiv ℝ).fderiv ℝ).mono ?_
  intro x hx hz
  exact hx (by simp [hessianSqStdBasis, bilinearIteratedFDerivTwo, hz])

end HessianSquares

private lemma laplacian_perturbation_bound (U V g : E → ℝ) (x : E) {C : ℝ}
    (hC : ‖gradient V x - gradient U x‖ ≤ C) :
    ‖weightedLaplacian V g x‖ ≤
      ‖weightedLaplacian U g x‖ + C * ‖gradient g x‖ := by
  have he :
      weightedLaplacian V g x =
        weightedLaplacian U g x -
          ⟪gradient V x - gradient U x, gradient g x⟫ := by
    simp only [weightedLaplacian_apply, inner_sub_left]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add le_rfl
      ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _))))

variable [MeasurableSpace E] [BorelSpace E]

/-- Keep the integration measure fixed while varying the smooth potential in Γ₂. -/
private lemma mixed_integral_identity {U V f : E → ℝ}
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, hessianSqStdBasis f x +
        ⟪fderiv ℝ (gradient V) x (gradient f x), gradient f x⟫
        ∂((volume : Measure E).tilted (-U))) =
      (∫ x, weightedLaplacian V (gamma f f) x
        ∂((volume : Measure E).tilted (-U))) / 2 +
      ∫ x, weightedLaplacian U f x * weightedLaplacian V f x
        ∂((volume : Measure E).tilted (-U)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by decide)
  have ha : ContDiff ℝ 2 (gamma f f) :=
    contDiff_gamma hf3 hf3 (by norm_num) (by norm_num)
  have haC := hasCompactSupport_gamma_left f hc
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hLV : ContDiff ℝ 1 (weightedLaplacian V f) :=
    contDiff_weightedLaplacian hV hf3 (by norm_num) (by norm_num)
  have hiQ : Integrable (weightedLaplacian V (gamma f f))
      ((volume : Measure E).tilted (-U)) :=
    (continuous_weightedLaplacian hV1 ha).integrable_of_hasCompactSupport
      (hasCompactSupport_weightedLaplacian V haC)
  have hiB : Integrable (gamma f (weightedLaplacian V f))
      ((volume : Measure E).tilted (-U)) :=
    (continuous_gamma hf1 hLV).integrable_of_hasCompactSupport
      (hasCompactSupport_gamma_left (weightedLaplacian V f) hc)
  have hibp :
      (∫ x, gamma f (weightedLaplacian V f) x
        ∂((volume : Measure E).tilted (-U))) =
      -(∫ x, weightedLaplacian U f x * weightedLaplacian V f x
        ∂((volume : Measure E).tilted (-U))) := by
    calc
      _ = ∫ x, -weightedLaplacian U f x * weightedLaplacian V f x
          ∂((volume : Measure E).tilted (-U)) :=
        integral_inner_gradient_tilted volume hU hf2 hc hLV
      _ = _ := by simp only [neg_mul, integral_neg]
  calc
    _ = ∫ x, weightedLaplacian V (gamma f f) x / 2 -
        gamma f (weightedLaplacian V f) x
        ∂((volume : Measure E).tilted (-U)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        have he := gammaTwo_eq_hessianSqStdBasis_add hV hf3 x
        rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hV] at he
        exact he.symm
    _ = _ := by
      rw [integral_sub (hiQ.div_const 2) hiB, integral_div, hibp]
      ring

end Helpers

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Bochner identity for a Lipschitz potential with Lipschitz gradient** (Brascamp–Lieb at
`C^{1,1}`): for `U ∈ C¹` Lipschitz with `G`-Lipschitz gradient and integrable
`e^{-U}`, and `f ∈ C_c^∞`, `∫ (ℒf)² dν = ∫ (‖∇²f‖² + ⟪D(∇U) ∇f, ∇f⟫) dν` with `ν = e^{-U} dx`
normalized, `ℒf = Δf − ⟪∇U, ∇f⟫`, and `D(∇U)` the a.e. derivative of the Lipschitz map `∇U`. -/
theorem integral_weightedLaplacian_sq_eq_of_lipschitz_gradient {U : E → ℝ} (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E)) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) =
      ∫ x,
        (hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient U) x (gradient f x),
            gradient f x⟫) ∂((volume : Measure E).tilted (-U)) := by
  classical
  have _hL := hL
  have _hexp := hexp
  obtain ⟨V, hV, he, hVG, _, hD⟩ :=
    FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient hU hG
  let μ : Measure E := (volume : Measure E).tilted (-U)
  let a : E → ℝ := gamma f f
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by decide)
  have ha2 : ContDiff ℝ 2 a := contDiff_gamma hf3 hf3 (by norm_num) (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha2.of_le (by norm_num)
  have hac : HasCompactSupport a := hasCompactSupport_gamma_left f hfc
  have hgf : Continuous (gradient f) := continuous_gradient hf1
  have hga : Continuous (gradient a) := continuous_gradient ha1
  have hLf : Continuous (weightedLaplacian U f) := continuous_weightedLaplacian hU hf2
  have hLa : Continuous (weightedLaplacian U a) := continuous_weightedLaplacian hU ha2
  have hS : Continuous (hessianSqStdBasis f) := continuous_hessian_square hf
  obtain ⟨B, hB0, hB⟩ := compact_norm_bound hgf (hasCompactSupport_gradient hfc)
  obtain ⟨D, hD0, hDb⟩ := compact_norm_bound hga (hasCompactSupport_gradient hac)
  obtain ⟨M, hM0, hM⟩ := compact_norm_bound hLf (hasCompactSupport_weightedLaplacian U hfc)
  obtain ⟨N, hN0, hN⟩ := compact_norm_bound hLa (hasCompactSupport_weightedLaplacian U hac)
  obtain ⟨S, hS0, hSb⟩ := compact_norm_bound hS (compact_hessian_square hfc)
  have herror (k : ℕ) (x : E) : ‖gradient (V k) x - gradient U x‖ ≤ (G : ℝ) :=
    (he k x).trans
      (div_le_self G.coe_nonneg
        (by
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith))
  have hgradlim (x : E) : Tendsto (fun k => gradient (V k) x) atTop (𝓝 (gradient U x)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm (fun k => he k x)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (G : ℝ)
    simpa only [mul_zero, mul_one_div] using ht
  have hLVlim (g : E → ℝ) (x : E) :
    Tendsto (fun k => weightedLaplacian (V k) g x) atTop (𝓝 (weightedLaplacian U g x)) := by
    exact tendsto_const_nhds.sub ((hgradlim x).inner tendsto_const_nhds)
  have hLVf (k : ℕ) (x : E) : ‖weightedLaplacian (V k) f x‖ ≤ M + (G : ℝ) * B := by
    exact
      (laplacian_perturbation_bound U (V k) f x (herror k x)).trans
        (add_le_add (hM x) (mul_le_mul_of_nonneg_left (hB x) G.coe_nonneg))
  have hLVa (k : ℕ) (x : E) : ‖weightedLaplacian (V k) a x‖ ≤ N + (G : ℝ) * D := by
    exact
      (laplacian_perturbation_bound U (V k) a x (herror k x)).trans
        (add_le_add (hN x) (mul_le_mul_of_nonneg_left (hDb x) G.coe_nonneg))
  have hQ :
    Tendsto (fun k => ∫ x, weightedLaplacian (V k) a x ∂μ) atTop
      (𝓝 (∫ x, weightedLaplacian U a x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => N + (G : ℝ) * D)
    · intro k
      exact (continuous_weightedLaplacian ((hV k).of_le (by decide)) ha2).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall (hLVa k)
    · exact Eventually.of_forall (hLVlim a)
  have hP :
    Tendsto (fun k => ∫ x, weightedLaplacian U f x * weightedLaplacian (V k) f x ∂μ) atTop
      (𝓝 (∫ x, weightedLaplacian U f x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M * (M + (G : ℝ) * B))
    · intro k
      exact
        (hLf.mul
            (continuous_weightedLaplacian ((hV k).of_le (by decide)) hf2)).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      apply Eventually.of_forall
      intro x
      rw [norm_mul]
      exact mul_le_mul (hM x) (hLVf k x) (norm_nonneg _) hM0
    · apply Eventually.of_forall
      intro x
      simpa only [pow_two] using (hLVlim f x).const_mul (weightedLaplacian U f x)
  have hHcont (k : ℕ) :
    Continuous
      (fun x =>
        hessianSqStdBasis f x + ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫) := by
    have hg : ContDiff ℝ 1 (gradient (V k)) := contDiff_gradient (hV k) (by decide)
    exact hS.add (((hg.continuous_fderiv one_ne_zero).clm_apply hgf).inner hgf)
  have hHbound (k : ℕ) (x : E) :
    ‖hessianSqStdBasis f x + ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫‖ ≤
      S + (G : ℝ) * B * B := by
    have hop : ‖fderiv ℝ (gradient (V k)) x‖ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hVG k)
    have happ : ‖fderiv ℝ (gradient (V k)) x (gradient f x)‖ ≤ (G : ℝ) * B :=
      ((fderiv ℝ (gradient (V k)) x).le_opNorm (gradient f x)).trans
        (mul_le_mul hop (hB x) (norm_nonneg _) G.coe_nonneg)
    exact
      (norm_add_le _ _).trans
        (add_le_add (hSb x)
          ((norm_inner_le_norm _ _).trans
            (mul_le_mul happ (hB x) (norm_nonneg _) (mul_nonneg G.coe_nonneg hB0))))
  have hDμ :
    ∀ᵐ x ∂μ,
      Tendsto (fun k => fderiv ℝ (gradient (V k)) x) atTop (𝓝 (fderiv ℝ (gradient U) x)) :=
    (tilted_absolutelyContinuous (volume : Measure E) (-U)).ae_le hD
  have hH :
    Tendsto
      (fun k =>
        ∫ x,
          hessianSqStdBasis f x + ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫ ∂μ)
      atTop
      (𝓝
        (∫ x,
          hessianSqStdBasis f x + ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => S + (G : ℝ) * B * B)
    · intro k
      exact (hHcont k).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall (hHbound k)
    · filter_upwards [hDμ] with x hx
      have hev : Continuous (fun A : E →L[ℝ] E => A (gradient f x)) :=
        continuous_id.clm_apply continuous_const
      exact tendsto_const_nhds.add (((hev.tendsto _).comp hx).inner tendsto_const_nhds)
  have hzero : ∫ x, weightedLaplacian U a x ∂μ = 0 := by
    have hi :=
      integral_inner_gradient_tilted (volume : Measure E) (U := U) (f := a) (g := fun _ : E =>
        (1 : ℝ)) hU ha2 hac (contDiff_const (c := (1 : ℝ)))
    simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one, integral_neg] at hi
    exact neg_eq_zero.mp hi.symm
  have hlimit :
    Tendsto
      (fun k =>
        ∫ x,
          hessianSqStdBasis f x + ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫ ∂μ)
      atTop (𝓝 (∫ x, weightedLaplacian U f x ^ 2 ∂μ)) := by
    have ht := (hQ.div_const 2).add hP
    rw [hzero, zero_div, zero_add] at ht
    apply ht.congr
    intro k
    exact (mixed_integral_identity hU ((hV k).of_le (by decide)) hf hfc).symm
  exact tendsto_nhds_unique hlimit hH

/--
Ordinary diffusion coercivity at `C^{1,1}`: for a C1 globally Lipschitz potential `U` with Lipschitz
gradient and
integrable `e^{-U}`, and `f ∈ C_c^∞`, the Hessian pairing `⟪D(∇U) ∇f, ∇f⟫` and `(ℒf)²` are
integrable for the tilted
measure and `∫ ⟪D(∇U) ∇f, ∇f⟫ ≤ ∫ (ℒf)²`. Lipschitz-gradient sibling of
`compact_ordinary_diffusion_coercivity`. -/
theorem compact_ordinary_diffusion_coercivity_of_lipschitz_gradient {U : E → ℝ}
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal}
    (hL : LipschitzWith L U) (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
        ((volume : Measure E).tilted (-U)) ∧
      Integrable (fun x => weightedLaplacian U f x ^ 2) ((volume : Measure E).tilted (-U)) ∧
        (∫ x,
            ⟪fderiv ℝ (gradient U) x (gradient f x),
              gradient f x⟫ ∂((volume : Measure E).tilted (-U))) ≤
          ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) := by
  classical
  let mu : Measure E := (volume : Measure E).tilted (-U)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hgf : Continuous (gradient f) := continuous_gradient hf1
  obtain ⟨C, hC⟩ :=
    ((hasCompactSupport_gradient hfc).isCompact_range hgf).isBounded.exists_norm_le
  have hb (x : E) : ‖gradient f x‖ ≤ C := hC _ ⟨x, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  have hmD : Measurable (fderiv ℝ (gradient U)) := measurable_fderiv ℝ (gradient U)
  have hev : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hmQ : Measurable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫) :=
    (hev.measurable.comp (hmD.prodMk hgf.measurable)).inner hgf.measurable
  have hQ : Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫) mu := by
    refine (integrable_const ((G : ℝ) * C * C)).mono' hmQ.aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro x
    have hop : ‖fderiv ℝ (gradient U) x‖ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hG
    have happ : ‖fderiv ℝ (gradient U) x (gradient f x)‖ ≤ (G : ℝ) * C :=
      ((fderiv ℝ (gradient U) x).le_opNorm _).trans
        (mul_le_mul hop (hb x) (norm_nonneg _) G.coe_nonneg)
    exact
      (norm_inner_le_norm _ _).trans
        (mul_le_mul happ (hb x) (norm_nonneg _) (mul_nonneg G.coe_nonneg hC0))
  have hScont : Continuous (hessianSqStdBasis f) := continuous_hessian_square hf
  have hSsupp : HasCompactSupport (hessianSqStdBasis f) := compact_hessian_square hfc
  have hS : Integrable (hessianSqStdBasis f) mu := hScont.integrable_of_hasCompactSupport hSsupp
  have hLap : Integrable (fun x => weightedLaplacian U f x ^ 2) mu := by
    have hc2 : HasCompactSupport (fun x => weightedLaplacian U f x ^ 2) :=
      (hasCompactSupport_weightedLaplacian U hfc).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    have hcont2 : Continuous (fun x => weightedLaplacian U f x ^ 2) :=
      (continuous_weightedLaplacian hU hf2).pow 2
    exact hcont2.integrable_of_hasCompactSupport hc2
  have hIdentity := integral_weightedLaplacian_sq_eq_of_lipschitz_gradient hU hG hL hexp hf hfc
  change
    (∫ x, weightedLaplacian U f x ^ 2 ∂mu) =
      ∫ x,
        hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫ ∂mu at hIdentity
  rw [integral_add hS hQ] at hIdentity
  have hnonneg : 0 ≤ ∫ x, hessianSqStdBasis f x ∂mu :=
    integral_nonneg fun x => hessianSqStdBasis_nonneg f x
  exact ⟨hQ, hLap, by linarith⟩

end FiniteDimensional

end FunctionalInequalities.Analysis.BakryEmery
