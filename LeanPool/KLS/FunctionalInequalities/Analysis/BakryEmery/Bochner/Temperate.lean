/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature

/-!
# The integrated Bochner formula on the class `𝒜`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), eq. (16): for `μ = m.tilted (-V)` with `V` of temperate
growth (every derivative of polynomial growth, as for the source's regular measures) and all
exponential moments, every `u` of temperate growth satisfies
`∫ (ℒu)² dμ = ∫ ‖∇²u‖²_HS dμ + ∫ ⟪∇²V ∇u, ∇u⟫ dμ`. Under `∇²V ≥ ρ` this gives
`∫ (ℒu)² dμ ≥ ∫ ‖∇²u‖²_HS dμ + ρ ∫ ‖∇u‖² dμ`, the inequality behind Lemma 3.4. The class `𝒜` is
closed under `∇`, `Δ`, `ℒ` and `Γ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### Closure of the class `𝒜` -/

section TemperateTransport

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem hasTemperateGrowth_iteratedFDeriv {f : E → ℝ} (hf : f.HasTemperateGrowth) (n : ℕ) :
    (iteratedFDeriv ℝ n f).HasTemperateGrowth := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact
      (continuousMultilinearCurryFin0 ℝ E
            ℝ).symm.toContinuousLinearEquiv.hasTemperateGrowth.comp
        hf
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E)
            ℝ).symm.toContinuousLinearEquiv.hasTemperateGrowth.comp
        (hasTemperateGrowth_fderiv ih)

private theorem hasTemperateGrowth_comp_linearIsometryEquiv
    (L : (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E) {g : E → (E →L[ℝ] ℝ)}
    (hg : g.HasTemperateGrowth) : (L ∘ g).HasTemperateGrowth := by
  constructor
  · exact (LinearIsometryEquiv.contDiff L).comp hg.1
  · intro n
    obtain ⟨k, C, hC⟩ := hg.2 n
    refine ⟨k, C, fun x => ?_⟩
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

end TemperateTransport

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasTemperateGrowth_gradient {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    (gradient f).HasTemperateGrowth := by
    change ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f).HasTemperateGrowth
    exact hasTemperateGrowth_comp_linearIsometryEquiv
      (InnerProductSpace.toDual ℝ E).symm (hasTemperateGrowth_fderiv hf)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem hasTemperateGrowth_laplacian {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    (Laplacian.laplacian f).HasTemperateGrowth := by
  let b := stdOrthonormalBasis ℝ E
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hf)
  have ht (i : Fin (Module.finrank ℝ E)) :
      (fun x => fderiv ℝ (fderiv ℝ f) x (b i) (b i)).HasTemperateGrowth := by
    have h1 : (fun x => fderiv ℝ (fderiv ℝ f) x (b i)).HasTemperateGrowth :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth
        (Function.HasTemperateGrowth.const (b i)) hdd
    exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth
      (Function.HasTemperateGrowth.const (b i)) h1
  have hs := Function.HasTemperateGrowth.sum (s := Finset.univ) (fun i _ => ht i)
  convert hs using 1
  ext x
  exact laplacian_eq_sum_fderiv_fderiv f x

omit [MeasurableSpace E] [BorelSpace E] in
theorem hasTemperateGrowth_weightedLaplacian {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hf : f.HasTemperateGrowth) : (weightedLaplacian V f).HasTemperateGrowth := by
    have hgradV : (gradient V).HasTemperateGrowth :=
      hasTemperateGrowth_gradient hV
    have hgradf : (gradient f).HasTemperateGrowth :=
      hasTemperateGrowth_gradient hf
    have hprod :
        (fun x : E => (innerSL ℝ) (gradient V x) (gradient f x)).HasTemperateGrowth :=
      ContinuousLinearMap.bilinear_hasTemperateGrowth
        (innerSL ℝ) hgradV hgradf
    have hsub :
        (fun x : E =>
          Laplacian.laplacian f x -
            (innerSL ℝ) (gradient V x) (gradient f x)).HasTemperateGrowth :=
      (hasTemperateGrowth_laplacian hf).sub hprod
    have hEq :
        weightedLaplacian V f =
          (fun x : E =>
            Laplacian.laplacian f x -
              (innerSL ℝ) (gradient V x) (gradient f x)) := by
      funext x
      rw [weightedLaplacian_apply, innerSL_apply_apply]
    rw [hEq]
    exact hsub

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasTemperateGrowth_gamma {f g : E → ℝ} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (gamma f g).HasTemperateGrowth := by
    have h :
        (fun x => innerSL ℝ (gradient f x) (gradient g x)).HasTemperateGrowth :=
      ContinuousLinearMap.bilinear_hasTemperateGrowth (innerSL ℝ)
        (hasTemperateGrowth_gradient hf) (hasTemperateGrowth_gradient hg)
    have hγ :
        gamma f g = fun x => innerSL ℝ (gradient f x) (gradient g x) := by
      funext x
      exact gamma_apply f g x
    rw [hγ]
    exact h

/-! ### The integrated identities -/

variable (m : Measure E) [m.IsAddHaarMeasure]

private theorem bochner_temperate_generator_zero (m : Measure E) [m.IsAddHaarMeasure]
    {V g : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V g x ∂(m.tilted (-V)) = 0 := by
  obtain ⟨kV, CV, hVb⟩ := hV.2 1
  obtain ⟨k, C, _, hb⟩ := hg.norm_iteratedFDeriv_le_uniform 2
  apply integral_weightedLaplacian_eq_zero_of_growth m
    (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun x => by simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hVb x)
    hexp (hg.1.of_le (WithTop.coe_le_coe.mpr le_top))
  · intro x
    exact ⟨by simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x,
      hb 1 (by omega) x, hb 2 le_rfl x⟩

/-- `∫ Γ₂(u) dμ = ∫ (ℒu)² dμ` for `u` and `V` of temperate growth. -/
theorem integral_gammaTwo_eq_of_hasTemperateGrowth {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, gammaTwo V f x ∂(m.tilted (-V)) = ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by
  have hLf := hasTemperateGrowth_weightedLaplacian hV hf
  have hG := hasTemperateGrowth_gamma hf hf
  have hLGi :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (hasTemperateGrowth_weightedLaplacian hV hG)
  have hGi :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (hasTemperateGrowth_gamma hf hLf)
  have hzero := bochner_temperate_generator_zero m hV hexp hG
  obtain ⟨kV, CV, hVb⟩ := hV.2 1
  have hibp :=
    integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth m
      (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun x => by simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hVb x) hexp hf
      hLf
  have hsq :
    (∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V))) =
      -(∫ x, gamma f (weightedLaplacian V f) x ∂(m.tilted (-V))) := by
    simpa only [pow_two, gamma_apply] using hibp
  simp only [gammaTwo_apply]
  rw [integral_sub (hLGi.div_const 2) hGi, integral_div, hzero]
  simpa using hsq.symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem bochner_sq_temperate_hessian_eval {f : E → ℝ} (hf : f.HasTemperateGrowth)
    {g h : E → E} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    (fun x => bilinearIteratedFDerivTwo ℝ f x (g x) (h x)).HasTemperateGrowth := by
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hf)
  have h1 : (fun x => fderiv ℝ (fderiv ℝ f) x (g x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth hg hdd
  exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hh h1

/-- **BKL (16)**, the integrated Bochner formula on `𝒜`:
`∫ (ℒu)² dμ = ∫ ‖∇²u‖²_HS dμ + ∫ ∇²V(∇u, ∇u) dμ`. -/
theorem integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth {V f : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) =
      ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) ∂(m.tilted (-V)) := by
  have hH : (hessianSqStdBasis f).HasTemperateGrowth := by
    unfold hessianSqStdBasis
    apply Function.HasTemperateGrowth.sum
    intro i _
    apply Function.HasTemperateGrowth.sum
    intro j _
    exact
      (bochner_sq_temperate_hessian_eval hf
            (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E i))
            (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E j))).pow
        2
  have hB :=
    bochner_sq_temperate_hessian_eval hV (hasTemperateGrowth_gradient hf)
      (hasTemperateGrowth_gradient hf)
  rw [← integral_gammaTwo_eq_of_hasTemperateGrowth m hV hexp hf]
  have hpoint :
    gammaTwo V f = fun x =>
      hessianSqStdBasis f x + bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) := by
    funext x
    exact
      gammaTwo_eq_hessianSqStdBasis_add (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
        (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)) x
  rw [hpoint,
    integral_add (FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp hH)
      (FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp hB)]

/-- The curvature form of (16) used in BKL Lemma 3.4: if `∇²V ≥ ρ`, then
`∫ (ℒu)² dμ ≥ ∫ ‖∇²u‖²_HS dμ + ρ ∫ ‖∇u‖² dμ` for `u ∈ 𝒜`. -/
theorem integral_hessianSq_add_le_of_hasTemperateGrowth {V f : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) :
    ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) + ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂(m.tilted (-V)) ≤
      ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by
  have hgrad := hasTemperateGrowth_gradient hf
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hV)
  have h1 : (fun x => fderiv ℝ (fderiv ℝ V) x (gradient f x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth hgrad hdd
  have hB :
    (fun x =>
        bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hgrad h1
  have hBi := FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp hB
  have hGi : Integrable (fun x => ‖gradient f x‖ ^ 2) (m.tilted (-V)) := by
    rw [← gamma_self_fun f]
    exact
      FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
        (hasTemperateGrowth_gamma hf hf)
  rw [integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth m hV hexp hf]
  apply add_le_add le_rfl
  rw [← integral_const_mul]
  exact integral_mono (hGi.const_mul ρ) hBi (fun x => hH x (gradient f x))

end FunctionalInequalities.Analysis.BakryEmery
