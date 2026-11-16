/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.JointRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic

/-!
# The log-partition function of the BKL posterior

`ψ(c, Q) = log ∫ e^{⟪c,x⟫ − ½⟪Qx,x⟫} dμ` for a compactly supported prior (Bizeul–Klartag–Lehec
arXiv:2610.05474v1, Section 4): `ψ` is jointly `C^∞`, the log-Laplace transform of the posterior is
`Λ_{μ_{c,Q}}(z) = ψ(c + z, Q) − ψ(c, Q)`, posterior cumulants are `c`-derivatives `κ_m = D_c^m ψ`
(`m ≥ 1`),
and `D_c ψ[h] = ⟪h, a(c, Q)⟫`. This is the deterministic bridge that turns the Itô computations (71)
and
(73) into generator identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Posterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private abbrev partitionParameterSpace :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))

private def partitionParameterChart : (E × (E →L[ℝ] E)) ≃L[ℝ]
    partitionParameterSpace (E := E) :=
  (Module.finBasis ℝ (E × (E →L[ℝ] E))).equivFunL.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ (E × (E →L[ℝ] E))) => ℝ)).symm

private def partitionParameterScore (x : E) :
    (E × (E →L[ℝ] E)) →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)) -
    (1 / 2 : ℝ) • ((innerSL ℝ x).comp
      ((ContinuousLinearMap.apply ℝ E x).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem partitionParameterScore_apply (x : E)
    (p : E × (E →L[ℝ] E)) :
    partitionParameterScore x p = quadraticExponent p.1 p.2 x := by
  change ⟪x, p.1⟫ - (1 / 2 : ℝ) * ⟪x, p.2 x⟫ =
    quadraticExponent p.1 p.2 x
  simp only [quadraticExponent]
  rw [real_inner_comm x p.1, real_inner_comm x (p.2 x)]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem partitionParameterScore_continuous :
    Continuous (partitionParameterScore (E := E)) := by
  have hi : Continuous (fun x : E => innerSL ℝ x) :=
    (InnerProductSpace.toDualMap ℝ E).continuous
  have he : Continuous (fun x : E =>
      (ContinuousLinearMap.apply ℝ E x).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) :=
    (ContinuousLinearMap.apply ℝ E).continuous.clm_comp_const _
  exact (hi.clm_comp_const _).sub
    ((hi.clm_comp he).const_smul (1 / 2 : ℝ))

private def partitionParameterFeature (x : E) :
    partitionParameterSpace (E := E) :=
  (InnerProductSpace.toDual ℝ _).symm
    ((partitionParameterScore x).comp
      (partitionParameterChart (E := E)).symm.toContinuousLinearMap)

section ParameterFeatures

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
private theorem partitionParameterFeature_continuous :
    Continuous (partitionParameterFeature (E := E)) :=
  (InnerProductSpace.toDual ℝ _).symm.continuous.comp
    ((partitionParameterScore_continuous (E := E)).clm_comp_const
      (partitionParameterChart (E := E)).symm.toContinuousLinearMap)

private theorem partitionParameterFeature_pairing
    (p : E × (E →L[ℝ] E)) (x : E) :
    ⟪partitionParameterChart p, partitionParameterFeature x⟫ =
      quadraticExponent p.1 p.2 x := by
  rw [real_inner_comm]
  unfold partitionParameterFeature
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    partitionParameterScore_apply]

end ParameterFeatures

private def partitionLaw (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (partitionParameterSpace (E := E)) :=
  -- The measurability witness stays referenced so that the definition keeps the section instances
  -- it used before `ProbabilityMeasure.map` began taking the function itself (Mathlib v4.35).
  have _hmeas := (partitionParameterFeature_continuous (E := E)).measurable
  μ.map (partitionParameterFeature (E := E))

section PosteriorSupport

omit [CompleteSpace E]
private theorem partitionLaw_support_subset (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    (partitionLaw μ : Measure (partitionParameterSpace (E := E))).support ⊆
      partitionParameterFeature (E := E) '' (μ : Measure E).support := by
  have hk : IsCompact
      (partitionParameterFeature (E := E) '' (μ : Measure E).support) :=
    hc.image (partitionParameterFeature_continuous (E := E))
  have ha : partitionParameterFeature (E := E) '' (μ : Measure E).support ∈
      ae (partitionLaw μ : Measure (partitionParameterSpace (E := E))) := by
    rw [mem_ae_iff]
    change ((μ : Measure E).map (partitionParameterFeature (E := E)))
      (partitionParameterFeature (E := E) '' (μ : Measure E).support)ᶜ = 0
    rw [Measure.map_apply (partitionParameterFeature_continuous (E := E)).measurable
      hk.isClosed.measurableSet.compl]
    apply measure_mono_null ?_ (μ : Measure E).measure_compl_support
    intro x hx hxS
    exact hx ⟨x, hxS, rfl⟩
  exact Measure.support_subset_of_isClosed hk.isClosed ha

private theorem partitionLaw_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    IsCompact
      (partitionLaw μ : Measure (partitionParameterSpace (E := E))).support :=
  (hc.image (partitionParameterFeature_continuous (E := E))).of_isClosed_subset
    (partitionLaw μ : Measure (partitionParameterSpace (E := E))).isClosed_support
    (partitionLaw_support_subset μ hc)

end PosteriorSupport

/--
The log-partition function `ψ(c, Q) = log ∫ e^{⟪c,x⟫ − ½⟪Qx,x⟫} dμ(x)` of the BKL posterior (67). -/
def logPartition (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) : ℝ :=
  Real.log (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- `ψ` is jointly `C^∞` in `(c, Q)` for a compactly supported prior. -/
theorem contDiff_logPartition_joint
     [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => logPartition μ p.1 p.2) := by
  have hexp : ∀ r : ℝ,
      Integrable
        (fun y : partitionParameterSpace (E := E) =>
          Real.exp (r * ‖y‖))
        (partitionLaw μ : Measure (partitionParameterSpace (E := E))) := by
    intro r
    exact integrable_exp_of_compact (partitionLaw μ) (partitionLaw_compact μ hc)
      (by fun_prop)
  have hsm :
      ContDiff ℝ ∞
        (fun z : partitionParameterSpace (E := E) =>
          ∫ y, Real.exp ⟪z, y⟫
            ∂(partitionLaw μ : Measure (partitionParameterSpace (E := E)))) := by
    simpa only [smul_eq_mul, mul_one] using
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul
        (partitionLaw μ : Measure (partitionParameterSpace (E := E))) hexp
        (g := fun _ : partitionParameterSpace (E := E) => (1 : ℝ))
        (M := 1) (k := 0)
        (hg := measurable_const.aestronglyMeasurable)
        (hgb := by
          intro y
          simp))
  have heq :
      (fun p : E × (E →L[ℝ] E) =>
        ∫ y, Real.exp ⟪partitionParameterChart p, y⟫
          ∂(partitionLaw μ : Measure (partitionParameterSpace (E := E)))) =
      (fun p : E × (E →L[ℝ] E) =>
        ∫ x, Real.exp (quadraticExponent p.1 p.2 x)
          ∂(μ : Measure E)) := by
    funext p
    have hp : Continuous
        (fun y : partitionParameterSpace (E := E) =>
          Real.exp ⟪partitionParameterChart p, y⟫) := by
      fun_prop
    have h := integral_map (μ := (μ : Measure E))
      (partitionParameterFeature_continuous (E := E)).measurable.aemeasurable
      (hp.measurable.aestronglyMeasurable)
    simpa only [partitionLaw, ProbabilityMeasure.toMeasure_map,
      Function.comp_apply, partitionParameterFeature_pairing] using h
  have hcomp :
      ContDiff ℝ ∞
        (fun p : E × (E →L[ℝ] E) =>
          ∫ y, Real.exp ⟪partitionParameterChart p, y⟫
            ∂(partitionLaw μ : Measure (partitionParameterSpace (E := E)))) := by
    convert hsm.comp (partitionParameterChart (E := E)).contDiff using 1
    rfl
  have hZ :
      ContDiff ℝ ∞
        (fun p : E × (E →L[ℝ] E) =>
          ∫ x, Real.exp (quadraticExponent p.1 p.2 x)
            ∂(μ : Measure E)) := by
    rw [heq] at hcomp
    exact hcomp
  have hpos : ∀ p : E × (E →L[ℝ] E),
      0 < ∫ x, Real.exp (quadraticExponent p.1 p.2 x)
        ∂(μ : Measure E) := by
    intro p
    exact integral_exp_pos
      (integrable_exp_of_compact μ hc (by
        unfold quadraticExponent
        fun_prop))
  have hlog := hZ.log (fun p => (hpos p).ne')
  simpa only [logPartition] using hlog

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem logLaplace_compactPosterior
     [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (z : E) :
    Analysis.BakryEmery.logLaplace (compactPosterior μ hc c Q : Measure E) z =
      logPartition μ (c + z) Q - logPartition μ c Q := by
  unfold Analysis.BakryEmery.logLaplace
  change Real.log
      (∫ x, Real.exp ⟪z, x⟫
        ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
      logPartition μ (c + z) Q - logPartition μ c Q
  rw [integral_tilted_eq_div]
  have heq :
      (fun x : E =>
        Real.exp (quadraticExponent c Q x) * Real.exp ⟪z, x⟫) =
      (fun x : E => Real.exp (quadraticExponent (c + z) Q x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [quadraticExponent, inner_add_left]
    ring
  rw [heq]
  simp only [logPartition]
  rw [Real.log_div
    (integral_exp_pos
      (integrable_exp_of_compact μ hc (by
        unfold quadraticExponent
        fun_prop))).ne'
    (integral_exp_pos
      (integrable_exp_of_compact μ hc (by
        unfold quadraticExponent
        fun_prop))).ne']

omit [CompleteSpace E] in
/--
**Posterior cumulants are `c`-derivatives of `ψ`**: `κ_m(μ_{c,Q}) = D_c^m ψ(c, Q)` for `m ≥ 1`. -/
theorem cumulant_compactPosterior (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) {m : ℕ} (hm : 1 ≤ m) :
    Analysis.BakryEmery.cumulant (compactPosterior μ hc c Q : Measure E) m =
      iteratedFDeriv ℝ m (fun y => logPartition μ y Q) c := by
  have hjoint := contDiff_logPartition_joint μ hc
  have hψ : ContDiff ℝ ∞ (fun y : E => logPartition μ y Q) := by
    have hmap : ContDiff ℝ ∞ (fun y : E => (y, Q)) := contDiff_id.prodMk contDiff_const
    have h := hjoint.comp hmap
    convert h using 1
    rfl
  have htrans : ContDiff ℝ ∞ (fun z : E => logPartition μ (c + z) Q) := by
    have hmap : ContDiff ℝ ∞ (fun z : E => c + z) := contDiff_const.add contDiff_id
    have h := hψ.comp hmap
    convert h using 1
    rfl
  have hsub :
    iteratedFDeriv ℝ m (fun z : E => logPartition μ (c + z) Q - logPartition μ c Q) =
      iteratedFDeriv ℝ m (fun z : E => logPartition μ (c + z) Q) -
        iteratedFDeriv ℝ m (fun _ : E => logPartition μ c Q) := by
    have hfun :
      (fun z : E => logPartition μ (c + z) Q - logPartition μ c Q) =
        (fun z : E => logPartition μ (c + z) Q) - (fun _ : E => logPartition μ c Q) := by
      funext z
      rfl
    rw [hfun]
    exact
      iteratedFDeriv_sub (htrans.of_le (WithTop.coe_le_coe.mpr le_top))
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => logPartition μ c Q)).of_le
          (WithTop.coe_le_coe.mpr le_top))
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hconst : iteratedFDeriv ℝ m (fun _ : E => logPartition μ c Q) = 0 :=
    iteratedFDeriv_const_of_ne hm0 _
  have hLL :
    Analysis.BakryEmery.logLaplace (compactPosterior μ hc c Q : Measure E) =
      (fun z : E => logPartition μ (c + z) Q - logPartition μ c Q) := by
    funext z
    exact logLaplace_compactPosterior μ hc c Q z
  unfold Analysis.BakryEmery.cumulant
  rw [hLL]
  calc
    iteratedFDeriv ℝ m (fun z : E => logPartition μ (c + z) Q - logPartition μ c Q) 0 =
        (iteratedFDeriv ℝ m (fun z : E => logPartition μ (c + z) Q) -
            iteratedFDeriv ℝ m (fun _ : E => logPartition μ c Q))
          0 :=
      congrFun hsub 0
    _ = iteratedFDeriv ℝ m (fun z : E => logPartition μ (c + z) Q) 0 := by
      rw [hconst]
      simp
    _ = iteratedFDeriv ℝ m (fun y : E => logPartition μ y Q) (c + 0) := by
      simpa only using
        (iteratedFDeriv_comp_add_left (𝕜 := ℝ) m c 0 (f := fun y : E => logPartition μ y Q))
    _ = iteratedFDeriv ℝ m (fun y : E => logPartition μ y Q) c := by simp

/-- The `c`-gradient of `ψ` is the posterior mean: `D_c ψ(c, Q)[h] = ⟪h, a(c, Q)⟫`. -/
theorem fderiv_logPartition_c_apply (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => logPartition μ y Q) c h = ⟪h, posteriorMean μ c Q⟫ := by
  have hZ : ContDiff ℝ ∞
      (fun y : E =>
        ∫ x, Real.exp (quadraticExponent y Q x) ∂(μ : Measure E)) := by
    simpa only [mul_one] using
      (contDiff_weighted_integral_quadraticExponent_of_compact μ hc
        (f := fun _ : E => (1 : ℝ)) measurable_const
        (C := 1) (by norm_num) (by intro x hx; simp) Q)
  have hpos (y : E) :
      0 < ∫ x, Real.exp (quadraticExponent y Q x) ∂(μ : Measure E) :=
    integral_exp_pos
      (integrable_exp_of_compact μ hc (by
        unfold quadraticExponent
        fun_prop))
  have hlog : ContDiff ℝ ∞
      (fun y : E =>
        Real.log (∫ x, Real.exp (quadraticExponent y Q x)
          ∂(μ : Measure E))) :=
    hZ.log (fun y => (hpos y).ne')
  have hφ : Continuous (quadraticExponent c Q) := by
    unfold quadraticExponent
    fun_prop
  have hg : Continuous (fun x : E => ⟪h, x⟫) := by
    fun_prop
  have hN := hasDerivAt_weighted_integral_of_compact μ hc
    (φ := quadraticExponent c Q) (g := fun x : E => ⟪h, x⟫)
    (f := fun _ : E => (1 : ℝ)) hφ hg measurable_const
    (C := 1) (by norm_num) (by intro x hx; simp)
  simp only [mul_one] at hN
  have hphase (t : ℝ) :
      quadraticExponent (c + t • h) Q =
        fun x : E => quadraticExponent c Q x + t * ⟪h, x⟫ := by
    funext x
    simp only [quadraticExponent, inner_add_left, real_inner_smul_left]
    ring
  have hN' :
      HasDerivAt
        (fun t : ℝ =>
          ∫ x, Real.exp (quadraticExponent (c + t • h) Q x)
            ∂(μ : Measure E))
        (∫ x, Real.exp (quadraticExponent c Q x) * ⟪h, x⟫
          ∂(μ : Measure E)) 0 := by
    simpa only [hphase] using hN
  have hlogD :=
    ((hlog.differentiable (by norm_num) c).hasFDerivAt).comp_hasDerivAt_of_eq
      (0 : ℝ) (Analysis.BakryEmery.hasDerivAt_line c h 0) (by simp)
  have hlogDfun :
      ((fun y : E =>
          Real.log (∫ x, Real.exp (quadraticExponent y Q x)
            ∂(μ : Measure E))) ∘
        (fun t : ℝ => c + t • h)) =
      (fun t : ℝ =>
        Real.log (∫ x, Real.exp (quadraticExponent (c + t • h) Q x)
          ∂(μ : Measure E))) := by
    funext t
    rfl
  rw [hlogDfun] at hlogD
  have hlogN := hN'.log (by simpa using (hpos c).ne')
  have hlogN' :
      HasDerivAt
        (fun t : ℝ =>
          Real.log (∫ x, Real.exp (quadraticExponent (c + t • h) Q x)
            ∂(μ : Measure E)))
        ((∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E))) 0 := by
    simpa only [zero_smul, add_zero, div_eq_mul_inv, mul_comm] using hlogN
  have hderivLog :
      fderiv ℝ
          (fun y : E =>
            Real.log (∫ x, Real.exp (quadraticExponent y Q x)
              ∂(μ : Measure E))) c h =
        (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E)) :=
    hlogD.unique hlogN'
  change fderiv ℝ
      (fun y : E =>
        Real.log (∫ x, Real.exp (quadraticExponent y Q x)
          ∂(μ : Measure E))) c h = _
  calc
    fderiv ℝ
        (fun y : E =>
          Real.log (∫ x, Real.exp (quadraticExponent y Q x)
            ∂(μ : Measure E))) c h =
        (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E)) := hderivLog
    _ = (∫ x, Real.exp (quadraticExponent c Q x) * ⟪h, x⟫
          ∂(μ : Measure E)) /
          ∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E) := by
      rw [div_eq_mul_inv]
      ring
    _ = ∫ x, ⟪h, x⟫
        ∂((μ : Measure E).tilted (quadraticExponent c Q)) := by
      rw [integral_tilted_eq_div]
    _ = ⟪h, posteriorMean μ c Q⟫ :=
      integral_inner_eq_inner_posteriorMean μ hc c Q h

end FunctionalInequalities.Probability.Posterior
