/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Affine
public import Mathlib.Probability.ConditionalProbability
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.InverseSqrt
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Log-concave laws conditioned on balls

Conditioning a log-concave law on a closed ball and pushing it forward by an affine map stays in the
regular
class used by the approximation step of Letwin's Lemma A.1.

* `exists_regularClass_eq_image_of_cond_closedBall_map` (with `K` the affine image of the ball) and
  `exists_regularClass_of_cond_closedBall_map`.
* `exists_whitening_tendsto_one_tendsto_moments`: whitening maps `x ↦ L k (x − c k)` with `L k → 1`,
  `c k → 0`
  preserving moment convergence; `tendsto_integral_comp_affine_sub` controls such near-identity
  perturbations.
-/

@[expose] public section

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS

private theorem letwin_cond_map_equiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A ≃ᵐ B) (S : Set A) (hS : MeasurableSet S) :
    (ProbabilityTheory.cond μ S).map e =
      ProbabilityTheory.cond (μ.map e) (e '' S) := by
  have hpre : e ⁻¹' (e '' S) = S :=
    Set.preimage_image_eq S e.injective
  have hm : (μ.map e) (e '' S) = μ S := by
    rw [Measure.map_apply e.measurable (e.measurableSet_image.mpr hS), hpre]
  rw [ProbabilityTheory.cond, Measure.map_smul _ e.measurable.aemeasurable,
    ProbabilityTheory.cond, hm, e.measurableEmbedding.restrict_map, hpre]

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem letwin_cond_density
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b)
    (S : Set E) (hS : MeasurableSet S) (h0 : (hV.law : Measure E) S ≠ 0) :
    ProbabilityTheory.cond (hV.law : Measure E) S =
      volume.withDensity
        (S.indicator fun x =>
          ENNReal.ofReal
            (Real.exp
              (-(V x + Real.log
                ((∫ y, Real.exp (-V y) ∂(volume : Measure E)) *
                  ((hV.law : Measure E) S).toReal))))) := by
  let Z : ℝ := ∫ x, Real.exp (-V x) ∂(volume : Measure E)
  let m : ℝ := ((hV.law : Measure E) S).toReal
  have hZ : 0 < Z := hV.integral_exp_neg_pos
  have hm : 0 < m :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have hi : ENNReal.ofReal m⁻¹ = ((hV.law : Measure E) S)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hm,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hd : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x) / Z)) :=
    (hV.temperate.1.continuous.neg.measurable.exp.div_const Z).ennreal_ofReal
  change
    ((hV.law : Measure E) S)⁻¹ •
      ((volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-V x) / Z))).restrict S) = _
  rw [restrict_withDensity hS, ← withDensity_smul _ hd, withDensity_indicator hS]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change
    ((hV.law : Measure E) S)⁻¹ * ENNReal.ofReal (Real.exp (-V x) / Z) =
      ENNReal.ofReal (Real.exp (-(V x + Real.log (Z * m))))
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Z * m)),
    Real.exp_log (mul_pos hZ hm)]
  have he :
      Real.exp (-V x) * (Z * m)⁻¹ =
        m⁻¹ * (Real.exp (-V x) / Z) := by
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), hi]

private theorem letwin_convex_sub_quadratic
    {f : E → ℝ} {a : ℝ} (hf : ContDiff ℝ 2 f)
    (h : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ f x v v) :
    ConvexOn ℝ univ (fun y => f y - (a / 2) * ‖y‖ ^ 2) := by
  have hc : ConvexOn ℝ univ (fun y => f y + (-a) / 2 * ‖y‖ ^ 2) := by
    apply Analysis.BakryEmery.convexOn_of_hessian_ge
      (hf.add (contDiff_const.mul (contDiff_norm_sq ℝ))) (ρ := 0) le_rfl
    intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic hf]
    have hh := h x v
    nlinarith
  simpa only [neg_div, neg_mul, ← sub_eq_add_neg] using hc

/--
**Ball-conditioned, affinely transported regular laws lie in Letwin's class** (Letwin Lemma A.1):
conditioning the law of a regular potential `V` on `closedBall 0 R` (`R > 0`) and pushing forward by
`x ↦ L (x − c)` gives `1_K e^{−W} dx` with `K = L (closedBall 0 R − c)` compact convex with nonempty
interior and `W`
smooth and uniformly convex. -/
theorem exists_regularClass_eq_image_of_cond_closedBall_map [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b)
    {R : ℝ} (hR : 0 < R) (L : E ≃L[ℝ] E) (c : E) :
    ∃ (K : Set E) (W : E → ℝ) (κ : ℝ),
      K = (fun x => L (x - c)) '' closedBall (0 : E) R ∧
        0 < κ ∧
          IsCompact K ∧
            Convex ℝ K ∧
              (interior K).Nonempty ∧
                ContDiff ℝ ∞ W ∧
                  ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
                    (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map
                        (fun x => L (x - c)) =
                      (volume : Measure E).withDensity
                        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
  let H : E ≃ₜ E := (Homeomorph.addRight (-c)).trans L.toHomeomorph
  let e : E ≃ᵐ E := H.toMeasurableEquiv
  let K : Set E := e '' closedBall (0 : E) R
  have he : (e : E → E) = fun x => L (x - c) := by
    funext x
    change L (x + -c) = L (x - c)
    rw [sub_eq_add_neg]
  have hKcompact : IsCompact K := by
    change IsCompact (H '' closedBall (0 : E) R)
    exact (isCompact_closedBall (0 : E) R).image H.continuous
  have hKconvex : Convex ℝ K := by
    have heq : K = L '' ((fun x => -c + x) '' closedBall (0 : E) R) := by
      change e '' closedBall (0 : E) R = L '' ((fun x => -c + x) '' closedBall (0 : E) R)
      rw [Set.image_image]
      congr 1
      funext x
      rw [he]
      change L (x - c) = L (-c + x)
      rw [sub_eq_add_neg, add_comm]
    rw [heq]
    exact ((convex_closedBall (0 : E) R).translate (-c)).linear_image (L : E →ₗ[ℝ] E)
  have hKinterior : (interior K).Nonempty := by
    change (interior (H '' closedBall (0 : E) R)).Nonempty
    rw [← H.image_interior]
    exact
      ⟨H 0,
        Set.mem_image_of_mem H (mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds (0 : E) hR))⟩
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  let U : E → ℝ := fun y => V (L.symm y + c)
  let κ : ℝ := RegularPotential.affineLowerConstant a L.symm
  have hU : RegularPotential U κ (RegularPotential.affineUpperConstant b L.symm) :=
    hV.comp_affine L.symm c
  have hmap : (hV.law : Measure E).map e = (hU.law : Measure E) := by
    rw [he]
    simpa only [ContinuousLinearEquiv.symm_symm] using (hV.law_comp_affine L.symm c).symm
  have hK0 : (hU.law : Measure E) K ≠ 0 := by
    obtain ⟨y, hy⟩ := hKinterior
    have hpos : 0 < (volume : Measure E) K :=
      Measure.measure_pos_of_mem_nhds volume (mem_interior_iff_mem_nhds.mp hy)
    intro hz
    exact (ne_of_gt hpos) (absolutelyContinuous_tilted hU.integrable_exp_neg hz)
  let d : ℝ :=
    Real.log ((∫ y, Real.exp (-U y) ∂(volume : Measure E)) * ((hU.law : Measure E) K).toReal)
  let W : E → ℝ := fun y => U y + d
  have hW : ContDiff ℝ ∞ W := hU.temperate.1.add contDiff_const
  have hconv : ConvexOn ℝ univ (fun y => U y - (κ / 2) * ‖y‖ ^ 2) :=
    letwin_convex_sub_quadratic (hU.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hU.lower
  have hWconv : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) := by
    have hh := hconv.add_const d
    change ConvexOn ℝ univ (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) at hh
    have heq : (fun y => W y - (κ / 2) * ‖y‖ ^ 2) = (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) := by
      funext y
      dsimp only [W]
      ring
    rw [heq]
    exact hh
  refine ⟨K, W, κ, by rw [← he], hU.pos, hKcompact, hKconvex, hKinterior, hW, hWconv, ?_⟩
  calc
    (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map
          (fun x => L (x - c)) =
        (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map e := by
      rw [he]
    _ = ProbabilityTheory.cond ((hV.law : Measure E).map e) K :=
      letwin_cond_map_equiv (hV.law : Measure E) e (closedBall (0 : E) R)
        measurableSet_closedBall
    _ = ProbabilityTheory.cond (hU.law : Measure E) K := by rw [hmap]
    _ =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) :=
      letwin_cond_density hU K hKmeas hK0

/--
**Ball-conditioned, affinely transported regular laws lie in Letwin's class** (Letwin Lemma A.1):
conditioning the law of a regular potential `V` on `closedBall 0 R` (`R > 0`) and pushing forward by
`x ↦ L (x − c)` gives `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth
and uniformly
convex. -/
theorem exists_regularClass_of_cond_closedBall_map [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b) {R : ℝ} (hR : 0 < R)
    (L : E ≃L[ℝ] E) (c : E) :
    ∃ (K : Set E) (W : E → ℝ) (κ : ℝ),
      0 < κ ∧
        IsCompact K ∧
          Convex ℝ K ∧
            (interior K).Nonempty ∧
              ContDiff ℝ ∞ W ∧
                ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
                  (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map
                      (fun x => L (x - c)) =
                    (volume : Measure E).withDensity
                      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
  obtain ⟨K, W, κ, -, h⟩ := exists_regularClass_eq_image_of_cond_closedBall_map hV hR L c
  exact ⟨K, W, κ, h⟩

end InnerProduct

end FunctionalInequalities.KLS

section WhiteningMoments

open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

/-! Whitening maps of laws with converging second moments converge to the identity and preserve
moment convergence (Letwin Lemma A.1 approximation). -/

namespace FunctionalInequalities.KLS

private lemma integrable_of_ball_support
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {f : E → F} (hf : Continuous f) :
    Integrable f (ν : Measure E) := by
  have ha : ∀ᵐ x ∂(ν : Measure E), x ∈ closedBall (0 : E) R :=
    ae_iff.mpr hs
  have hi := hf.continuousOn.integrableOn_compact
    (μ := (ν : Measure E)) (isCompact_closedBall (0 : E) R)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E]

private lemma memLp_two_of_ball_support
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0) :
    MemLp id 2 (ν : Measure E) := by
  apply (memLp_two_iff_integrable_sq_norm
    continuous_id.aestronglyMeasurable).2
  exact integrable_of_ball_support ν hs (by fun_prop)

/--
**Near-identity affine perturbations of laws on a fixed ball.** If the laws `λ k` are all carried by
`closedBall 0 R`, `A k → 1` and `c k → 0`, then for continuous `f` the integrals of `f ∘ (x ↦ A k (x
− c k))` and of `f`
against `λ k` differ by `o(1)`: uniform convergence on the compact ball gives a bound independent of
the law. -/
theorem tendsto_integral_comp_affine_sub {lam : ℕ → ProbabilityMeasure E} {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0) {A : ℕ → E →L[ℝ] E}
    {c : ℕ → E} (hA : Tendsto A atTop (𝓝 1)) (hc : Tendsto c atTop (𝓝 0)) {f : E → ℝ}
    (hf : Continuous f) :
    Tendsto
      (fun k => (∫ x, f (A k (x - c k)) ∂(lam k : Measure E)) - ∫ x, f x ∂(lam k : Measure E))
      atTop (𝓝 0) := by
  let : CompactSpace (closedBall (0 : E) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let F : ((E →L[ℝ] E) × E) → closedBall (0 : E) R → ℝ := fun p x => f (p.1 ((x : E) - p.2))
  have hF : Continuous ↿F := by
    dsimp only [F]
    exact hf.comp (by fun_prop)
  have hu := Continuous.tendstoUniformly F hF (1, 0)
  have hp := hA.prodMk_nhds hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hp.eventually ((Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε))
  filter_upwards [he] with k hk
  have hb : ∀ᵐ x ∂(lam k : Measure E), ‖f (A k (x - c k)) - f x‖ ≤ ε / 2 := by
    filter_upwards [show ∀ᵐ x ∂(lam k : Measure E), x ∈ closedBall (0 : E) R from
        ae_iff.mpr (hsupp k)] with
      x hx
    have hh := hk ⟨x, hx⟩
    have hh' : dist (f x) (f (A k (x - c k))) < ε / 2 := by
      simpa only [F, sub_zero, one_apply_eq_self] using hh
    rw [dist_comm, dist_eq_norm] at hh'
    exact hh'.le
  have hi : Integrable (fun x => f (A k (x - c k))) (lam k : Measure E) :=
    integrable_of_ball_support (lam k) (hsupp k) (hf.comp (by fun_prop))
  have hj : Integrable f (lam k : Measure E) := integrable_of_ball_support (lam k) (hsupp k) hf
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hi hj, probReal_univ, mul_one] at hb'
  rw [dist_zero_right]
  exact hb'.trans_lt (half_lt_self hε)

private lemma mean_tendsto_zero
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => ∫ x, x ∂(lam k : Measure E)) atTop (𝓝 0) := by
  have hv (v : E) :
      Tendsto (fun k => ⟪v, ∫ x, x ∂(lam k : Measure E)⟫)
        atTop (𝓝 (0 : ℝ)) := by
    have h_lam (k : ℕ) :
        (∫ x, ⟪v, x⟫ ∂(lam k : Measure E)) =
          ⟪v, ∫ x, x ∂(lam k : Measure E)⟫ := by
      exact (innerSL ℝ v).integral_comp_comm
        (integrable_of_ball_support (lam k) (hsupp k) continuous_id)
    have h_mu : (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) = 0 := by
      have hi : Integrable (fun x : E => x) (μ : Measure E) :=
        hiso.memLp_two.integrable (by norm_num)
      have hh := (innerSL ℝ v).integral_comp_comm hi
      change (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) =
        ⟪v, ∫ x, x ∂(μ : Measure E)⟫ at hh
      rw [hh, hiso.mean_zero, inner_zero_right]
    simpa only [Fin.prod_univ_one, h_lam, h_mu] using
      hmom 1 (by norm_num) (fun _ => v)
  let b := stdOrthonormalBasis ℝ E
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => (hv (b i)).smul_const (b i))
  simpa only [b.sum_repr', zero_smul, Finset.sum_const_zero] using h

private lemma covariance_positive
    (ν : ProbabilityMeasure E) :
    (Covariance.operator (ν : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).2
  constructor
  · intro x y
    change ⟪Covariance.operator (ν : Measure E) x, y⟫ =
      ⟪x, Covariance.operator (ν : Measure E) y⟫
    calc
      _ = ProbabilityTheory.covarianceBilin (ν : Measure E) x y :=
        Covariance.operator_inner _ _ _
      _ = ProbabilityTheory.covarianceBilin (ν : Measure E) y x :=
        ProbabilityTheory.covarianceBilin_comm x y
      _ = ⟪Covariance.operator (ν : Measure E) y, x⟫ :=
        (Covariance.operator_inner _ _ _).symm
      _ = _ := real_inner_comm _ _
  · intro x
    rw [Covariance.operator_inner]
    exact ProbabilityTheory.covarianceBilin_self_nonneg x

private lemma covariance_tendsto_one
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => Covariance.operator (lam k : Measure E)) atTop (𝓝 1) := by
  let m : ℕ → E := fun k => ∫ x, x ∂(lam k : Measure E)
  have hm : Tendsto m atTop (𝓝 0) :=
    mean_tendsto_zero hiso hsupp hmom
  have hcenter (u v : E) :
      Tendsto
        (fun k => ∫ x, ⟪u, x - m k⟫ * ⟪v, x - m k⟫
          ∂(lam k : Measure E)) atTop (𝓝 ⟪u, v⟫) := by
    have hr :
        Tendsto (fun k => ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(lam k : Measure E))
          atTop (𝓝 ⟪u, v⟫) := by
      simpa [Fin.prod_univ_two, hiso.integral_inner_mul_inner] using
        hmom 2 (by norm_num) ![u, v]
    have hp := tendsto_integral_comp_affine_sub hsupp
      (A := fun _ => (1 : E →L[ℝ] E)) tendsto_const_nhds hm
      (f := fun x => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)
    simpa only [one_apply_eq_self, sub_add_cancel, zero_add] using hp.add hr
  have hcoord (u v : E) :
      Tendsto (fun k => ⟪u, Covariance.operator (lam k : Measure E) v⟫)
        atTop (𝓝 ⟪u, v⟫) := by
    have he (k : ℕ) :
        ⟪u, Covariance.operator (lam k : Measure E) v⟫ =
          ∫ x, ⟪v, x - m k⟫ * ⟪u, x - m k⟫ ∂(lam k : Measure E) := by
      rw [real_inner_comm (Covariance.operator (lam k : Measure E) v) u,
        Covariance.operator_inner,
        ProbabilityTheory.covarianceBilin_apply
          (memLp_two_of_ball_support (lam k) (hsupp k))]
      rfl
    have h := hcenter v u
    rw [real_inner_comm u v] at h
    simpa only [he] using h
  let b := stdOrthonormalBasis ℝ E
  have hM :
      Tendsto (fun k => Analysis.operatorMatrix b (Covariance.operator (lam k : Measure E)))
        atTop (𝓝 (Analysis.operatorMatrix b (1 : E →L[ℝ] E))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => by
      simpa only [Analysis.operatorMatrix_apply_eq_operatorEntry,
        Analysis.operatorEntry, one_apply_eq_self] using hcoord (b i) (b j)
  have hh := ((Analysis.operatorOfMatrixL b).continuous.tendsto _).comp
    ((Analysis.continuous_matrixEntries.tendsto _).comp hM)
  simpa only [Function.comp_def, Analysis.operatorOfMatrixL_matrixEntries,
    Analysis.operatorOfMatrix_operatorMatrix] using hh

end MeasurableSpace

private lemma whitening_sequence (C : ℕ → E →L[ℝ] E)
    (hpos : ∀ k, (C k).IsPositive) (hC : Tendsto C atTop (𝓝 1)) :
    ∃ L : ℕ → E ≃L[ℝ] E,
      Tendsto (fun k => (L k).toContinuousLinearMap) atTop (𝓝 1) ∧
      ∀ᶠ k in atTop,
        IsSelfAdjoint (L k).toContinuousLinearMap ∧
        (L k).toContinuousLinearMap * C k * (L k).toContinuousLinearMap = 1 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hu : ∀ᶠ k in atTop, IsUnit (C k) :=
    hC.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hi0 : ContinuousAt Ring.inverse (1 : E →L[ℝ] E) :=
    NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)
  have hi : Tendsto (fun k => Ring.inverse (C k)) atTop (𝓝 (1 : E →L[ℝ] E)) := by
    simpa only [Function.comp_def, Ring.inverse_one] using hi0.tendsto.comp hC
  have hmatrix : Continuous (Analysis.operatorMatrix b) :=
    ((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
      LinearMap.toContinuousLinearMap.symm.toLinearMap).continuous_of_finiteDimensional
  have hread : Continuous (Analysis.operatorOfMatrix b) := by
    simpa only [Function.comp_def, Analysis.operatorOfMatrixL_matrixEntries] using
      (Analysis.operatorOfMatrixL b).continuous.comp Analysis.continuous_matrixEntries
  have hmi :
      Tendsto (fun k => (Analysis.operatorMatrix b (C k))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)) := by
    have hh := (hmatrix.tendsto (1 : E →L[ℝ] E)).comp hi
    have he :
        (fun k => Analysis.operatorMatrix b (Ring.inverse (C k))) =ᶠ[atTop]
          (fun k => (Analysis.operatorMatrix b (C k))⁻¹) :=
      hu.mono fun k hk => (Analysis.operatorMatrix_ringInverse b (C k) hk).symm
    have hh' : Tendsto (fun k => Analysis.operatorMatrix b (Ring.inverse (C k)))
        atTop (𝓝 (Analysis.operatorMatrix b (1 : E →L[ℝ] E))) := hh
    simpa only [Analysis.operatorMatrix_one] using hh'.congr' he
  have hroot :
      Tendsto (fun k => CFC.sqrt ((Analysis.operatorMatrix b (C k))⁻¹))
        atTop
        (𝓝 (CFC.sqrt
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ))) := by
    have hs :
        ContinuousWithinAt
          (CFC.sqrt :
            Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →
            Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
          {a | 0 ≤ a} 1 :=
      CFC.continuousOn_sqrt
        (A := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
        1
        (show (0 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) ≤ 1 from zero_le_one)
    apply hs.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmi, Eventually.of_forall fun k => ?_⟩
    exact ((Analysis.operatorMatrix_posSemidef_iff b (C k)).2 (hpos k)).inv.nonneg
  have hone : Analysis.operatorOfMatrix b
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) =
      (1 : E →L[ℝ] E) := by
    simpa only [Analysis.operatorMatrix_one] using
      Analysis.operatorOfMatrix_operatorMatrix b (1 : E →L[ℝ] E)
  have hW : Tendsto (fun k => Analysis.inverseSqrt (C k)) atTop (𝓝 1) := by
    have hh := (hread.tendsto _).comp hroot
    change Tendsto
      (fun k => Analysis.operatorOfMatrix b
        (CFC.sqrt ((Analysis.operatorMatrix b (C k))⁻¹))) atTop (𝓝 1)
    simpa only [Function.comp_def, CFC.sqrt_one, hone] using hh
  let L : ℕ → E ≃L[ℝ] E := fun k =>
    if hk : IsUnit (C k) then
      ContinuousLinearEquiv.ofUnit
        (Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit
    else ContinuousLinearEquiv.refl ℝ E
  have he :
      (fun k => (L k).toContinuousLinearMap) =ᶠ[atTop]
        (fun k => Analysis.inverseSqrt (C k)) := by
    filter_upwards [hu] with k hk
    dsimp only [L]
    rw [dite_eq_left hk]
    change
      (↑(Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit :
        E →L[ℝ] E) = Analysis.inverseSqrt (C k)
    exact (Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit_spec
  refine ⟨L, hW.congr' he.symm, ?_⟩
  filter_upwards [hu, he] with k hk heq
  rw [heq]
  exact ⟨Analysis.inverseSqrtIn_isSelfAdjoint b (C k),
    Analysis.inverseSqrt_mul_mul_inverseSqrt (C k) (hpos k) hk⟩

/--
**Whitening preserves convergence of low moments** (Letwin Lemma A.1 approximation): if the laws
`λ k`, all carried by a fixed ball, have mixed moments of degree `≤ 4` converging to those of an
isotropic `μ`, then
there are affine maps `x ↦ L k (x − c k)` with `L k → 1` and `c k → 0` that make `λ k` isotropic for
large `k` (mean
zero, identity second moments) and keep the convergence of the moments of degree `≤ 4`. -/
theorem exists_whitening_tendsto_one_tendsto_moments [MeasurableSpace E] [BorelSpace E]
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E} (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hμsupp : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom :
      ∀ d : ℕ,
        d ≤ 4 →
          ∀ v : Fin d → E,
            Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
              (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    ∃ (L : ℕ → E ≃L[ℝ] E) (c : ℕ → E),
      Tendsto (fun k => (L k : E →L[ℝ] E)) atTop (𝓝 1) ∧
        Tendsto c atTop (𝓝 0) ∧
          (∀ᶠ k in atTop,
              ∫ x, L k (x - c k) ∂(lam k : Measure E) = 0 ∧
                ∀ u v : E,
                  ∫ x, ⟪u, L k (x - c k)⟫ * ⟪v, L k (x - c k)⟫ ∂(lam k : Measure E) = ⟪u, v⟫) ∧
            ∀ d : ℕ,
              d ≤ 4 →
                ∀ v : Fin d → E,
                  Tendsto (fun k => ∫ x, ∏ i, ⟪v i, L k (x - c k)⟫ ∂(lam k : Measure E)) atTop
                    (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
  classical
  have hiso : Isotropic μ :=
    ⟨memLp_two_of_ball_support μ hμsupp, hiso.mean_zero, hiso.covariance_identity⟩
  let m : ℕ → E := fun k => ∫ x, x ∂(lam k : Measure E)
  let C : ℕ → E →L[ℝ] E := fun k => Covariance.operator (lam k : Measure E)
  have hm : Tendsto m atTop (𝓝 0) := mean_tendsto_zero hiso hsupp hmom
  have hC : Tendsto C atTop (𝓝 1) := covariance_tendsto_one hiso hsupp hmom
  obtain ⟨L, hL, hwhite⟩ := whitening_sequence C (fun k => covariance_positive (lam k)) hC
  refine ⟨L, m, hL, hm, ?_, ?_⟩
  · filter_upwards [hwhite] with k hk
    let W := (L k).toContinuousLinearMap
    have hsa : IsSelfAdjoint W := hk.1
    have hsand : W * C k * W = 1 := hk.2
    have hi : Integrable (fun x : E => x) (lam k : Measure E) :=
      integrable_of_ball_support (lam k) (hsupp k) continuous_id
    have htwo := memLp_two_of_ball_support (lam k) (hsupp k)
    constructor
    · change (∫ x, W (x - m k) ∂(lam k : Measure E)) = 0
      have hsub : Integrable (fun x : E => x - m k) (lam k : Measure E) :=
        integrable_of_ball_support (lam k) (hsupp k) (by fun_prop)
      have hcomm :
        (∫ x, W (x - m k) ∂(lam k : Measure E)) = W (∫ x, x - m k ∂(lam k : Measure E)) :=
        W.integral_comp_comm hsub
      rw [hcomm, integral_sub hi (integrable_const (m k))]
      simp only [integral_const, probReal_univ, one_smul]
      change W (m k - m k) = 0
      rw [sub_self, map_zero]
    · intro u v
      change (∫ x, ⟪u, W (x - m k)⟫ * ⟪v, W (x - m k)⟫ ∂(lam k : Measure E)) = ⟪u, v⟫
      calc
        _ = ProbabilityTheory.covarianceBilin (lam k : Measure E) (W u) (W v) := by
          simp_rw [← W.adjoint_inner_left, hsa.adjoint_eq]
          exact (ProbabilityTheory.covarianceBilin_apply htwo (W u) (W v)).symm
        _ = ⟪C k (W u), W v⟫ := (Covariance.operator_inner (lam k : Measure E) (W u) (W v)).symm
        _ = ⟪W (C k (W u)), v⟫ := by rw [← W.adjoint_inner_right, hsa.adjoint_eq]
        _ = ⟪u, v⟫ := by
          have hh := congrArg (fun T : E →L[ℝ] E => T u) hsand
          change W (C k (W u)) = u at hh
          rw [hh]
  · intro d hd v
    have hp :=
      tendsto_integral_comp_affine_sub hsupp hL hm (f := fun x => ∏ i, ⟪v i, x⟫) (by fun_prop)
    have hr := hmom d hd v
    simpa only [sub_add_cancel, zero_add, ContinuousLinearEquiv.coe_coe] using hp.add hr

/--
**Whitening preserves convergence of low moments** (Letwin Lemma A.1 approximation): if the laws
`λ k`, all carried by a fixed ball, have mixed moments of degree `≤ 4` converging to those of an
isotropic `μ`, then
there are affine maps `x ↦ L k (x − c k)` that make `λ k` isotropic for large `k` (mean zero,
identity second
moments) and keep the convergence of the moments of degree `≤ 4`. -/
theorem exists_whitening_tendsto_moments [MeasurableSpace E] [BorelSpace E]
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E} (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hμsupp : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom :
      ∀ d : ℕ,
        d ≤ 4 →
          ∀ v : Fin d → E,
            Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
              (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    ∃ (L : ℕ → E ≃L[ℝ] E) (c : ℕ → E),
      (∀ᶠ k in atTop,
          ∫ x, L k (x - c k) ∂(lam k : Measure E) = 0 ∧
            ∀ u v : E,
              ∫ x, ⟪u, L k (x - c k)⟫ * ⟪v, L k (x - c k)⟫ ∂(lam k : Measure E) = ⟪u, v⟫) ∧
        ∀ d : ℕ,
          d ≤ 4 →
            ∀ v : Fin d → E,
              Tendsto (fun k => ∫ x, ∏ i, ⟪v i, L k (x - c k)⟫ ∂(lam k : Measure E)) atTop
                (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
  obtain ⟨L, c, -, -, h⟩ := exists_whitening_tendsto_one_tendsto_moments hiso hsupp hμsupp hmom
  exact ⟨L, c, h⟩

end FiniteDimensional

end FunctionalInequalities.KLS

end WhiteningMoments
