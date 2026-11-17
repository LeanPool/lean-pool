/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.LogPartition
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
/-!
# BKL Lemma 4.3 in generator form

For `m ≥ 3`, every slot `i₀` and directions `h`, `𝓛_p κ_m(μ_p)(h) = −(m κ_m(h) + L_m(h))` with `L_m`
the middle term (72)
(`generator_cumulant_posterior`): the generator commutes with `D_z^m` (coefficients independent of
`z`), (71) gives
`𝓛Λ_p(z) = −½⟪v, A⁻¹v⟫`, and the grouped Leibniz expansion (74) finishes.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

section Calculus

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem dir_append (a b : List U) (f : U → ℝ) :
    directional (a ++ b) f = directional a (directional b f) := by
  induction a with
  | nil => rfl
  | cons u a ih =>
      simp only [List.cons_append, directional, ih]

private theorem dir_comm {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (a b : List U) :
    directional a (directional b f) = directional b (directional a f) := by
  rw [← dir_append, ← dir_append]
  exact directional_perm hf List.perm_append_comm

private theorem dir_affine {f : U → ℝ} (hf : ContDiff ℝ ∞ f) (L : V →L[ℝ] U) (a : U)
    (l : List V) (x : V) :
    directional l (fun y => f (a + L y)) x = directional (l.map L) f (a + L x) := by
  induction l generalizing x with
  | nil => rfl
  | cons v l ih =>
    simp only [List.map_cons, directional]
    rw [show directional l (fun y => f (a + L y)) = (fun y => directional (l.map L) f (a + L y))
        from funext ih]
    have hd := (directional_contDiff hf (l.map L)).differentiable (by simp) (a + L x)
    have he := (hd.hasFDerivAt.comp x (HasFDerivAt.const_add a L.hasFDerivAt)).fderiv
    convert congrArg (fun T : V →L[ℝ] ℝ => T v) he using 1 <;> rfl

private theorem dir_add {f g : U → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (l : List U) (x : U) :
    directional l (fun y => f y + g y) x =
      directional l f x + directional l g x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => f y + g y)) x u = _
      rw [show directional l (fun y => f y + g y) =
          (fun y => directional l f y + directional l g y) from funext ih]
      rw [fderiv_fun_add
        ((directional_contDiff hf l).differentiable (by simp) x)
        ((directional_contDiff hg l).differentiable (by simp) x)]
      rfl

private theorem dir_mul {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (l : List U) (x : U) :
    directional l (fun y => c * f y) x = c * directional l f x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => c * f y)) x u = _
      rw [show directional l (fun y => c * f y) =
          (fun y => c * directional l f y) from funext ih]
      rw [fderiv_const_mul
        ((directional_contDiff hf l).differentiable (by simp) x)]
      rfl

private theorem dir_sum {d : ℕ} {f : Fin d → U → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (l : List U) (x : U) :
    directional l (fun y => ∑ i, f i y) x =
      ∑ i, directional l (f i) x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => ∑ i, f i y)) x u = _
      rw [show directional l (fun y => ∑ i, f i y) =
          (fun y => ∑ i, directional l (f i) y) from funext ih]
      rw [fderiv_fun_sum (fun i _ =>
        (directional_contDiff (hf i) l).differentiable (by simp) x)]
      simp only [sum_apply, directional]

private theorem dir_two {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (u x : U) :
    directional [u, u] f x = fderiv ℝ (fderiv ℝ f) x u u := by
  change fderiv ℝ (fun y => fderiv ℝ f y u) x u = _
  rw [fderiv_clm_apply
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const u)]
  simp

private theorem smooth_right {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : U) :
    ContDiff ℝ ∞ (fun z => f (p, z)) := by
  have hmap : ContDiff ℝ ∞ (fun z : V => (p, z)) :=
    (contDiff_const (c := p)).prodMk contDiff_id
  convert hf.comp hmap using 1
  rfl

private theorem smooth_left {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : V) :
    ContDiff ℝ ∞ (fun p => f (p, z)) := by
  have hmap : ContDiff ℝ ∞ (fun p : U => (p, z)) :=
    contDiff_id.prodMk (contDiff_const (c := z))
  convert hf.comp hmap using 1
  rfl

private theorem dir_right {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List V) (p : U) (z : V) :
    directional l (fun y => f (p, y)) z =
      directional (l.map (fun v => ((0 : U), v))) f (p, z) := by
  have he := dir_affine hf (ContinuousLinearMap.inr ℝ U V) (p, 0) l z
  have hmap : (⇑(ContinuousLinearMap.inr ℝ U V)) =
      (fun v : V => ((0 : U), v)) := by
    funext v
    rfl
  rw [hmap] at he
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using he

private theorem dir_left {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List U) (p : U) (z : V) :
    directional l (fun q => f (q, z)) p =
      directional (l.map (fun u => (u, (0 : V)))) f (p, z) := by
  have he := dir_affine hf (ContinuousLinearMap.inl ℝ U V) (0, z) l p
  have hmap : (⇑(ContinuousLinearMap.inl ℝ U V)) =
      (fun u : U => (u, (0 : V))) := by
    funext u
    rfl
  rw [hmap] at he
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using he

private def fixedOp {d : ℕ} (b : U) (s : Fin d → U)
    (f : U → ℝ) (p : U) : ℝ :=
  fderiv ℝ f p b + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ f) p (s k) (s k)

private theorem fixedOp_slice {d : ℕ} {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : U) (s : Fin d → U) (p : U) (z : V) :
    fixedOp b s (fun q => f (q, z)) p =
      directional [(b, (0 : V))] f (p, z) +
        (1 / 2 : ℝ) * ∑ k,
          directional [(s k, (0 : V)), (s k, (0 : V))] f (p, z) := by
  unfold fixedOp
  have hfirst :
      fderiv ℝ (fun q => f (q, z)) p b =
        directional [(b, (0 : V))] f (p, z) := by
    simpa only [List.map_cons, List.map_nil, directional] using
      dir_left hf [b] p z
  have hsecond (k : Fin d) :
      fderiv ℝ (fderiv ℝ (fun q => f (q, z))) p (s k) (s k) =
        directional [(s k, (0 : V)), (s k, (0 : V))] f (p, z) := by
    rw [← dir_two (smooth_left hf z)]
    simpa only [List.map_cons, List.map_nil] using dir_left hf [s k, s k] p z
  simp only [hfirst, hsecond]

private theorem fixedOp_iterated {d m : ℕ} {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : U) (s : Fin d → U)
    (p : U) (h : Fin m → V) :
    fixedOp b s (fun q => iteratedFDeriv ℝ m (fun z => f (q, z)) 0 h) p =
      iteratedFDeriv ℝ m (fun z => fixedOp b s (fun q => f (q, z)) p) 0 h := by
  let l : List (U × V) := (List.ofFn h).map (fun v => ((0 : U), v))
  let g : U × V → ℝ := directional l f
  have hg : ContDiff ℝ ∞ g := directional_contDiff hf l
  let a : U × V → ℝ := directional [(b, (0 : V))] f
  let t : Fin d → U × V → ℝ :=
    fun k => directional [(s k, (0 : V)), (s k, (0 : V))] f
  have ha : ContDiff ℝ ∞ a := directional_contDiff hf _
  have ht (k : Fin d) : ContDiff ℝ ∞ (t k) := directional_contDiff hf _
  have hsum : ContDiff ℝ ∞ (fun x => ∑ k, t k x) :=
    ContDiff.sum (fun k _ => ht k)
  let H : U × V → ℝ := fun x => a x + (1 / 2 : ℝ) * ∑ k, t k x
  have hH : ContDiff ℝ ∞ H :=
    ha.add (contDiff_const.mul hsum)
  have hjet :
      (fun q => iteratedFDeriv ℝ m (fun z => f (q, z)) 0 h) =
        (fun q => g (q, 0)) := by
    funext q
    rw [← directional_ofFn (smooth_right hf q), dir_right hf]
  have hop :
      (fun z => fixedOp b s (fun q => f (q, z)) p) =
        (fun z => H (p, z)) := by
    funext z
    exact fixedOp_slice hf b s p z
  rw [hjet, hop, fixedOp_slice hg,
    ← directional_ofFn (smooth_right hH p), dir_right hH]
  change directional [(b, (0 : V))] (directional l f) (p, 0) +
      (1 / 2 : ℝ) * ∑ k,
        directional [(s k, (0 : V)), (s k, (0 : V))]
          (directional l f) (p, 0) =
    directional l (fun x => a x + (1 / 2 : ℝ) * ∑ k, t k x) (p, 0)
  rw [dir_add ha (contDiff_const.mul hsum), dir_mul hsum, dir_sum ht]
  congr 1
  · exact congrFun (dir_comm hf _ l) (p, 0)
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (dir_comm hf _ l) (p, 0)

end Calculus

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/--
**BKL Lemma 4.3, (73), in generator form**: for `m ≥ 3`, every slot `i₀` and directions `h`, the
generator of
(67) applied to the posterior cumulant `p ↦ κ_m(μ_p)(h)` is `−(m κ_m(h) + L_m(h))`, where `L_m` is
the middle term
(72) taken at the slot `i₀`. -/
theorem generator_cumulant_posterior (hiso : KLS.Isotropic μ) {m : ℕ} (hm : 3 ≤ m)
    (h : Fin m → EuclideanSpace ℝ (Fin n)) (i₀ : Fin m) (p : Param n) :
    generator μ hc
        (fun q : Param n =>
          cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h)
        p =
      -((m : ℝ) *
            cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) m h +
          lowerDrift (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) h
            i₀) := by
  classical
  let F : Param n × EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    logLaplace (compactPosterior μ hc r.1.1 r.1.2 : Measure (EuclideanSpace ℝ (Fin n))) r.2
  have hF : ContDiff ℝ ∞ F := by
    have hmap :
      ContDiff ℝ ∞
        (fun r : Param n × EuclideanSpace ℝ (Fin n) => ((r.1.1 + r.2, r.1.2) : Param n)) :=
      ((contDiff_fst.fst).add contDiff_snd).prodMk contDiff_fst.snd
    have h₁ :
      ContDiff ℝ ∞
        (fun r : Param n × EuclideanSpace ℝ (Fin n) => logPartition μ (r.1.1 + r.2) r.1.2) := by
      convert (contDiff_logPartition_joint μ hc).comp hmap using 1
      rfl
    have h₂ :
      ContDiff ℝ ∞ (fun r : Param n × EuclideanSpace ℝ (Fin n) => logPartition μ r.1.1 r.1.2) := by
      convert (contDiff_logPartition_joint μ hc).comp contDiff_fst using 1
      rfl
    have heq : F = fun r => logPartition μ (r.1.1 + r.2) r.1.2 - logPartition μ r.1.1 r.1.2 := by
      funext r
      exact logLaplace_compactPosterior μ hc r.1.1 r.1.2 r.2
    rw [heq]
    exact h₁.sub h₂
  let ν := compactPosterior μ hc p.1 p.2
  have hν : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    dsimp only [ν]
    rw [compactPosterior_support]
    exact hc
  let Λ := logLaplace (ν : Measure (EuclideanSpace ℝ (Fin n)))
  have hΛ : ContDiff ℝ ∞ Λ := contDiff_logLaplace _ (compact_support_integrable_exp _ hν)
  have hlog : Λ = fun z => logPartition μ (p.1 + z) p.2 - logPartition μ p.1 p.2 := by
    funext z
    exact logLaplace_compactPosterior μ hc p.1 p.2 z
  have hgrad (z : EuclideanSpace ℝ (Fin n)) : gradient Λ z = posteriorMean μ (p.1 + z) p.2 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_gradient_left, hlog, fderiv_sub_const]
    rw [fderiv_comp_add_left (f := fun y => logPartition μ y p.2) p.1]
    rw [fderiv_logPartition_c_apply μ hc]
    exact (real_inner_comm w (posteriorMean μ (p.1 + z) p.2)).symm
  have hg : ContDiff ℝ ∞ (gradient Λ) := by
    let T : ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv
    exact T.contDiff.comp (hΛ.fderiv_right (by simp))
  let v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun z =>
    gradient Λ z - gradient Λ 0
  let R : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ⟪v z, Ring.inverse (cov μ hc p) (v z)⟫
  have hv : ContDiff ℝ ∞ v := hg.sub contDiff_const
  have hR : ContDiff ℝ ∞ R := hv.inner ℝ ((Ring.inverse (cov μ hc p)).contDiff.comp hv)
  have h71 : (fun z => generator μ hc (fun q => F (q, z)) p) = (fun z => -(1 / 2 : ℝ) * R z) := by
    funext z
    simpa only [F, logLaplace_compactPosterior, R, v, hgrad, add_zero] using
      generator_logLaplace_posterior μ hc hiso z p
  change
    fixedOp (drift μ hc p) (noise μ hc p) (fun q => iteratedFDeriv ℝ m (fun z => F (q, z)) 0 h)
        p =
      _
  rw [fixedOp_iterated hF]
  change iteratedFDeriv ℝ m (fun z => generator μ hc (fun q => F (q, z)) p) 0 h = _
  rw [h71]
  have hscale :
    iteratedFDeriv ℝ m (fun z => -(1 / 2 : ℝ) * R z) 0 h =
      -(1 / 2 : ℝ) * iteratedFDeriv ℝ m R 0 h := by
    have hRm : ContDiffAt ℝ m R 0 := (hR.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hs :
      iteratedFDeriv ℝ m (fun z => (-(1 / 2 : ℝ)) • R z) 0 =
        (-(1 / 2 : ℝ)) • iteratedFDeriv ℝ m R 0 :=
      iteratedFDeriv_const_smul_apply' hRm
    simpa only [smul_eq_mul, smul_apply] using congrArg (fun T => T h) hs
  rw [hscale]
  have hgroup :
    iteratedFDeriv ℝ m R 0 h =
      (2 * (m : ℝ)) * cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
        2 * lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀ := by
    exact
      iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact ν hν
        (Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2) hm h i₀
  rw [hgroup]
  change
    -(1 / 2 : ℝ) *
        ((2 * (m : ℝ)) * cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
          2 * lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀) =
      -((m : ℝ) * cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
          lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀)
  ring

end FunctionalInequalities.KLS.BKL.Localization
