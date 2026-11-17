/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# A locally integrable function with zero weak gradient is almost everywhere constant

On a finite-dimensional real inner product space with a Haar measure `m`, let `h` be locally
integrable with `∫ h ∂_w φ dm = 0` for every `φ ∈ C_c^∞` and every direction `w`. Then `h` is
`m`-almost everywhere equal to a constant.

The proof avoids mollification. Differentiating `t ↦ ∫ h(x) φ(x - t v) dm` under the integral sign
and using the weak equation shows that `∫ h(x) (φ(x) - φ(x - v)) dm = 0`. With Haar translation
invariance and the fundamental lemma of the calculus of variations this gives `h(· + v) = h`
almost everywhere, for every `v`. A Fubini argument on `V × V` then shows that a function
invariant under every translation up to null sets is almost everywhere constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivative of a smooth function along the translation `r ↦ x - r v`. -/
theorem hasDerivAt_comp_sub_smul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : V) (s : ℝ) :
    HasDerivAt (fun r : ℝ => φ (x - r • v)) (-(fderiv ℝ φ (x - s • v) v)) s := by
  have h1 : HasDerivAt (fun r : ℝ => x - r • v) (-v) s := by
    simpa using ((hasDerivAt_id' s).smul_const v).const_sub x
  have h2 :=
    ((hφ.differentiable (by simp)) (x - s • v)).hasFDerivAt.comp_hasDerivAt s h1
  exact h2.congr_deriv (by simp)

/-- Domination of the translated derivative near `t` by an indicator of a compact thickening of
the support. -/
theorem norm_mul_fderiv_comp_sub_smul_le {φ : V → ℝ} {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ φ y‖ ≤ M) (h : V → ℝ) (v : V) {t s : ℝ} (hs : dist s t < 1) (x : V) :
    ‖h x * fderiv ℝ φ (x - s • v) v‖ ≤
      (Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)).indicator
        (fun y => |h y| * (M * ‖v‖)) x := by
  by_cases hx : x ∈ Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)
  · rw [Set.indicator_of_mem hx]
    calc
      ‖h x * fderiv ℝ φ (x - s • v) v‖ =
          |h x| * ‖fderiv ℝ φ (x - s • v) v‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |h x| * (‖fderiv ℝ φ (x - s • v)‖ * ‖v‖) := by
            gcongr
            exact (fderiv ℝ φ (x - s • v)).le_opNorm v
      _ ≤ |h x| * (M * ‖v‖) := by
            gcongr
            exact hM _
  · rw [Set.indicator_of_notMem hx]
    have hzero : fderiv ℝ φ (x - s • v) = 0 := by
      by_contra hne
      have hy : x - s • v ∈ tsupport φ :=
        (support_fderiv_subset ℝ) (Function.mem_support.mpr hne)
      apply hx
      refine Metric.mem_cthickening_of_dist_le x (x - s • v)
        ((|t| + 1) * ‖v‖) _ hy ?_
      rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
      have hs' : |s - t| < 1 := by
        simpa [Real.dist_eq] using hs
      have htri : |s| ≤ |t| + |s - t| := by
        calc
          |s| = |t + (s - t)| := by
            congr 1
            ring
          _ ≤ |t| + |s - t| := by
            simpa only [Real.norm_eq_abs] using (norm_add_le t (s - t))
      have habs : |s| ≤ |t| + 1 := by
        have hlt : |s| < |t| + 1 := by
          linarith
        exact hlt.le
      exact mul_le_mul_of_nonneg_right habs (norm_nonneg v)
    rw [hzero]
    simp

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]

section ZeroGradientTranslations

omit [m.IsAddHaarMeasure]
/-- Differentiation under the integral sign for a translated test: for locally integrable `h`,
`d/dt ∫ h(x) φ(x - t v) dm = -∫ h(x) Dφ(x - t v) v dm`. -/
theorem hasDerivAt_integral_mul_translate {h : V → ℝ} (hh : LocallyIntegrable h m) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, h x * φ (x - s • v) ∂m)
      (-∫ x, h x * fderiv ℝ φ (x - t • v) v ∂m) t := by
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_fderiv_of_hasCompactSupport (hφ.of_le (by simp)) hφc
  let K : Set V :=
    Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)
  have hK : IsCompact K := by
    dsimp [K]
    exact hφc.isCompact.cthickening
  have hbound :
      Integrable (K.indicator (fun y => |h y| * (M * ‖v‖))) m := by
    have hi : IntegrableOn (fun y => |h y| * (M * ‖v‖)) K m := by
      change Integrable (fun y => |h y| * (M * ‖v‖)) (m.restrict K)
      simpa [Real.norm_eq_abs] using
        ((hh.integrableOn_isCompact hK).norm.mul_const (M * ‖v‖))
    exact hi.integrable_indicator hK.measurableSet
  have hcont : ∀ r : ℝ, Continuous (fun x : V => φ (x - r • v)) := by
    intro r
    exact hφ.continuous.comp (continuous_id.sub continuous_const)
  have hF_meas :
      ∀ᶠ r in 𝓝 t,
        AEStronglyMeasurable (fun x : V => h x * φ (x - r • v)) m := by
    filter_upwards [] with r
    exact hh.aestronglyMeasurable.mul (hcont r).aestronglyMeasurable
  have hF_int : Integrable (fun x : V => h x * φ (x - t • v)) m := by
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := fun x : V => φ (x - t • v))
        (hcont t)
        (hφc.comp_homeomorph (Homeomorph.subRight (t • v)))
    simpa [smul_eq_mul, mul_comm] using hi
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : V => h x * (-(fderiv ℝ φ (x - t • v) v))) m := by
    have hc : Continuous (fun x : V => fderiv ℝ φ (x - t • v) v) :=
      ((hφ.continuous_fderiv (by simp)).comp
        (continuous_id.sub continuous_const)).clm_apply continuous_const
    exact hh.aestronglyMeasurable.mul hc.neg.aestronglyMeasurable
  have h_bound :
      ∀ᵐ a ∂m, ∀ r ∈ Metric.ball t 1,
        ‖h a * (-(fderiv ℝ φ (a - r • v) v))‖ ≤
          K.indicator (fun y => |h y| * (M * ‖v‖)) a := by
    filter_upwards [] with a r hr
    dsimp [K]
    simpa [norm_mul, norm_neg] using
      (norm_mul_fderiv_comp_sub_smul_le hM h v (Metric.mem_ball.mp hr) a)
  have h_diff :
      ∀ᵐ a ∂m, ∀ r ∈ Metric.ball t 1,
        HasDerivAt
          (fun s : ℝ => h a * φ (a - s • v))
          (h a * (-(fderiv ℝ φ (a - r • v) v))) r := by
    filter_upwards [] with a r hr
    exact (hasDerivAt_comp_sub_smul hφ a v r).const_mul (h a)
  have hkey :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := m)
      (F := fun (r : ℝ) (x : V) => h x * φ (x - r • v))
      (F' := fun (r : ℝ) (x : V) => h x * (-(fderiv ℝ φ (x - r • v) v)))
      (x₀ := t)
      (bound := K.indicator (fun y => |h y| * (M * ‖v‖)))
      (s := Metric.ball t 1)
      (Metric.ball_mem_nhds t one_pos)
      hF_meas
      hF_int
      hF'_meas
      h_bound
      hbound
      h_diff
  have h2 := hkey.2
  simp only [mul_neg, integral_neg] at h2
  exact h2

/-- Zero weak gradient makes `∫ h(x) (φ(x) - φ(x - v)) dm` vanish. -/
theorem integral_mul_sub_translate_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) :
    ∫ x, h x * (φ x - φ (x - v)) ∂m = 0 := by
  let F : ℝ → ℝ := fun s => ∫ x, h x * φ (x - s • v) ∂m
  have hderiv_translate :
      ∀ s : ℝ, ∀ x : V,
        fderiv ℝ (fun y : V => φ (y - s • v)) x =
          fderiv ℝ φ (x - s • v) := by
    intro s x
    have h1 :
        HasFDerivAt (fun y : V => y - s • v)
          (ContinuousLinearMap.id ℝ V) x :=
      (hasFDerivAt_id x).sub_const (s • v)
    have h2 :=
      ((hφ.differentiable (by simp)) (x - s • v)).hasFDerivAt.comp x h1
    have h2' := h2.fderiv
    have hcomp :
        fderiv ℝ φ (x - s • v) ∘L (ContinuousLinearMap.id ℝ V) =
          fderiv ℝ φ (x - s • v) :=
      ContinuousLinearMap.comp_id _
    exact h2'.trans hcomp
  have hzero : ∀ s : ℝ,
      ∫ x, h x * fderiv ℝ φ (x - s • v) v ∂m = 0 := by
    intro s
    have hψ : ContDiff ℝ ∞ (fun x : V => φ (x - s • v)) :=
      hφ.comp (contDiff_id.sub contDiff_const)
    have hψc : HasCompactSupport (fun x : V => φ (x - s • v)) :=
      hφc.comp_homeomorph (Homeomorph.subRight (s • v))
    have hz := h0 (fun x : V => φ (x - s • v)) hψ hψc v
    simpa only [hderiv_translate s] using hz
  have hder : ∀ s : ℝ,
      HasDerivAt F
        (-(∫ x, h x * fderiv ℝ φ (x - s • v) v ∂m)) s := by
    intro s
    simpa [F] using
      (hasDerivAt_integral_mul_translate m hh hφ hφc v s)
  have hFdiff : Differentiable ℝ F := by
    intro s
    exact (hder s).differentiableAt
  have hFderiv : ∀ s : ℝ, deriv F s = 0 := by
    intro s
    rw [(hder s).deriv, hzero s]
    simp
  have hconst : F 0 = F 1 :=
    is_const_of_deriv_eq_zero hFdiff hFderiv 0 1
  have hF01 :
      (∫ x, h x * φ x ∂m) =
        ∫ x, h x * φ (x - v) ∂m := by
    simpa [F] using hconst
  have hi0 : Integrable (fun x => h x * φ x) m := by
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := φ) hφ.continuous hφc
    simpa [smul_eq_mul, mul_comm] using hi
  have hi1 : Integrable (fun x => h x * φ (x - v)) m := by
    have hφv : Continuous (fun x : V => φ (x - v)) :=
      hφ.continuous.comp (continuous_id.sub continuous_const)
    have hφvc : HasCompactSupport (fun x : V => φ (x - v)) :=
      hφc.comp_homeomorph (Homeomorph.subRight v)
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := fun x : V => φ (x - v)) hφv hφvc
    simpa [smul_eq_mul, mul_comm] using hi
  calc
    ∫ x, h x * (φ x - φ (x - v)) ∂m =
        ∫ x, (h x * φ x - h x * φ (x - v)) ∂m := by
          congr 1
          funext x
          ring
    _ = (∫ x, h x * φ x ∂m) - ∫ x, h x * φ (x - v) ∂m :=
      integral_sub hi0 hi1
    _ = 0 := sub_eq_zero.mpr hF01

end ZeroGradientTranslations

omit [SecondCountableTopology V] in
/-- Translates of a locally integrable function are locally integrable for Haar measure. -/
theorem locallyIntegrable_comp_add_right {h : V → ℝ} (hh : LocallyIntegrable h m) (v : V) :
    LocallyIntegrable (fun x => h (x + v)) m := by
  refine locallyIntegrable_iff.mpr ?_
  intro K hK
  have hKv : IsCompact ((fun x : V => x + v) '' K) :=
    hK.image (continuous_add_const v)
  have hi : IntegrableOn h ((fun x : V => x + v) '' K) m :=
    hh.integrableOn_isCompact hKv
  have hchange :
      IntegrableOn h ((fun x : V => x + v) '' K) m ↔
        IntegrableOn (h ∘ (fun x : V => x + v)) K m :=
    (measurePreserving_add_right m v).integrableOn_image
      (MeasurableEquiv.addRight v).measurableEmbedding
  have hi' := hchange.mp hi
  simpa [Function.comp_def] using hi'

omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Change of variables `y = x + v` for Haar measure. -/
theorem integral_mul_comp_add_right (h φ : V → ℝ) (v : V) :
    ∫ x, φ x * h (x + v) ∂m = ∫ x, φ (x - v) * h x ∂m := by
  simpa [add_sub_cancel_right] using
    (integral_add_right_eq_self (μ := m)
      (fun y : V => φ (y - v) * h y) v)

/-- Zero weak gradient makes `h` invariant under every translation, up to null sets. -/
theorem ae_add_eq_of_integral_mul_fderiv_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    (v : V) :
    ∀ᵐ x ∂m, h (x + v) = h x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (μ := m) (f := fun x => h (x + v)) (f' := h)
    (locallyIntegrable_comp_add_right m hh v) hh
  intro g hg hgc
  have hi0 : Integrable (fun x => h x * g x) m := by
    have hi :=
      hh.integrable_smul_right_of_hasCompactSupport
        (g := g) hg.continuous hgc
    simpa [smul_eq_mul] using hi
  have hgv : Continuous (fun x : V => g (x - v)) :=
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hgvc : HasCompactSupport (fun x : V => g (x - v)) :=
    hgc.comp_homeomorph (Homeomorph.subRight v)
  have hi1 : Integrable (fun x => h x * g (x - v)) m := by
    have hi :=
      hh.integrable_smul_right_of_hasCompactSupport
        (g := fun x : V => g (x - v)) hgv hgvc
    simpa [smul_eq_mul] using hi
  have hsub :
      ∫ x, h x * (g x - g (x - v)) ∂m = 0 :=
    integral_mul_sub_translate_eq_zero m hh h0 hg hgc v
  have hsub' :
      ∫ x, (h x * g x - h x * g (x - v)) ∂m = 0 := by
    calc
      ∫ x, (h x * g x - h x * g (x - v)) ∂m =
          ∫ x, h x * (g x - g (x - v)) ∂m := by
            exact integral_congr_ae
              (Eventually.of_forall fun x => by ring)
      _ = 0 := hsub
  have heq :
      (∫ x, h x * g x ∂m) = ∫ x, h x * g (x - v) ∂m := by
    rw [integral_sub hi0 hi1] at hsub'
    exact sub_eq_zero.mp hsub'
  calc
    ∫ x, g x • h (x + v) ∂m =
        ∫ x, g x * h (x + v) ∂m := by
          exact integral_congr_ae
            (Eventually.of_forall fun x => by simp only [smul_eq_mul])
    _ = ∫ x, g (x - v) * h x ∂m :=
      integral_mul_comp_add_right m h g v
    _ = ∫ x, h x * g (x - v) ∂m := by
      exact integral_congr_ae
        (Eventually.of_forall fun x => by ring)
    _ = ∫ x, h x * g x ∂m := heq.symm
    _ = ∫ x, g x • h x ∂m := by
      exact integral_congr_ae
        (Eventually.of_forall fun x => by simp [smul_eq_mul, mul_comm])

omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Translation invariance up to null sets passes to the measurable representative. -/
theorem forall_ae_add_eq_mk {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) (v : V) :
    ∀ᵐ x ∂m, hh.mk h (x + v) = hh.mk h x := by
  have hmk : ∀ᵐ x ∂m, h (x + v) = hh.mk h (x + v) :=
    (measurePreserving_add_right m v).quasiMeasurePreserving.ae hh.ae_eq_mk
  filter_upwards [hmk, htr v, hh.ae_eq_mk] with x hx₁ hx₂ hx₃
  exact hx₁.symm.trans (hx₂.trans hx₃)

/-- A measurable function invariant under every translation up to null sets is almost everywhere
constant. -/
theorem exists_ae_eq_const_of_measurable_of_forall_ae_add_eq {g : V → ℝ} (hg : Measurable g)
    (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, g x = c := by
  have hmeas :
      MeasurableSet {q : V × V | g (q.2 + q.1) = g q.2} := by
    exact measurableSet_eq_fun
      (hg.comp (measurable_snd.add measurable_fst))
      (hg.comp measurable_snd)
  have hprod : ∀ᵐ v ∂m, ∀ᵐ y ∂m, g (y + v) = g y := by
    filter_upwards [] with v
    exact htr v
  have hcomm : ∀ᵐ y ∂m, ∀ᵐ v ∂m, g (y + v) = g y :=
    (Measure.ae_ae_comm (μ := m) (ν := m) hmeas).mp hprod
  have hm0 : m ≠ 0 := NeZero.ne m
  have hne : (ae m).NeBot := ae_neBot.2 hm0
  obtain ⟨y₀, hy₀⟩ := Filter.Eventually.exists hcomm
  have hpull : ∀ᵐ z ∂m, g (y₀ + (z - y₀)) = g y₀ :=
    (measurePreserving_sub_right m y₀).quasiMeasurePreserving.ae hy₀
  refine ⟨g y₀, ?_⟩
  filter_upwards [hpull] with z hz
  have hEq : y₀ + (z - y₀) = z := by
    abel
  rw [hEq] at hz
  exact hz

/-- A function invariant under every translation up to null sets is almost everywhere constant. -/
theorem exists_ae_eq_const_of_forall_ae_add_eq {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  obtain ⟨c, hc⟩ :=
    exists_ae_eq_const_of_measurable_of_forall_ae_add_eq m
      hh.measurable_mk (forall_ae_add_eq_mk m hh htr)
  refine ⟨c, ?_⟩
  filter_upwards [hh.ae_eq_mk, hc] with x hx₁ hx₂
  exact hx₁.trans hx₂

/-- **Zero weak gradient implies constancy**: a locally integrable `h` with
`∫ h ∂_w φ dm = 0` for all `φ ∈ C_c^∞` and all `w` is `m`-almost everywhere constant. -/
theorem exists_ae_eq_const_of_integral_mul_fderiv_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  exact exists_ae_eq_const_of_forall_ae_add_eq m hh.aestronglyMeasurable
    (fun v => ae_add_eq_of_integral_mul_fderiv_eq_zero m hh h0 v)

end FunctionalInequalities.Energy.Euclidean
