/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg
public import LeanPool.EllipticPDE.Embedding.WeakGradUnique


/-!
# Chain rule for weak gradients

A `C¹` function of a class with a weak gradient has a weak gradient, the derivative of the
function at the class times the gradient, once the derivative is bounded. The proof mollifies
the class inside the domain: on the support of a test function, the partials of the
mollifications are the mollified gradient, the classical chain rule and integration by parts
apply to each mollification, and both sides pass to the limit. The function side uses the
Lipschitz bound on `f`; the gradient side uses a subsequence converging almost everywhere and
dominated convergence for the continuous, bounded derivative.

The positive part follows from the chain rule applied to the `C¹` functions
`t ↦ √((t⁺)² + ε²) - ε`, which increase to `t⁺` as `ε` decreases to `0` with derivatives
bounded by one, and from dominated convergence once more. The weak gradient of `u⁺` is the
gradient of `u` where `u > 0` and zero elsewhere. Splitting `u - c` into positive and negative
parts and using uniqueness of the weak gradient, the gradient vanishes almost everywhere on
every level set.

Integrability is asked for locally on the domain throughout, which is the class the sources
state the results for, and the domain is open.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_comp`: the chain rule for a `C¹` function with bounded
  derivative.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart`: the weak gradient of the positive part.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart_sub_const`: the weak gradient of `(u - c)⁺`.
* `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn`: the weak gradient vanishes
  almost everywhere on a level set.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§7.4 Lemma 7.5 (p. 151), Lemma 7.6 and Lemma 7.7 (p. 152);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.10 Problems 17 and 18 (p. 308).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Integrability against a test factor -/

/-- **Integrability against a test factor.** A locally integrable class on a set, times a
continuous function with compact support inside the set, is integrable on the whole space. -/
theorem integrable_mul_of_locallyIntegrableOn {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hs : tsupport h ⊆ Ω) :
    Integrable (fun x => u x * h x) volume := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hK : IntegrableOn u (tsupport h) volume := hu.integrableOn_compact_subset hs hcs
  have hprod : IntegrableOn (fun x => u x * h x) (tsupport h) volume :=
    integrableOn_mul_bounded hK hc hC
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right u h).trans (subset_tsupport h))).mp hprod

/-- **Product of two bounded factors and an integrable one.** -/
theorem integrable_bdd_mul_mul_bdd {a b c : EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : AEStronglyMeasurable a volume) {A : ℝ} (hA : ∀ x, ‖a x‖ ≤ A)
    (hb : Integrable b volume) (hc : AEStronglyMeasurable c volume) {C : ℝ}
    (hC : ∀ x, ‖c x‖ ≤ C) : Integrable (fun x => a x * b x * c x) volume := by
  refine Integrable.mono' (hb.norm.const_mul (A * C)) ((ha.mul hb.1).mul hc) ?_
  filter_upwards with x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  rw [norm_mul, norm_mul]
  calc ‖a x‖ * ‖b x‖ * ‖c x‖ ≤ A * ‖b x‖ * C := by
        gcongr
        · exact hA x
        · exact hC x
    _ = A * C * ‖b x‖ := by ring

/-- **Lipschitz function of an integrable class against a test factor.** The product with a
continuous compactly supported factor is integrable. -/
theorem integrable_comp_mul_of_lipschitz {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : Integrable w volume) {f : ℝ → ℝ} {M : ℝ≥0} (hf : LipschitzWith M f)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    Integrable (fun x => f (w x) * h x) volume := by
  have hm : AEStronglyMeasurable (fun x => f (w x) * h x) volume :=
    (hf.continuous.comp_aestronglyMeasurable hw.1).mul hc.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hint1 : Integrable (fun x => ‖h x‖ * ‖w x‖) volume :=
    hw.norm.bdd_mul hc.norm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [norm_norm]; exact hC x)
  have hint2 : Integrable (fun x => ‖h x‖) volume :=
    hc.norm.integrable_of_hasCompactSupport hcs.norm
  refine Integrable.mono' ((hint1.const_mul (M : ℝ)).add (hint2.const_mul |f 0|)) hm ?_
  filter_upwards with x
  have h1 : |f (w x) - f 0| ≤ (M : ℝ) * |w x| := by
    have := hf.dist_le_mul (w x) 0
    simpa [Real.dist_eq] using this
  have h2 : |f (w x)| ≤ (M : ℝ) * |w x| + |f 0| := by
    have : |f (w x)| ≤ |f (w x) - f 0| + |f 0| := by
      have := abs_sub_abs_le_abs_sub (f (w x)) (f 0)
      linarith [abs_nonneg (f 0)]
    linarith
  simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs]
  calc |f (w x)| * |h x| ≤ ((M : ℝ) * |w x| + |f 0|) * |h x| := by gcongr
    _ = (M : ℝ) * (|h x| * |w x|) + |f 0| * |h x| := by ring

/-! ### Elementary closure properties with local integrability -/

/-- **Negation of a weak gradient.** -/
theorem HasWeakGradOn.neg {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B (fun x => -u x) (fun k x => -g k x) := by
  intro φ hφc hφcs hφB k
  have key := h φ hφc hφcs hφB k
  simp only [neg_mul, integral_neg, key, neg_neg]

/-- **Additivity of a weak gradient**, with local integrability on an open set. -/
theorem HasWeakGradOn.add_of_locallyIntegrableOn
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hh : ∀ k, LocallyIntegrableOn (h k) Ω volume)
    (hU : HasWeakGradOn Ω u g) (hV : HasWeakGradOn Ω v h) :
    HasWeakGradOn Ω (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  have hL : ∫ x in Ω, (u x + v x) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) + ∫ x in Ω, v x * partialD k φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      (integrable_mul_of_locallyIntegrableOn hv hφpc hφpcs hps).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hR : ∫ x in Ω, (g k x + h k x) * φ x
      = (∫ x in Ω, g k x * φ x) + ∫ x in Ω, h k x * φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφs).integrableOn
      (integrable_mul_of_locallyIntegrableOn (hh k) hφcont hφcs hφs).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- **Subtracting a constant** leaves the weak gradient unchanged. -/
theorem hasWeakGradOn_sub_const {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) : HasWeakGradOn Ω (fun x => u x - c) g := by
  intro φ hφc hφcs hφs k
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  -- the integral of a partial of a test function vanishes
  have hzero : ∫ x, partialD k φ x = 0 := by
    have h0 : ∀ x : EuclideanSpace ℝ (Fin d), fderiv ℝ (fun _ => (1 : ℝ)) x = 0 := fun x =>
      by simp
    have hI1 : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))) volume :=
      hφpc.integrable_of_hasCompactSupport hφpcs
    have hI2 : Integrable φ volume := hφc.continuous.integrable_of_hasCompactSupport hφcs
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ => (1 : ℝ)) (g := φ) (v := EuclideanSpace.single k (1 : ℝ))
      (by simp only [h0, _root_.zero_apply, zero_mul]; exact integrable_zero _ _ _)
      (by simpa using hI1) (by simpa using hI2)
      (fun x _ => differentiableAt_const _) (fun x _ => (hφc.differentiable (by simp)) x)
    simp only [one_mul, h0, _root_.zero_apply, zero_mul, integral_zero,
      neg_zero] at key
    simpa [partialD] using key
  have hzeroΩ : ∫ x in Ω, partialD k φ x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hc => hx (hps hc)]
    exact hzero
  have hsplit : ∫ x in Ω, (u x - c) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) - c * ∫ x in Ω, partialD k φ x := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      ((hφpc.integrable_of_hasCompactSupport hφpcs).integrableOn.const_mul c)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hsplit, hzeroΩ, mul_zero, sub_zero, hwg φ hφc hφcs hφs k]

/-- **Uniqueness of the weak gradient on an open set**, with local integrability. -/
theorem hasWeakGradOn_unique_ae_of_locallyIntegrableOn (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hg' : ∀ k, LocallyIntegrableOn (g' k) Ω volume)
    (h : HasWeakGradOn Ω u g) (h' : HasWeakGradOn Ω u g') (k : Fin d) :
    g k =ᵐ[volume.restrict Ω] g' k := by
  have hloc : LocallyIntegrableOn (fun x => g k x - g' k x) Ω volume := (hg k).sub (hg' k)
  have key : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → ∫ x, φ x • (g k x - g' k x) ∂volume = 0 := by
    intro φ hφc hφcs hφB
    have hcompl : ∀ x ∉ Ω, φ x • (g k x - g' k x) = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hφB hc), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    have hgg' : ∫ x in Ω, g k x * φ x = ∫ x in Ω, g' k x * φ x := by
      have h1 := h φ hφc hφcs hφB k
      have h2 := h' φ hφc hφcs hφB k
      linarith [h1, h2]
    have hsplit : ∫ x in Ω, φ x • (g k x - g' k x)
        = (∫ x in Ω, g k x * φ x) - ∫ x in Ω, g' k x * φ x := by
      rw [← integral_sub
        (integrable_mul_of_locallyIntegrableOn (hg k) hφc.continuous hφcs hφB).integrableOn
        (integrable_mul_of_locallyIntegrableOn (hg' k) hφc.continuous hφcs hφB).integrableOn]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        simp only [smul_eq_mul]; ring)
    rw [hsplit, hgg', sub_self]
  have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    fun φ hφc hφcs hφB => key φ (by exact_mod_cast hφc) hφcs hφB
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hΩ.measurableSet] with x hx hxB
  have := hx hxB
  linarith

/-! ### The chain rule -/

private lemma smooth_chain_integral : ∀ {d : ℕ} {f : ℝ → ℝ} (_ : ContDiff ℝ 1 f) (φ :
  EuclideanSpace ℝ (Fin d) → ℝ)
  (_ : ContDiff ℝ (⊤ : ℕ∞) φ) (_ : HasCompactSupport φ) (k : Fin d) (_ : Differentiable ℝ f)
    (_ : Continuous φ)
  (_ : Continuous (partialD k φ)) (_ : HasCompactSupport (partialD k φ)) (v w : ℕ →
    EuclideanSpace ℝ (Fin d) → ℝ)
  (_ : ∀ (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (v n)) (_ : ∀ (n : ℕ), ∀ x ∈ tsupport φ, partialD
    k (v n) x = w n x)
  (n : ℕ),
  ∫ (x : EuclideanSpace ℝ (Fin d)), f (v n x) * partialD k φ x =
    -∫ (x : EuclideanSpace ℝ (Fin d)), deriv f (v n x) * w n x * φ x := by
  classical
  intro d f hf φ hφc hφcs k hfd hφcont hpc hpcs v w hvsmooth hpartial n
  have hv1 : ContDiff ℝ 1 (v n) := (hvsmooth n).of_le (WithTop.coe_le_coe.mpr le_top)
  have hfv : ContDiff ℝ 1 (f ∘ v n) := hf.comp hv1
  have hfvd : Differentiable ℝ (f ∘ v n) := hfv.differentiable one_ne_zero
  have hfderiv : ∀ x, fderiv ℝ (f ∘ v n) x (EuclideanSpace.single k (1 : ℝ))
      = deriv f (v n x) * partialD k (v n) x := by
    intro x
    have h := (hfd (v n x)).hasDerivAt.comp_hasFDerivAt x
      (hv1.differentiable one_ne_zero x).hasFDerivAt
    rw [h.fderiv, _root_.smul_apply, smul_eq_mul]
    rfl
  have hcont1 : Continuous fun x =>
      fderiv ℝ (f ∘ v n) x (EuclideanSpace.single k (1 : ℝ)) :=
    (hfv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := f ∘ v n) (g := φ) (v := EuclideanSpace.single k (1 : ℝ))
    ((hcont1.mul hφcont).integrable_of_hasCompactSupport hφcs.mul_left)
    ((hfv.continuous.mul hpc).integrable_of_hasCompactSupport hpcs.mul_left)
    ((hfv.continuous.mul hφcont).integrable_of_hasCompactSupport hφcs.mul_left)
    (fun x _ => hfvd x) (fun x _ => (hφc.differentiable (by simp)) x)
  have hL' : (fun x => (f ∘ v n) x * fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ)))
      = fun x => f (v n x) * partialD k φ x := rfl
  rw [hL'] at key
  rw [key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hfderiv x]
  by_cases hx : x ∈ tsupport φ
  · rw [hpartial n x hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]


private lemma tendsto_chain_gradient_integral {d : ℕ} {f : ℝ → ℝ} {M : ℝ≥0} (φ : EuclideanSpace ℝ
  (Fin d) → ℝ) (hf'c : Continuous (deriv f))
  (hMr : ∀ (t : ℝ), ‖deriv f t‖ ≤ ↑M) (hφcont : Continuous φ) (Cφ : ℝ)
  (hCφ : ∀ (x : EuclideanSpace ℝ (Fin d)), ‖φ x‖ ≤ Cφ) (U G : EuclideanSpace ℝ (Fin d) → ℝ)
  (hGint : Integrable G volume) (v w : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hvc : ∀ (n : ℕ),
    Continuous (v n))
  (hwc : ∀ (n : ℕ), Continuous (w n)) (hwint : ∀ (n : ℕ), Integrable (w n) volume)
  (htoRealG : Tendsto (fun n => ↑M * Cφ * (eLpNorm (w n - G) 1 volume).toReal) atTop (𝓝 0)) (ns :
    ℕ → ℕ)
  (hns : StrictMono ns) (hae : ∀ᵐ (x : EuclideanSpace ℝ (Fin d)), Tendsto (fun i => v (ns i) x)
    atTop (𝓝 (U x))) :
  Tendsto (fun i => ∫ (x : EuclideanSpace ℝ (Fin d)), deriv f (v (ns i) x) * w (ns i) x * φ x) atTop
    (𝓝 (∫ (x : EuclideanSpace ℝ (Fin d)), deriv f (U x) * G x * φ x)) := by
  classical
  have hA : ∀ n, Integrable (fun x => deriv f (v n x) * (w n x - G x) * φ x) volume :=
    fun n => integrable_bdd_mul_mul_bdd (hf'c.comp (hvc n)).aestronglyMeasurable
      (fun x => hMr _) ((hwint n).sub hGint) hφcont.aestronglyMeasurable hCφ
  have hB : ∀ n, Integrable (fun x => deriv f (v n x) * G x * φ x) volume :=
    fun n => integrable_bdd_mul_mul_bdd (hf'c.comp (hvc n)).aestronglyMeasurable
      (fun x => hMr _) hGint hφcont.aestronglyMeasurable hCφ
  have hsplit : ∀ i, ∫ x, deriv f (v (ns i) x) * w (ns i) x * φ x
      = (∫ x, deriv f (v (ns i) x) * (w (ns i) x - G x) * φ x)
        + ∫ x, deriv f (v (ns i) x) * G x * φ x := by
    intro i
    rw [← integral_add (hA _) (hB _)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hpiece1 : Tendsto (fun i => ∫ x, deriv f (v (ns i) x) * (w (ns i) x - G x) * φ x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (a := fun i => (M : ℝ) * Cφ * (eLpNorm (w (ns i) - G) 1 volume).toReal)
      (fun i => ?_) (htoRealG.comp hns.tendsto_atTop)
    have hbd : Integrable (fun x => (M : ℝ) * Cφ * ‖(w (ns i) - G) x‖) volume :=
      ((hwint _).sub hGint).norm.const_mul _
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Pi.sub_apply, norm_mul, norm_mul]
      calc ‖deriv f (v (ns i) x)‖ * ‖w (ns i) x - G x‖ * ‖φ x‖
          ≤ (M : ℝ) * ‖w (ns i) x - G x‖ * Cφ := by
            gcongr
            · exact hMr _
            · exact hCφ x
        _ = (M : ℝ) * Cφ * ‖w (ns i) x - G x‖ := by ring
    · rw [integral_const_mul, integral_norm_eq_lintegral_enorm
        ((hwc _).aestronglyMeasurable.sub hGint.1), eLpNorm_one_eq_lintegral_enorm
          ((hwc _).aestronglyMeasurable.sub hGint.1)]
  have hpiece2 : Tendsto (fun i => ∫ x, deriv f (v (ns i) x) * G x * φ x) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (M : ℝ) * Cφ * ‖G x‖)
      (fun i => (hB (ns i)).1) (hGint.norm.const_mul _)
      (fun i => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul, norm_mul]
      calc ‖deriv f (v (ns i) x)‖ * ‖G x‖ * ‖φ x‖ ≤ (M : ℝ) * ‖G x‖ * Cφ := by
            gcongr
            · exact hMr _
            · exact hCφ x
        _ = (M : ℝ) * Cφ * ‖G x‖ := by ring
    · filter_upwards [hae] with x hx
      exact (((hf'c.tendsto (U x)).comp hx).mul_const (G x)).mul_const (φ x)
  have := hpiece1.add hpiece2
  rw [zero_add] at this
  exact this.congr fun i => (hsplit i).symm

/-- **Chain rule for weak gradients** (Gilbarg and Trudinger Lemma 7.5, Evans §5.10 Problem
17). A `C¹` function with bounded derivative, composed with a class with a locally integrable
weak gradient on an open set, has the weak gradient `f'(u) ∇u` there. -/
theorem hasWeakGradOn_comp (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0} (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakGradOn Ω (fun x => f (u x)) (fun k x => deriv f (u x) * g k x) := by
  classical
  intro φ hφc hφcs hφΩ k
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfl : LipschitzWith M f := lipschitzWith_of_nnnorm_deriv_le hfd hM
  have hf'c : Continuous (deriv f) := hf.continuous_deriv_one
  have hMr : ∀ t, ‖deriv f t‖ ≤ (M : ℝ) := fun t => by
    have := hM t
    rwa [← NNReal.coe_le_coe, coe_nnnorm] at this
  -- the test function and its partial
  have hφcont : Continuous φ := hφc.continuous
  have hpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφcont
  obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  have hCp0 : 0 ≤ Cp := (norm_nonneg _).trans (hCp 0)
  -- a compact neighbourhood of the support inside the domain
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hφcs hΩ hφΩ
  set K' := cthickening δ (tsupport φ) with hK'def
  have hK'c : IsCompact K' := IsCompact.cthickening hφcs
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  have hKK' : tsupport φ ⊆ K' := self_subset_cthickening _
  have huK : IntegrableOn u K' volume := hu.integrableOn_compact_subset hK' hK'c
  have hgK : ∀ j, IntegrableOn (g j) K' volume := fun j =>
    (hg j).integrableOn_compact_subset hK' hK'c
  have hwgK : HasWeakGradOn K' u g := hwg.mono hK'
  -- extensions by zero off `K'`, integrable on the whole space
  set U : EuclideanSpace ℝ (Fin d) → ℝ := K'.indicator u with hUdef
  set G : EuclideanSpace ℝ (Fin d) → ℝ := K'.indicator (g k) with hGdef
  have hUint : Integrable U volume := (integrable_indicator_iff hK'm).mpr huK
  have hGint : Integrable G volume := (integrable_indicator_iff hK'm).mpr (hgK k)
  have hUK : ∀ x ∈ K', U x = u x := fun x hx => indicator_of_mem hx u
  have hGK : ∀ x ∈ K', G x = g k x := fun x hx => indicator_of_mem hx (g k)
  have hUcs : HasCompactSupport U :=
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hK'c.isClosed)
  have hGcs : HasCompactSupport G :=
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hK'c.isClosed)
  -- the mollifiers
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := δ / (n + 1 : ℝ) / 2
      rOut := δ / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = δ / (n + 1 : ℝ) := fun _ => rfl
  have hrIn : ∀ n : ℕ, (φb n).rIn = δ / (n + 1 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  have hφratio : ∀ᶠ n in atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  have hrOut_le : ∀ n : ℕ, (φb n).rOut ≤ δ := fun n => by
    rw [hrOut]
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => U ⋆[L, volume] (φb n).normed volume with hvdef
  set w : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => G ⋆[L, volume] (φb n).normed volume with hwdef
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L)
      hUint.locallyIntegrable (φb n).contDiff_normed
  have hwsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L)
      hGint.locallyIntegrable (φb n).contDiff_normed
  have hvc : ∀ n, Continuous (v n) := fun n => (hvsmooth n).continuous
  have hwc : ∀ n, Continuous (w n) := fun n => (hwsmooth n).continuous
  have hvcs : ∀ n, HasCompactSupport (v n) := fun n =>
    HasCompactSupport.convolution (L := L) hUcs (φb n).hasCompactSupport_normed
  have hwcs : ∀ n, HasCompactSupport (w n) := fun n =>
    HasCompactSupport.convolution (L := L) hGcs (φb n).hasCompactSupport_normed
  have hvint : ∀ n, Integrable (v n) volume := fun n =>
    (hvc n).integrable_of_hasCompactSupport (hvcs n)
  have hwint : ∀ n, Integrable (w n) volume := fun n =>
    (hwc n).integrable_of_hasCompactSupport (hwcs n)
  -- on the support of `φ` the partial of the mollification is the mollified gradient
  have hpartial : ∀ n, ∀ x ∈ tsupport φ, partialD k (v n) x = w n x := by
    intro n x hx
    exact partialD_convolution_eq_of_hasWeakGradOn hK'm huK hwgK (φb n) k
      ((closedBall_subset_closedBall (hrOut_le n)).trans (closedBall_subset_cthickening hx δ))
  -- `L¹` convergence of the mollifications
  have h1 : ENNReal.ofReal (1 : ℝ) = 1 := ENNReal.ofReal_one
  have hMU : MemLp U (ENNReal.ofReal 1) volume := by
    rw [h1]; exact memLp_one_iff_integrable.mpr hUint
  have hMG : MemLp G (ENNReal.ofReal 1) volume := by
    rw [h1]; exact memLp_one_iff_integrable.mpr hGint
  have hconvU : Tendsto (fun n => eLpNorm (v n - U) 1 volume) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_convolution_sub le_rfl hMU hφrOut hφratio
    rwa [h1] at this
  have hconvG : Tendsto (fun n => eLpNorm (w n - G) 1 volume) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_convolution_sub le_rfl hMG hφrOut hφratio
    rwa [h1] at this
  have htoRealU : Tendsto (fun n => (M : ℝ) * Cp * (eLpNorm (v n - U) 1 volume).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvU).const_mul
      ((M : ℝ) * Cp)
    simpa using this
  have htoRealG : Tendsto (fun n => (M : ℝ) * Cφ * (eLpNorm (w n - G) 1 volume).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvG).const_mul
      ((M : ℝ) * Cφ)
    simpa using this
  -- a subsequence converging almost everywhere
  have hmeas : TendstoInMeasure volume v atTop U :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hconvU
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- the classical identity for every mollification
  have hclassical : ∀ n, ∫ x, f (v n x) * partialD k φ x
      = -∫ x, deriv f (v n x) * w n x * φ x := by
    exact smooth_chain_integral hf φ hφc hφcs k hfd hφcont hpc hpcs v w hvsmooth hpartial
  -- limit of the function side
  have hintU : Integrable (fun x => f (U x) * partialD k φ x) volume :=
    integrable_comp_mul_of_lipschitz hUint hfl hpc hpcs
  have hlimL : Tendsto (fun n => ∫ x, f (v n x) * partialD k φ x) atTop
      (𝓝 (∫ x, f (U x) * partialD k φ x)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun n => ?_) htoRealU
    have hint : Integrable (fun x => f (v n x) * partialD k φ x) volume :=
      ((hfl.continuous.comp (hvc n)).mul hpc).integrable_of_hasCompactSupport hpcs.mul_left
    rw [← integral_sub hint hintU]
    have hbd : Integrable (fun x => (M : ℝ) * Cp * ‖(v n - U) x‖) volume :=
      ((hvint n).sub hUint).norm.const_mul _
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Pi.sub_apply, ← sub_mul, norm_mul]
      have h1 : ‖f (v n x) - f (U x)‖ ≤ (M : ℝ) * ‖v n x - U x‖ := by
        have := hfl.dist_le_mul (v n x) (U x)
        rwa [dist_eq_norm, dist_eq_norm] at this
      calc ‖f (v n x) - f (U x)‖ * ‖partialD k φ x‖
          ≤ ((M : ℝ) * ‖v n x - U x‖) * Cp := by gcongr; exact hCp x
        _ = (M : ℝ) * Cp * ‖v n x - U x‖ := by ring
    · rw [integral_const_mul, integral_norm_eq_lintegral_enorm ((hvc n).aestronglyMeasurable.sub
        hUint.1), eLpNorm_one_eq_lintegral_enorm
          ((hvc n).aestronglyMeasurable.sub hUint.1)]
  -- limit of the gradient side along the subsequence
  have hintG : Integrable (fun x => deriv f (U x) * G x * φ x) volume :=
    integrable_bdd_mul_mul_bdd (hf'c.comp_aestronglyMeasurable hUint.1) (fun x => hMr _)
      hGint hφcont.aestronglyMeasurable hCφ
  have hlimR : Tendsto (fun i => ∫ x, deriv f (v (ns i) x) * w (ns i) x * φ x) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * φ x)) := by
    exact tendsto_chain_gradient_integral φ hf'c hMr hφcont Cφ hCφ U G hGint v w hvc hwc hwint
      htoRealG ns hns hae
  -- the two limits agree
  have hlimL' : Tendsto (fun i => ∫ x, f (v (ns i) x) * partialD k φ x) atTop
      (𝓝 (∫ x, f (U x) * partialD k φ x)) := hlimL.comp hns.tendsto_atTop
  have hlimR' : Tendsto (fun i => ∫ x, f (v (ns i) x) * partialD k φ x) atTop
      (𝓝 (-∫ x, deriv f (U x) * G x * φ x)) := by
    simp only [hclassical]
    exact hlimR.neg
  have hwhole : ∫ x, f (U x) * partialD k φ x = -∫ x, deriv f (U x) * G x * φ x :=
    tendsto_nhds_unique hlimL' hlimR'
  -- back to the domain
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφΩ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hps hc), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hφΩ hc), mul_zero]]
  have e1 : (fun x => f (u x) * partialD k φ x) = fun x => f (U x) * partialD k φ x := by
    funext x
    by_cases hx : x ∈ K'
    · rw [hUK x hx]
    · rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hKK' (tsupport_partialD_subset k φ hc)),
        mul_zero, mul_zero]
  have e2 : (fun x => deriv f (u x) * g k x * φ x) = fun x => deriv f (U x) * G x * φ x := by
    funext x
    by_cases hx : x ∈ K'
    · rw [hUK x hx, hGK x hx]
    · rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hKK' hc), mul_zero, mul_zero]
  rw [e1, e2]
  exact hwhole

/-! ### The positive part -/

/-- The `C¹` approximation of the positive part, `√((t⁺)² + ε²) - ε`. -/
def posPartApprox (ε t : ℝ) : ℝ := Real.sqrt ((max t 0) ^ 2 + ε ^ 2) - ε

/-- The square of the positive part is differentiable, with derivative `2 t⁺`. -/
theorem hasDerivAt_max_sq (t : ℝ) : HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      (gt_mem_nhds ht).mono fun s hs => by simp [max_eq_right hs.le]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h0
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    simp only [zero_add, max_self, zero_pow two_ne_zero, sub_zero, mul_zero, smul_eq_mul]
    have hcont : Tendsto (fun s : ℝ => max s 0) (𝓝[≠] 0) (𝓝 0) := by
      have hc0 : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
      have := hc0.tendsto (0 : ℝ)
      simp only [max_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hcont.congr' (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun s hs => ?_))
    rcases lt_or_gt_of_ne hs with hs' | hs'
    · simp [max_eq_right hs'.le]
    · simp only [max_eq_left hs'.le]
      field_simp
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 :=
      (lt_mem_nhds ht).mono fun s hs => by simp [max_eq_left hs.le]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq h0

/-- The square of the positive part is `C¹`. -/
theorem contDiff_max_sq : ContDiff ℝ 1 fun s : ℝ => (max s 0) ^ 2 := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_max_sq t).differentiableAt, ?_⟩
  rw [funext fun t => (hasDerivAt_max_sq t).deriv]
  exact continuous_const.mul (continuous_id.max continuous_const)

/-- The argument of the square root in `posPartApprox` is positive. -/
theorem posPartApprox_arg_pos {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) : 0 < (max t 0) ^ 2 + ε ^ 2 := by
  have := pow_pos (abs_pos.mpr hε) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (max t 0)]

/-- The derivative of the approximation. -/
theorem hasDerivAt_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (posPartApprox ε)
      (2 * max t 0 / (2 * Real.sqrt ((max t 0) ^ 2 + ε ^ 2))) t :=
  (((hasDerivAt_max_sq t).add_const (ε ^ 2)).sqrt (posPartApprox_arg_pos hε t).ne').sub_const ε

/-- The approximation is `C¹`. -/
theorem contDiff_posPartApprox {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_max_sq.add contDiff_const).sqrt fun t => (posPartApprox_arg_pos hε t).ne').sub
    contDiff_const

/-- The derivative of the approximation, in closed form. -/
theorem deriv_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    deriv (posPartApprox ε) t = max t 0 / Real.sqrt ((max t 0) ^ 2 + ε ^ 2) := by
  rw [(hasDerivAt_posPartApprox hε t).deriv, mul_div_mul_left _ _ two_ne_zero]

/-- The derivative of the approximation lies in `[0, 1]`. -/
theorem deriv_posPartApprox_mem {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    0 ≤ deriv (posPartApprox ε) t ∧ deriv (posPartApprox ε) t ≤ 1 := by
  rw [deriv_posPartApprox hε]
  have hm : 0 ≤ max t 0 := le_max_right _ _
  have hs : 0 < Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (posPartApprox_arg_pos hε t)
  refine ⟨div_nonneg hm hs.le, (div_le_one hs).mpr ?_⟩
  exact (Real.le_sqrt hm (posPartApprox_arg_pos hε t).le).mpr (by nlinarith [sq_nonneg ε])

/-- The derivative of the approximation has nonnegative norm at most one. -/
theorem nnnorm_deriv_posPartApprox_le {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    ‖deriv (posPartApprox ε) t‖₊ ≤ 1 := by
  obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem hε t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h0, NNReal.coe_one]
  exact h1

/-- The approximation lies between `0` and the positive part. -/
theorem posPartApprox_mem {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ posPartApprox ε t ∧ posPartApprox ε t ≤ max t 0 := by
  have hm : 0 ≤ max t 0 := le_max_right _ _
  unfold posPartApprox
  constructor
  · rw [sub_nonneg]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
      _ ≤ Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (max t 0)])
  · rw [sub_le_iff_le_add]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

/-- The approximation tends to the positive part as `ε → 0`. -/
theorem tendsto_posPartApprox (t : ℝ) :
    Tendsto (fun ε => posPartApprox ε t) (𝓝 0) (𝓝 (max t 0)) := by
  have hc : Continuous fun ε : ℝ => posPartApprox ε t := by
    unfold posPartApprox
    fun_prop
  have := hc.tendsto 0
  simp only [posPartApprox, zero_pow two_ne_zero, add_zero, sub_zero,
    Real.sqrt_sq (le_max_right t 0)] at this
  exact this

/-- The derivative of the approximation tends to the indicator of `{t > 0}` as `ε → 0`
along positive values. -/
theorem tendsto_deriv_posPartApprox (t : ℝ) :
    Tendsto (fun n : ℕ => deriv (posPartApprox (1 / (n + 1 : ℝ))) t) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  have hεne : ∀ n : ℕ, (1 / (n + 1 : ℝ)) ≠ 0 := fun n => by positivity
  simp only [fun n => deriv_posPartApprox (hεne n) t]
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hc : Continuous fun ε : ℝ => t / Real.sqrt (t ^ 2 + ε ^ 2) := by
      refine continuous_const.div (continuous_const.add (continuous_id.pow 2)).sqrt fun ε => ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have := (hc.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [Function.comp_def, zero_pow two_ne_zero, add_zero, Real.sqrt_sq ht.le,
      div_self ht.ne'] at this
    exact this
  · rw [max_eq_right (not_lt.mp ht)]
    simp only [zero_div]
    exact tendsto_const_nhds

/-- **Weak gradient of the positive part** (Gilbarg and Trudinger Lemma 7.6, Evans §5.10
Problem 18). On an open set, `u⁺ = max u 0` has the weak gradient `∇u` where `u > 0` and `0`
elsewhere. -/
theorem hasWeakGradOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => max (u x) 0) (fun k x => if 0 < u x then g k x else 0) := by
  intro φ hφc hφcs hφΩ k
  have hφcont : Continuous φ := hφc.continuous
  have hpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφΩ
  set ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the identity for every approximation
  have hn : ∀ n, ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x
      = -∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x := fun n =>
    hasWeakGradOn_comp hΩ hu hg hwg (contDiff_posPartApprox (hεpos n).ne') (M := 1)
      (nnnorm_deriv_posPartApprox_le (hεpos n).ne') φ hφc hφcs hφΩ k
  -- the function side
  have hL : Tendsto (fun n => ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x) atTop
      (𝓝 (∫ x in Ω, max (u x) 0 * partialD k φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x * partialD k φ x‖)
      (fun n => ((contDiff_posPartApprox (hεpos n).ne').continuous.comp_aestronglyMeasurable
        hum).mul hpc.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn hu hpc hpcs hps).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := posPartApprox_mem (hεpos n).le (u x)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      gcongr
      refine h1.trans ?_
      rw [Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · exact ((tendsto_posPartApprox (u x)).comp hε0).mul_const _
  -- the gradient side
  have hR : Tendsto (fun n => ∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x) atTop
      (𝓝 (∫ x in Ω, (if 0 < u x then 1 else 0) * g k x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g k x * φ x‖)
      (fun n => (((contDiff_posPartApprox (hεpos n).ne').continuous_deriv_one
        |>.comp_aestronglyMeasurable hum).mul (hg k).aestronglyMeasurable).mul
        hφcont.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφΩ).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem (hεpos n).ne' (u x)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
      calc deriv (posPartApprox (ε n)) (u x) * ‖g k x‖ * ‖φ x‖
          ≤ 1 * ‖g k x‖ * ‖φ x‖ := by gcongr
        _ = ‖g k x‖ * ‖φ x‖ := by ring
    · exact ((tendsto_deriv_posPartApprox (u x)).mul_const _).mul_const _
  have hlim := tendsto_nhds_unique hL (by simp only [hn]; exact hR.neg)
  rw [hlim]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  split_ifs <;> simp

/-- **Weak gradient of `(u - c)⁺`.** -/
theorem hasWeakGradOn_posPart_sub_const (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) (c : ℝ) :
    HasWeakGradOn Ω (fun x => max (u x - c) 0) (fun k x => if c < u x then g k x else 0) := by
  have huc : LocallyIntegrableOn (fun x => u x - c) Ω volume :=
    hu.sub (locallyIntegrableOn_const c)
  have := hasWeakGradOn_posPart hΩ huc hg (hasWeakGradOn_sub_const hu hwg c)
  simpa only [sub_pos] using this

/-- **Local integrability by domination.** -/
theorem locallyIntegrableOn_of_norm_le (hΩ : IsOpen Ω) {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : LocallyIntegrableOn g Ω volume) (hf : AEStronglyMeasurable f (volume.restrict Ω))
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : LocallyIntegrableOn f Ω volume :=
  (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr fun _ hK hKc =>
    (hg.integrableOn_compact_subset hK hKc).norm.mono'
      (hf.mono_measure (Measure.restrict_mono hK le_rfl)) (Eventually.of_forall h)

/-- **Measurability of a truncation.** -/
theorem aestronglyMeasurable_ite_lt {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {u w : EuclideanSpace ℝ (Fin d) → ℝ} (hu : AEStronglyMeasurable u μ)
    (hw : AEStronglyMeasurable w μ) (c : ℝ) :
    AEStronglyMeasurable (fun x => if c < u x then w x else 0) μ := by
  refine ⟨fun x => if c < hu.mk u x then hw.mk w x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hw.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x h1 h2
    simp only [h1, h2]

/-- **Local integrability of a truncated gradient.** -/
theorem locallyIntegrableOn_ite_lt (hΩ : IsOpen Ω) {u w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) (hw : LocallyIntegrableOn w Ω volume)
    (c : ℝ) : LocallyIntegrableOn (fun x => if c < u x then w x else 0) Ω volume :=
  locallyIntegrableOn_of_norm_le hΩ hw (aestronglyMeasurable_ite_lt hu hw.aestronglyMeasurable c)
    fun x => by split_ifs <;> simp

/-- **Local integrability of the positive part of `u - c`.** -/
theorem locallyIntegrableOn_posPart_sub_const (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume) (c : ℝ) :
    LocallyIntegrableOn (fun x => max (u x - c) 0) Ω volume := by
  refine locallyIntegrableOn_of_norm_le hΩ (hu.sub (locallyIntegrableOn_const c))
    (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hu.aestronglyMeasurable) fun x => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Vanishing of the weak gradient on level sets** (Gilbarg and Trudinger Lemma 7.7). On an
open set, the weak gradient of `u` is zero almost everywhere on `{u = c}`. -/
theorem ae_eq_zero_of_eq_const_of_hasWeakGradOn (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) (k : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), u x = c → g k x = 0 := by
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the positive parts of `u - c` and of `-u - (-c)`
  have hpos := hasWeakGradOn_posPart_sub_const hΩ hu hg hwg c
  have hneg := hasWeakGradOn_posPart_sub_const hΩ hu.neg (fun j => (hg j).neg) hwg.neg (-c)
  have hind : ∀ j, LocallyIntegrableOn (fun x => if c < u x then g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum (hg j) c
  have hind' : ∀ j, LocallyIntegrableOn (fun x => if -c < -u x then -g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum.neg (hg j).neg (-c)
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart_sub_const hΩ hu c)
    (locallyIntegrableOn_posPart_sub_const hΩ hu.neg (-c)).neg hind (fun j => (hind' j).neg)
    hneg.neg
  -- the sum is `u - c`, whose weak gradient is `g`
  have heq : (fun x => max (u x - c) 0 + -max (-u x - -c) 0) = fun x => u x - c := by
    funext x
    rw [neg_sub_neg, ← neg_sub (u x) c, ← sub_eq_add_neg, max_zero_sub_max_neg_zero_eq_self]
  simp only [Pi.neg_apply] at hsum
  rw [heq] at hsum
  have hsumint : ∀ j, LocallyIntegrableOn
      (fun x => (if c < u x then g j x else 0) + -(if -c < -u x then -g j x else 0)) Ω volume :=
    fun j => (hind j).add (hind' j).neg
  have huniq := hasWeakGradOn_unique_ae_of_locallyIntegrableOn hΩ hg hsumint
    (hasWeakGradOn_sub_const hu hwg c) hsum k
  filter_upwards [huniq] with x hx hxc
  rw [hx]
  simp [hxc]

/-- **Weak gradient of the negative part** (Gilbarg and Trudinger Lemma 7.6, second clause).
`u⁻ = min u 0` has the weak gradient `∇u` where `u < 0` and `0` elsewhere. -/
theorem hasWeakGradOn_negPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => min (u x) 0) (fun k x => if u x < 0 then g k x else 0) := by
  have h := (hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg).neg
  refine h.congr_ae (Eventually.of_forall fun x => ?_) fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    by_cases hx : u x ≤ 0
    · rw [min_eq_left hx, max_eq_left (by linarith), neg_neg]
    · have hx' : 0 < u x := not_le.mp hx
      rw [min_eq_right hx'.le, max_eq_right (by linarith), neg_zero]
  · simp only [Pi.neg_apply, neg_pos]
    split_ifs <;> simp

/-- Local integrability of the positive part. -/
theorem locallyIntegrableOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) :
    LocallyIntegrableOn (fun x => max (u x) 0) Ω volume := by
  have := locallyIntegrableOn_posPart_sub_const hΩ hu 0
  simpa only [sub_zero] using this

/-- **Weak gradient of the absolute value** (Gilbarg and Trudinger Lemma 7.6, third clause).
`|u|` has the weak gradient `∇u` where `u > 0`, `-∇u` where `u < 0`, and `0` elsewhere. -/
theorem hasWeakGradOn_abs (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => |u x|)
      fun k x => if 0 < u x then g k x else if u x < 0 then -g k x else 0 := by
  have hpos := hasWeakGradOn_posPart hΩ hu hg hwg
  have hneg := hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart hΩ hu)
    (locallyIntegrableOn_posPart hΩ hu.neg)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.aestronglyMeasurable (hg k) 0)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.neg.aestronglyMeasurable (hg k).neg 0) hneg
  refine hsum.congr_ae (Eventually.of_forall fun x => ?_)
    fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    exact max_zero_add_max_neg_zero_eq_abs_self (u x)
  · simp only [Pi.neg_apply, neg_pos]
    rcases lt_trichotomy (u x) 0 with h | h | h
    · have h' : ¬ 0 < u x := not_lt.mpr h.le
      simp [h, h']
    · simp [h]
    · have h' : ¬ u x < 0 := not_lt.mpr h.le
      simp [h, h']

end EllipticPdes.Embedding
