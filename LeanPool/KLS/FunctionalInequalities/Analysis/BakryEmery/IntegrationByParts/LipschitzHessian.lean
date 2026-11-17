/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.ChainRule
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Testing

/-!
# Mean of the Hessian at `C^{1,1}`

`∫⟪D(∇φ)u, v⟫ dν = ∫ ∂_uφ ∂_vφ dν` for `ν = e^{−φ}dx` with `φ` convex `C¹` with Lipschitz gradient
(Letwin
arXiv:2607.24164v1, Lemma 2.3, analytic part, weak route).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Mean Hessian identity for a `C¹` potential with Lipschitz gradient** (Letwin
arXiv:2607.24164v1, Lemma 2.3, analytic part, at `C^{1,1}`):
`∫ ⟪D(∇φ)(x) u, v⟫ dν = ∫ ∂_uφ ∂_vφ dν` for convex `φ ∈ C¹` with `G`-Lipschitz gradient,
`e^{-φ}` a probability density and `∇φ ∈ L²(ν)`, where `D(∇φ)` is the a.e. (Rademacher)
derivative of the Lipschitz map `∇φ`. -/
theorem integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) {G : NNReal} (hG : LipschitzWith G (gradient φ))
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂((volume : Measure E).tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by
  have _hconvex := hc
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  let f : E → ℝ := fun x => ⟪gradient φ x, v⟫
  let g : E → ℝ := fun x => fderiv ℝ f x u
  let p : E → ℝ := fun x => fderiv ℝ φ x u * f x
  have hfLip : LipschitzWith ((G : ℝ) * ‖v‖).toNNReal f := by
    dsimp only [f]
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [dist_eq_norm, ← inner_sub_left]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (gradient φ x - gradient φ y) v
    have hg := mul_le_mul_of_nonneg_right (hG.dist_le_mul x y) (norm_nonneg v)
    rw [dist_eq_norm] at hg
    nlinarith
  have hf2 : MemLp f 2 μ := hgrad.inner_const (𝕜 := ℝ) v
  have hf1 : Integrable f μ := hf2.integrable (by norm_num)
  have hu2 : MemLp (fun x => fderiv ℝ φ x u) 2 μ := by
    simpa only [inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) u
  have hp : Integrable p μ := hu2.integrable_mul hf2
  have hgmeas : Measurable g :=
    (show Continuous (fun A : E →L[ℝ] ℝ => A u) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hg : Integrable g μ := by
    apply (integrable_const
      ((((G : ℝ) * ‖v‖).toNNReal : ℝ) * ‖u‖)).mono' hgmeas.aestronglyMeasurable
    exact ae_of_all _ fun x =>
      ((fderiv ℝ f x).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hfLip) (norm_nonneg u))
  have hgeq : g =ᵐ[μ] fun x => ⟪fderiv ℝ (gradient φ) x u, v⟫ := by
    have hdiff : ∀ᵐ x : E ∂(volume : Measure E), DifferentiableAt ℝ (gradient φ) x :=
      hG.ae_differentiableAt
    have hdiffμ : ∀ᵐ x : E ∂μ, DifferentiableAt ℝ (gradient φ) x :=
      (tilted_absolutelyContinuous (volume : Measure E) (-φ)).ae_le hdiff
    filter_upwards [hdiffμ] with x hx
    dsimp only [g, f]
    simpa using fderiv_inner_apply ℝ hx (differentiableAt_const v) u
  have hscaledNorm (R : ℝ) (x : E) : ‖scaled R x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg R x)]
    exact scaled_le_one R x
  have hcut (k : E → ℝ) (hk : Integrable k μ) (R : ℝ) :
      Integrable (fun x => scaled R x * k x) μ := by
    refine hk.norm.mono'
      ((continuous_scaled R).aestronglyMeasurable.mul hk.aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm R x)
  have hevent (x : E) : ∀ᶠ n : ℕ in atTop, ‖x‖ < (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun n hn => ?_⟩
    exact lt_of_le_of_lt (hN.trans (Nat.cast_le.mpr hn)) (lt_add_one _)
  have hcutLim (k : E → ℝ) (hk : Integrable k μ) :
      Tendsto (fun n : ℕ => ∫ x, scaled ((n : ℝ) + 1) x * k x ∂μ)
        atTop (𝓝 (∫ x, k x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖k x‖)
      (fun n => (hcut k hk ((n : ℝ) + 1)).aestronglyMeasurable) hk.norm
    · intro n
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm _ x)
    · filter_upwards [] with x
      have heq : (fun n : ℕ => scaled ((n : ℝ) + 1) x * k x) =ᶠ[atTop]
          fun _ => k x := by
        filter_upwards [hevent x] with n hn
        rw [scaled_eq_one (by positivity) hn.le, one_mul]
      exact tendsto_const_nhds.congr' heq.symm
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  have hcof (n : ℕ) (x : E) :
      ‖fderiv ℝ (scaled ((n : ℝ) + 1)) x u‖ ≤ M * ‖u‖ := by
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    have hd : ‖fderiv ℝ (scaled ((n : ℝ) + 1)) x‖ ≤ M :=
      (norm_fderiv_scaled_le hR hM x).trans
        (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (scaled ((n : ℝ) + 1)) x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg u))
  have herrMeas (n : ℕ) :
      AEStronglyMeasurable
        (fun x => fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x) μ :=
    (((contDiff_scaled ((n : ℝ) + 1)).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.mul hf1.aestronglyMeasurable
  have herrBound (n : ℕ) (x : E) :
      ‖fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x‖ ≤
        (M * ‖u‖) * ‖f x‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcof n x) (norm_nonneg _)
  have herrInt (n : ℕ) :
      Integrable (fun x => fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x) μ :=
    (hf1.norm.const_mul (M * ‖u‖)).mono' (herrMeas n) (ae_of_all _ (herrBound n))
  have herrLim :
      Tendsto (fun n : ℕ =>
        ∫ x, fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x ∂μ) atTop (𝓝 0) := by
    have ht :
        Tendsto (fun n : ℕ =>
          ∫ x, fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x ∂μ)
          atTop (𝓝 (∫ _x : E, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (M * ‖u‖) * ‖f x‖) herrMeas
        (hf1.norm.const_mul (M * ‖u‖))
      · exact fun n => ae_of_all _ (herrBound n)
      · filter_upwards [] with x
        have heq : (fun n : ℕ =>
            fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x) =ᶠ[atTop]
            fun _ => (0 : ℝ) := by
          filter_upwards [hevent x] with n hn
          rw [fderiv_scaled_eq_zero (by positivity) hn]
          simp only [zero_apply, zero_mul]
        exact tendsto_const_nhds.congr' heq.symm
    simpa only [integral_zero] using ht
  have htilt (k : E → ℝ) :
      (∫ x, k x ∂μ) = ∫ x, Real.exp (-φ x) * k x ∂(volume : Measure E) := by
    change (∫ x, k x ∂((volume : Measure E).tilted (-φ))) = _
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
  have hidentity (n : ℕ) :
      (∫ x, scaled ((n : ℝ) + 1) x * g x ∂μ) =
        (∫ x, scaled ((n : ℝ) + 1) x * p x ∂μ) -
          ∫ x, fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x ∂μ := by
    let R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hχ : ContDiff ℝ 1 (scaled (E := E) R) :=
      (contDiff_scaled R).of_le (by simp)
    have hd (x : E) :
        fderiv ℝ (fun y => scaled R y * Real.exp (-φ y)) x u =
          Real.exp (-φ x) * fderiv ℝ (scaled R) x u -
            Real.exp (-φ x) * scaled R x * fderiv ℝ φ x u := by
      have hd' : HasFDerivAt (fun y => scaled R y * Real.exp (-φ y))
          (scaled R x • (Real.exp (-φ x) • -fderiv ℝ φ x) +
            Real.exp (-φ x) • fderiv ℝ (scaled R) x) x :=
        (hχ.differentiable one_ne_zero x).hasFDerivAt.mul
          ((hφ.differentiable one_ne_zero x).hasFDerivAt.neg.exp)
      rw [hd'.fderiv]
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
    have hw := (hasWeakDerivAlong_of_lipschitz hfLip u).2.2
      (fun x => scaled R x * Real.exp (-φ x))
      (hχ.mul hφ.neg.exp) (hasCompactSupport_scaled hR).mul_right
    have he :
        (∫ x, (fderiv ℝ (scaled R) x u * f x - scaled R x * p x) ∂μ) =
          -(∫ x, scaled R x * g x ∂μ) := by
      calc
        _ = ∫ x, Real.exp (-φ x) *
            (fderiv ℝ (scaled R) x u * f x - scaled R x * p x)
              ∂(volume : Measure E) := htilt _
        _ = ∫ x, f x *
            fderiv ℝ (fun y => scaled R y * Real.exp (-φ y)) x u
              ∂(volume : Measure E) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hd x]
          dsimp only [p]
          ring
        _ = -(∫ x, g x * (scaled R x * Real.exp (-φ x))
              ∂(volume : Measure E)) := hw
        _ = -(∫ x, scaled R x * g x ∂μ) := by
          rw [htilt]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    rw [integral_sub (herrInt n) (hcut p hp R)] at he
    change (∫ x, scaled R x * g x ∂μ) =
      (∫ x, scaled R x * p x ∂μ) -
        ∫ x, fderiv ℝ (scaled R) x u * f x ∂μ
    linarith only [he]
  have hlimits := (hcutLim p hp).sub herrLim
  have heq :
      (fun n : ℕ => (∫ x, scaled ((n : ℝ) + 1) x * p x ∂μ) -
        ∫ x, fderiv ℝ (scaled ((n : ℝ) + 1)) x u * f x ∂μ) =
      (fun n : ℕ => ∫ x, scaled ((n : ℝ) + 1) x * g x ∂μ) :=
    funext fun n => (hidentity n).symm
  rw [heq] at hlimits
  have hmean : (∫ x, g x ∂μ) = ∫ x, p x ∂μ := by
    simpa only [sub_zero] using tendsto_nhds_unique (hcutLim g hg) hlimits
  calc
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂μ) =
        ∫ x, g x ∂μ := integral_congr_ae hgeq.symm
    _ = ∫ x, p x ∂μ := hmean
    _ = ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂μ := by
      simp only [p, f, inner_gradient_left]

end FunctionalInequalities.Analysis.BakryEmery

section BoundedLipschitzTiltedIBP

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/--
Weighted integration by parts for a bounded globally Lipschitz test `η` against the normalized
exponential tilt of a
globally Lipschitz potential `U`: both pairings are integrable and `∫ D_v η dν = ∫ η D_v U dν`; all
finite dimensions. -/
theorem integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz {n : ℕ}
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ} {L Leta : NNReal} (hU : LipschitzWith L U)
    (heta : LipschitzWith Leta eta) (C : ℝ) (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hnorm : (∫ x, Real.exp (-U x) ∂volume) = 1) (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => fderiv ℝ eta x v)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
      Integrable (fun x => eta x * fderiv ℝ U x v)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
        (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
          ∫ x,
            eta x *
              fderiv ℝ U x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) := by
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-U)
  have hexp : Integrable (fun x => Real.exp (-U x)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure mu := isProbabilityMeasure_tilted hexp
  have hdf (F : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal} (hF : LipschitzWith K F) (x) :
    ‖fderiv ℝ F x v‖ ≤ (K : ℝ) * ‖v‖ :=
    ((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg v))
  have hdmeas (F : EuclideanSpace ℝ (Fin n) → ℝ) : Measurable (fun x => fderiv ℝ F x v) :=
    (continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ F)
  have hdet : Integrable (fun x => fderiv ℝ eta x v) mu :=
    (integrable_const ((Leta : ℝ) * ‖v‖)).mono' (hdmeas eta).aestronglyMeasurable
      (ae_of_all _ (hdf eta heta))
  have het : Integrable eta mu :=
    (integrable_const C).mono' heta.continuous.measurable.aestronglyMeasurable
      (ae_of_all _ hbound)
  have hedu : Integrable (fun x => eta x * fderiv ℝ U x v) mu := by
    apply
      (het.norm.const_mul ((L : ℝ) * ‖v‖)).mono'
        (heta.continuous.measurable.mul (hdmeas U)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖eta x * fderiv ℝ U x v‖ ≤ _
    rw [norm_mul]
    nlinarith [hdf U hU x, norm_nonneg (eta x)]
  obtain ⟨hwexp, hdexp⟩ := hasWeakDerivAlong_exp_neg_of_lipschitz hU v
  have hweta := hasWeakDerivAlong_of_lipschitz heta v
  have hetderiv (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => fderiv ℝ eta x v) 2 (volume.restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    apply MemLp.of_bound (hdmeas eta).aestronglyMeasurable ((Leta : ℝ) * ‖v‖)
    exact ae_of_all _ (hdf eta heta)
  have hw :=
    (hwexp.mul_of_locally_bounded hweta
        (fun S hS =>
          memLp_top_restrict_of_continuous (Real.continuous_exp.comp hU.continuous.neg) S hS)
        (memLp_top_restrict_of_continuous heta.continuous) hdexp hetderiv).1
  have hleft : Integrable (fun x => Real.exp (-U x) * eta x) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using (integrable_tilted_iff hexp eta).mp het
  have hright1 : Integrable (fun x => Real.exp (-U x) * (eta x * fderiv ℝ U x v)) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using
      (integrable_tilted_iff hexp (fun x => eta x * fderiv ℝ U x v)).mp hedu
  have hright2 : Integrable (fun x => Real.exp (-U x) * fderiv ℝ eta x v) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using
      (integrable_tilted_iff hexp (fun x => fderiv ℝ eta x v)).mp hdet
  have hprod :
    Integrable
      (fun x =>
        (-Real.exp (-U x) * fderiv ℝ U x v) * eta x + Real.exp (-U x) * fderiv ℝ eta x v)
      volume := by
    apply (hright1.neg.add hright2).congr
    filter_upwards [] with x
    change
      -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) + Real.exp (-U x) * fderiv ℝ eta x v = _
    ring
  have hz := integral_eq_zero_of_integrable_weak_derivative hw hleft hprod
  have heq :
    (∫ x,
        (-Real.exp (-U x) * fderiv ℝ U x v) * eta x +
          Real.exp (-U x) * fderiv ℝ eta x v ∂volume) =
      -(∫ x, Real.exp (-U x) * (eta x * fderiv ℝ U x v) ∂volume) +
        ∫ x, Real.exp (-U x) * fderiv ℝ eta x v ∂volume := by
    calc
      _ =
          ∫ x,
            -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) +
              Real.exp (-U x) * fderiv ℝ eta x v ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ =
          (∫ x, -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) ∂volume) +
            ∫ x, Real.exp (-U x) * fderiv ℝ eta x v ∂volume :=
        integral_add hright1.neg hright2
      _ = _ := by rw [integral_neg]
  have htilt (k : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, k x ∂mu) = ∫ x, Real.exp (-U x) * k x ∂volume := by
    change (∫ x, k x ∂volume.tilted (-U)) = _
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
  refine ⟨hdet, hedu, ?_⟩
  change (∫ x, fderiv ℝ eta x v ∂mu) = ∫ x, eta x * fderiv ℝ U x v ∂mu
  rw [htilt, htilt]
  linarith

end FunctionalInequalities.Analysis

end BoundedLipschitzTiltedIBP
