/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.Profile
public import LeanPool.CIVAxisymmetric.Comparison.Direct.RHSBounds
public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Comparison.PartialLaplacianParts
public import LeanPool.CIVAxisymmetric.Comparison.EnergySpatialIntegration
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality4

/-!
# The spatial energy inequality at one time slice

This is the spatial half of `eq:aniso:comparison:positive:energy`. Fix a time `s` at which the
slice `q(·, s)` is measurable and essentially bounded, and the drift slice `B(·, s)` is bounded,
Lipschitz, with bounded weak divergence. Let `w = q_ε(·, s) - Ψ_σ(·, s)` be the excess of the
mollified slice over the barrier `eq:aniso:comparison:barrier`, `G` the comparison profile and
`H` the right side of `eq:aniso:comparison:mollified`. Then

`∫ G'(w) (H - ∂_τΨ_σ) ≤ Λ ∫ G(w) + ∫ G'(w) |R_ε|`.

The three contributions are those of the manuscript: the barrier is a supersolution, so
`H - ∂_τΨ_σ ≤ Δ_X w - B·∇w + R_ε` pointwise; the diffusion term `∫ G'(w) Δ_X w = -∫ G''(w)|∇_X w|²`
is nonpositive (integration by parts twice, `G` convex); the transport term
`-∫ G'(w) B·∇w = ∫ (div B) G(w)` is at most `Λ ∫ G(w)` by the weak divergence identity applied to
the test function `G ∘ w`, which is smooth with compact support since `w < 0` off a ball.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-- Chain rule for a scalar function composed with a function on `Vec m`. -/
theorem fderiv_comp_real_apply {g : ℝ → ℝ} {f : Vec m → ℝ} {x : Vec m} (hg : Differentiable ℝ g)
    (hf : DifferentiableAt ℝ f x) (v : Vec m) :
    fderiv ℝ (fun y => g (f y)) x v = deriv g (f x) * fderiv ℝ f x v := by
  have h := ((hg (f x)).hasDerivAt).comp_hasFDerivAt x hf.hasFDerivAt
  have h' : fderiv ℝ (g ∘ f) x = deriv g (f x) • fderiv ℝ f x := h.fderiv
  change fderiv ℝ (g ∘ f) x v = _
  rw [h']
  simp

/-- The excess of the mollified slice over the barrier is negative off the ball of radius
`Mq / σ`, once the slice is bounded by `Mq` and `τ₀ ≤ s`. -/
theorem mollifySlice_sub_barrier_neg {ε : ℝ} (hε : 0 < ε) {q : Vec m × ℝ → ℝ} {s Mq M σ K τ₀ : ℝ}
    (hσ : 0 < σ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hτs : τ₀ ≤ s)
    (hmeas : AEStronglyMeasurable (fun y => q (y, s)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, s)| ≤ Mq) {x : Vec m}
    (hx : x ∉ Metric.closedBall (0 : Vec m) (Mq / σ)) :
    mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s) < 0 := by
  have hQ := abs_mollifySlice_le hε hmeas hbdd x
  have hP := le_barrier M K τ₀ s x hσ.le hK hτs
  have hxn : Mq / σ < ‖x‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hσx : Mq < σ * ‖x‖ := by
    rw [div_lt_iff₀ hσ] at hxn
    linarith only [hxn]
  have hQ' := (abs_le.mp hQ).2
  linarith only [hQ', hP, hσx, hM]

/-- **Spatial energy inequality** at one time slice. -/
theorem integral_smoothTransition_mul_mollifiedRHS_le (d : ℕ) {ε σ M Mq τ₀ s : ℝ} {Λ : NNReal}
    (hε : 0 < ε) (hσ : 0 < σ) (hM : 0 ≤ M) (hMq : 0 ≤ Mq) (hτs : τ₀ ≤ s)
    {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, s)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, s)| ≤ Mq)
    (hBb : ∀ x, ‖B (x, s)‖ ≤ Λ) (hBlip : LipschitzWith Λ (fun x => B (x, s)))
    (hdiv : ∀ x, |divB (x, s)| ≤ Λ) (hdivm : AEStronglyMeasurable (fun x => divB (x, s)) volume)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, divB (x, s) * ψ x = -∫ x, ∑ i, B (x, s) i * fderiv ℝ ψ x (basisVec i)) :
    ∫ x, Real.smoothTransition
        (mollifySlice m ε q (x, s) - barrier m M σ (barrierRate m d Λ) τ₀ (x, s))
        * (mollifiedRHS m d ε B divB q x s - σ * barrierRate m d Λ)
      ≤ (Λ : ℝ) * (∫ x, comparisonProfile
          (mollifySlice m ε q (x, s) - barrier m M σ (barrierRate m d Λ) τ₀ (x, s)))
        + ∫ x, Real.smoothTransition
            (mollifySlice m ε q (x, s) - barrier m M σ (barrierRate m d Λ) τ₀ (x, s))
          * |diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
              (fun y => q (y, s)) x| := by
  set K : ℝ := barrierRate m d Λ with hKdef
  have hK : 0 ≤ K := barrierRate_nonneg m d Λ.coe_nonneg
  set W : Vec m × ℝ → ℝ := fun z => mollifySlice m ε q z - barrier m M σ K τ₀ z with hWdef
  set S : Vec m × ℝ → ℝ := fun z => Real.smoothTransition (W z) with hSdef
  set R : Vec m → ℝ := fun x => diPernaLionsCommutator m ε (fun y => B (y, s))
    (fun y => divB (y, s)) (fun y => q (y, s)) x with hRdef
  -- smoothness of the slices
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => mollifySlice m ε q (x, s)) :=
    contDiff_mollifySlice hε s q Mq hmeas hbdd
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => barrier m M σ K τ₀ (x, s)) :=
    (contDiff_barrier M σ K τ₀).comp (contDiff_id.prodMk contDiff_const)
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => W (x, s)) := hQ.sub hP
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => S (x, s)) :=
    Real.smoothTransition.contDiff.comp hW
  have hGW : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => comparisonProfile (W (x, s))) :=
    contDiff_comparisonProfile.comp hW
  have hWd : Differentiable ℝ (fun x : Vec m => W (x, s)) := hW.differentiable (by simp)
  -- support
  have hneg : ∀ x, x ∉ Metric.closedBall (0 : Vec m) (Mq / σ) → W (x, s) < 0 :=
    fun x hx => mollifySlice_sub_barrier_neg hε hσ hM hK hτs hmeas hbdd hx
  have hSsupp : HasCompactSupport (fun x : Vec m => S (x, s)) :=
    HasCompactSupport.intro (isCompact_closedBall _ _) fun x hx =>
      Real.smoothTransition.zero_of_nonpos (hneg x hx).le
  have hGsupp : HasCompactSupport (fun x : Vec m => comparisonProfile (W (x, s))) :=
    HasCompactSupport.intro (isCompact_closedBall _ _) fun x hx =>
      comparisonProfile_eq_zero_of_nonpos (hneg x hx).le
  have hSint : Integrable (fun x : Vec m => S (x, s)) volume :=
    hS.continuous.integrable_of_hasCompactSupport hSsupp
  have hGint : Integrable (fun x : Vec m => comparisonProfile (W (x, s))) volume :=
    hGW.continuous.integrable_of_hasCompactSupport hGsupp
  have hSnn : ∀ x, 0 ≤ S (x, s) := fun x => Real.smoothTransition.nonneg _
  have hS1 : ∀ x, ‖S (x, s)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnn x)]; exact Real.smoothTransition.le_one _
  -- continuity and measurability of the terms
  have hBc : Continuous (fun x : Vec m => B (x, s)) := hBlip.continuous
  have hLapc : ∀ (f : Vec m × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f (x, s)) →
      Continuous (fun x : Vec m => partialLaplacian m d f (x, s)) := by
    intro f hf
    unfold partialLaplacian
    refine continuous_finsetSum _ fun i _ => ?_
    split_ifs
    · have hg := contDiff_gradPair_of_contDiff hf i
      exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact continuous_const
  have hGradc : ∀ (f : Vec m × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f (x, s)) →
      Continuous (fun x : Vec m => gradPair m f (x, s) (B (x, s))) := by
    intro f hf
    unfold gradPair
    exact (hf.continuous_fderiv (by simp)).clm_apply hBc
  have hRm : AEStronglyMeasurable R volume :=
    aestronglyMeasurable_diPernaLionsCommutator ε hBc hdivm hmeas
  have hHm : AEStronglyMeasurable (fun x => mollifiedRHS m d ε B divB q x s - σ * K) volume := by
    unfold mollifiedRHS
    exact ((((hLapc _ hQ).sub (hGradc _ hQ)).aestronglyMeasurable).add hRm).sub
      aestronglyMeasurable_const
  have hHb : ∀ x, ‖mollifiedRHS m d ε B divB q x s - σ * K‖
      ≤ mollifiedRHSBound m d ε Λ Mq + |σ * K| := by
    intro x
    rw [Real.norm_eq_abs]
    have h1 := abs_sub (mollifiedRHS m d ε B divB q x s) (σ * K)
    have h2 := abs_mollifiedRHS_le d hε hMq hmeas hbdd hBb hBlip hdiv hdivm x
    linarith only [h1, h2]
  have hRb : ∀ x, ‖|R x|‖ ≤ Λ * Mq * (mollifierGradConst m + 1) := by
    intro x
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_diPernaLionsCommutator_le_of_ae hε hMq hBlip hdiv hdivm hbdd hmeas x
  -- the pointwise inequality
  have hpt : ∀ x, S (x, s) * (mollifiedRHS m d ε B divB q x s - σ * K)
      ≤ S (x, s) * partialLaplacian m d W (x, s)
        - S (x, s) * gradPair m W (x, s) (B (x, s)) + S (x, s) * |R x| := by
    intro x
    have hsup := barrier_supersolution d M τ₀ (Λ : ℝ) hσ.le B (x, s) (hBb x)
    rw [timeDeriv_barrier] at hsup
    have hLap : partialLaplacian m d W (x, s)
        = partialLaplacian m d (mollifySlice m ε q) (x, s)
          - partialLaplacian m d (barrier m M σ K τ₀) (x, s) :=
      partialLaplacian_sub (x, s) hQ hP
    have hGrad : gradPair m W (x, s) (B (x, s))
        = gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
          - gradPair m (barrier m M σ K τ₀) (x, s) (B (x, s)) :=
      gradPair_sub (x, s) hQ hP (B (x, s))
    have hRabs : R x ≤ |R x| := le_abs_self _
    have hin : mollifiedRHS m d ε B divB q x s - σ * K
        ≤ partialLaplacian m d W (x, s) - gradPair m W (x, s) (B (x, s)) + |R x| := by
      rw [hLap, hGrad]
      unfold mollifiedRHS
      linarith only [hsup, hRabs]
    have h := mul_le_mul_of_nonneg_left hin (hSnn x)
    linarith only [h]
  -- integrability of the pieces
  have hI1 : Integrable (fun x => S (x, s) * (mollifiedRHS m d ε B divB q x s - σ * K)) volume :=
    hSint.mul_bdd hHm (Eventually.of_forall hHb)
  have hI2 : Integrable (fun x => S (x, s) * partialLaplacian m d W (x, s)) volume :=
    (hS.continuous.mul (hLapc _ hW)).integrable_of_hasCompactSupport hSsupp.mul_right
  have hI3 : Integrable (fun x => S (x, s) * gradPair m W (x, s) (B (x, s))) volume :=
    (hS.continuous.mul (hGradc _ hW)).integrable_of_hasCompactSupport hSsupp.mul_right
  have hI4 : Integrable (fun x => S (x, s) * |R x|) volume :=
    hSint.mul_bdd hRm.norm (Eventually.of_forall hRb)
  have hmono : ∫ x, S (x, s) * (mollifiedRHS m d ε B divB q x s - σ * K)
      ≤ ∫ x, (S (x, s) * partialLaplacian m d W (x, s)
        - S (x, s) * gradPair m W (x, s) (B (x, s)) + S (x, s) * |R x|) :=
    integral_mono hI1 ((hI2.sub' hI3).fun_add hI4) hpt
  rw [integral_add (hI2.sub' hI3) hI4, integral_sub hI2 hI3] at hmono
  -- the diffusion term is nonpositive
  have hdiff : ∫ x, S (x, s) * partialLaplacian m d W (x, s) ≤ 0 := by
    rw [integral_partialLaplacian_mul_comm_of_hasCompactSupport hW hS hSsupp,
      integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul hS hW hSsupp]
    refine neg_nonpos.mpr (integral_nonneg fun x => ?_)
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have hchain : gradPair m S (x, s) (basisVec i)
          = deriv Real.smoothTransition (W (x, s)) * gradPair m W (x, s) (basisVec i) :=
        fderiv_comp_real_apply (f := fun y : Vec m => W (y, s))
          (Real.smoothTransition.contDiff (n := 1)).differentiable_one (hWd x) (basisVec i)
      rw [hchain]
      have hd : 0 ≤ deriv Real.smoothTransition (W (x, s)) :=
        Real.smoothTransition.monotone.deriv_nonneg
      have hsq := mul_nonneg hd (mul_self_nonneg (gradPair m W (x, s) (basisVec i)))
      linarith only [hsq]
    · exact le_refl 0
  -- the transport term
  have htrans : -∫ x, S (x, s) * gradPair m W (x, s) (B (x, s))
      ≤ (Λ : ℝ) * ∫ x, comparisonProfile (W (x, s)) := by
    have hw := hweak _ hGW hGsupp
    have hrw : ∀ x, ∑ i, B (x, s) i * fderiv ℝ (fun y => comparisonProfile (W (y, s))) x
        (basisVec i) = S (x, s) * gradPair m W (x, s) (B (x, s)) := by
      intro x
      have hc : ∀ v, fderiv ℝ (fun y => comparisonProfile (W (y, s))) x v
          = Real.smoothTransition (W (x, s)) * gradPair m W (x, s) v := by
        intro v
        rw [fderiv_comp_real_apply (f := fun y : Vec m => W (y, s))
          differentiable_comparisonProfile (hWd x) v, deriv_comparisonProfile]
        rfl
      simp only [hc]
      rw [gradPair, apply_eq_sum_basisVec (fderiv ℝ (fun y => W (y, s)) x) (B (x, s)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hSdef, gradPair]
      ring
    simp only [hrw] at hw
    rw [← hw]
    have hdi : Integrable (fun x => divB (x, s) * comparisonProfile (W (x, s))) volume :=
      hGint.bdd_mul hdivm (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hdiv x)
    rw [← integral_const_mul]
    refine integral_mono hdi (hGint.const_mul _) fun x => ?_
    have hG0 := comparisonProfile_nonneg (W (x, s))
    have hdle : divB (x, s) ≤ Λ := le_trans (le_abs_self _) (hdiv x)
    exact mul_le_mul_of_nonneg_right hdle hG0
  linarith only [hmono, hdiff, htrans]

end CIV
