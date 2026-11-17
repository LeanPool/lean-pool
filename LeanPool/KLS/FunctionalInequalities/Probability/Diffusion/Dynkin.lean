/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Setup
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFinsetSum

/-!
# Dynkin's identity for diffusions with compactly supported coefficients

For continuous compactly supported coefficients and every `C²` function `F`, `F(Y_T)` is integrable
and
`E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds` (vector Itô formula and the mean-zero Brownian integral); and
linear
functionals annihilating the noise evolve pathwise by the drift. These are the only stochastic
inputs of
the generator-form treatment of BKL arXiv:2610.05474v1, Lemmas 4.3, 5.1 and 5.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace FunctionalInequalities.Probability.Diffusion

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito

private theorem compact_sum {α ι : Type*} [TopologicalSpace α]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : α → ℝ)
      exact HasCompactSupport.zero
  | @insert i s hi ih =>
      have hh := (hf i).add ih
      have he :
          (f i + fun x => ∑ j ∈ s, f j x) =
            (fun x => f i x + ∑ j ∈ s, f j x) := rfl
      rw [he] at hh
      simp only [Finset.sum_insert hi]
      exact hh

private theorem compact_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (Y : ℝ → Ω → Fin N → ℝ) :
    ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (Y s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact energy_lt_top_of_bounded fun ω s => by
    simpa only [Real.norm_eq_abs] using hC (Y s ω)

private theorem compact_integral_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    {Y : ℝ → Ω → Fin N → ℝ}
    (hm : Measurable (Function.uncurry fun ω s => Y s ω)) (T : ℝ) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, g (Y s ω)) P := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  have hi : Integrable (Function.uncurry fun ω s => g (Y s ω))
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) :=
    Integrable.of_bound (hc.measurable.comp hm).aestronglyMeasurable C
      (Eventually.of_forall fun z => hC (Y z.2 z.1))
  exact hi.integral_prod_left

private theorem brownian_integrable_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (stochasticIntegralBrownian W ℱ hW H hm hp hq T) P ∧
      ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq T ω ∂P = 0 := by
  have hM := martingale_stochasticIntegralBrownian W ℱ hW H hm hp hq
  refine ⟨hM.integrable T, ?_⟩
  calc
    ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq T ω ∂P =
        ∫ ω, P[stochasticIntegralBrownian W ℱ hW H hm hp hq T | ℱ (-1)] ω ∂P :=
      (integral_condExp (ℱ.le (-1))).symm
    _ = ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq (-1) ω ∂P :=
      integral_congr_ae (hM.condExp_ae_eq (by linarith : (-1 : ℝ) ≤ T))
    _ = 0 := by
      rw [integral_congr_ae
        (stochasticIntegralBrownian_ae_zero_of_neg W ℱ hW H hm hp hq
          (by norm_num : (-1 : ℝ) < 0))]
      exact integral_zero _ _

section Diffusion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}

/-- **Dynkin's identity**: for continuous compactly supported coefficients and `C²` `F`, `F(Y_T)` is
integrable and `E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds`. -/
theorem IsDiffusion.dynkin {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
    {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y)
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
  classical
  obtain ⟨hm, hp, hq, hv⟩ := h
  have h0 := version_ae_eq_zero W ℱ hW hv
  by_cases ht : T = 0
  · subst T
    have he : (fun ω => F (Y 0 ω)) =ᵐ[P] fun _ => F x₀ :=
      h0.fun_comp F
    refine ⟨(integrable_const (F x₀)).congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    simp
  have ht : 0 < T := lt_of_le_of_ne hT (Ne.symm ht)
  let f' := fderiv ℝ F
  let f'' := fderiv ℝ f'
  have hf' : ContDiff ℝ 1 f' := hF.fderiv_right (by norm_num)
  have hf'c : Continuous f' := hf'.continuous
  have hf''c : Continuous f'' := hf'.continuous_fderiv (by norm_num)
  have hbc' (p : Fin N) : Continuous fun x => b x p :=
    (continuous_apply p).comp hbc
  have hbs' (p : Fin N) : HasCompactSupport fun x => b x p := by
    have hh := hbs.comp_left (g := fun z : Fin N → ℝ => z p) (by rfl)
    have he : ((fun z : Fin N → ℝ => z p) ∘ b) = (fun x => b x p) := rfl
    rw [he] at hh
    exact hh
  have hσc' (p : Fin N) (k : Fin d) : Continuous fun x => σ x k p :=
    (continuous_apply p).comp (hσc k)
  have hσs' (p : Fin N) (k : Fin d) : HasCompactSupport fun x => σ x k p := by
    have hh := (hσs k).comp_left (g := fun z : Fin N → ℝ => z p) (by rfl)
    have he :
        ((fun z : Fin N → ℝ => z p) ∘ fun x => σ x k) =
          (fun x => σ x k p) := rfl
    rw [he] at hh
    exact hh
  let A : Fin N → (Fin N → ℝ) → ℝ :=
    fun p x => coordDeriv f' p x * b x p
  let C : Fin N → Fin N → (Fin N → ℝ) → ℝ :=
    fun p q x => coordDeriv₂ f'' p q x * ∑ k, σ x k p * σ x k q
  let G : Fin N → Fin d → (Fin N → ℝ) → ℝ :=
    fun p k x => coordDeriv f' p x * σ x k p
  have hAc (p : Fin N) : Continuous (A p) :=
    (continuous_coordDeriv hf'c p).mul (hbc' p)
  have hAs (p : Fin N) : HasCompactSupport (A p) :=
    (hbs' p).mul_left
  have hCc (p q : Fin N) : Continuous (C p q) :=
    (continuous_coordDeriv₂ hf''c p q).mul
      (continuous_finsetSum _ fun k _ => (hσc' p k).mul (hσc' q k))
  have hCs (p q : Fin N) : HasCompactSupport (C p q) :=
    (compact_sum Finset.univ (fun k x => σ x k p * σ x k q)
      (fun k => (hσs' p k).mul_right)).mul_left
  have hGc (p : Fin N) (k : Fin d) : Continuous (G p k) :=
    (continuous_coordDeriv hf'c p).mul (hσc' p k)
  have hGs (p : Fin N) (k : Fin d) : HasCompactSupport (G p k) :=
    (hσs' p k).mul_left
  have hmg (p : Fin N) (k : Fin d) :
      Measurable (Function.uncurry fun ω s => G p k (Y s ω)) :=
    hv.measurable_uncurry_comp (hGc p k).measurable
  have hpg (p : Fin N) (k : Fin d) :
      Probability.ProgressivelyMeasurable ℱ fun ω s => G p k (Y s ω) :=
    hv.progressivelyMeasurable_comp (hGc p k)
  have hqg (p : Fin N) (k : Fin d) :=
    compact_energy (P := P) (hGc p k) (hGs p k) Y
  have hito := itoFormula_of_unbounded W ℱ hW hv hℱ0 hnull
    (fun _ => measurable_const)
    (fun p => hv.measurable_uncurry_comp (hbc' p).measurable)
    (fun p => hv.progressivelyMeasurable_comp (hbc' p))
    (fun p => compact_energy (P := P) (hbc' p) (hbs' p) Y)
    hF
    (fun x => (hF.differentiable (by norm_num) x).hasFDerivAt)
    (fun x => (hf'.differentiable (by norm_num) x).hasFDerivAt)
    hmg hpg hqg ht
  have hgen (x : Fin N → ℝ) :
      diffusionGenerator b σ F x =
        ∑ p, A p x + (1 / 2 : ℝ) * ∑ p, ∑ q, C p q x := by
    have hfirst : f' x (b x) = ∑ p, A p x := by
      rw [apply_eq_sum_coordDeriv]
      apply Finset.sum_congr rfl
      intro p _
      exact mul_comm _ _
    have hsecond : (∑ k, f'' x (σ x k) (σ x k)) =
        ∑ p, ∑ q, C p q x := by
      simp_rw [apply₂_eq_sum_coordDeriv₂]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact congrArg₂ (fun a c : ℝ => a + (1 / 2 : ℝ) * c) hfirst hsecond
  have hAi (p : Fin N) (ω : Ω) :
      IntegrableOn (fun s => A p (Y s ω)) (Set.Ioc (0 : ℝ) T) volume :=
    ((hAc p).comp (hv.continuous_path ω)).integrableOn_Ioc
  have hCi (p q : Fin N) (ω : Ω) :
      IntegrableOn (fun s => C p q (Y s ω)) (Set.Ioc (0 : ℝ) T) volume :=
    ((hCc p q).comp (hv.continuous_path ω)).integrableOn_Ioc
  have hAE (p : Fin N) :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) P :=
    compact_integral_integrable (hAc p) (hAs p) hv.measurable_uncurry T
  have hCE (p q : Fin N) :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω)) P :=
    compact_integral_integrable (hCc p q) (hCs p q) hv.measurable_uncurry T
  let D : Ω → ℝ :=
    fun ω => ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω)
  have hD (ω : Ω) :
      D ω = (∑ p, ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) +
        (1 / 2 : ℝ) * ∑ p, ∑ q, ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω) := by
    dsimp [D]
    simp_rw [hgen]
    rw [integral_add
      (integrable_finsetSum _ fun p _ => hAi p ω)
      ((integrable_finsetSum _ fun p _ =>
        integrable_finsetSum _ fun q _ => hCi p q ω).const_mul _),
      integral_finsetSum _ (fun p _ => hAi p ω), integral_const_mul,
      integral_finsetSum _ (fun p _ =>
        integrable_finsetSum _ fun q _ => hCi p q ω)]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact integral_finsetSum _ fun q _ => hCi p q ω
  have hDi : Integrable D P := by
    have hi := (integrable_finsetSum Finset.univ fun p _ => hAE p).add
      ((integrable_finsetSum Finset.univ fun p _ =>
        integrable_finsetSum Finset.univ fun q _ => hCE p q).const_mul (1 / 2 : ℝ))
    exact hi.congr (Eventually.of_forall fun ω => (hD ω).symm)
  let M : Fin N → Fin d → Ω → ℝ := fun p k =>
    stochasticIntegralBrownian (W.W k) ℱ (hW k)
      (fun ω s => G p k (Y s ω)) (hmg p k) (hpg p k) (hqg p k) T
  have hM (p : Fin N) (k : Fin d) :
      Integrable (M p k) P ∧ ∫ ω, M p k ω ∂P = 0 :=
    brownian_integrable_mean_zero (W.W k) ℱ (hW k) _ (hmg p k) (hpg p k)
      (hqg p k) hT
  let S : Ω → ℝ := fun ω => ∑ p, ∑ k, M p k ω
  have hSi : Integrable S P :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun k _ => (hM p k).1
  have hSE : ∫ ω, S ω ∂P = 0 := by
    dsimp [S]
    rw [integral_finsetSum _ (fun p _ =>
      integrable_finsetSum _ fun k _ => (hM p k).1)]
    simp_rw [integral_finsetSum _ (fun k _ => (hM _ k).1)]
    simp only [(hM _ _).2, Finset.sum_const_zero]
  have he : (fun ω => F (Y T ω)) =ᵐ[P] fun ω => F x₀ + D ω + S ω := by
    filter_upwards [hito, h0] with ω hi hz
    change F (Y T ω) - F (Y 0 ω) =
      (∑ p, ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) + S ω +
        (1 / 2 : ℝ) * ∑ p, ∑ q,
          ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω) at hi
    rw [hz] at hi
    rw [hD]
    linarith
  have hsumI : Integrable (fun ω => F x₀ + D ω) P :=
    (integrable_const (F x₀)).add hDi
  have hFi : Integrable (fun ω => F (Y T ω)) P :=
    (hsumI.add hSi).congr he.symm
  refine ⟨hFi, ?_⟩
  rw [integral_congr_ae he,
    integral_add hsumI hSi,
    integral_add (f := fun _ : Ω => F x₀) (g := D)
      (integrable_const (F x₀)) hDi, hSE]
  simp [D]

private theorem weighted_noise_zero
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ)
    (H : Fin N → Ω → ℝ → ℝ)
    (hm : ∀ p, Measurable (Function.uncurry (H p)))
    (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (H p))
    (hq : ∀ p (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : Fin N → ℝ) (hz : ∀ ω s, ∑ p, c p * H p ω s = 0)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∑ p, c p * stochasticIntegralBrownian W ℱ hW
      (H p) (hm p) (hp p) (hq p) T ω = 0 := by
  classical
  let K : Fin N → Ω → ℝ → ℝ := fun p ω s => c p * H p ω s
  have hkm (p : Fin N) : Measurable (Function.uncurry (K p)) :=
    measurable_const.mul (hm p)
  have hkp (p : Fin N) : Probability.ProgressivelyMeasurable ℱ (K p) :=
    (Probability.progressivelyMeasurable_const ℱ (c p)).mul (hp p)
  have hkq (p : Fin N) :
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖K p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lintegral_sq_bounded_mul_lt_top (hq p) (abs_nonneg (c p)) (fun _ _ => le_rfl)
  obtain ⟨hsm, hsp, hsq, hsum⟩ :=
    exists_stochasticIntegralBrownian_finsetSum W ℱ hW K hkm hkp hkq Finset.univ hT
  have heq : (fun ω s => ∑ p, K p ω s) = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
    funext ω s
    exact hz ω s
  have hzm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
    measurable_const
  have hzp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
    Probability.progressivelyMeasurable_zero ℱ
  have hzq : ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T _
    simp
  have hzero : stochasticIntegralBrownian W ℱ hW
      (fun ω s => ∑ p, K p ω s) hsm hsp hsq T =ᵐ[P] 0 := by
    rw [stochasticIntegralBrownian_congr_fun W ℱ hW heq hsm hsp hsq hzm hzp hzq T]
    exact stochasticIntegralBrownian_ae_zero W ℱ hW hzm hzp hzq T
  have hscale : ∀ᵐ ω ∂P, ∀ p : Fin N,
      stochasticIntegralBrownian W ℱ hW (K p) (hkm p) (hkp p) (hkq p) T ω =
        c p * stochasticIntegralBrownian W ℱ hW (H p) (hm p) (hp p) (hq p) T ω :=
    ae_all_iff.mpr fun p =>
      stochasticIntegralBrownian_const_mul W ℱ hW (hm p) (hp p) (hq p) (c p)
        (hkm p) (hkp p) (hkq p) hT
  filter_upwards [hsum, hzero, hscale] with ω hs h0 hc
  calc
    ∑ p, c p * stochasticIntegralBrownian W ℱ hW (H p) (hm p) (hp p) (hq p) T ω =
        ∑ p, stochasticIntegralBrownian W ℱ hW (K p) (hkm p) (hkp p) (hkq p) T ω :=
      Finset.sum_congr rfl fun p _ => (hc p).symm
    _ = 0 := hs.symm.trans h0

theorem IsDiffusion.ae_linear_eq_integral {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    (hbc : Continuous b) {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B) {Y : ℝ → Ω → Fin N → ℝ}
    (h : IsDiffusion W ℱ hW b σ x₀ Y) (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (hℓ : ∀ x k, ℓ (σ x k) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ℓ (Y t ω) = ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω)) := by
  classical
  obtain ⟨hm, hp, hq, hv⟩ := h
  let c : Fin N → ℝ := fun p => ℓ (Pi.single p 1)
  have hfixed (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ℓ (Y t ω) = ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω)) := by
    by_cases hz : t = 0
    · subst t
      filter_upwards [version_ae_eq_zero W ℱ hW hv] with ω hω
      rw [hω]
      simp
    have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hn :
      ∀ᵐ ω ∂P,
        ∀ k : Fin d,
          ∑ p,
              c p *
                stochasticIntegralBrownian (W.W k) ℱ (hW k) (fun ω s => σ (Y s ω) k p) (hm p k)
                  (hp p k) (hq p k) t ω =
            0 := by
      apply ae_all_iff.mpr
      intro k
      apply
        weighted_noise_zero (W.W k) ℱ (hW k) (fun p ω s => σ (Y s ω) k p) (fun p => hm p k)
          (fun p => hp p k) (fun p => hq p k) c _ ht'
      intro ω s
      calc
        ∑ p, c p * σ (Y s ω) k p = ∑ p, σ (Y s ω) k p * ℓ (Pi.single p 1) :=
          Finset.sum_congr rfl fun p _ => mul_comm _ _
        _ = ℓ (σ (Y s ω) k) := (clm_apply_pi_real ℓ _).symm
        _ = 0 := hℓ _ _
    filter_upwards [hv.ae_eq t ht, hn] with ω hy hnω
    have hbi (p : Fin N) : IntegrableOn (fun s => b (Y s ω) p) (Set.Ioc (0 : ℝ) t) volume := by
      apply
        Integrable.of_bound
          (((continuous_apply p).comp
              (hbc.comp (hv.continuous_path ω))).measurable.aestronglyMeasurable)
          B
      exact Eventually.of_forall fun s => (norm_le_pi_norm (b (Y s ω)) p).trans (hbB (Y s ω))
    have hdi :
      (∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω))) =
        ∑ p, (∫ s in Set.Ioc (0 : ℝ) t, b (Y s ω) p) * c p := by
      calc
        (∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω))) =
            ∫ s in Set.Ioc (0 : ℝ) t, ∑ p, b (Y s ω) p * c p :=
          integral_congr_ae (Eventually.of_forall fun s => clm_apply_pi_real ℓ (b (Y s ω)))
        _ = ∑ p, (∫ s in Set.Ioc (0 : ℝ) t, b (Y s ω) p) * c p := by
          rw [integral_finsetSum _ (fun p _ => (hbi p).mul_const (c p))]
          apply Finset.sum_congr rfl
          intro p _
          exact integral_mul_const _ _
    have hni :
      (∑ p,
          ∑ k,
            stochasticIntegralBrownian (W.W k) ℱ (hW k) (fun ω s => σ (Y s ω) k p) (hm p k)
                (hp p k) (hq p k) t ω *
              c p) =
        0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simpa only [mul_comm] using hnω k
    rw [hy, clm_apply_pi_real ℓ]
    simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, integral_Icc_eq_integral_Ioc]
    change
      (∑ p, x₀ p * c p) + (∑ p, (∫ s in Set.Ioc (0 : ℝ) t, b (Y s ω) p) * c p) +
          (∑ p,
            ∑ k,
              stochasticIntegralBrownian (W.W k) ℱ (hW k) (fun ω s => σ (Y s ω) k p) (hm p k)
                  (hp p k) (hq p k) t ω *
                c p) =
        ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω))
    rw [hni, add_zero, hdi, clm_apply_pi_real ℓ x₀]
  have hrat :
    ∀ᵐ ω ∂P,
      ∀ q : ℚ, ℓ (Y (max 0 (q : ℝ)) ω) = ℓ x₀ + ∫ s in (0 : ℝ)..max 0 (q : ℝ), ℓ (b (Y s ω)) := by
    apply ae_all_iff.mpr
    intro q
    simpa only [intervalIntegral.integral_of_le (le_max_left 0 (q : ℝ))] using
      hfixed (max 0 (q : ℝ)) (le_max_left _ _)
  filter_upwards [hrat] with ω hω
  have hc : Continuous fun s => ℓ (b (Y s ω)) :=
    ℓ.continuous.comp (hbc.comp (hv.continuous_path ω))
  have hi : Continuous fun t => ∫ s in (0 : ℝ)..t, ℓ (b (Y s ω)) :=
    intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0
  have hmax : Continuous fun t : ℝ => max 0 t := continuous_const.max continuous_id
  have he :
    (fun t : ℝ => ℓ (Y (max 0 t) ω)) = fun t : ℝ =>
      ℓ x₀ + ∫ s in (0 : ℝ)..max 0 t, ℓ (b (Y s ω)) :=
    (Rat.denseRange_cast : DenseRange fun q : ℚ => (q : ℝ)).equalizer
      ((ℓ.continuous.comp (hv.continuous_path ω)).comp hmax)
      (continuous_const.add (hi.comp hmax)) (funext hω)
  intro t ht
  have het := congrFun he t
  simpa only [max_eq_right ht, intervalIntegral.integral_of_le ht] using het

end Diffusion

end FunctionalInequalities.Probability.Diffusion
