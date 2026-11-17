/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Setup
public import LeanPool.KLS.LevyStochCalc.Ito.PicardGlobal
public import LeanPool.KLS.LevyStochCalc.Ito.VectorItoVersionLimit
public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnbounded
public import LeanPool.KLS.LevyStochCalc.Brownian.AugmentedFiltration
public import LeanPool.KLS.LevyStochCalc.Brownian.MultidimFiltered
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionMaster
public import LeanPool.KLS.LevyStochCalc.Probability.DoobContinuous

/-!
# Existence of diffusions with globally Lipschitz bounded coefficients

On any filtered space carrying a multidimensional Brownian motion with a usual filtration,
autonomous globally
Lipschitz bounded coefficients on `Fin N → ℝ` have an everywhere continuous adapted solution with
Itô
representation along itself (`exists_isDiffusion`): the vendored Picard global solution with zero
jumps (a
zero-intensity Poisson random measure), its continuous Itô version, and their identification. Used
for the cutoff
Eldan localization equations (BKL arXiv:2610.05474v1, (67)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace FunctionalInequalities.Probability.Diffusion

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito


private def zeroPoisson {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] : Poisson.PoissonRandomMeasure.{u, 0, 0} P (0 : Measure Unit)
    where
  N := fun _ => 0
  measurable_eval := fun _ => measurable_const
  integer_valued := fun _ _ => Filter.Eventually.of_forall fun _ => ⟨0, by simp⟩
  infinite_at_infinite_intensity := by
    intro B _ h
    simp [Poisson.referenceIntensity] at h
  poisson_law := by
    intro B _ _
    have hz : poissonMeasure 0 = Measure.dirac 0 := by
      apply Measure.ext_of_singleton
      intro n
      cases n <;> simp [poissonMeasure_singleton]
    change P.map (fun _ => (0 : ℝ≥0∞)) = _
    rw [Measure.map_const]
    simp [Poisson.referenceIntensity, Poisson.poissonMeasureENN, hz]
  independent_disjoint := by
    classical
    intro ι _ _ _ _
    apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro S sets hs
    clear hs
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => by_cases hz : (0 : ℝ≥0∞) ∈ sets i <;> simp_all [Set.preimage_const]
  joint_past_future_independent := by
    intro s t _ _ A _ _
    simp only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const]
    exact indep_bot_right _

private theorem zeroPoisson_filtration {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Poisson.IsPoissonFiltration (zeroPoisson P) ℱ := by
  constructor
  · intro t B _ _
    exact measurable_const
  · intro s _
    change Indep (ℱ s)
      (⨆ D ∈ {D : Set (ℝ × Unit) |
          D ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet D},
        MeasurableSpace.comap (fun _ : Ω => (0 : ℝ≥0∞)) inferInstance) P
    simp only [MeasurableSpace.comap_const, iSup_bot]
    exact indep_bot_right _

private def diffusionCoeffs {N d : ℕ}
    (b : (Fin N → ℝ) → Fin N → ℝ)
    (σ : (Fin N → ℝ) → Fin d → Fin N → ℝ) :
    LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs N d Unit :=
  ⟨fun _ => b, fun _ x i k => σ x k i, fun _ _ _ => 0⟩

private theorem diffusionCoeffs_regular {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    (hb : Measurable b) (hσ : ∀ k, Measurable fun x => σ x k) :
    (diffusionCoeffs b σ).IsRegular (0 : Measure Unit) := by
  refine ⟨hb.comp measurable_snd, ?_, measurable_const, ?_, ?_, ?_⟩
  · exact Measurable.of_eval fun i =>
      Measurable.of_eval fun k => ((hσ k).eval (a := i)).comp measurable_snd
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T, (‖b 0‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      isCompact_Icc.measure_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∑ i, ∑ k, (‖σ 0 k i‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    refine ENNReal.mul_lt_top ?_ isCompact_Icc.measure_lt_top
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.pow_lt_top ENNReal.coe_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∫⁻ _e, (‖(0 : Fin N → ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure Unit) ∂volume) < ⊤
    simp

private theorem diffusionCoeffs_lipschitz {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k) :
    ∃ L : ℝ, (diffusionCoeffs b σ).IsLipschitz (0 : Measure Unit) L := by
  classical
  let c : ℝ := (N : ℝ) * (d : ℝ)
  let L : ℝ := (c + 1) * (K : ℝ)
  have hc : 0 ≤ c := by positivity
  have hk : 0 ≤ (K : ℝ) := by positivity
  have hKL : (K : ℝ) ≤ L := by
    dsimp [L]
    nlinarith [mul_nonneg hc hk]
  have hL : 0 ≤ L := hk.trans hKL
  have hfac : c ≤ (c + 1) ^ 2 := by nlinarith
  have hsq : c * (K : ℝ) ^ 2 ≤ L ^ 2 := by
    calc
      c * (K : ℝ) ^ 2 ≤ (c + 1) ^ 2 * (K : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
      _ = L ^ 2 := (mul_pow _ _ _).symm
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro _ x y
    exact (hb.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))
  · intro _ x y
    have hp : ∀ i k, (σ x k i - σ y k i) ^ 2 ≤
        (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
      intro i k
      have hh : |σ x k i - σ y k i| ≤ (K : ℝ) * ‖x - y‖ :=
        (norm_le_pi_norm (σ x k - σ y k) i).trans ((hσ k).norm_sub_le x y)
      have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      simpa only [sq_abs, mul_pow] using hh'
    change (∑ i, ∑ k, (σ x k i - σ y k i) ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2
    calc
      (∑ i, ∑ k, (σ x k i - σ y k i) ^ 2) ≤
          ∑ _i : Fin N, ∑ _k : Fin d, (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hp i k
      _ = c * (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [c]
        ring
      _ ≤ L ^ 2 * ‖x - y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  · intro _ _ _
    change (∫⁻ _e, _ ∂(0 : Measure Unit)) ≤ _
    simp

section Diffusion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}

open LevyStochCalc.Ito.Picard in
/--
Globally Lipschitz bounded autonomous coefficients with zero jumps: an everywhere continuous adapted
solution with Itô representation along itself exists on any Brownian setup with a usual filtration.
-/
theorem exists_isDiffusion (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k) {B : ℝ}
    (hbB : ∀ x, ‖b x‖ ≤ B) (hσB : ∀ x k, ‖σ x k‖ ≤ B) (x₀ : Fin N → ℝ) :
    ∃ Y : ℝ → Ω → Fin N → ℝ, IsDiffusion W ℱ hW b σ x₀ Y := by
  classical
  let C := diffusionCoeffs b σ
  let Z := zeroPoisson P
  have hZ : Poisson.IsPoissonFiltration Z ℱ := zeroPoisson_filtration P ℱ
  have hReg : C.IsRegular (0 : Measure Unit) :=
    diffusionCoeffs_regular hb.continuous.measurable (fun k => (hσ k).continuous.measurable)
  obtain ⟨L, hLip⟩ := diffusionCoeffs_lipschitz hb hσ
  obtain ⟨X, hXm, hXp, _hX0, _hXcad, _hXS, hSol⟩ :=
    exists_globalSolution W Z ℱ hW hZ C hℱ0 hnull hReg hLip x₀
  let S := hSol 0
  let H : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (X s ω) k i
  let a : Fin N → Ω → ℝ → ℝ := fun i ω s => b (X s ω) i
  have hm : ∀ i k, Measurable (Function.uncurry (H i k)) := S.h_σ_meas
  have hp : ∀ i k, Probability.ProgressivelyMeasurable ℱ (H i k) := S.h_σ_progMeas
  have hq :
    ∀ i k (T : ℝ),
      0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    S.h_σ_sq
  have ham : ∀ i, Measurable (Function.uncurry (a i)) := measurable_mu_comp_state C hReg hXm
  have hap : ∀ i, Probability.ProgressivelyMeasurable ℱ (a i) := by
    intro i
    exact
      progressivelyMeasurable_comp_state (X := X) (f := fun _ x => b x i) hXp
        ((hb.continuous.measurable.eval (a := i)).comp measurable_snd)
  have haq :
    ∀ i (T : ℝ),
      0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i
    exact
      energy_lt_top_of_bounded (fun ω s => (norm_le_pi_norm (b (X s ω)) i).trans (hbB (X s ω)))
  obtain ⟨Y, hY⟩ :=
    exists_isVectorItoVersion_of_unbounded W ℱ hW H hm hp hq hℱ0 hnull (X₀ := fun _ => x₀)
      (fun _ => measurable_const) a ham hap haq
  have hXrep :
    ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t := by
    intro t ht
    rcases eq_or_lt_of_le ht with he | ht
    · rw [← he]
      filter_upwards [ae_eq_initial_of_solvesOn W Z ℱ hW hZ C x₀ le_rfl (hSol 0),
        vectorItoProcess_ae_eq_zero W ℱ hW hm hp hq (fun _ => x₀) a] with ω hXω hVω
      exact hXω.trans hVω.symm
    · have hj :
        ∀ᵐ ω ∂P,
          ∀ i : Fin N,
            picardStepJump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i = 0 := by
        apply ae_all_iff.mpr
        intro i
        have hiso :=
          Poisson.Compensated.isometry_stochasticIntegral Z ℱ hZ
            (fun ω s e => C.γ s (X s ω) e i) (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ht
        have hjm :=
          measurable_compensatedIntegral_slice Z ℱ hZ (fun ω s e => C.γ s (X s ω) e i)
            (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t
        have hz :
          (∫⁻ ω,
              (‖Poisson.Compensated.stochasticIntegral Z ℱ hZ (fun ω s e => C.γ s (X s ω) e i)
                      (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω‖₊ :
                  ℝ≥0∞) ^
                2 ∂P) =
            0 := by
          simpa using hiso
        filter_upwards [(lintegral_eq_zero_iff ((hjm.nnnorm.coe_nnreal_ennreal).pow_const 2)).mp
            hz] with
          ω hω
        change
          Poisson.Compensated.stochasticIntegral Z ℱ hZ (fun ω s e => C.γ s (X s ω) e i)
              (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω =
            0
        simpa using hω
      filter_upwards [(hSol t).eqn t ⟨ht.le, le_rfl⟩, hj] with ω heq hz
      funext i
      have hi := heq i
      change
        X t ω i =
          vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t ω i +
            picardStepJump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i at hi
      simpa only [hz i, add_zero] using hi
  have hXY : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] Y t := fun t ht =>
    (hXrep t ht).trans (hY.ae_eq t ht).symm
  have hXY_window :
    ∀ t : ℝ, ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t), X s ω = Y s ω := by
    intro t
    have he : MeasurableSet {p : Ω × ℝ | X p.2 p.1 = Y p.2 p.1} :=
      measurableSet_eq_fun (hXm.comp measurable_swap) hY.measurable_uncurry
    apply (Measure.ae_ae_comm (p := fun ω s => X s ω = Y s ω) he).mpr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    exact hXY s hs.1
  let G : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (Y s ω) k i
  let c : Fin N → Ω → ℝ → ℝ := fun i ω s => b (Y s ω) i
  have gm : ∀ i k, Measurable (Function.uncurry (G i k)) := by
    intro i k
    exact hY.measurable_uncurry_comp ((hσ k).continuous.measurable.eval (a := i))
  have gp : ∀ i k, Probability.ProgressivelyMeasurable ℱ (G i k) := by
    intro i k
    exact hY.progressivelyMeasurable_comp ((continuous_apply i).comp (hσ k).continuous)
  have gq :
    ∀ i k (T : ℝ),
      0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖G i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i k
    exact
      energy_lt_top_of_bounded
        (fun ω s => (norm_le_pi_norm (σ (Y s ω) k) i).trans (hσB (Y s ω) k))
  refine ⟨Y, gm, gp, gq, hY.continuous_path, hY.adapted, ?_⟩
  intro t ht
  refine (hY.ae_eq t ht).trans ?_
  rcases eq_or_lt_of_le ht with he | ht
  · subst t
    exact
      (vectorItoProcess_ae_eq_zero W ℱ hW hm hp hq (fun _ => x₀) a).trans
        (vectorItoProcess_ae_eq_zero W ℱ hW gm gp gq (fun _ => x₀) c).symm
  · have hI :
      ∀ᵐ ω ∂P,
        ∀ (i : Fin N) (k : Fin d),
          coordItoIntegral W ℱ hW H hm hp hq i k t ω =
            coordItoIntegral W ℱ hW G gm gp gq i k t ω := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro k
      apply
        itoIntegral_congr_ae (W.W k) ℱ (hW k) (H i k) (G i k) (hm i k) (hp i k) (hq i k)
          (gm i k) (gp i k) (gq i k) ht
      filter_upwards [hXY_window t] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (fun x => σ x k i) hs
    filter_upwards [hXY_window t, hI] with ω hω hIω
    funext i
    have ha :
      (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) = ∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume := by
      apply integral_congr_ae
      filter_upwards [hω] with s hs
      exact congrArg (fun x => b x i) hs
    have hM :
      vectorItoMartingale W ℱ hW H hm hp hq i t ω =
        vectorItoMartingale W ℱ hW G gm gp gq i t ω :=
      Finset.sum_congr rfl fun k _ => hIω i k
    change
      x₀ i + (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) +
          vectorItoMartingale W ℱ hW H hm hp hq i t ω =
        x₀ i + (∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume) +
          vectorItoMartingale W ℱ hW G gm gp gq i t ω
    rw [ha, hM]

theorem IsDiffusion.ae_initial {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y) :
    ∀ᵐ ω ∂P, Y 0 ω = x₀ := by
  obtain ⟨hm, hp, hq, hY⟩ := h
  exact (hY.ae_eq 0 le_rfl).trans
    (vectorItoProcess_ae_eq_zero W ℱ hW hm hp hq
      (fun _ => x₀) (fun i ω s => b (Y s ω) i))

theorem exists_brownianSetup (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (_ : MultidimBrownianMotion P d), True := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists.{0} d
  exact ⟨Ω, inferInstance, P, inferInstance, W, trivial⟩

end Diffusion

end FunctionalInequalities.Probability.Diffusion
