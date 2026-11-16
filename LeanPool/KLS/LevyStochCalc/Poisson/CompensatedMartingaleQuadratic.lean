/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedMartingaleIncrement

/-!
# Quadratic-variation martingale of the compensated simple integral

The set-level weighted isometry `∫ g·(Iₜ − Iₛ)² = ∑_i ν̂(Rᵢ).toReal · ∫ g·ξᵢ²` over the
increment boxes `Rᵢ = timeRect i t \ timeRect i s`, membership of `simpleIntegral N φ t` in
`L²(P)` at every running time, its vanishing at nonpositive times, and the resulting
martingale property of the compensated square
`t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` with respect to a Poisson
filtration; also the joint measurability of the simple integrand `eval` in `(s, e, ω)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Set-level weighted quadratic-variation isometry.** For an adapted simple
integrand `φ`, an `ℱ_s`-measurable bounded weight `g`, and `0 ≤ s ≤ t`,
`∫ g·(Iₜ − Iₛ)² = ∑_i ν̂(Rᵢ).toReal · ∫ g·ξᵢ²` with `Rᵢ = timeRect i t \ timeRect i s`.
The increment squares onto the increment boxes (`simpleIntegral_sub_eq_increment_ae`);
off-diagonal terms vanish (`offDiagonal_increment_zero`) and diagonal terms give the
box intensities (`diagonal_increment_sq`). The compensated analogue of the Brownian
`simpleIntegral_sub_sq_bochner_clamped_weighted`. -/
lemma simpleIntegral_sub_sq_weighted
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν
            (φ.timeRect i t \ φ.timeRect i s)).toReal
          * ∫ ω, g ω * (φ.ξ i ω) ^ 2 ∂P := by
  have hgmeas : Measurable g := (hg.mono (ℱ.le' s)).measurable
  have hRm : ∀ i : Fin φ.N, MeasurableSet (φ.timeRect i t \ φ.timeRect i s) := fun i =>
    (measurableSet_Ioc.prod (φ.A_measurable i)).diff (measurableSet_Ioc.prod (φ.A_measurable i))
  have hRf : ∀ i : Fin φ.N,
      LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t \ φ.timeRect i s) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (referenceIntensity_timeRect_ne_top φ i t) (measure_mono Set.sdiff_subset)
  have hRbox : ∀ k : Fin φ.N, φ.timeRect k t \ φ.timeRect k s
      = Set.Ioc (max s (min (φ.partition k.castSucc) t))
          (max s (min (φ.partition k.succ) t)) ×ˢ φ.A k :=
    fun k => timeRect_sdiff_eq_box φ k hst
  have h_a_le_b : ∀ k : Fin φ.N,
      max s (min (φ.partition k.castSucc) t) ≤ max s (min (φ.partition k.succ) t) :=
    fun k => max_le_max (le_refl s)
      (min_le_min (le_of_lt (φ.partition_strictMono Fin.castSucc_lt_succ)) (le_refl t))
  set term : Fin φ.N → Ω → ℝ :=
    fun i ω => φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω with hterm
  -- integrability of every weighted cross product
  have h_cross : ∀ i j : Fin φ.N,
      MeasureTheory.Integrable (fun ω => g ω * (term i ω * term j ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := φ.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := φ.ξ_bounded j
    have hcross := compensated_cross_integrable N (hRm i) (hRm j) (hRf i) (hRf j)
    have hbdd_part : MeasureTheory.Integrable
        (fun ω => (g ω * (φ.ξ i ω * φ.ξ j ω))
          * (N.compensated (φ.timeRect i t \ φ.timeRect i s) ω
              * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)) P := by
      refine MeasureTheory.Integrable.bdd_mul hcross
        ((hgmeas.mul ((φ.ξ_measurable i).mul (φ.ξ_measurable j))).aestronglyMeasurable)
        (c := Cg * (|Mi| * |Mj|)) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (hg_bdd ω)
        (mul_le_mul ((hMi ω).trans (le_abs_self Mi)) ((hMj ω).trans (le_abs_self Mj))
          (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (le_trans (abs_nonneg _) (hg_bdd ω))
    refine hbdd_part.congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [hterm]; ring
  -- expand the squared increment as a double sum
  have h_expand : (fun ω => g ω * (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2)
      =ᵐ[P] fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N, g ω * (term i ω * term j ω) := by
    filter_upwards [simpleIntegral_sub_eq_increment_ae N φ hst] with ω hω
    rw [hω]
    rw [show (∑ i : Fin φ.N, term i ω) ^ 2
          = ∑ i : Fin φ.N, ∑ j : Fin φ.N, term i ω * term j ω from by
        rw [sq, Finset.sum_mul_sum]]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
  rw [MeasureTheory.integral_congr_ae h_expand]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j), Finset.sum_eq_single i]
  · -- diagonal j = i
    rcases eq_or_lt_of_le (h_a_le_b i) with h_deg | h_gen
    · -- degenerate: increment empty, both sides 0
      have hRe : φ.timeRect i t \ φ.timeRect i s = ∅ := by
        rw [hRbox i, ← h_deg, Set.Ioc_self, Set.empty_prod]
      have h0 : (fun ω => g ω * (term i ω * term i ω)) = fun _ => (0 : ℝ) := by
        funext ω; simp only [hterm, hRe]
        unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
      rw [h0, MeasureTheory.integral_zero, hRe]; simp
    · -- genuine: diagonal second moment
      rw [show (fun ω => g ω * (term i ω * term i ω))
            = fun ω => (g ω * (φ.ξ i ω) ^ 2)
                * (N.compensated (φ.timeRect i t \ φ.timeRect i s) ω) ^ 2 from by
          funext ω; simp only [hterm]; ring]
      rw [diagonal_increment_sq N ℱ hℱ φ i hs hst (h_adapt i) hg h_gen, mul_comm]
  · intro j _ hj
    simp only [hterm]
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rcases eq_or_lt_of_le (h_a_le_b i) with h_deg | h_gen
      · have hRe : φ.timeRect i t \ φ.timeRect i s = ∅ := by
            rw [hRbox i, ← h_deg, Set.Ioc_self, Set.empty_prod]
        rw [show (fun ω => g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
              * (φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)))
            = fun _ => (0 : ℝ) from by
          funext ω; rw [hRe]
          unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp,
          MeasureTheory.integral_zero]
      · rw [show (fun ω => g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
              * (φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)))
              = fun ω => g ω * ((φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)
                * (φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)) from by
            funext ω; ring]
        exact offDiagonal_increment_zero N ℱ hℱ φ h_lt hs hst (h_adapt j) (h_adapt i) hg h_gen
    · rcases eq_or_lt_of_le (h_a_le_b j) with h_deg | h_gen
      · have hRe : φ.timeRect j t \ φ.timeRect j s = ∅ := by
            rw [hRbox j, ← h_deg, Set.Ioc_self, Set.empty_prod]
        rw [show (fun ω => g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
              * (φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)))
            = fun _ => (0 : ℝ) from by
          funext ω; rw [hRe]
          unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp,
          MeasureTheory.integral_zero]
      · exact offDiagonal_increment_zero N ℱ hℱ φ h_gt hs hst (h_adapt i) (h_adapt j) hg h_gen
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`simpleIntegral N φ t ∈ L²(P)` at every running time `t`.** Each summand
`ξᵢ·Ñ(timeRect i t)` is the product of a bounded coefficient and a compensated mass
in `L²` (`compensated_sq_integrable`), so the finite sum is in `L²`. No adaptedness
needed (unlike the full-horizon isometry route). -/
lemma simpleIntegral_memLp_at
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ t ω) 2 P := by
  have h_unfold : (fun ω => simpleIntegral N φ t ω)
      = ∑ i : Fin φ.N, fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω := by
    funext ω; rw [Finset.sum_apply]; rfl
  rw [h_unfold]
  refine MeasureTheory.memLp_finsetSum' _ (fun i _ => ?_)
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hmeas : MeasurableSet (φ.timeRect i t) := measurableSet_Ioc.prod (φ.A_measurable i)
  have hÑ_aesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => N.compensated (φ.timeRect i t) ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hmeas)).sub_const _).aestronglyMeasurable
  have hÑ_memLp : MeasureTheory.MemLp (fun ω => N.compensated (φ.timeRect i t) ω) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hÑ_aesm).mpr
      (compensated_sq_integrable N hmeas (referenceIntensity_timeRect_ne_top φ i t))
  refine MeasureTheory.MemLp.mono' (hÑ_memLp.norm.const_mul |M|)
    ((φ.ξ_measurable i).aestronglyMeasurable.mul hÑ_aesm) ?_
  filter_upwards with ω
  change ‖φ.ξ i ω * N.compensated (φ.timeRect i t) ω‖
    ≤ |M| * ‖N.compensated (φ.timeRect i t) ω‖
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self M)

/-- The simple integral vanishes at every nonpositive time (each time-rectangle
`(tᵢ ∧ u, tᵢ₊₁ ∧ u]` is empty since `0 ≤ tᵢ` and `u ≤ 0`). -/
lemma simpleIntegral_eq_zero_of_nonpos
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {u : ℝ} (hu : u ≤ 0) (ω : Ω) :
    simpleIntegral N φ u ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have hps_nn : 0 ≤ φ.partition i.succ := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.succ)
    rwa [φ.partition_zero] at this
  have hrect : φ.timeRect i u = ∅ := by
    rw [SimplePredictable.timeRect, min_eq_right (hu.trans hpc_nn),
      min_eq_right (hu.trans hps_nn), Set.Ioc_self, Set.empty_prod]
  rw [hrect]
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp

/-- **Conditional Pythagoras for a martingale.** `𝔼[(Mₜ − Mₛ)² | ℱ_s] =ᵐ 𝔼[Mₜ²|ℱ_s] − Mₛ²`.
Generic (no compensated-Poisson content); a local copy of the Brownian-side lemma to
avoid a backward layer dependency. -/
private lemma condExp_sq_increment_of_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hMt.aestronglyMeasurable).mp hMt
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hMs.aestronglyMeasurable).mp hMs
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P := hMs.integrable_mul hMt
  have hMsm : StronglyMeasurable[ℱ s] (M s) := hmart.stronglyAdapted s
  have hMs2m : StronglyMeasurable[ℱ s] (fun ω => (M s ω) ^ 2) := by
    have heq : (fun ω => (M s ω) ^ 2) = (fun ω => M s ω * M s ω) := by funext ω; ring
    rw [heq]; exact hMsm.mul hMsm
  have hf_int : MeasureTheory.Integrable (fun ω => (M t ω - M s ω) ^ 2) P := by
    have heq : (fun ω => (M t ω - M s ω) ^ 2)
        = (fun ω => (M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) := by funext ω; ring
    rw [heq]; exact (hMt2.sub (hcr.const_mul 2)).add hMs2
  have hcross_ae : P[(fun ω => M s ω * M t ω) | ℱ s] =ᵐ[P] fun ω => (M s ω) ^ 2 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ s) hMsm
      (show MeasureTheory.Integrable ((M s) * (M t)) P from hcr)
      (hmart.integrable t)
    filter_upwards [hpull, hmart.condExp_ae_eq hst] with ω hp hmeq
    have hp' : P[(fun ω => M s ω * M t ω) | ℱ s] ω = M s ω * (P[M t | ℱ s]) ω := by
      have : (fun ω => M s ω * M t ω) = (M s) * (M t) := rfl
      rw [this]; simpa [Pi.mul_apply] using hp
    rw [hp', hmeq, ← pow_two]
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf_int
    (fun B _ _ => (MeasureTheory.integrable_condExp.sub hMs2).integrableOn)
    (fun B hB _ => ?_)
    ((MeasureTheory.stronglyMeasurable_condExp.sub hMs2m).aestronglyMeasurable)
  have hcross : ∫ ω in B, M s ω * M t ω ∂P = ∫ ω in B, (M s ω) ^ 2 ∂P :=
    calc ∫ ω in B, M s ω * M t ω ∂P
        = ∫ ω in B, (P[(fun ω => M s ω * M t ω) | ℱ s]) ω ∂P :=
          (MeasureTheory.setIntegral_condExp hm hcr hB).symm
      _ = ∫ ω in B, (M s ω) ^ 2 ∂P :=
          MeasureTheory.setIntegral_congr_ae (hm B hB) (hcross_ae.mono (fun ω hω _ => hω))
  have e1 : ∫ ω in B, ((P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2) ∂P
      = (∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P) - ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn hMs2.integrableOn
  have e1' : ∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P = ∫ ω in B, (M t ω) ^ 2 ∂P :=
    MeasureTheory.setIntegral_condExp hm hMt2 hB
  have hexp : ∫ ω in B, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P :=
    MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => by ring)
  have e2a : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
      = (∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_add ((hMt2.sub (hcr.const_mul 2)).integrableOn) hMs2.integrableOn
  have e2b : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
      = (∫ ω in B, (M t ω) ^ 2 ∂P) - ∫ ω in B, 2 * (M s ω * M t ω) ∂P :=
    MeasureTheory.integral_sub hMt2.integrableOn (hcr.const_mul 2).integrableOn
  have e2c : ∫ ω in B, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω in B, M s ω * M t ω ∂P :=
    MeasureTheory.integral_const_mul 2 _
  rw [e1, e1', hexp, e2a, e2b, e2c, hcross]; ring

/-- **Simple-level quadratic-variation martingale (compensated).** For an adapted
simple integrand `φ`, the compensated square
`t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` is a martingale wrt the
natural filtration. The conditional increment `𝔼[(Iₜ − Iₛ)² | ℱ_s]` equals
`𝔼[Aₜ − Aₛ | ℱ_s]` by the set-level isometry (`simpleIntegral_sub_sq_weighted` with
`g = 1_B`), matched against the clamped compensator
(`setIntegral_eval_sq_Icc_clamped`); the conditional Pythagoras then gives the
martingale identity for `0 ≤ s ≤ t`, with the `s < 0` case via the tower property.
Compensated analogue of `martingale_simpleIntegral_sq_sub_compensator`. -/
lemma martingale_simpleIntegral_sq_sub_compensator
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral N φ t ω) ^ 2
        - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
      ℱ P := by
  have hImart : MeasureTheory.Martingale (fun u => simpleIntegral N φ u) ℱ P :=
    martingale_simpleIntegral_compensated N ℱ hℱ φ h_adapt
  have hIL2 : ∀ u, MeasureTheory.MemLp (fun ω => simpleIntegral N φ u ω) 2 P :=
    fun u => simpleIntegral_memLp_at N φ u
  set c : Fin φ.N → ℝ → ℝ :=
    fun i u => (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i u)).toReal with hc
  -- `ξᵢ²` integrable.
  have hξ2int : ∀ i : Fin φ.N, MeasureTheory.Integrable (fun ω => (φ.ξ i ω) ^ 2) P := fun i => by
    obtain ⟨M, hM⟩ := φ.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (M ^ 2))
      ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  -- The compensator coefficient vanishes once `u < tᵢ`.
  have hc_zero : ∀ i : Fin φ.N, ∀ u : ℝ, u < φ.partition i.castSucc → c i u = 0 := by
    intro i u hu
    have hps : φ.partition i.castSucc < φ.partition i.succ :=
      φ.partition_strictMono Fin.castSucc_lt_succ
    have hrect : φ.timeRect i u = ∅ := by
      rw [SimplePredictable.timeRect, min_eq_right hu.le,
        min_eq_right (hu.le.trans hps.le), Set.Ioc_self, Set.empty_prod]
    change (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i u)).toReal = 0
    rw [hrect]; simp
  -- `A u = ∑ᵢ c i u · ξᵢ²` for `u ≥ 0`; `A u = 0` for `u < 0`.
  have hA_clamped : ∀ u : ℝ, 0 ≤ u → ∀ ω,
      (∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
        = ∑ i : Fin φ.N, c i u * (φ.ξ i ω) ^ 2 :=
    fun u hu ω => setIntegral_eval_sq_Icc_clamped φ ω hu
  have hA_neg : ∀ u : ℝ, u < 0 → ∀ ω,
      (∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume) = 0 := by
    intro u hu ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
  -- Compensator integrability.
  have hAint : ∀ u, MeasureTheory.Integrable
      (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume) P := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
            = fun ω => ∑ i : Fin φ.N, c i u * (φ.ξ i ω) ^ 2 from funext (hA_clamped u hu)]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hξ2int i).const_mul _)
    · rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
            = fun _ => (0 : ℝ) from funext (hA_neg u hu)]
      exact MeasureTheory.integrable_const 0
  -- Compensator adaptedness.
  have hA_adapt : ∀ u, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
      (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume) := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
            = fun ω => ∑ i : Fin φ.N, c i u * (φ.ξ i ω) ^ 2 from funext (hA_clamped u hu)]
      refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
      by_cases hpc : φ.partition i.castSucc ≤ u
      · have hξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
            (fun ω => (φ.ξ i ω) ^ 2) := by
          simpa [pow_two, Pi.mul_def] using ((h_adapt i).mono (ℱ.mono hpc)).mul ((h_adapt i).mono
            (ℱ.mono hpc))
        exact hξ2.const_mul _
      · push Not at hpc
        rw [show (fun ω => c i u * (φ.ξ i ω) ^ 2) = fun _ => (0 : ℝ) from by
          funext ω; rw [hc_zero i u hpc, zero_mul]]
        exact stronglyMeasurable_const
    · rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) u, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume)
            = fun _ => (0 : ℝ) from funext (hA_neg u hu)]
      exact stronglyMeasurable_const
  -- The compensator increment matches the increment-box intensities.
  have hnu_sub : ∀ i : Fin φ.N, ∀ {s t : ℝ}, 0 ≤ s → s ≤ t →
      c i t - c i s = (LevyStochCalc.Poisson.referenceIntensity ν
        (φ.timeRect i t \ φ.timeRect i s)).toReal := by
    intro i s t hs hst
    have hsub := timeRect_subset φ i hst
    have hmeas_s : MeasurableSet (φ.timeRect i s) := measurableSet_Ioc.prod (φ.A_measurable i)
    have hfin_s := referenceIntensity_timeRect_ne_top φ i s
    change (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t)).toReal
        - (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i s)).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t \ φ.timeRect i s)).toReal
    rw [MeasureTheory.measure_sdiff hsub hmeas_s.nullMeasurableSet hfin_s,
      ENNReal.toReal_sub_of_le (measure_mono hsub) (referenceIntensity_timeRect_ne_top φ i t)]
  -- conditional martingale identity for `0 ≤ s ≤ t`, via set integrals.
  have hcond : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P[(fun ω => (simpleIntegral N φ t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) | ℱ.seq s]
        =ᵐ[P] fun ω => (simpleIntegral N φ s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume := by
    intro s t hs hst
    have hm : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    have hIt2 : MeasureTheory.Integrable (fun ω => (simpleIntegral N φ t ω) ^ 2) P :=
      (MeasureTheory.memLp_two_iff_integrable_sq (hIL2 t).aestronglyMeasurable).mp (hIL2 t)
    have hIs2 : MeasureTheory.Integrable (fun ω => (simpleIntegral N φ s ω) ^ 2) P :=
      (MeasureTheory.memLp_two_iff_integrable_sq (hIL2 s).aestronglyMeasurable).mp (hIL2 s)
    have hIinc_int : MeasureTheory.Integrable
        (fun ω => (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2) P := by
      have heq : (fun ω => (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2)
          = fun ω => (simpleIntegral N φ t ω) ^ 2
            - 2 * (simpleIntegral N φ s ω * simpleIntegral N φ t ω)
            + (simpleIntegral N φ s ω) ^ 2 := by funext ω; ring
      rw [heq]
      exact (hIt2.sub (((hIL2 s).integrable_mul (hIL2 t)).const_mul 2)).add hIs2
    have hNs_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        (fun ω => (simpleIntegral N φ s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) := by
      have hIs2m : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
          (fun ω => (simpleIntegral N φ s ω) ^ 2) := by
        simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted s).mul (hImart.stronglyAdapted s)
      exact hIs2m.sub (hA_adapt s)
    refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm (hIt2.sub (hAint t))
      (fun B _ _ => (hIs2.sub (hAint s)).integrableOn) (fun B hB _ => ?_)
      hNs_meas.aestronglyMeasurable).symm
    simp only [Pi.sub_apply]
    have hsplitN_s : ∫ ω in B, ((simpleIntegral N φ s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral N φ s ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P :=
      MeasureTheory.integral_sub hIs2.integrableOn (hAint s).integrableOn
    have hsplitN_t : ∫ ω in B, ((simpleIntegral N φ t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral N φ t ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P :=
      MeasureTheory.integral_sub hIt2.integrableOn (hAint t).integrableOn
    -- set Pythagoras: `∫_B (I_t−I_s)² = ∫_B I_t² − ∫_B I_s²`.
    have hsetpyth : ∫ ω in B, (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2 ∂P
        = (∫ ω in B, (simpleIntegral N φ t ω) ^ 2 ∂P)
          - ∫ ω in B, (simpleIntegral N φ s ω) ^ 2 ∂P := by
      have hpyth := condExp_sq_increment_of_martingale hImart (hIL2 s) (hIL2 t) hst
      calc ∫ ω in B, (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2 ∂P
          = ∫ ω in B, (P[(fun ω => (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2)
              | ℱ.seq s]) ω ∂P := (MeasureTheory.setIntegral_condExp hm hIinc_int hB).symm
        _ = ∫ ω in B, ((P[(fun ω => (simpleIntegral N φ t ω) ^ 2) | ℱ.seq s]) ω
              - (simpleIntegral N φ s ω) ^ 2) ∂P :=
            MeasureTheory.setIntegral_congr_ae (hm B hB) (hpyth.mono (fun ω hω _ => hω))
        _ = (∫ ω in B, (P[(fun ω => (simpleIntegral N φ t ω) ^ 2) | ℱ.seq s]) ω ∂P)
              - ∫ ω in B, (simpleIntegral N φ s ω) ^ 2 ∂P :=
            MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn
              hIs2.integrableOn
        _ = (∫ ω in B, (simpleIntegral N φ t ω) ^ 2 ∂P)
              - ∫ ω in B, (simpleIntegral N φ s ω) ^ 2 ∂P := by
            rw [MeasureTheory.setIntegral_condExp hm hIt2 hB]
    -- the `ℱ_s`-measurable bounded indicator weight `g = 1_B`.
    have hg : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        (Set.indicator B (fun _ => (1 : ℝ))) := stronglyMeasurable_const.indicator hB
    have hg_bdd : ∀ ω, |Set.indicator B (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]; norm_num
      · rw [Set.indicator_of_notMem hω]; norm_num
    have hind : ∀ (F : Ω → ℝ), ∫ ω in B, F ω ∂P
        = ∫ ω, Set.indicator B (fun _ => (1 : ℝ)) ω * F ω ∂P := by
      intro F
      have heqf : (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω * F ω) = Set.indicator B F := by
        funext ω
        by_cases hω : ω ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [heqf, MeasureTheory.integral_indicator (hm B hB)]
    -- set isometry: `∫_B (I_t−I_s)² = ∑ᵢ ν̂(Rᵢ).toReal · ∫_B ξᵢ²`.
    have hiso_set : ∫ ω in B, (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2 ∂P
        = ∑ i : Fin φ.N, (c i t - c i s) * ∫ ω in B, (φ.ξ i ω) ^ 2 ∂P := by
      rw [hind, simpleIntegral_sub_sq_weighted N ℱ hℱ φ h_adapt hs hst hg hg_bdd]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hnu_sub i hs hst, hind (fun ω => (φ.ξ i ω) ^ 2)]
    -- compensator increment: `∫_B (A_t − A_s) = ∑ᵢ (c i t − c i s)·∫_B ξᵢ²`.
    have hAdiff_set : (∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) ∂P
        = ∑ i : Fin φ.N, (c i t - c i s) * ∫ ω in B, (φ.ξ i ω) ^ 2 ∂P := by
      rw [MeasureTheory.setIntegral_congr_fun (hm B hB)
            (fun ω _ => hA_clamped t (hs.trans hst) ω),
          MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => hA_clamped s hs ω)]
      rw [MeasureTheory.integral_finsetSum _
            (fun i _ => ((hξ2int i).const_mul (c i t)).integrableOn),
          MeasureTheory.integral_finsetSum _
            (fun i _ => ((hξ2int i).const_mul (c i s)).integrableOn),
          ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← sub_mul]
    rw [hsplitN_s, hsplitN_t]
    have hkey : (∫ ω in B, (simpleIntegral N φ t ω) ^ 2 ∂P)
          - ∫ ω in B, (simpleIntegral N φ s ω) ^ 2 ∂P
        = ∑ i : Fin φ.N, (c i t - c i s) * ∫ ω in B, (φ.ξ i ω) ^ 2 ∂P := hsetpyth ▸ hiso_set
    linarith [hkey, hAdiff_set]
  -- assemble the full martingale (handle `s < 0` by the tower property).
  refine ⟨?_, fun s t hst => ?_⟩
  · intro u
    have hI2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
        (fun ω => (simpleIntegral N φ u ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted u).mul (hImart.stronglyAdapted u)
    exact hI2.sub (hA_adapt u)
  · rcases le_or_gt 0 s with hs | hs
    · exact hcond s t hs hst
    · have hc0 : ∀ i : Fin φ.N, c i 0 = 0 := by
        intro i
        have hpc_nn : 0 ≤ φ.partition i.castSucc := by
          have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
          rwa [φ.partition_zero] at this
        have hps_nn : 0 ≤ φ.partition i.succ := by
          have := φ.partition_strictMono.monotone (Fin.zero_le i.succ)
          rwa [φ.partition_zero] at this
        have hrect : φ.timeRect i 0 = ∅ := by
          rw [SimplePredictable.timeRect, min_eq_right hpc_nn, min_eq_right hps_nn,
            Set.Ioc_self, Set.empty_prod]
        change (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i 0)).toReal = 0
        rw [hrect]; simp
      have hN0 : (fun ω => (simpleIntegral N φ 0 ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) =ᵐ[P] 0 := by
        filter_upwards with ω
        rw [simpleIntegral_zero N φ ω, hA_clamped 0 (le_refl 0) ω,
          Finset.sum_eq_zero (fun i _ => by rw [hc0 i, zero_mul])]; simp
      have hle0 : ℱ.seq s ≤ ℱ.seq 0 := ℱ.mono (le_of_lt hs)
      rcases le_or_gt 0 t with ht | ht
      · have h0 := hcond 0 t (le_refl 0) ht
        calc P[(fun ω => (simpleIntegral N φ t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) | ℱ.seq s]
            =ᵐ[P] P[P[(fun ω => (simpleIntegral N φ t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume)
                | ℱ.seq 0] | ℱ.seq s] :=
              (MeasureTheory.condExp_condExp_of_le hle0 (ℱ.le 0)).symm
          _ =ᵐ[P] P[(fun ω => (simpleIntegral N φ 0 ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) | ℱ.seq s] :=
              MeasureTheory.condExp_congr_ae h0
          _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hN0
          _ =ᵐ[P] fun ω => (simpleIntegral N φ s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos N φ (le_of_lt hs) ω,
                hA_neg s hs ω]; simp
      · have hNt : (fun ω => (simpleIntegral N φ t ω) ^ 2
            - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) =ᵐ[P] 0 := by
          filter_upwards with ω
          rw [simpleIntegral_eq_zero_of_nonpos N φ (le_of_lt ht) ω, hA_neg t ht ω]; simp
        calc P[(fun ω => (simpleIntegral N φ t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume) | ℱ.seq s]
            =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hNt
          _ =ᵐ[P] fun ω => (simpleIntegral N φ s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, ∫ e, (φ.eval u e ω) ^ 2 ∂ν ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos N φ (le_of_lt hs) ω, hA_neg s hs ω]; simp

/-- **Joint measurability of the simple integrand `eval`** in `(s, e, ω)`. A finite
sum of indicators of the measurable time-mark rectangles, with measurable coefficients.
Needed for the `L²(P ⊗ ds ⊗ ν)` norm computations of the density layer. -/
lemma SimplePredictable.eval_jointly_measurable
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (φ : SimplePredictable Ω E ν T) :
    Measurable (fun p : ℝ × E × Ω => φ.eval p.1 p.2.1 p.2.2) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ?_ ((φ.ξ_measurable i).comp (measurable_snd.comp measurable_snd))
    measurable_const
  exact MeasurableSet.inter (measurable_fst measurableSet_Ioi)
    (MeasurableSet.inter (measurable_fst measurableSet_Iic)
      ((measurable_fst.comp measurable_snd) (φ.A_measurable i)))

end LevyStochCalc.Poisson.Compensated
