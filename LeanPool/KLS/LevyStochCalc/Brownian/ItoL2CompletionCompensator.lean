/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionConvergence

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- `∫ (W_b − W_a) = 0` for `0 ≤ a < b`. -/
lemma brownian_incr_mean
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ∂P = 0 := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ∂P)
        = ∫ x : ℝ, x ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x) _)).symm,
    W.increment_gaussian ha hab]
  exact ProbabilityTheory.integral_id_gaussianReal

/-- **Off-diagonal building block.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a) = 0` — the increment is centred and independent of `g`. -/
lemma integral_factor_increment_eq_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ∂P = 0 := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono (ℱ.le a)).measurable
  have h_indep_F := hℱ.indep ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤ ℱ a :=
    hg_meas.measurable.comap_le
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω)) = g * ΔW from rfl,
    h_indep_g_ΔW.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
      hΔW_meas.aestronglyMeasurable,
    brownian_incr_mean W ha hab, mul_zero]

/-- **Weighted off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`), `Fᵢ`-measurable coefficients, and
a bounded `F_{a₁}`-measurable weight `g`,
`∫ g · (ξ₁·ΔW₁)·(ξ₂·ΔW₂) = 0`. The weighted analogue of
`offDiagonal_increment_integral_zero`: `f := g·ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable
and `ΔW₂ ⟂ F_{a₂}` is centred, so `𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. With `g = 1_B`
(`B ∈ F_s`, `s ≤ a₁`) this gives the off-diagonal of the set-level Itô isometry. -/
lemma offDiagonal_increment_integral_zero_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  have hgmeas : Measurable g :=
    (hg.mono (ℱ.le a₁)).measurable
  set f : Ω → ℝ := fun ω => g ω * (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * ξ₂ ω with hf_def
  rw [show (fun ω => g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * ΔW₂ ω)))
        = fun ω => f ω * ΔW₂ ω from by funext ω; simp only [hf_def]; ring]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono
        (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_g_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) g :=
    hg.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_g_F_meas.mul (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas))).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hgmeas.mul (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁)))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v (h_f_comap_le u hu) hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := brownian_incr_mean W ha₂_nn h₂
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl,
    h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable, h_ΔW₂_mean, mul_zero]

/-- **Clamped-increment identity.** For `s ≤ t`,
`simpleIntegral W H t − simpleIntegral W H s = ∑ᵢ ξᵢ·(W_{cᵢ₊₁} − W_{cᵢ})` where
`cᵢ = max s (min pᵢ t)` clamps the partition points into `[s, t]`. The increment
of the simple integral between `s` and `t` rebuilds as a single sum of increments
over the `[s,t]`-clamped partition — the starting point for the conditional
(set-level) Itô isometry. -/
lemma simpleIntegral_sub_eq_clamp_sum
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    simpleIntegral W H t ω - simpleIntegral W H s ω
      = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
          - W.W (max s (min (H.partition i.castSucc) t)) ω) := by
  have key : ∀ p : ℝ,
      W.W (min p t) ω - W.W (min p s) ω = W.W (max s (min p t)) ω - W.W s ω := by
    intro p
    rcases le_or_gt s p with hsp | hps
    · rw [min_eq_right hsp, max_eq_right (le_min hsp hst)]
    · rw [min_eq_left (le_of_lt hps), min_eq_left (le_of_lt (lt_of_lt_of_le hps hst)),
        max_eq_left (le_of_lt hps), sub_self, sub_self]
  unfold simpleIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 := key (H.partition i.succ)
  have e2 := key (H.partition i.castSucc)
  rw [← mul_sub]
  congr 1
  rw [show W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω
        - (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω)
      = (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.succ) s) ω)
        - (W.W (min (H.partition i.castSucc) t) ω
            - W.W (min (H.partition i.castSucc) s) ω) from by ring]
  rw [e1, e2]; ring

/-- **Weighted clamped Bochner increment second moment.** For adapted simple `H`,
`0 ≤ s ≤ t`, and a bounded `F_s`-measurable weight `g`,
`∫ g·(I_t − I_s)² = ∑ᵢ (cᵢ₊₁ − cᵢ)·∫ g·ξᵢ²` with `cᵢ = max s (min pᵢ t)`.
The set-level (`g = 1_B`, `B ∈ F_s`) conditional Itô isometry at simple level:
the increment squares onto the `[s,t]`-clamped partition, off-diagonal terms vanish
(`offDiagonal_increment_integral_zero_weighted`), and the diagonal gives the
clamped lengths weighted by `g` (`integral_factor_increment_sq`). -/
lemma simpleIntegral_sub_sq_bochner_clamped_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
          * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P := by
  have hgmeas : Measurable g := (hg.mono (ℱ.le s)).measurable
  have h_cl_nn : ∀ p : ℝ, 0 ≤ max s (min p t) := fun p => le_trans hs (le_max_left _ _)
  have h_cl_mono : ∀ {a b : ℝ}, a ≤ b → max s (min a t) ≤ max s (min b t) :=
    fun hab => max_le_max (le_refl s) (min_le_min hab (le_refl t))
  have h_a_le_b : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) ≤ max s (min (H.partition i.succ) t) :=
    fun i => h_cl_mono (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  -- In the genuine (non-degenerate) case the lower clamp dominates the partition pt.
  have h_padapt : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        H.partition i.castSucc ≤ max s (min (H.partition i.castSucc) t) := by
    intro i hlt
    by_cases hpt : H.partition i.castSucc ≤ t
    · rw [min_eq_left hpt]; exact le_max_right _ _
    · push Not at hpt
      exfalso
      have h1 : min (H.partition i.castSucc) t = t := min_eq_right (le_of_lt hpt)
      have h2 : min (H.partition i.succ) t = t :=
        min_eq_right (le_of_lt (lt_trans hpt (H.partition_strictMono Fin.castSucc_lt_succ)))
      rw [h1, h2] at hlt; exact lt_irrefl _ hlt
  -- ξ adaptedness lifted to the clamped left endpoint (genuine case).
  have h_ξ_cl : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (H.ξ i) :=
    fun i hlt => (h_adapt i).mono (ℱ.mono (h_padapt i hlt))
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
      - W.W (max s (min (H.partition i.castSucc) t)) ω) with hterm
  -- integrability of every weighted cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => g ω * (term i ω * term j ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    refine MeasureTheory.Integrable.bdd_mul (c := Cg)
      (cross_increment_integrable W (h_cl_nn _) (h_a_le_b i) (h_cl_nn _) (h_a_le_b j)
        (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj)
      hgmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (Real.norm_eq_abs (g ω)).le.trans (hg_bdd ω)))
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, g ω * (term i ω * term j ω) ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · have hbi_le_aj : max s (min (H.partition i.succ) t)
            ≤ max s (min (H.partition j.castSucc) t) :=
          h_cl_mono (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij))
        exact offDiagonal_increment_integral_zero_weighted W ℱ hℱ (h_cl_nn _) hi_lt hbi_le_aj hj_lt
          (H.ξ i) (H.ξ j) g (h_ξ_cl i hi_lt) (h_ξ_cl j hj_lt)
          (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t))))
  rw [show (fun ω => g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, g ω * (term i ω * term j ω) from by
    funext ω
    rw [simpleIntegral_sub_eq_clamp_sum W H hst ω,
      show (∑ i : Fin H.N, term i ω) ^ 2
          = ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
        rw [sq, Finset.sum_mul_sum], Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => g ω * (term i ω * term i ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq, sub_self, zero_mul]
    · have hg2 : @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (fun ω => g ω * (H.ξ i ω) ^ 2) := by
        refine (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t)))).mul ?_
        simpa [pow_two, Pi.mul_def] using (h_ξ_cl i hi_lt).mul (h_ξ_cl i hi_lt)
      have hdiag := integral_factor_increment_sq W ℱ hℱ (h_cl_nn _) hi_lt hg2
      rw [show (fun ω => g ω * (term i ω * term i ω))
            = fun ω => (g ω * (H.ξ i ω) ^ 2)
                * (W.W (max s (min (H.partition i.succ) t)) ω
                    - W.W (max s (min (H.partition i.castSucc) t)) ω) ^ 2 from by
          funext ω; simp only [hterm]; ring, hdiag, mul_comm]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => g ω * (term i ω * term j ω))
            = fun ω => g ω * (term j ω * term i ω) from by funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Real clamped compensator integral.** For `0 ≤ t`,
`∫_{[0,t]} (G.eval u ω)² du = ∑ᵢ (min pᵢ₊₁ t − min pᵢ t)·ξᵢ²`. The real-Bochner
companion of `lintegral_eval_sq_clamped`, obtained from it by
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.toReal`. The simple-level
quadratic-variation compensator `A_t = ∫_{[0,t]} (eval)²` in closed sum form. -/
lemma setIntegral_eval_sq_Icc_clamped {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by
  have h_len_nn : ∀ i : Fin G.N,
      0 ≤ min (G.partition i.succ) t - min (G.partition i.castSucc) t :=
    fun i => sub_nonneg.mpr (min_le_min_right t
      (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))
  have h_eval_meas : Measurable (fun u => G.eval u ω) :=
    G.eval_jointly_measurable.comp
      (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
        (h_eval_meas.pow_const 2).aestronglyMeasurable]
  rw [show (fun u => ENNReal.ofReal ((G.eval u ω) ^ 2))
        = fun u => (‖G.eval u ω‖₊ : ℝ≥0∞) ^ 2 from funext (fun u => (h_norm_sq _).symm),
    lintegral_eval_sq_clamped G ω,
    show (fun i : Fin G.N => ENNReal.ofReal (min (G.partition i.succ) t
          - min (G.partition i.castSucc) t) * (‖G.ξ i ω‖₊ : ℝ≥0∞) ^ 2)
        = fun i => ENNReal.ofReal ((min (G.partition i.succ) t
            - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2) from
      funext (fun i => by rw [h_norm_sq, ← ENNReal.ofReal_mul (h_len_nn i)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)),
    ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)))]

/-- **Simple-level quadratic-variation martingale.** For a simple integrand `G`
(horizon `T > 0`) adapted to a filtration `ℱ` for which `W` is a Brownian
motion, the compensated square
`t ↦ (∫₀ᵗ G dW)² − ∫₀ᵗ G² ds` is a martingale wrt `ℱ`. The
conditional increment `𝔼[(I_t − I_s)² | ℱ_s]` equals `𝔼[A_t − A_s | ℱ_s]` by the
set-level Itô isometry (`simpleIntegral_sub_sq_bochner_clamped_weighted` with
`g = 1_B`), matched against the clamped compensator
(`setIntegral_eval_sq_Icc_clamped`); the conditional Pythagoras
(`condExp_sq_increment_of_martingale`) then gives the martingale identity for
`0 ≤ s ≤ t`, and the `s < 0` case follows by the tower property. -/
lemma martingale_simpleIntegral_sq_sub_compensator
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral W G t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
      ℱ P := by
  have hImart : MeasureTheory.Martingale (fun u => simpleIntegral W G u) ℱ P :=
    martingale_simpleIntegral_brownian W ℱ hℱ G h_adapt
  -- `I_u ∈ L²(P)` at every time.
  have hIL2 : ∀ u, MeasureTheory.MemLp (fun ω => simpleIntegral W G u ω) 2 P := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have heq : (fun ω => simpleIntegral W G u ω) = fun _ => (0 : ℝ) :=
        funext (fun ω => simpleIntegral_eq_zero_of_nonpos W G hu ω)
      rw [heq]; exact MeasureTheory.memLp_const 0
    · rcases le_or_gt u T with huT | huT
      · exact simpleIntegral_memLp_intermediate_brownian W ℱ hℱ hT G h_adapt (le_of_lt hu) huT
      · have heq : (fun ω => simpleIntegral W G u ω) = (fun ω => simpleIntegral W G T ω) := by
          funext ω; unfold simpleIntegral
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hps : G.partition i.succ ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          have hpc : G.partition i.castSucc ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          rw [min_eq_left (le_trans hps (le_of_lt huT)),
            min_eq_left (le_trans hpc (le_of_lt huT)), min_eq_left hps, min_eq_left hpc]
        rw [heq]
        exact simpleIntegral_memLp_intermediate_brownian W ℱ hℱ hT G h_adapt (le_of_lt hT)
          (le_refl T)
  -- `ξᵢ²` integrable.
  have hξ2int : ∀ i : Fin G.N, MeasureTheory.Integrable (fun ω => (G.ξ i ω) ^ 2) P := fun i => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (M ^ 2))
      ((G.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  -- The compensator `A_u = ∫₀ᵘ G²` is integrable …
  have hAint : ∀ u, MeasureTheory.Integrable
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) P := by
    intro u
    rcases le_or_gt 0 u with _ | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => setIntegral_eval_sq_Icc_clamped G ω)
      rw [heq]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hξ2int i).const_mul _)
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  -- … and `ℱ_u`-adapted.
  have hA_adapt : ∀ u, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) := by
    intro u
    rcases le_or_gt 0 u with _ | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => setIntegral_eval_sq_Icc_clamped G ω)
      rw [heq]
      refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
      by_cases hc : G.partition i.castSucc < u
      · have hle : ℱ.seq (G.partition i.castSucc) ≤ ℱ.seq u := ℱ.mono (le_of_lt hc)
        have hξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u) (fun ω => (G.ξ i ω) ^ 2) := by
          simpa [pow_two, Pi.mul_def] using ((h_adapt i).mono hle).mul ((h_adapt i).mono hle)
        exact hξ2.const_mul _
      · push Not at hc
        have hcoef : min (G.partition i.succ) u - min (G.partition i.castSucc) u = 0 := by
          rw [min_eq_right hc, min_eq_right
            (le_trans hc (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))]; ring
        rw [show (fun ω => (min (G.partition i.succ) u - min (G.partition i.castSucc) u)
              * (G.ξ i ω) ^ 2) = fun _ => (0 : ℝ) from by funext ω; rw [hcoef, zero_mul]]
        exact stronglyMeasurable_const
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact stronglyMeasurable_const
  -- the per-point clamp identity `(Δᵗ − Δˢ) = max s (min p t) − …`.
  have hclamp : ∀ (s t : ℝ), s ≤ t → ∀ p : ℝ,
      max s (min p t) = s + min p t - min p s := by
    intro s t hst p
    have h1 : min s (min p t) = min p s := by
      rw [min_comm s (min p t), min_assoc, min_eq_right hst]
    have h2 := max_add_min s (min p t)
    rw [h1] at h2; linarith
  -- conditional martingale identity for `0 ≤ s ≤ t`, via set integrals.
  have hcond : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P[(fun ω => (simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
        =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
    intro s t hs hst
    have hm : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    have hIt2 : MeasureTheory.Integrable (fun ω => (simpleIntegral W G t ω) ^ 2) P :=
      (hIL2 t).integrable_sq
    have hIs2 : MeasureTheory.Integrable (fun ω => (simpleIntegral W G s ω) ^ 2) P :=
      (hIL2 s).integrable_sq
    have hIinc_int : MeasureTheory.Integrable
        (fun ω => (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2) P := by
      simpa [pow_two] using ((hIL2 t).sub (hIL2 s)).integrable_sq
    have hNs_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        (fun ω => (simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) := by
      have hIs2m : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
          (fun ω => (simpleIntegral W G s ω) ^ 2) := by
        simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted s).mul (hImart.stronglyAdapted s)
      exact hIs2m.sub (hA_adapt s)
    refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm (hIt2.sub (hAint t))
      (fun B _ _ => (hIs2.sub (hAint s)).integrableOn) (fun B hB _ => ?_)
      hNs_meas.aestronglyMeasurable).symm
    -- goal: `∫_B N_s = ∫_B N_t`. Split both via term-mode `integral_sub`.
    simp only [Pi.sub_apply]
    have hsplitN_s : ∫ ω in B, ((simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIs2.integrableOn (hAint s).integrableOn
    have hsplitN_t : ∫ ω in B, ((simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIt2.integrableOn (hAint t).integrableOn
    have hsplitA : ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub (hAint t).integrableOn (hAint s).integrableOn
    -- set Pythagoras: `∫_B (I_t−I_s)² = ∫_B I_t² − ∫_B I_s²`.
    have hsetpyth : ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
        = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P := by
      have hpyth := condExp_sq_increment_of_martingale hImart (hIL2 s) (hIL2 t) hst
      calc ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
          = ∫ ω in B, (P[(fun ω => (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2)
              | ℱ.seq s]) ω ∂P := (MeasureTheory.setIntegral_condExp hm hIinc_int hB).symm
        _ = ∫ ω in B, ((P[(fun ω => (simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω
              - (simpleIntegral W G s ω) ^ 2) ∂P :=
            MeasureTheory.setIntegral_congr_ae (hm B hB) (hpyth.mono (fun ω hω _ => hω))
        _ = (∫ ω in B, (P[(fun ω => (simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω ∂P)
              - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P :=
            MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn
              hIs2.integrableOn
        _ = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
              - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P := by
            rw [MeasureTheory.setIntegral_condExp hm hIt2 hB]
    -- set isometry: `∫_B (I_t−I_s)² = ∫_B (A_t − A_s)`.
    have hgmeas : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
      (measurable_const).indicator (hm B hB)
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
    have hiso_set : ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
        = ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P := by
      rw [hind, simpleIntegral_sub_sq_bochner_clamped_weighted W ℱ hℱ G h_adapt hs hst
        (stronglyMeasurable_const.indicator hB) hg_bdd]
      have hAdiff : ∀ ω, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume
          = ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
              - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2 := by
        intro ω
        rw [setIntegral_eval_sq_Icc_clamped G ω,
          setIntegral_eval_sq_Icc_clamped G ω, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← sub_mul]; congr 1
        rw [hclamp s t hst (G.partition i.succ), hclamp s t hst (G.partition i.castSucc)]; ring
      rw [MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => hAdiff ω), hind,
        show (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω
              * ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2)
            = fun ω => ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t))
                  * (Set.indicator B (fun _ => (1 : ℝ)) ω * (G.ξ i ω) ^ 2) from by
          funext ω; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
        (((hξ2int i).bdd_mul (c := 1) hgmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall
            (fun ω => (Real.norm_eq_abs _).le.trans (hg_bdd ω)))).const_mul _))]
      exact Finset.sum_congr rfl (fun i _ => by rw [MeasureTheory.integral_const_mul])
    -- combine: `∫_B N_s = ∫_B N_t`.
    rw [hsetpyth] at hiso_set
    linarith [hiso_set, hsplitN_s, hsplitN_t, hsplitA]
  -- assemble the full martingale (handle `s < 0` by the tower property).
  refine ⟨?_, fun s t hst => ?_⟩
  · intro u
    have hI2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
        (fun ω => (simpleIntegral W G u ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted u).mul (hImart.stronglyAdapted u)
    exact hI2.sub (hA_adapt u)
  · rcases le_or_gt 0 s with hs | hs
    · exact hcond s t hs hst
    · have hN0 : (fun ω => (simpleIntegral W G 0 ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
        filter_upwards with ω
        rw [simpleIntegral_eq_zero_of_nonpos W G (le_refl 0) ω,
          setIntegral_eval_sq_Icc_clamped G ω]
        have : ∀ i : Fin G.N, (min (G.partition i.succ) (0 : ℝ)
            - min (G.partition i.castSucc) (0 : ℝ)) * (G.ξ i ω) ^ 2 = 0 := by
          intro i
          have hp1 : (0 : ℝ) ≤ G.partition i.succ := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.succ)
            rwa [G.partition_zero] at this
          have hp2 : (0 : ℝ) ≤ G.partition i.castSucc := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.castSucc)
            rwa [G.partition_zero] at this
          rw [min_eq_right hp1, min_eq_right hp2, sub_self, zero_mul]
        rw [Finset.sum_eq_zero (fun i _ => this i)]; simp
      have hle0 : ℱ.seq s ≤ ℱ.seq 0 := ℱ.mono (le_of_lt hs)
      rcases le_or_gt 0 t with ht | ht
      · have h0 := hcond 0 t (le_refl 0) ht
        calc P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq 0] | ℱ.seq s] :=
              (MeasureTheory.condExp_condExp_of_le hle0 (ℱ.le 0)).symm
          _ =ᵐ[P] P[(fun ω => (simpleIntegral W G 0 ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s] :=
              MeasureTheory.condExp_congr_ae h0
          _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hN0
          _ =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]
              simp
      · -- `t < 0`: both sides are a.e. `0`.
        have hNt : (fun ω => (simpleIntegral W G t ω) ^ 2
            - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
          filter_upwards with ω
          rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt ht) ω,
            Set.Icc_eq_empty (not_le.mpr ht)]; simp
        calc P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hNt
          _ =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]; simp

end LevyStochCalc.Brownian.Ito
