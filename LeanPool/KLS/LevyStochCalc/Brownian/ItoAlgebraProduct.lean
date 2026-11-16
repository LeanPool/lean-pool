/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- At most one cell of a strictly monotone partition contains a given time, so a product of
two step sums over that partition is the step sum of the pointwise product. -/
theorem sum_ite_mul_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f g : Fin M → ℝ) (s : ℝ) :
    (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      * (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j * g j else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => ite_eq_right fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact ite_eq_left hj₀
    rw [hsum f, hsum g, hsum fun j => f j * g j]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => ite_eq_right fun hc => absurd hc.2 (not_le.mpr
        (h j hc.1))
    rw [hz f, hz g, hz fun j => f j * g j, mul_zero]


/-- The product of two simple integrands, carried on their common refinement. -/
noncomputable def SimplePredictable.mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := H₁.mergedπ_zero H₂
  partition_le_T := (H₁.mergedπ_last H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    refine ⟨max C₁ 0 * max C₂ 0, fun ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC₁ ω).trans (le_max_left _ _)) ((hC₂ ω).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).mul (H₂.ξ_measurable _)

/-- The product on the common refinement evaluates to the product of the evaluations. -/
theorem SimplePredictable.eval_mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by
  have hl := H₁.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq) (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω
  have hr := H₂.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (h_eq ▸ H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq) (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω
  rw [SimplePredictable.eval] at hl hr ⊢
  change (∑ j : Fin (H₁.mergedM H₂),
      if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
    = H₁.eval s ω * H₂.eval s ω
  rw [← hl, ← hr]
  exact (sum_ite_mul_sum_ite (H₁.mergedπ_strictMono H₂) _ _ s).symm


private lemma min_min_of_le {a b t : ℝ} (h : a ≤ b) : min a (min b t) = min a t := by
  rw [← min_assoc, min_eq_left h]

private lemma min_min_of_le' {a b t : ℝ} (h : a ≤ b) : min b (min a t) = min a t := by
  rw [← min_assoc, min_eq_right h]

/-- **The elementary integral against an elementary integral.** Summing the increments of
`simpleIntegral W K` against the coefficients of `G` gives the elementary integral of the
product `G · K` on the common refinement. -/
theorem SimplePredictable.sum_xi_mul_simpleIntegral_sub
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (simpleIntegral W K (min (G.partition i.succ) t) ω
          - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = simpleIntegral W (G.mul_on_common K h_eq) t ω := by
  classical
  set π : Fin (G.mergedM K + 1) → ℝ := G.mergedπ K with hπ
  set L : Fin (G.mergedM K) → Fin G.N := G.mergedIdxMap_left K h_eq with hL
  set R : Fin (G.mergedM K) → Fin K.N := G.mergedIdxMap_right K h_eq with hR
  have hmono : StrictMono π := G.mergedπ_strictMono K
  have hLle : ∀ j, G.partition (L j).castSucc ≤ π j.castSucc :=
    G.mergedIdxMap_left_idx_le K h_eq
  have hLge : ∀ j, π j.succ ≤ G.partition (L j).succ := G.mergedIdxMap_left_idx_ge K h_eq
  -- `K`'s elementary integral, read on the merged partition
  have hK : ∀ u : ℝ, simpleIntegral W K u ω
      = ∑ j : Fin (G.mergedM K), K.ξ (R j) ω
        * (W.W (min (π j.succ) u) ω - W.W (min (π j.castSucc) u) ω) := by
    intro u
    rw [← K.simpleIntegral_refine_intermediate W (G.mergedM K) π (G.mergedπ_zero K)
      (h_eq ▸ G.mergedπ_last K h_eq) hmono R (G.mergedIdxMap_right_idx_le K h_eq)
      (G.mergedIdxMap_right_idx_ge K h_eq) (G.mergedπ_refines_right K) u ω]
    rfl
  set ΔW : Fin (G.mergedM K) → ℝ := fun j =>
    W.W (min (π j.succ) t) ω - W.W (min (π j.castSucc) t) ω with hΔW
  set D : Fin G.N → Fin (G.mergedM K) → ℝ := fun i j =>
    (W.W (min (π j.succ) (min (G.partition i.succ) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.succ) t)) ω)
      - (W.W (min (π j.succ) (min (G.partition i.castSucc) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.castSucc) t)) ω) with hD
  have hDself : ∀ j, D (L j) j = ΔW j := by
    intro j
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have h2 : G.partition (L j).castSucc ≤ π j.castSucc := hLle j
    rw [hD, hΔW]
    simp only
    rw [min_min_of_le (hLge j), min_min_of_le (h1.trans (hLge j)),
      min_min_of_le' (h2.trans h1), min_min_of_le' h2]
    ring
  have hDzero : ∀ (j : Fin (G.mergedM K)) (i : Fin G.N), i ≠ L j → D i j = 0 := by
    intro j i hne
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have hGi : G.partition i.castSucc ≤ G.partition i.succ :=
      G.partition_strictMono.monotone Fin.castSucc_lt_succ.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.succ : Fin (G.N + 1)) ≤ (L j).castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
      have hstep : G.partition i.succ ≤ π j.castSucc :=
        (G.partition_strictMono.monotone hle).trans (hLle j)
      rw [hD]
      simp only
      rw [min_min_of_le' hstep, min_min_of_le' (hstep.trans h1),
        min_min_of_le' (hGi.trans hstep), min_min_of_le' ((hGi.trans hstep).trans h1)]
      ring
    · have hle : ((L j).succ : Fin (G.N + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
      have hstep : π j.succ ≤ G.partition i.castSucc :=
        (hLge j).trans (G.partition_strictMono.monotone hle)
      rw [hD]
      simp only
      rw [min_min_of_le (hstep.trans hGi), min_min_of_le (h1.trans (hstep.trans hGi)),
        min_min_of_le hstep, min_min_of_le (h1.trans hstep)]
      ring
  calc (∑ i : Fin G.N, G.ξ i ω *
          (simpleIntegral W K (min (G.partition i.succ) t) ω
            - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = ∑ i : Fin G.N, ∑ j : Fin (G.mergedM K), G.ξ i ω * (K.ξ (R j) ω * D i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK, hK, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD]; ring
    _ = ∑ j : Fin (G.mergedM K), ∑ i : Fin G.N, G.ξ i ω * (K.ξ (R j) ω * D i j) :=
        Finset.sum_comm
    _ = ∑ j : Fin (G.mergedM K), G.ξ (L j) ω * K.ξ (R j) ω * ΔW j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (L j)
          (fun i _ hne => by rw [hDzero j i hne, mul_zero, mul_zero])
          (fun hnm => absurd (Finset.mem_univ _) hnm), hDself j]
        ring
    _ = simpleIntegral W (G.mul_on_common K h_eq) t ω := by
        unfold simpleIntegral
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΔW]
        rfl


/-- Adaptedness passes to the product on the common refinement. -/
theorem SimplePredictable.mul_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.mul_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.mul_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.mul_on_common H₂ h_eq).ξ j) := by
  intro j
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_left_idx_le H₂ h_eq j))
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_right_idx_le H₂ h_eq j))
  exact h₁.mul h₂

/-- The elementary integral of a simple integrand against an arbitrary process. -/
noncomputable def SimplePredictable.integralAgainst {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin G.N, G.ξ i ω *
    (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)

/-- The zero-extension leaves the elementary integral against a process unchanged. -/
theorem SimplePredictable.appendInterval_integralAgainst
    {T : ℝ} (G : SimplePredictable Ω T) {T' : ℝ}
    (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω := by
  unfold SimplePredictable.integralAgainst
  rw [G.appendInterval_partition_eq hlt, G.appendInterval_xi_eq hlt]
  change (∑ i : Fin (G.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) G.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.succ) t) ω
            - M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.castSucc) t) ω))
    = ∑ i : Fin G.N, G.ξ i ω
        * (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Fin.castSucc i).succ = Fin.castSucc i.succ from Fin.ext rfl]
  simp only [Fin.snoc_castSucc]

section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **Difference isometry between an elementary integral and an `L²` integral.** -/
theorem isometry_simple_sub_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖simpleIntegral W G T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) H
    G.measurable_uncurry_eval hm (G.progressivelyMeasurable_eval ℱ h_adapt) hp
    (G.lintegral_eval_sq_lt_top P) hq hT
  rw [← hiso]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegralBrownian_eval_simple W ℱ hℱ G h_adapt
    G.measurable_uncurry_eval (G.progressivelyMeasurable_eval ℱ h_adapt)
    (G.lintegral_eval_sq_lt_top P) hT.le] with ω hω
  rw [hω]

end SimpleVsGeneral

/-- **The product of two simple integrands as a simple integrand.** For adapted `G` and `K` with
arbitrary horizons there is an adapted simple integrand `Q` whose evaluation is the product of
the evaluations and whose elementary integral is the elementary integral of `G` against the
elementary integral of `K`. -/
theorem SimplePredictable.exists_mul_simple
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
          = simpleIntegral W Q t ω) := by
  have hG : G.partition (Fin.last G.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_left (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have hK : K.partition (Fin.last K.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_right (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have h_eq : (G.appendInterval hG).partition (Fin.last (G.appendInterval hG).N)
      = (K.appendInterval hK).partition (Fin.last (K.appendInterval hK).N) :=
    (G.appendInterval_partition_last hG).trans (K.appendInterval_partition_last hK).symm
  refine ⟨_, (G.appendInterval hG).mul_on_common (K.appendInterval hK) h_eq, ?_, ?_, ?_⟩
  · exact SimplePredictable.mul_on_common_adapt ℱ _ _ h_eq
      (G.appendInterval_adapt ℱ hG h_adaptG) (K.appendInterval_adapt ℱ hK h_adaptK)
  · intro s ω
    rw [SimplePredictable.eval_mul_on_common, G.appendInterval_eval hG,
      K.appendInterval_eval hK]
  · intro t ω
    rw [← SimplePredictable.sum_xi_mul_simpleIntegral_sub W (G.appendInterval hG)
      (K.appendInterval hK) h_eq t ω]
    have hKfun : (fun u (ω' : Ω) => simpleIntegral W K u ω')
        = fun u ω' => simpleIntegral W (K.appendInterval hK) u ω' := by
      funext u ω'; exact (K.appendInterval_simpleIntegral W hK u ω').symm
    rw [hKfun, ← G.appendInterval_integralAgainst hG
      (fun u ω' => simpleIntegral W (K.appendInterval hK) u ω') t ω]
    rfl

end LevyStochCalc.Brownian.Ito
