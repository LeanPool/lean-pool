/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Gaps

/-!
# The pointwise covering bound

`covering_pointwise`, its cleaned-up form with every `ω`-dependent index removed, and
`covering_bound`: the estimate `C ≤ q + 4ε(1 + |q|)`, then `ε → 0`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-- **Integrating a pointwise bound with eight terms.** Packaging the bookkeeping keeps the
covering argument's final estimate readable: supply integrability of each summand and a bound on
each summand's integral. -/
theorem integral_le_of_le_sum_eight {μ : Measure Ω} {F g1 g2 g3 g4 g5 g6 g7 g8 : Ω → ℝ}
    (hF : Integrable F μ)
    (h1 : Integrable g1 μ) (h2 : Integrable g2 μ) (h3 : Integrable g3 μ)
    (h4 : Integrable g4 μ) (h5 : Integrable g5 μ) (h6 : Integrable g6 μ)
    (h7 : Integrable g7 μ) (h8 : Integrable g8 μ)
    (hpt : ∀ᵐ ω ∂μ, F ω ≤ g1 ω + g2 ω + g3 ω + g4 ω + g5 ω + g6 ω + g7 ω + g8 ω)
    {c1 c2 c3 c4 c5 c6 c7 c8 : ℝ}
    (b1 : ∫ ω, g1 ω ∂μ ≤ c1) (b2 : ∫ ω, g2 ω ∂μ ≤ c2) (b3 : ∫ ω, g3 ω ∂μ ≤ c3)
    (b4 : ∫ ω, g4 ω ∂μ ≤ c4) (b5 : ∫ ω, g5 ω ∂μ ≤ c5) (b6 : ∫ ω, g6 ω ∂μ ≤ c6)
    (b7 : ∫ ω, g7 ω ∂μ ≤ c7) (b8 : ∫ ω, g8 ω ∂μ ≤ c8) :
    ∫ ω, F ω ∂μ ≤ c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 := by
  have H2 : Integrable (fun ω => g1 ω + g2 ω) μ := h1.add h2
  have H3 : Integrable (fun ω => g1 ω + g2 ω + g3 ω) μ := H2.add h3
  have H4 : Integrable (fun ω => g1 ω + g2 ω + g3 ω + g4 ω) μ := H3.add h4
  have H5 : Integrable (fun ω => g1 ω + g2 ω + g3 ω + g4 ω + g5 ω) μ := H4.add h5
  have H6 : Integrable (fun ω => g1 ω + g2 ω + g3 ω + g4 ω + g5 ω + g6 ω) μ := H5.add h6
  have H7 : Integrable (fun ω => g1 ω + g2 ω + g3 ω + g4 ω + g5 ω + g6 ω + g7 ω) μ := H6.add h7
  have H8 : Integrable
      (fun ω => g1 ω + g2 ω + g3 ω + g4 ω + g5 ω + g6 ω + g7 ω + g8 ω) μ := H7.add h8
  have hmono := integral_mono_ae hF H8 hpt
  rw [integral_add H7 h8, integral_add H6 h7, integral_add H5 h6, integral_add H4 h5,
      integral_add H3 h4, integral_add H2 h3, integral_add h1 h2] at hmono
  linarith

/-- Null trimming makes the good-window properties hold at every retained center. -/
private theorem exists_good_windows_everywhere [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (σ : Ω → Ω) μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily (σ : Ω → Ω) f) (q ε₁ : ℝ) (hε₁0 : 0 < ε₁) (N₀ : ℕ)
    (hinf : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ j : ℕ, k ≤ j ∧ 1 ≤ j ∧
      f (2 * j) (zIter σ (-(j : ℤ)) ω) < 2 * j * q) :
    ∃ (A : Set Ω) (jω : Ω → ℕ), MeasurableSet A ∧ Measurable jω ∧
      (A.PairwiseDisjoint fun x =>
        (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x)) ∧
      (∀ ω' ∈ A, 1 ≤ jω ω' ∧
        f (2 * jω ω') (zIter σ (-(jω ω' : ℤ)) ω') < 2 * (jω ω') * q) ∧
      (∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω') ∧
      (∀ ω' ∈ A, N₀ ≤ jω ω') ∧
      ENNReal.ofReal (1 - ε₁) <
        μ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) := by
  classical
  -- **The good windows.**
  obtain ⟨A₀, jω, hA₀m, hjm, hdisj₀, hcov₀, hae⟩ :=
    exists_good_windows μ σ hσ f hf.1 q ε₁ hε₁0 N₀ hinf
  -- **Shrink the centre set to where goodness and orbit injectivity really hold.**
  have hae2 : ∀ᵐ ω ∂μ, (ω ∈ A₀ → N₀ ≤ jω ω ∧ 1 ≤ jω ω ∧
      f (2 * jω ω) (zIter σ (-(jω ω : ℤ)) ω) < 2 * (jω ω) * q)
      ∧ Function.Injective fun i : ℤ => zIter σ i ω :=
    hae.and (ae_injective_zIter μ σ hσ)
  rw [ae_iff] at hae2
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null hae2
  set A : Set Ω := A₀ \ Z with hAdef
  have hAsub : A ⊆ A₀ := Set.sdiff_subset
  have hAm : MeasurableSet A := hA₀m.diff hZm
  have hprop : ∀ ω' ∈ A, (ω' ∈ A₀ → N₀ ≤ jω ω' ∧ 1 ≤ jω ω' ∧
      f (2 * jω ω') (zIter σ (-(jω ω' : ℤ)) ω') < 2 * (jω ω') * q)
      ∧ Function.Injective fun i : ℤ => zIter σ i ω' := by
    intro ω' hω'
    by_contra hc
    exact hω'.2 (hZsub hc)
  have hdisj : A.PairwiseDisjoint
      fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x) := hdisj₀.subset hAsub
  have hgood : ∀ ω' ∈ A, 1 ≤ jω ω' ∧
      f (2 * jω ω') (zIter σ (-(jω ω' : ℤ)) ω') < 2 * (jω ω') * q := by
    intro ω' hω'
    exact ((hprop ω' hω').1 hω'.1).2
  have hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω' :=
    fun ω' hω' => (hprop ω' hω').2
  have hpos : ∀ ω' ∈ A, 1 ≤ jω ω' := fun ω' h => (hgood ω' h).1
  have hrad : ∀ ω' ∈ A, N₀ ≤ jω ω' := fun ω' hω' => ((hprop ω' hω').1 hω'.1).1
  -- **Coverage survives the shrink**, because the discarded centres form a null set.
  have hnullwin : μ (⋃ ω' ∈ A₀ ∩ Z, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
      = 0 :=
    measure_iUnion_windows_of_null σ hσ (hA₀m.inter hZm)
      (measure_mono_null Set.inter_subset_right hZ0) jω
  have hcov : ENNReal.ofReal (1 - ε₁)
      < μ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) := by
    refine lt_of_lt_of_le hcov₀ ?_
    have hsub : (⋃ ω' ∈ A₀, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
        ⊆ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
          ∪ ⋃ ω' ∈ A₀ ∩ Z, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
      intro x hx
      obtain ⟨ω', hω', hxw⟩ := Set.mem_iUnion₂.mp hx
      by_cases hz : ω' ∈ Z
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨ω', ⟨hω', hz⟩, hxw⟩)
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨ω', ⟨hω', hz⟩, hxw⟩)
    calc μ (⋃ ω' ∈ A₀, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
        ≤ μ ((⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
            ∪ ⋃ ω' ∈ A₀ ∩ Z, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) :=
          measure_mono hsub
      _ ≤ μ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
            + μ (⋃ ω' ∈ A₀ ∩ Z, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) :=
          measure_union_le _ _
      _ = μ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) := by
          rw [hnullwin, add_zero]
  exact ⟨A, jω, hAm, hjm, hdisj, hgood, hinj, hrad, hcov⟩

/-- Forward and backward hitting-time tails control the exceptional end segments uniformly. -/
private theorem exists_small_badSet_cutoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (σ : Ω → Ω) μ) (A : Set Ω) (jω : Ω → ℕ)
    (hΛmm : MeasurableSet (leftEnd σ jω '' A))
    (hΛpm : MeasurableSet (rightEnd σ jω '' A)) (hA0 : μ A ≠ 0)
    (hdisj : A.PairwiseDisjoint fun x =>
      (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (ε₁ : ℝ) (hε₁0 : 0 < ε₁) :
    ∃ M n₀ : ℕ,
      (∀ᵐ ω ∂μ, ∀ m : ℕ,
        ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ rightEnd σ jω '' A) ∧
      (∀ᵐ ω ∂μ, ∀ m : ℕ,
        ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ leftEnd σ jω '' A) ∧
      (∀ n : ℕ, MeasurableSet (badSet σ jω A M n)) ∧
      ∀ n : ℕ, n₀ ≤ n → μ (badSet σ jω A M n) ≤ ENNReal.ofReal (3 * (ε₁ / 4)) := by
  classical
  have hmp := hσ.toMeasurePreserving
  -- **The endpoint sets are non-null**, so the hitting times are almost surely finite.
  have hΛm0 : μ (leftEnd σ jω '' A) ≠ 0 :=
    measure_ne_zero_of_endpoints σ hσ hΛmm (leftEnd σ jω) (fun ω' => (jω ω' : ℤ))
      (fun ω' hω' => ⟨⟨ω', hω', rfl⟩, by
        rw [leftEnd, ← zIter_add, show (jω ω' : ℤ) + -(jω ω' : ℤ) = 0 from by ring]
        simp [zIter_zero_apply]⟩) hA0
  have hΛp0 : μ (rightEnd σ jω '' A) ≠ 0 :=
    measure_ne_zero_of_endpoints σ hσ hΛpm (rightEnd σ jω) (fun ω' => -(jω ω' : ℤ))
      (fun ω' hω' => ⟨⟨ω', hω', rfl⟩, by
        rw [rightEnd, ← zIter_add, show -(jω ω' : ℤ) + (jω ω' : ℤ) = 0 from by ring]
        simp [zIter_zero_apply]⟩) hA0
  have hrecpAE : ∀ᵐ ω ∂μ, ∀ m : ℕ,
      ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ rightEnd σ jω '' A :=
    ae_forall_exists_mem_iterate hσ hΛpm hΛp0
  have hrecmAE : ∀ᵐ ω ∂μ, ∀ m : ℕ,
      ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ leftEnd σ jω '' A :=
    ae_forall_exists_mem_iterate hσ hΛmm hΛm0
    -- **A measurable conull set carrying the recurrence**, so that `badSet` can be bounded.
  have hrecpAE' := hrecpAE
  rw [ae_iff] at hrecpAE'
  obtain ⟨Zr, hZrsub, hZrm, hZr0⟩ := exists_measurable_superset_of_null hrecpAE'
  -- **The cutoffs.**
  have hquarter : (0 : ℝ≥0∞) < ENNReal.ofReal (ε₁ / 4) := by
    rw [ENNReal.ofReal_pos]; linarith
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_measure_hitTime_ge μ σ.measurable hΛmm).eventually (gt_mem_nhds hquarter))
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    ((tendsto_measure_hitTime_ge μ σ.symm.measurable hΛpm).eventually (gt_mem_nhds hquarter))
  set M : ℕ := max (max M₁ M₂) 1 with hMdef
  have hMbound1 : μ {ω | M ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ω}
      < ENNReal.ofReal (ε₁ / 4) := hM₁ M (le_trans (le_max_left _ _) (le_max_left _ _))
  have hMbound2 : μ {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω}
      < ENNReal.ofReal (ε₁ / 4) := hM₂ M (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_measure_blockCount_eq_zero μ σ.measurable hΛmm hΛpm).eventually
      (gt_mem_nhds hquarter))
  have hbadm : ∀ n : ℕ, MeasurableSet (badSet σ jω A M n) :=
    fun n => measurableSet_badSet hΛmm hΛpm M n
  -- **The exceptional set is small, uniformly in `n`.**
  have hbadμ : ∀ n : ℕ, n₀ ≤ n → μ (badSet σ jω A M n) ≤ ENNReal.ofReal (3 * (ε₁ / 4)) := by
    intro n hn
    have hH2m : MeasurableSet {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω} :=
      measurableSet_le measurable_const (measurable_hitTime σ.symm.measurable hΛpm)
    have hsub : badSet σ jω A M n
        ⊆ {ω | M ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ω}
          ∪ ({ω | blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω = 0}
             ∪ (((σ : Ω → Ω)^[n]) ⁻¹'
                 {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω} ∪ Zr)) := by
      rintro ω (h1 | h2)
      · have h1' : M ≤ firstGap σ jω A n ω := h1
        refine Or.inl ?_
        change M ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ω
        refine le_trans h1' ?_
        rw [firstGap, aWalk_zero, rMinus]
        exact min_le_left _ _
      · refine Or.inr ?_
        by_cases hz : ω ∈ Zr
        · exact Or.inr (Or.inr hz)
        by_cases hbc : blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω = 0
        · exact Or.inl hbc
        refine Or.inr (Or.inl ?_)
        obtain ⟨t, ht⟩ : ∃ t, blockCount (σ : Ω → Ω) (leftEnd σ jω '' A)
            (rightEnd σ jω '' A) n ω = t + 1 :=
          ⟨blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω - 1, by omega⟩
        have hrec : ∀ m : ℕ,
            ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ rightEnd σ jω '' A := by
          by_contra hc
          exact hz (hZrsub hc)
        have hbn' : bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω ≤ n := by
          rw [← ht]; exact bWalk_blockCount_le _ _ _ _ _
        have hover : n < bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
            (t + 1 + 1) ω := by
          rw [show t + 1 + 1 = blockCount (σ : Ω → Ω) (leftEnd σ jω '' A)
            (rightEnd σ jω '' A) n ω + 1 from by omega]
          exact lt_bWalk_succ_blockCount _ _ _ _ _
        have hle := sub_bWalk_le_hitBack hdisj hpos hinj hrec hbn' hover
        have hlast : lastBlock σ jω A n ω
            = bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω := by
          rw [lastBlock, ht]
        have h2' : lastBlock σ jω A n ω + M ≤ n := h2
        change M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ((σ : Ω → Ω)^[n] ω)
        rw [hlast] at h2'
        omega
    have hpre : μ (((σ : Ω → Ω)^[n]) ⁻¹'
        {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω})
        = μ {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω} :=
      (hmp.iterate n).measure_preimage hH2m.nullMeasurableSet
    have hsum3 : ENNReal.ofReal (ε₁ / 4)
        + (ENNReal.ofReal (ε₁ / 4) + (ENNReal.ofReal (ε₁ / 4) + 0))
        = ENNReal.ofReal (3 * (ε₁ / 4)) := by
      rw [add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring
    have hchain : μ ({ω | M ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ω}
          ∪ ({ω | blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω = 0}
             ∪ (((σ : Ω → Ω)^[n]) ⁻¹'
                 {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω} ∪ Zr)))
        ≤ μ {ω | M ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ω}
          + (μ {ω | blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω = 0}
            + (μ (((σ : Ω → Ω)^[n]) ⁻¹'
                {ω | M ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ω}) + μ Zr)) := by
      refine le_trans (measure_union_le _ _) (add_le_add (le_refl _) ?_)
      exact le_trans (measure_union_le _ _) (add_le_add (le_refl _) (measure_union_le _ _))
    refine le_trans (measure_mono hsub) (le_trans hchain ?_)
    rw [← hsum3, hpre, hZr0]
    exact add_le_add hMbound1.le
      (add_le_add (hn₀ n hn).le (add_le_add hMbound2.le (le_refl 0)))
  exact ⟨M, n₀, hrecpAE, hrecmAE, hbadm, hbadμ⟩

/-- **The covering estimate: `C ≤ q`.** This is §4's hardest step (`human/proof_met.tex`
lines 517-612), in the null-threshold form the zero-one law consumes: if almost every orbit has
infinitely many *balanced good times* `j` with `f_{-j→j}(ω) < 2jq`, then the Kingman constant is
at most `q`.

The argument: backward Vitali packs disjoint good windows covering all but `ε` of the space;
the greedy walk decomposes `[0, n)` into good blocks (growth `≤ q` per step) and gaps (whose
points are uncovered, hence contribute `∫_B |f₁| ≤ ε` on average); the two end segments are
short outside a set of measure `< ε`. Integrating and dividing by `n` gives
`C ≤ q + 4ε(1 + |q|)`, and `ε → 0` finishes.

Departure from the paper: the paper's gap bound `Σ 1_B(σⁱω) f₁∘σⁱ` misses the left end of each
gap, which is a *right endpoint* and so covered. `gapMaj` adds the `Λ₊` term, and forcing every
window radius to be at least `N₀` makes `μ Λ₊ ≤ 1/(2N₀+1)` small (`measure_rightEnd_le`), so the
repair costs nothing. -/
theorem covering_bound [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (σ : Ω → Ω) μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily (σ : Ω → Ω) f) (hL1 : ∀ n, Integrable (f n) μ) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) (q : ℝ)
    (hinf : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ j : ℕ, k ≤ j ∧ 1 ≤ j ∧
      f (2 * j) (zIter σ (-(j : ℤ)) ω) < 2 * j * q) :
    C ≤ q := by
  classical
  have hmp : MeasurePreserving (σ : Ω → Ω) μ μ := hσ.toMeasurePreserving
  have habs1 : Integrable (fun ω => |f 1 ω|) μ := (hL1 1).abs
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hq1 : (0 : ℝ) < 1 + |q| := by positivity
  set e : ℝ := ε / (4 * (1 + |q|)) with hedef
  have he0 : 0 < e := by rw [hedef]; positivity
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_setIntegral_abs_le (μ := μ) (f 1) (hL1 1) he0
  set ε₁ : ℝ := min (min e δ) (1 / 2) with hε₁def
  have hε₁0 : 0 < ε₁ := lt_min (lt_min he0 hδ0) (by norm_num)
  have hε₁e : ε₁ ≤ e := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₁δ : ε₁ ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₁half : ε₁ ≤ 1 / 2 := min_le_right _ _
  -- **The window radius.** Large radii force `μ Λ₊` small.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (1 : ℝ) ≤ (2 * (N₀ : ℝ) + 1) * ε₁ := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε₁)
    refine ⟨N₀, ?_⟩
    have h1 : 1 / ε₁ < (N₀ : ℝ) := hN₀
    rw [div_lt_iff₀ hε₁0] at h1
    have h2 : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨A, jω, hAm, hjm, hdisj, hgood, hinj, hrad, hcov⟩ :=
    exists_good_windows_everywhere μ σ hσ f hf q ε₁ hε₁0 N₀ hinf
  have hpos : ∀ ω' ∈ A, 1 ≤ jω ω' := fun ω' h => (hgood ω' h).1
  -- **The uncovered set `B`, and the two endpoint sets.**
  have hUm : MeasurableSet (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) :=
    measurableSet_iUnion_windows hAm hjm hdisj
  have hBm : MeasurableSet (uncovered σ jω A) := hUm.compl
  have hΛmm : MeasurableSet (leftEnd σ jω '' A) := measurableSet_leftEnd_image hAm hjm hdisj
  have hΛpm : MeasurableSet (rightEnd σ jω '' A) := measurableSet_rightEnd_image hAm hjm hdisj
  have hpos1 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - ε₁) := by
    rw [ENNReal.ofReal_pos]; linarith
  have hA0 : μ A ≠ 0 := by
    intro h0
    exact absurd (measure_iUnion_windows_of_null σ hσ hAm h0 jω) (by
      intro hz; rw [hz] at hcov; exact absurd hcov (by simp))
  -- `μ B ≤ ε₁`
  have hBμ : μ (uncovered σ jω A) ≤ ENNReal.ofReal ε₁ := by
    rw [uncovered, measure_compl hUm (measure_ne_top μ _), measure_univ]
    have h1 : (1 : ℝ≥0∞) - μ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
        ≤ 1 - ENNReal.ofReal (1 - ε₁) := tsub_le_tsub_left hcov.le 1
    refine le_trans h1 (le_of_eq ?_)
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp, ← ENNReal.ofReal_sub _ (by linarith)]
    congr 1
    ring
  -- `μ Λ₊ ≤ ε₁`, the repair of the paper's dropped endpoint terms
  have hΛpμ : μ (rightEnd σ jω '' A) ≤ ENNReal.ofReal ε₁ := by
    have hbound := measure_rightEnd_le σ hσ N₀ hΛpm hdisj hrad hinj
    have hfac : (2 * (N₀ : ℝ≥0∞) + 1) ≠ 0 := by positivity
    have hfac' : (2 * (N₀ : ℝ≥0∞) + 1) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top N₀), by simp⟩
    have hR : (2 * (N₀ : ℝ≥0∞) + 1) * ENNReal.ofReal ε₁
        = ENNReal.ofReal ((2 * (N₀ : ℝ) + 1) * ε₁) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      simp [ENNReal.ofReal_natCast]
    rw [← ENNReal.mul_le_mul_iff_left hfac hfac']
    calc μ (rightEnd σ jω '' A) * (2 * (N₀ : ℝ≥0∞) + 1)
        = (2 * (N₀ : ℝ≥0∞) + 1) * μ (rightEnd σ jω '' A) := mul_comm _ _
      _ ≤ 1 := hbound
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal ((2 * (N₀ : ℝ) + 1) * ε₁) := ENNReal.ofReal_le_ofReal hN₀
      _ = (2 * (N₀ : ℝ≥0∞) + 1) * ENNReal.ofReal ε₁ := hR.symm
      _ = ENNReal.ofReal ε₁ * (2 * (N₀ : ℝ≥0∞) + 1) := mul_comm _ _
  obtain ⟨M, n₀, hrecpAE, hrecmAE, hbadm, hbadμ⟩ :=
    exists_small_badSet_cutoff μ σ hσ A jω hΛmm hΛpm hA0 hdisj hpos hinj ε₁ hε₁0
  have hbadδ : ∀ n : ℕ, n₀ ≤ n → μ (badSet σ jω A M n) ≤ ENNReal.ofReal δ := fun n hn =>
    le_trans (hbadμ n hn) (ENNReal.ofReal_le_ofReal (by linarith))
  have hbadreal : ∀ n : ℕ, n₀ ≤ n → (μ (badSet σ jω A M n)).toReal ≤ ε₁ := by
    intro n hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbadμ n hn)
    rw [ENNReal.toReal_ofReal (by linarith)] at h
    linarith
  -- **The two averaged observables.**
  have hgapMajInt : Integrable (gapMaj σ jω A f) μ :=
    (habs1.indicator hBm).add (habs1.indicator hΛpm)
  have hgapCountInt : Integrable (gapCount σ jω A) μ :=
    ((integrable_const (1 : ℝ)).indicator hBm).add ((integrable_const (1 : ℝ)).indicator hΛpm)
  have hgapMajBd : ∫ ω, gapMaj σ jω A f ω ∂μ ≤ 2 * e := by
    rw [integral_gapMaj hBm hΛpm (hL1 1)]
    have h1 := hδ (uncovered σ jω A) hBm (le_trans hBμ (ENNReal.ofReal_le_ofReal hε₁δ))
    have h2 := hδ (rightEnd σ jω '' A) hΛpm (le_trans hΛpμ (ENNReal.ofReal_le_ofReal hε₁δ))
    linarith
  have hgapCountBd : ∫ ω, gapCount σ jω A ω ∂μ ≤ 2 * ε₁ := by
    rw [integral_gapCount hBm hΛpm]
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBμ
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hΛpμ
    rw [ENNReal.toReal_ofReal hε₁0.le] at h1 h2
    linarith
  -- **The per-`n` estimate.**
  have hstep : ∀ n : ℕ, n₀ ≤ n → M ≤ n → 1 ≤ n →
      (∫ ω, f n ω ∂μ) / n
        ≤ q + (2 * (∫ ω, f 0 ω ∂μ) + 2 * (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) + |q| * (2 * M)) / n
          + (4 * e + 4 * |q| * ε₁) := by
    intro n hn0 hnM hn1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
    have i1 : Integrable (fun ω => 2 * f 0 ω) μ := (hL1 0).const_mul 2
    have i2 : Integrable (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ω) μ :=
      integrable_birkhoffSum hmp habs1 M
    have i3 : Integrable
        (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ((σ : Ω → Ω)^[n - M] ω)) μ :=
      (hmp.iterate (n - M)).integrable_comp_of_integrable i2
    have i4 : Integrable (fun ω => 2 * (badSet σ jω A M n).indicator
        (fun x => birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n x) ω) μ :=
      ((integrable_birkhoffSum hmp habs1 n).indicator (hbadm n)).const_mul 2
    have i5 : Integrable (fun ω => birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω) μ :=
      integrable_birkhoffSum hmp hgapMajInt n
    have i6 : Integrable (fun _ : Ω => q * (n : ℝ) + |q| * (2 * (M : ℝ))) μ := integrable_const _
    have i7 : Integrable (fun ω => 2 * |q| * (n : ℝ)
        * (badSet σ jω A M n).indicator (fun _ => (1 : ℝ)) ω) μ :=
      ((integrable_const (1 : ℝ)).indicator (hbadm n)).const_mul _
    have i8 : Integrable
        (fun ω => |q| * birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) μ :=
      (integrable_birkhoffSum hmp hgapCountInt n).const_mul _
    have hpt : ∀ᵐ ω ∂μ, f n ω ≤ (fun ω => 2 * f 0 ω) ω
        + (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ω) ω
        + (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ((σ : Ω → Ω)^[n - M] ω)) ω
        + (fun ω => 2 * (badSet σ jω A M n).indicator
            (fun x => birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n x) ω) ω
        + (fun ω => birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω) ω
        + (fun _ : Ω => q * (n : ℝ) + |q| * (2 * (M : ℝ))) ω
        + (fun ω => 2 * |q| * (n : ℝ)
            * (badSet σ jω A M n).indicator (fun _ => (1 : ℝ)) ω) ω
        + (fun ω => |q| * birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) ω := by
      filter_upwards [hrecpAE, hrecmAE] with ω hp hm
      refine le_trans (covering_pointwise_clean hf hdisj hgood hinj hp hm hnM) (le_of_eq ?_)
      ring
    have b1 : ∫ ω, (fun ω => 2 * f 0 ω) ω ∂μ ≤ 2 * (∫ ω, f 0 ω ∂μ) :=
      le_of_eq (integral_const_mul 2 (f 0))
    have b2 : ∫ ω, (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ω) ω ∂μ
        ≤ (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) :=
      le_of_eq (integral_birkhoffSum hmp _ habs1 M)
    have b3 : ∫ ω, (fun ω => birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M
        ((σ : Ω → Ω)^[n - M] ω)) ω ∂μ ≤ (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) := by
      rw [integral_comp_iterate hmp i2 (n - M)]
      exact le_of_eq (integral_birkhoffSum hmp _ habs1 M)
    have b4 : ∫ ω, (fun ω => 2 * (badSet σ jω A M n).indicator
        (fun x => birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n x) ω) ω ∂μ
        ≤ 2 * ((n : ℝ) * e) := by
      rw [integral_const_mul, integral_indicator (hbadm n)]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_birkhoffSum_le σ hσ (hbadm n) (hL1 1) hδ (hbadδ n hn0) n) (by norm_num)
    have b5 : ∫ ω, (fun ω => birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω) ω ∂μ
        ≤ (n : ℝ) * (2 * e) := by
      rw [integral_birkhoffSum hmp _ hgapMajInt n]
      exact mul_le_mul_of_nonneg_left hgapMajBd hnnn
    have b6 : ∫ _ω, (fun _ : Ω => q * (n : ℝ) + |q| * (2 * (M : ℝ))) _ω ∂μ
        ≤ q * (n : ℝ) + |q| * (2 * (M : ℝ)) := by
      simp
    have b7 : ∫ ω, (fun ω => 2 * |q| * (n : ℝ)
        * (badSet σ jω A M n).indicator (fun _ => (1 : ℝ)) ω) ω ∂μ
        ≤ 2 * |q| * (n : ℝ) * ε₁ := by
      rw [integral_const_mul, integral_indicator (hbadm n)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [setIntegral_const, smul_eq_mul, mul_one]
      exact hbadreal n hn0
    have b8 : ∫ ω, (fun ω => |q| * birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) ω ∂μ
        ≤ |q| * ((n : ℝ) * (2 * ε₁)) := by
      rw [integral_const_mul, integral_birkhoffSum hmp _ hgapCountInt n]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgapCountBd hnnn) (abs_nonneg q)
    have hint := integral_le_of_le_sum_eight (hL1 n) i1 i2 i3 i4 i5 i6 i7 i8 hpt
      b1 b2 b3 b4 b5 b6 b7 b8
    rw [div_le_iff₀ hnR]
    have hexp : (q + (2 * (∫ ω, f 0 ω ∂μ) + 2 * (M : ℝ) * (∫ ω, |f 1 ω| ∂μ)
          + |q| * (2 * (M : ℝ))) / n + (4 * e + 4 * |q| * ε₁)) * (n : ℝ)
        = 2 * (∫ ω, f 0 ω ∂μ) + (M : ℝ) * (∫ ω, |f 1 ω| ∂μ)
          + (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) + 2 * ((n : ℝ) * e) + (n : ℝ) * (2 * e)
          + (q * (n : ℝ) + |q| * (2 * (M : ℝ))) + 2 * |q| * (n : ℝ) * ε₁
          + |q| * ((n : ℝ) * (2 * ε₁)) := by
      field_simp
      try ring
    rw [hexp]
    exact hint
  -- **Pass to the limit in `n`, then in `ε`.**
  have hlim : Tendsto (fun n : ℕ => q
      + (2 * (∫ ω, f 0 ω ∂μ) + 2 * (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) + |q| * (2 * (M : ℝ))) / n
      + (4 * e + 4 * |q| * ε₁)) atTop
      (nhds (q + 0 + (4 * e + 4 * |q| * ε₁))) :=
    (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)).add tendsto_const_nhds
  have hev : (fun n : ℕ => (∫ ω, f n ω ∂μ) / n) ≤ᶠ[atTop]
      fun n : ℕ => q
        + (2 * (∫ ω, f 0 ω ∂μ) + 2 * (M : ℝ) * (∫ ω, |f 1 ω| ∂μ) + |q| * (2 * (M : ℝ))) / n
        + (4 * e + 4 * |q| * ε₁) := by
    filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop M, eventually_ge_atTop 1]
      with n h1 h2 h3
    exact hstep n h1 h2 h3
  have hCle := le_of_tendsto_of_tendsto hC hlim hev
  have hqe : 4 * e + 4 * |q| * e = ε := by
    rw [hedef]
    field_simp
  have hmono : 4 * |q| * ε₁ ≤ 4 * |q| * e :=
    mul_le_mul_of_nonneg_left hε₁e (by positivity)
  linarith

end MultiplicativeErgodic
