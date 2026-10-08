/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.TangentMeasures.Basic

/-!
# Mattila's Lemmas 14.5 and 14.6

This file proves the compactness and normalization results for tangent measures appearing in
Mattila's Lemmas 14.5 and 14.6.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-! ## Auxiliary material for Lemmas 14.5 and 14.6 -/

section TangentAux

variable {n : ℕ}

/-- A positive sequence converging to `0` converges to `0` from the right. -/
lemma tendsto_nhdsGT_zero_of_pos {u : ℕ → ℝ} (hpos : ∀ i, 0 < u i)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto u atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 (Eventually.of_forall hpos)

/-- The integral of a compactly supported continuous function against a measure which is finite
on the support is bounded by the supremum norm times the measure of the support. -/
lemma norm_integral_cc_le {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (M : Measure X) (f : CompactlySupportedContinuousMap X ℝ) {K : Set X}
    (hK : tsupport f ⊆ K) (hfin : M K < ∞) :
    ‖∫ x, f x ∂M‖ ≤ ‖f.toBoundedContinuousFunction‖ * (M K).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hK h)))]
  simpa [Measure.real] using
    norm_setIntegral_le_of_norm_le_const (μ := M) (s := K) hfin
      (fun x _ ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x)

/-- If two sequences of Radon measures have asymptotically the same integrals against
compactly supported continuous functions, then they have the same weak limits. -/
lemma weaklyConverges_of_tendsto_integral_sub
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {F G : ℕ → Measure X} {ν : Measure X}
    (h : Measure.WeaklyConverges F ν)
    (hd : ∀ f : CompactlySupportedContinuousMap X ℝ,
      Tendsto (fun i ↦ (∫ x, f x ∂G i) - ∫ x, f x ∂F i) atTop (𝓝 0)) :
    Measure.WeaklyConverges G ν := by
  intro f
  simpa using (hd f).add (h f)

/-- Weak convergence of the blow-ups gives a uniform bound for the mass of balls. -/
lemma eventually_smul_measure_closedBall_le
    {μ ν : Measure (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i)
    {hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular} {hν : ν.Regular}
    (hconv : Measure.WeaklyConverges (fun i ↦ c i • μ.map (blowUpMap a (r i))) ν)
    (S : ℝ) :
    ∀ᶠ i in atTop, c i * μ (closedBall a (r i * S)) ≤ ν (closedBall 0 S) + 1 := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have h1 := hb.1 (closedBall 0 S) (isCompact_closedBall _ _)
  have heq : ∀ i, (c i • μ.map (blowUpMap a (r i))) (closedBall 0 S)
      = c i * μ (closedBall a (r i * S)) := by
    intro i
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr i)]
  have hfin : ν (closedBall 0 S) ≠ ∞ := (regular_measure_closedBall_lt_top hν 0 S).ne
  have hlt : limsup (fun i ↦ c i * μ (closedBall a (r i * S))) atTop
      < ν (closedBall 0 S) + 1 := by
    refine lt_of_le_of_lt ?_ (ENNReal.lt_add_right hfin one_ne_zero)
    simpa only [heq] using h1
  exact (eventually_lt_of_limsup_lt hlt).mono fun i hi ↦ hi.le

/-- If `B` has density one at `a` and the normalized masses of the balls stay bounded, then
the normalized masses of the sets `B̄ (a, r i t) \ B` tend to `0`. -/
lemma tendsto_mul_measure_diff_zero
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : μ.Regular)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hdens : Tendsto (fun s : ℝ ↦ μ (ball a s \ B) / μ (ball a s)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    {c : ℕ → ℝ≥0∞} {t : ℝ} (ht : 0 < t) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbd : ∀ᶠ i in atTop, c i * μ (closedBall a (2 * (r i * t))) ≤ M) :
    Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun i ↦ 2 * (r i * t) with hs
  have hspos : ∀ i, 0 < s i := fun i ↦ by
    have := mul_pos (hr i) ht
    simp only [hs]
    linarith
  have hs0 : Tendsto s atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsGT_zero_of_pos hspos ?_
    have : Tendsto (fun i ↦ 2 * (r i * t)) atTop (𝓝 (2 * (0 * t))) :=
      (hr0.mul_const t).const_mul 2
    simpa using this
  have heps : Tendsto (fun i ↦ μ (ball a (s i) \ B) / μ (ball a (s i))) atTop (𝓝 0) :=
    hdens.comp hs0
  have hlim : Tendsto (fun i ↦ (μ (ball a (s i) \ B) / μ (ball a (s i))) * M)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const heps (Or.inr hM)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hbd] with i hi
  have hpos : μ (ball a (s i)) ≠ 0 := (measure_ball_pos_of_mem_support ha (hspos i)).ne'
  have hfin : μ (ball a (s i)) ≠ ∞ := (regular_measure_ball_lt_top hμ a (s i)).ne
  have hsub : closedBall a (r i * t) \ B ⊆ ball a (s i) \ B := by
    refine sdiff_subset_sdiff_left (closedBall_subset_ball ?_)
    have := mul_pos (hr i) ht
    simp only [hs]
    linarith
  calc c i * μ (closedBall a (r i * t) \ B) ≤ c i * μ (ball a (s i) \ B) := by gcongr
    _ = (μ (ball a (s i) \ B) / μ (ball a (s i))) * (c i * μ (ball a (s i))) := by
        rw [show (μ (ball a (s i) \ B) / μ (ball a (s i))) * (c i * μ (ball a (s i)))
            = c i * (μ (ball a (s i) \ B) / μ (ball a (s i)) * μ (ball a (s i))) from by
              ring,
          ENNReal.div_mul_cancel hpos hfin]
    _ ≤ (μ (ball a (s i) \ B) / μ (ball a (s i))) * M := by
        gcongr
        exact le_trans (by gcongr; exact ball_subset_closedBall) hi

/-- If `B` has density one at `a`, then at small scales the measure of a ball is at most twice
the measure of its intersection with `B`. -/
lemma eventually_measure_ball_le_two_mul_inter
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : μ.Regular)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (hdens : Tendsto (fun s : ℝ ↦ μ (ball a s \ B) / μ (ball a s)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), μ (ball a s) ≤ 2 * μ (ball a s ∩ B) := by
  have hhalf : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), μ (ball a s \ B) / μ (ball a s) < 1 / 2 :=
    hdens (Iio_mem_nhds hhalf)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos'
  have hspos : 0 < s := hspos'
  have hy0 : μ (ball a s) ≠ 0 := (measure_ball_pos_of_mem_support ha hspos).ne'
  have hytop : μ (ball a s) ≠ ∞ := (regular_measure_ball_lt_top hμ a s).ne
  have hsplit : μ (ball a s) = μ (ball a s ∩ B) + μ (ball a s \ B) := by
    exact (measure_inter_add_sdiff (μ := μ) (ball a s) hB).symm
  have hx : μ (ball a s \ B) < μ (ball a s) / 2 := by
    rw [ENNReal.div_lt_iff (Or.inl hy0) (Or.inl hytop)] at hs
    have heq : (1 : ℝ≥0∞) / 2 * μ (ball a s) = μ (ball a s) / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    rwa [heq] at hs
  have hhalffin : μ (ball a s) / 2 ≠ ∞ := by simp [ENNReal.div_eq_top, hytop]
  have hkey : μ (ball a s) / 2 ≤ μ (ball a s ∩ B) := by
    have h1 : μ (ball a s) / 2 + μ (ball a s) / 2
        ≤ μ (ball a s ∩ B) + μ (ball a s) / 2 := by
      rw [ENNReal.add_halves]
      calc μ (ball a s) = μ (ball a s ∩ B) + μ (ball a s \ B) := hsplit
        _ ≤ μ (ball a s ∩ B) + μ (ball a s) / 2 := add_le_add le_rfl hx.le
    exact (ENNReal.add_le_add_iff_right hhalffin).mp h1
  calc μ (ball a s) = μ (ball a s) / 2 + μ (ball a s) / 2 := (ENNReal.add_halves _).symm
    _ ≤ μ (ball a s ∩ B) + μ (ball a s ∩ B) := add_le_add hkey hkey
    _ = 2 * μ (ball a s ∩ B) := (two_mul _).symm

/-- The key estimate behind Mattila's Lemma 14.5: if the normalized masses outside `B` tend
to `0`, then the blow-ups of `μ` and of `μ.restrict B` have asymptotically equal integrals. -/
lemma tendsto_integral_sub_restrict
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (a : EuclideanSpace ℝ (Fin n)) {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) {c : ℕ → ℝ≥0∞}
    (hcfin : ∀ i, c i ≠ ∞)
    (hF : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular)
    (hdiff : ∀ t : ℝ, 0 < t →
      Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0))
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    Tendsto (fun i ↦
        (∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))) atTop (𝓝 0) := by
  obtain ⟨t, ht, htsup⟩ : ∃ t : ℝ, 0 < t ∧ tsupport f ⊆ closedBall 0 t := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨max 1 R, lt_of_lt_of_le one_pos (le_max_left _ _),
      hR.trans (closedBall_subset_closedBall (le_max_right _ _))⟩
  have key : ∀ i, ‖(∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))‖
      ≤ ‖f.toBoundedContinuousFunction‖ * (c i * μ (closedBall a (r i * t) \ B)).toReal := by
    intro i
    have hmeas : Measurable (blowUpMap a (r i)) := measurable_blowUpMap a (r i)
    set D : Measure (EuclideanSpace ℝ (Fin n)) :=
      c i • (μ.restrict Bᶜ).map (blowUpMap a (r i)) with hD
    have hdec : c i • μ.map (blowUpMap a (r i))
        = c i • (μ.restrict B).map (blowUpMap a (r i)) + D := by
      rw [hD, ← smul_add, ← Measure.map_add _ _ hmeas,
        Measure.restrict_add_restrict_compl hB]
    have _ : (c i • μ.map (blowUpMap a (r i))).Regular := hF i
    have hintF : Integrable f (c i • μ.map (blowUpMap a (r i))) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hleG : c i • (μ.restrict B).map (blowUpMap a (r i))
        ≤ c i • μ.map (blowUpMap a (r i)) := by
      rw [hdec]
      exact Measure.le_add_right le_rfl
    have hleD : D ≤ c i • μ.map (blowUpMap a (r i)) := by
      rw [hdec]
      exact Measure.le_add_left le_rfl
    have hintG := hintF.mono_measure hleG
    have hintD := hintF.mono_measure hleD
    have hsplit : (∫ x, f x ∂(c i • μ.map (blowUpMap a (r i))))
        = (∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          + ∫ x, f x ∂D := by
      rw [hdec, integral_add_measure hintG hintD]
    have hDK : D (closedBall 0 t) = c i * μ (closedBall a (r i * t) \ B) := by
      rw [hD, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply hmeas measurableSet_closedBall,
        blowUpMap_preimage_closedBall a (hr i), Measure.restrict_apply measurableSet_closedBall,
        ← Set.sdiff_eq]
    have hDfin : D (closedBall 0 t) < ∞ := by
      rw [hDK]
      exact ENNReal.mul_lt_top (hcfin i).lt_top
        (lt_of_le_of_lt (measure_mono sdiff_subset) (regular_measure_closedBall_lt_top hμ a _))
    rw [hsplit]
    have hbound : ‖-∫ x, f x ∂D‖
        ≤ ‖f.toBoundedContinuousFunction‖ * (D (closedBall 0 t)).toReal := by
      rw [norm_neg]
      exact norm_integral_cc_le D f htsup hDfin
    rw [hDK] at hbound
    simpa using hbound
  refine squeeze_zero_norm key ?_
  have h0 : Tendsto (fun i ↦ (c i * μ (closedBall a (r i * t) \ B)).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp (hdiff t ht)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  simpa using h0.const_mul ‖f.toBoundedContinuousFunction‖

end TangentAux

/-- **Mattila, Lemma 14.5.** If `B` has density one with respect to `μ` at `a`, then
restricting `μ` to `B` does not change the tangent measures at `a`. -/
theorem isTangentMeasure_restrict_iff
    {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : MeasurableSet B)
    (hμB : (μ.restrict B).Regular) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (hdens : Tendsto (fun r : ℝ ↦ μ (ball a r \ B) / μ (ball a r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    IsTangentMeasure μ ν a ↔ IsTangentMeasure (μ.restrict B) ν a := by
  constructor
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hdiff : ∀ t : ℝ, 0 < t →
        Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
      intro t ht
      have hbd := eventually_smul_measure_closedBall_le (hseq := hseq) (hν := hν) hr hconv (2 * t)
      refine tendsto_mul_measure_diff_zero hμ ha hdens hr hr0 ht
        (M := ν (closedBall 0 (2 * t)) + 1)
        (by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 (2 * t)).ne]) ?_
      filter_upwards [hbd] with i hi
      have hrw : r i * (2 * t) = 2 * (r i * t) := by ring
      rwa [hrw] at hi
    exact ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0,
      weaklyConverges_of_tendsto_integral_sub hconv
        (tendsto_integral_sub_restrict μ hμ hB a hr hcfin hseq hdiff)⟩
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconvB⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hseqB : ∀ i, (c i • (μ.restrict B).map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμB a (hr i).ne' (hcfin i)
    have hdiff : ∀ t : ℝ, 0 < t →
        Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
      intro t ht
      have hbd := eventually_smul_measure_closedBall_le (hseq := hseqB) (hν := hν)
        hr hconvB (4 * t)
      have hballs : ∀ᶠ i in atTop,
          μ (ball a (4 * (r i * t))) ≤ 2 * μ (ball a (4 * (r i * t)) ∩ B) := by
        have hu : Tendsto (fun i ↦ 4 * (r i * t)) atTop (𝓝[>] (0 : ℝ)) := by
          refine tendsto_nhdsGT_zero_of_pos
            (fun i ↦ by have := mul_pos (hr i) ht; linarith) ?_
          have h4 : Tendsto (fun i ↦ 4 * (r i * t)) atTop (𝓝 (4 * (0 * t))) :=
            (hr0.mul_const t).const_mul 4
          simpa using h4
        exact hu.eventually (eventually_measure_ball_le_two_mul_inter hμ ha hB hdens)
      refine tendsto_mul_measure_diff_zero hμ ha hdens hr hr0 ht
        (M := 2 * (ν (closedBall 0 (4 * t)) + 1))
        (by simp [ENNReal.mul_eq_top, ENNReal.add_eq_top,
          (regular_measure_closedBall_lt_top hν 0 (4 * t)).ne]) ?_
      filter_upwards [hbd, hballs] with i h1 h2
      have hrt : 0 < r i * t := mul_pos (hr i) ht
      calc c i * μ (closedBall a (2 * (r i * t)))
          ≤ c i * μ (ball a (4 * (r i * t))) := by
            gcongr
            exact closedBall_subset_ball (by linarith)
        _ ≤ c i * (2 * μ (ball a (4 * (r i * t)) ∩ B)) := by gcongr
        _ = 2 * (c i * μ (ball a (4 * (r i * t)) ∩ B)) := by ring
        _ ≤ 2 * (c i * (μ.restrict B) (closedBall a (r i * (4 * t)))) := by
            have hres : μ (ball a (4 * (r i * t)) ∩ B)
                ≤ (μ.restrict B) (closedBall a (r i * (4 * t))) := by
              rw [Measure.restrict_apply measurableSet_closedBall]
              exact measure_mono (inter_subset_inter_left B
                (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
            gcongr
        _ ≤ 2 * (ν (closedBall 0 (4 * t)) + 1) := by gcongr
    have hkey := tendsto_integral_sub_restrict μ hμ hB a hr hcfin hseq hdiff
    exact ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0,
      weaklyConverges_of_tendsto_integral_sub hconvB (fun f ↦ by simpa using (hkey f).neg)⟩

/-! ## Auxiliary material for Lemma 14.6 -/

section DensityAux

variable {n : ℕ}

/-- Two measures agreeing on bounded measurable sets are equal. -/
lemma measure_ext_of_bounded {m₁ m₂ : Measure (EuclideanSpace ℝ (Fin n))}
    (h : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      m₁ B = m₂ B) : m₁ = m₂ := by
  ext B hB
  have hcover : B = ⋃ k : ℕ, B ∩ closedBall 0 k := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_ge (dist y 0)
      exact ⟨k, hy, hk⟩
    · rintro ⟨k, hy, -⟩
      exact hy
  have hdir : Directed (· ⊆ ·)
      (fun k : ℕ ↦ B ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) k) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;>
      exact inter_subset_inter_right _ (closedBall_subset_closedBall (by
        simp only [Nat.cast_le]
        omega))
  rw [hcover, hdir.measure_iUnion, hdir.measure_iUnion]
  exact iSup_congr fun k ↦ h _ (hB.inter measurableSet_closedBall)
    (Metric.isBounded_closedBall.subset inter_subset_right)

/-- A measure specified as `φ μ` on bounded measurable sets is `μ.withDensity φ`. -/
lemma measure_eq_withDensity
    (μ L : Measure (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_nonneg : ∀ x, 0 ≤ φ x)
    (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ)) :
    L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
  refine measure_ext_of_bounded fun B hB hBb ↦ ?_
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hint : IntegrableOn φ B μ :=
    (hφ_loc.integrableOn_isCompact (isCompact_closedBall 0 R)).mono_set hR
  rw [hL_eq B hB hBb, withDensity_apply _ hB,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ_nonneg)]

/-- Lebesgue differentiation theorem for a Radon measure on Euclidean space. -/
lemma ae_tendsto_setAverage_norm_sub (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ_loc : LocallyIntegrable φ μ) :
    ∀ᵐ a ∂μ, Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let _ : μ.Regular := hμ
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hφ_loc] with a ha
  exact ha.comp (Besicovitch.tendsto_filterAt μ a)

/-- The integral of a compactly supported continuous function against a scaled blow-up. -/
lemma integral_blowUp_smul (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) (c : ℝ≥0∞)
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    (∫ x, f x ∂(c • μ.map (blowUpMap a r)))
      = c.toReal * ∫ x, f (blowUpMap a r x) ∂μ := by
  have hmeas : Measurable (blowUpMap a r) := measurable_blowUpMap a r
  rw [integral_smul_measure,
    integral_map (f := fun y ↦ f y) hmeas.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), smul_eq_mul]

lemma integral_withDensity_real (m : Measure (EuclideanSpace ℝ (Fin n)))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, g x ∂(m.withDensity fun x ↦ ENNReal.ofReal (φ x)) = ∫ x, φ x * g x ∂m := by
  rw [integral_withDensity_eq_integral_toReal_smul hφ_meas.ennreal_ofReal
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hφ_nonneg _), smul_eq_mul]

/-- The key per-scale estimate behind Mattila's Lemma 14.6. -/
lemma norm_integral_blowUp_density_sub_le
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞}
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) {t : ℝ}
    (htsup : tsupport f ⊆ closedBall 0 t) :
    ‖(∫ x, f x ∂((c / ENNReal.ofReal (φ a)) • L.map (blowUpMap a r)))
        - ∫ x, f x ∂(c • μ.map (blowUpMap a r))‖
      ≤ (c.toReal / φ a) * ‖f.toBoundedContinuousFunction‖
          * ∫ y in closedBall a (r * t), ‖φ y - φ a‖ ∂μ := by
  set T := blowUpMap a r with hT
  set C := ‖f.toBoundedContinuousFunction‖ with hC
  set K := closedBall a (r * t) with hK
  have hCnn : (0 : ℝ) ≤ C := norm_nonneg _
  have hfbd : ∀ x, ‖f x‖ ≤ C := fun x ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x
  have hTcont : Continuous T := continuous_blowUpMap a r
  have hpre : T ⁻¹' (closedBall 0 t) = K := blowUpMap_preimage_closedBall a hr t
  have hzero : ∀ x, x ∉ K → f (T x) = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun h ↦ hx ?_
    rw [← hpre]
    exact mem_preimage.2 (htsup h)
  let _ : μ.Regular := hμ
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hmfin : μ K < ∞ := hKcompact.measure_lt_top
  have hφB : IntegrableOn φ K μ := hφ_loc.integrableOn_isCompact hKcompact
  have hg1 : Integrable (fun x ↦ f (T x)) μ := by
    refine Continuous.integrable_of_hasCompactSupport (f.continuous.comp hTcont) ?_
    exact HasCompactSupport.intro hKcompact hzero
  have hg2 : Integrable (fun x ↦ φ x * f (T x)) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := K) (hφB.mul_bdd ?_ (Eventually.of_forall fun x ↦ hfbd (T x))) ?_
    · exact (f.continuous.comp hTcont).aestronglyMeasurable
    · intro x hx
      simp [hzero x hx]
  have hg3 : Integrable (fun x ↦ (φ x - φ a) * f (T x)) μ := by
    have : (fun x ↦ (φ x - φ a) * f (T x))
        = fun x ↦ φ x * f (T x) - φ a * f (T x) := by
      ext x
      ring
    rw [this]
    exact hg2.sub (hg1.const_mul (φ a))
  rw [integral_blowUp_smul μ a r c f,
    integral_blowUp_smul L a r (c / ENNReal.ofReal (φ a)) f, hLm,
    integral_withDensity_real μ hφ_meas hφ_nonneg,
    ENNReal.toReal_div, ENNReal.toReal_ofReal hφa.le]
  have hsplit : c.toReal / φ a * (∫ x, φ x * f (T x) ∂μ)
      - c.toReal * ∫ x, f (T x) ∂μ
      = (c.toReal / φ a) * ∫ x, (φ x - φ a) * f (T x) ∂μ := by
    have hcongr : (fun x ↦ (φ x - φ a) * f (T x))
        = fun x ↦ φ x * f (T x) - φ a * f (T x) := by
      ext x
      ring
    rw [hcongr, integral_sub hg2 (hg1.const_mul (φ a)), integral_const_mul]
    field_simp
  rw [hsplit, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c.toReal / φ a), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ x, (φ x - φ a) * f (T x) ∂μ‖
        ≤ ∫ x, ‖(φ x - φ a) * f (T x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x in K, ‖(φ x - φ a) * f (T x)‖ ∂μ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro x hx
        simp [hzero x hx]
    _ ≤ ∫ x in K, C * ‖φ x - φ a‖ ∂μ := by
        refine integral_mono ?_ ?_ ?_
        · exact hg3.norm.integrableOn
        · exact ((hφB.sub (integrableOn_const hmfin.ne)).norm.const_mul C)
        · intro x
          change ‖(φ x - φ a) * f (T x)‖ ≤ C * ‖φ x - φ a‖
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hfbd (T x)) (norm_nonneg _)
    _ = C * ∫ x in K, ‖φ x - φ a‖ ∂μ := integral_const_mul _ _

lemma tendsto_mul_setIntegral_norm_sub_zero
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t)
    {c : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbdd : ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M) :
    Tendsto (fun i ↦ (c i).toReal * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := by
  let _ : μ.Regular := hμ
  have hs : Tendsto (fun i ↦ r i * t) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsGT_zero_of_pos (fun i ↦ mul_pos (hr i) ht) (by simpa using hr0.mul_const t)
  have heps : Tendsto (fun i ↦ ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := hleb.comp hs
  have hlim : Tendsto
      (fun i ↦ M.toReal * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := by
    simpa using heps.const_mul M.toReal
  refine squeeze_zero' (Eventually.of_forall fun i ↦ ?_) ?_ hlim
  · exact mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun y ↦ norm_nonneg _)
  filter_upwards [hbdd] with i hi
  have hmpos : 0 < μ (closedBall a (r i * t)) :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support ha (mul_pos (hr i) ht))
      (measure_mono ball_subset_closedBall)
  have hmfin : μ (closedBall a (r i * t)) < ∞ := (isCompact_closedBall _ _).measure_lt_top
  have hmreal : (μ (closedBall a (r i * t))).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hmpos.ne', hmfin.ne]
  have hint : (∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      = (μ (closedBall a (r i * t))).toReal
        * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, measureReal_def,
      mul_inv_cancel₀ hmreal, one_mul]
  have hle : (c i * μ (closedBall a (r i * t))).toReal ≤ M.toReal :=
    ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hM hi) hM |>.2 hi
  calc (c i).toReal * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ
      = (c i * μ (closedBall a (r i * t))).toReal
        * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
        rw [hint, ENNReal.toReal_mul, mul_assoc]
    _ ≤ M.toReal * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
        refine mul_le_mul_of_nonneg_right hle ?_
        rw [setAverage_eq, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
          (integral_nonneg fun y ↦ norm_nonneg _)

/-- At a Lebesgue point `a` of `φ` with `φ a > 0`, the measure `L = φ μ` of a small ball is at
least `φ a / 2` times the `μ`-measure of that ball. -/
lemma eventually_ofReal_mul_measure_closedBall_le
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ))
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support) (hφa : 0 < φ a)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (φ a / 2) * μ (closedBall a s) ≤ L (closedBall a s) := by
  let _ : μ.Regular := hμ
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ < φ a / 2 :=
    hleb (Iio_mem_nhds (by positivity))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos'
  have hspos : 0 < s := hspos'
  have hmfin : μ (closedBall a s) < ∞ := (isCompact_closedBall _ _).measure_lt_top
  have hmpos : 0 < μ (closedBall a s) :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support ha hspos)
      (measure_mono ball_subset_closedBall)
  have hmreal : (0 : ℝ) < (μ (closedBall a s)).toReal := by
    simpa [ENNReal.toReal_pos_iff] using ⟨hmpos, hmfin⟩
  have hint : IntegrableOn φ (closedBall a s) μ :=
    hφ_loc.integrableOn_isCompact (isCompact_closedBall _ _)
  have hI : (∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      = (μ (closedBall a s)).toReal * ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, measureReal_def,
      mul_inv_cancel₀ hmreal.ne', one_mul]
  have hIle : (∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      ≤ (φ a / 2) * (μ (closedBall a s)).toReal := by
    rw [hI, mul_comm]
    exact mul_le_mul_of_nonneg_right hs.le hmreal.le
  have hlow : (φ a / 2) * (μ (closedBall a s)).toReal
      ≤ ∫ y in closedBall a s, φ y ∂μ := by
    have hconst : (∫ _y in closedBall a s, φ a ∂μ)
        = (μ (closedBall a s)).toReal * φ a := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    have h1 : (∫ y in closedBall a s, (φ y - φ a) ∂μ)
        = (∫ y in closedBall a s, φ y ∂μ) - (μ (closedBall a s)).toReal * φ a := by
      rw [integral_sub hint (integrableOn_const hmfin.ne), hconst]
    have h2 : |∫ y in closedBall a s, (φ y - φ a) ∂μ|
        ≤ ∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := μ.restrict (closedBall a s))
          (f := fun y ↦ φ y - φ a)
    have h3 := (abs_le.mp (h2.trans hIle)).1
    have harith : (μ (closedBall a s)).toReal * φ a
        - (φ a / 2) * (μ (closedBall a s)).toReal
        = (φ a / 2) * (μ (closedBall a s)).toReal := by ring
    linarith [h1, h3, harith]
  rw [hL_eq _ measurableSet_closedBall Metric.isBounded_closedBall]
  calc ENNReal.ofReal (φ a / 2) * μ (closedBall a s)
      = ENNReal.ofReal ((φ a / 2) * (μ (closedBall a s)).toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmfin.ne]
    _ ≤ ENNReal.ofReal (∫ y in closedBall a s, φ y ∂μ) := ENNReal.ofReal_le_ofReal hlow

/-- At a positive Lebesgue point of `φ`, appropriately normalized blow-ups of `μ` and `φ μ`
have asymptotically equal integrals. -/
lemma tendsto_integral_sub_density
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) (ha : a ∈ μ.support)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) {c : ℕ → ℝ≥0∞}
    (hbdd : ∀ t : ℝ, 0 < t → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M)
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    Tendsto (fun i ↦
        (∫ x, f x ∂((c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))) atTop (𝓝 0) := by
  set C := ‖f.toBoundedContinuousFunction‖ with hC
  obtain ⟨t, ht, htsup⟩ : ∃ t : ℝ, 0 < t ∧ tsupport f ⊆ closedBall 0 t := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨max 1 R, lt_of_lt_of_le one_pos (le_max_left _ _),
      hR.trans (closedBall_subset_closedBall (le_max_right _ _))⟩
  obtain ⟨M, hM, hbd⟩ := hbdd t ht
  have hlim := tendsto_mul_setIntegral_norm_sub_zero μ hμ a ha φ hleb hr hr0 ht hM hbd
  refine squeeze_zero_norm (fun i ↦ ?_) (by simpa using hlim.const_mul (C / φ a))
  calc ‖(∫ x, f x ∂((c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))))
        - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))‖
      ≤ ((c i).toReal / φ a) * C
          * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ :=
        norm_integral_blowUp_density_sub_le μ L hμ φ hφ_meas hφ_nonneg hφ_loc
          hLm a hφa (hr i) f htsup
    _ = C / φ a * ((c i).toReal
        * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ) := by ring

/-- Mattila, Lemma 14.6, at a fixed Lebesgue point of the density. -/
lemma isTangentMeasure_iff_of_lebesgue_point
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular) (hL : L.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ))
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) (ha : a ∈ μ.support)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    IsTangentMeasure μ ν a ↔ IsTangentMeasure L ν a := by
  have hofR0 : ENNReal.ofReal (φ a) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hφa]
  have hofRtop : ENNReal.ofReal (φ a) ≠ ∞ := ENNReal.ofReal_ne_top
  have hhalf0 : ENNReal.ofReal (φ a / 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hφa]
  constructor
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hcfin' : ∀ i, c i / ENNReal.ofReal (φ a) ≠ ∞ :=
      fun i ↦ (ENNReal.div_lt_top (hcfin i) hofR0).ne
    refine ⟨hν, hν0, r, fun i ↦ c i / ENNReal.ofReal (φ a), hr,
      fun i ↦ ENNReal.div_pos (hcpos i).ne' hofRtop, hcfin', hr0, ?_⟩
    refine weaklyConverges_of_tendsto_integral_sub hconv fun f ↦ ?_
    refine tendsto_integral_sub_density μ L hμ φ hφ_meas hφ_nonneg hφ_loc hLm
      a hφa ha hleb hr hr0 ?_ f
    intro t ht
    exact ⟨ν (closedBall 0 t) + 1,
      by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 t).ne],
      eventually_smul_measure_closedBall_le (hseq := hseq) (hν := hν) hr hconv t⟩
  · rintro ⟨hν, hν0, r, cL, hr, hcpos, hcfin, hr0, hconvL⟩
    set c : ℕ → ℝ≥0∞ := fun i ↦ cL i * ENNReal.ofReal (φ a) with hc
    have hcancel : ∀ i, c i / ENNReal.ofReal (φ a) = cL i := fun i ↦
      ENNReal.mul_div_cancel_right hofR0 hofRtop
    have hcpos' : ∀ i, 0 < c i := fun i ↦ ENNReal.mul_pos (hcpos i).ne' hofR0
    have hcfin' : ∀ i, c i ≠ ∞ := fun i ↦ ENNReal.mul_ne_top (hcfin i) hofRtop
    have hseqL : ∀ i, (cL i • L.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hL a (hr i).ne' (hcfin i)
    have hconvL' : Measure.WeaklyConverges
        (fun i ↦ (c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))) ν :=
      Measure.WeaklyConverges.congr_seq (fun i ↦ by rw [hcancel i]) hconvL
    have hbdd : ∀ t : ℝ, 0 < t → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
        ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M := by
      intro t ht
      have hb0 := eventually_smul_measure_closedBall_le (hseq := hseqL) (hν := hν)
        hr hconvL t
      have hb1 : ∀ᶠ i in atTop, ENNReal.ofReal (φ a / 2) * μ (closedBall a (r i * t))
          ≤ L (closedBall a (r i * t)) := by
        have hu : Tendsto (fun i ↦ r i * t) atTop (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsGT_zero_of_pos (fun i ↦ mul_pos (hr i) ht)
            (by simpa using hr0.mul_const t)
        exact hu.eventually
          (eventually_ofReal_mul_measure_closedBall_le μ L hμ φ hφ_loc hL_eq
            a ha hφa hleb)
      refine ⟨ENNReal.ofReal (φ a)
        * ((ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2)), ?_, ?_⟩
      · refine ENNReal.mul_ne_top hofRtop ?_
        exact (ENNReal.div_lt_top
          (by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 t).ne])
          hhalf0).ne
      · filter_upwards [hb0, hb1] with i h0 h1
        have hstep : cL i * μ (closedBall a (r i * t))
            ≤ (ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hhalf0) (Or.inl ENNReal.ofReal_ne_top)]
          calc cL i * μ (closedBall a (r i * t)) * ENNReal.ofReal (φ a / 2)
              = cL i * (ENNReal.ofReal (φ a / 2) * μ (closedBall a (r i * t))) := by ring
            _ ≤ cL i * L (closedBall a (r i * t)) := by gcongr
            _ ≤ ν (closedBall 0 t) + 1 := h0
        calc c i * μ (closedBall a (r i * t))
            = ENNReal.ofReal (φ a) * (cL i * μ (closedBall a (r i * t))) := by
                rw [hc]
                ring
          _ ≤ ENNReal.ofReal (φ a)
              * ((ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2)) := by gcongr
    have hkey := tendsto_integral_sub_density μ L hμ φ hφ_meas hφ_nonneg hφ_loc
      hLm a hφa ha hleb hr hr0 hbdd
    exact ⟨hν, hν0, r, c, hr, hcpos', hcfin', hr0,
      weaklyConverges_of_tendsto_integral_sub hconvL' (fun f ↦ by simpa using (hkey f).neg)⟩

end DensityAux

/-- **Mattila, Lemma 14.6.** If `λ = φ μ` with `φ ≥ 0` locally `μ`-integrable, then `μ`
and `λ` have the same tangent measures at `λ`-almost every point. -/
theorem isTangentMeasure_iff_ae_of_density
    {n : ℕ} (μ «λ» : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) («hλ» : «λ».Regular) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    («hλ_eq» : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      Bornology.IsBounded B →
      «λ» B = ENNReal.ofReal (∫ x in B, φ x ∂μ)) :
    ∀ᵐ a ∂«λ», ∀ ν : Measure (EuclideanSpace ℝ (Fin n)),
      IsTangentMeasure μ ν a ↔ IsTangentMeasure «λ» ν a := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦ max (hφ_loc.aestronglyMeasurable.mk φ x) 0 with hgdef
  have hg_meas : Measurable g :=
    (hφ_loc.aestronglyMeasurable.stronglyMeasurable_mk.measurable).max measurable_const
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x ↦ le_max_right _ _
  have hgφ : φ =ᵐ[μ] g := by
    filter_upwards [hφ_loc.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [hgdef]
    simp only
    rw [← hx, max_eq_left (hφ_nonneg x)]
  have hg_loc : LocallyIntegrable g μ := fun x ↦
    let ⟨s, hs, hi⟩ := hφ_loc x; ⟨s, hs, hi.congr (ae_restrict_of_ae hgφ)⟩
  have hg_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      «λ» B = ENNReal.ofReal (∫ x in B, g x ∂μ) := by
    intro B hB hBb
    rw [«hλ_eq» B hB hBb]
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae hgφ)
  have hLm : «λ» = μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) :=
    measure_eq_withDensity μ «λ» g hg_nonneg hg_loc hg_eq
  have hac : «λ» ≪ μ := by
    rw [hLm]
    exact withDensity_absolutelyContinuous _ _
  have h1 : ∀ᵐ a ∂«λ», 0 < g a := by
    rw [hLm, ae_withDensity_iff hg_meas.ennreal_ofReal]
    filter_upwards with x hx
    simpa [ENNReal.ofReal_eq_zero, not_le] using hx
  have h2 : ∀ᵐ a ∂«λ», a ∈ μ.support :=
    hac.ae_le (ae_iff.2 μ.measure_compl_support)
  have h3 : ∀ᵐ a ∂«λ», Tendsto
      (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖g y - g a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hac.ae_le (ae_tendsto_setAverage_norm_sub μ hμ g hg_loc)
  filter_upwards [h1, h2, h3] with a ha1 ha2 ha3
  intro ν
  exact isTangentMeasure_iff_of_lebesgue_point μ «λ» hμ «hλ» g hg_meas hg_nonneg
    hg_loc hg_eq hLm a ha1 ha2 ha3 ν



-- 14.7 stuff starts here
