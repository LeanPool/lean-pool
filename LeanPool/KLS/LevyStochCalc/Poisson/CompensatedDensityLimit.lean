/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
-- Modified 2026-10-31 by the KLS formalization project: `eLpNorm_two_rpow_eq_lintegral_sq`
-- takes `hg : AEStronglyMeasurable g P`, which `eLpNorm_nnreal_pow_eq_lintegral` requires in
-- Mathlib v4.35.0 (where `eLpNorm` of a non-a.e.-strongly-measurable function is `∞`); its
-- caller passes an existing `MemLp` witness.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityRefinement

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The compensated integral of a finite-intensity box is in `L²(P)`. -/
lemma compensated_memLp
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.MemLp (fun ω => N.compensated B ω) 2 P := by
  have hmeas : Measurable (fun ω => N.compensated B ω) := by
    change Measurable (fun ω => (N.N ω B).toReal
      - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
    exact ((N.measurable_eval hB).ennreal_toReal).sub_const _
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
    (compensated_sq_integrable N hB hfin)

/-- A bounded measurable factor preserves `L²`-membership. -/
lemma memLp_bdd_mul {P : Measure Ω} {f g : Ω → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ ω, |f ω| ≤ M) (hg : MeasureTheory.MemLp g 2 P) :
    MeasureTheory.MemLp (fun ω => f ω * g ω) 2 P := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)).mpr ?_
  refine MeasureTheory.Integrable.mono' (hg.integrable_sq.const_mul (M ^ 2))
    ((hf.aemeasurable.mul hg.aemeasurable).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hfb ω)
  simp only [Pi.mul_apply, Real.norm_eq_abs]
  rw [show (f ω * g ω) ^ 2 = f ω ^ 2 * g ω ^ 2 from by ring, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (by nlinarith [hfb ω, abs_nonneg (f ω), sq_abs (f ω), hM0]) (sq_nonneg _)

/-- The Euler step integral `∑ᵢ∑ₖ ciₖ·Ñ((pᵢ,pᵢ₊₁]×Biₖ)` is in `L²(P)`. -/
lemma eulerStepIntegral_memLp
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k)) :
    MeasureTheory.MemLp (fun ω => ∑ i : Fin N₀, ∑ k₀, ci i k₀ ω
      * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω) 2 P := by
  have hterm : ∀ (i : Fin N₀) (k₀ : Fin (Ki i)),
      MeasureTheory.MemLp (fun ω => ci i k₀ ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω) 2 P := by
    intro i k₀
    obtain ⟨M, hM⟩ := hcib i k₀
    exact memLp_bdd_mul (hcim i k₀) hM
      (compensated_memLp N (measurableSet_Ioc.prod (hBim i k₀))
        (referenceIntensity_Ioc_prod_ne_top (hBif i k₀)))
  exact MeasureTheory.memLp_finsetSum Finset.univ (fun i _ =>
    MeasureTheory.memLp_finsetSum Finset.univ (fun k₀ _ => hterm i k₀))

/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²(P)`. -/
lemma lintegral_sq_eq_ofReal_integral {P : Measure Ω} {g : Ω → ℝ}
    (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- **Real↔`ℝ≥0∞` triple-integral bridge.** For a bounded `φ`-difference-style function
`h` supported on marks in a finite-measure set `S`,
`ofReal (∫ω∫e∫_{[0,T]} h²) = ∫⁻ω∫⁻e∫⁻_{[0,T]} ‖h‖²`. (Nested
`ofReal_integral_eq_lintegral_ofReal`; integrability at each level from the bound and
the finite mark support.) -/
lemma triple_ofReal_integral_eq_lintegral
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (h : Ω → ℝ → E → ℝ) (hmeas : Measurable (fun p : Ω × ℝ × E => h p.1 p.2.1 p.2.2))
    {C : ℝ} (hC : ∀ ω s e, |h ω s e| ≤ C) {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ S → h ω s e = 0) :
    ENNReal.ofReal (∫ ω, ∫ e, ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume ∂ν ∂P)
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖h ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  classical
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set vT : ℝ := (volume (Set.Icc (0 : ℝ) T)).toReal with hvT
  have hvT0 : 0 ≤ vT := ENNReal.toReal_nonneg
  -- innermost `s`-integrand measurability and integrability.
  have hsm : ∀ ω e, Measurable (fun s => (h ω s e) ^ 2) := fun ω e =>
    ((hmeas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))).pow_const 2)
  have hsint : ∀ ω e, MeasureTheory.Integrable (fun s => (h ω s e) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun ω e =>
    MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (C ^ 2))
      (hsm ω e).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hC ω s e, abs_nonneg (h ω s e), sq_abs (h ω s e)]))
  set g1 : Ω → E → ℝ := fun ω e => ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume with hg1
  have hg1_nonneg : ∀ ω e, 0 ≤ g1 ω e := fun ω e =>
    MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
  have hg1_supp : ∀ ω e, e ∉ S → g1 ω e = 0 := fun ω e he => by
    change ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume = 0
    have hz : ∀ s, (h ω s e) ^ 2 = 0 := fun s => by rw [hsupp ω s e he]; ring
    simp only [hz, integral_zero]
  have hg1_bound : ∀ ω e, g1 ω e ≤ C ^ 2 * vT := fun ω e => by
    calc g1 ω e ≤ ∫ _s in Set.Icc (0 : ℝ) T, C ^ 2 ∂volume :=
          MeasureTheory.setIntegral_mono_on (hsint ω e)
            (MeasureTheory.integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
            (fun s _ => by nlinarith [hC ω s e, abs_nonneg (h ω s e), sq_abs (h ω s e)])
      _ = C ^ 2 * vT := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm, hvT,
              MeasureTheory.measureReal_def]
  -- joint measurability of `g1` and its `ν`-integral.
  have hg1m : Measurable (fun q : Ω × E => g1 q.1 q.2) := by
    have hr : Measurable (fun p : (Ω × E) × ℝ => (h p.1.1 p.2 p.1.2) ^ 2) :=
      ((hmeas.comp (by fun_prop : Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2)
        : Ω × ℝ × E))).pow_const 2)
    exact (hr.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable
  have hdom_e : MeasureTheory.Integrable (S.indicator (fun _ => C ^ 2 * vT)) ν :=
    (MeasureTheory.integrable_indicator_iff hS).mpr (MeasureTheory.integrableOn_const hSfin)
  have heint : ∀ ω, MeasureTheory.Integrable (fun e => g1 ω e) ν := fun ω =>
    MeasureTheory.Integrable.mono' hdom_e
      (hg1m.comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => by
        by_cases he : e ∈ S
        · rw [Set.indicator_of_mem he, Real.norm_eq_abs, abs_of_nonneg (hg1_nonneg ω e)]
          exact hg1_bound ω e
        · rw [Set.indicator_of_notMem he, hg1_supp ω e he, norm_zero]))
  set g2 : Ω → ℝ := fun ω => ∫ e, g1 ω e ∂ν with hg2
  have hg2_nonneg : ∀ ω, 0 ≤ g2 ω := fun ω =>
    MeasureTheory.integral_nonneg (fun e => hg1_nonneg ω e)
  have hg2m : Measurable g2 :=
    (hg1m.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have homega : MeasureTheory.Integrable g2 P :=
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const ((C ^ 2 * vT) * (ν S).toReal)) hg2m.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg2_nonneg ω)]
        calc g2 ω = ∫ e, g1 ω e ∂ν := rfl
          _ ≤ ∫ e, S.indicator (fun _ => C ^ 2 * vT) e ∂ν :=
              MeasureTheory.integral_mono (heint ω) hdom_e (fun e => by
                by_cases he : e ∈ S
                · rw [Set.indicator_of_mem he]; exact hg1_bound ω e
                · rw [Set.indicator_of_notMem he, hg1_supp ω e he])
          _ = (C ^ 2 * vT) * (ν S).toReal := by
              rw [MeasureTheory.integral_indicator hS, MeasureTheory.setIntegral_const,
                smul_eq_mul, mul_comm, MeasureTheory.measureReal_def]))
  -- nested `ofReal` ↦ `∫⁻`.
  rw [show (∫ ω, ∫ e, ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume ∂ν ∂P) = ∫ ω, g2 ω ∂P
      from rfl,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal homega
      (Filter.Eventually.of_forall hg2_nonneg)]
  refine lintegral_congr (fun ω => ?_)
  rw [hg2, MeasureTheory.ofReal_integral_eq_lintegral_ofReal (heint ω)
    (Filter.Eventually.of_forall (fun e => hg1_nonneg ω e))]
  refine lintegral_congr (fun e => ?_)
  rw [hg1, MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsint ω e)
    (Filter.Eventually.of_forall (fun s => sq_nonneg _))]
  refine lintegral_congr (fun s => ?_)
  rw [show ((h ω s e) ^ 2) = ‖h ω s e‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs],
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark-step eval is uniformly bounded (finite sum of bounded-coeff × indicators). -/
lemma markEval_bounded {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) :
    ∃ C, ∀ ω s e, |∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator
        (fun _ => (1 : ℝ)) s * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e| ≤ C := by
  classical
  refine ⟨∑ i : Fin N₀, ∑ k, (hcib i k).choose, fun ω s e => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (by rw [Set.indicator_apply]; split_ifs <;>
    simp)).trans ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_)))
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (by rw [Set.indicator_apply]; split_ifs <;>
    simp)).trans ((hcib i k).choose_spec ω)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark-step eval vanishes for marks outside the (shared) support set `S`. -/
lemma markEval_supp {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    {S : Set E} (hBiS : ∀ i k, Bi i k ⊆ S) (ω : Ω) (s : ℝ) (e : E) (he : e ∉ S) :
    (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
      * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Finset.sum_eq_zero (fun k _ => ?_), mul_zero]
  rw [Set.indicator_of_notMem (fun h => he (hBiS i k h)), mul_zero]

/-- Joint `(ω,s,e)`-measurability of the mark-step eval. -/
lemma markEval_measurable {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hcim : ∀ i k, Measurable (ci i k)) :
    Measurable (fun q : Ω × ℝ × E => ∑ i : Fin N₀,
      (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) q.2.1
      * ∑ k, ci i k q.1 * (Bi i k).indicator (fun _ => (1 : ℝ)) q.2.2) := by
  refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.comp measurable_snd)
  · refine Finset.measurable_sum _ (fun k _ => Measurable.mul ?_ ?_)
    · exact (hcim i k).comp measurable_fst
    · exact (measurable_const.indicator (hBim i k)).comp (measurable_snd.comp measurable_snd)

/-- **Cross-resolution difference isometry.** For two step approximants at dyadic
levels `n ≤ m`, the `L²(P)` distance of the integrals equals the `L²(P⊗vol⊗ν)`
distance of the integrands. The level-`n` integral/eval are re-expressed on the
level-`m` partition (`stepIntegral_dyadic_refine_integral`/`_eval`), reducing to the
same-partition `markStepIntegral_diff_isometry`. -/
lemma stepIntegral_crossres_diff_isometry
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {n
      m : ℕ}
    (hnm : n ≤ m)
    {Ki1 : Fin (2 ^ n) → ℕ} {Ki2 : Fin (2 ^ m) → ℕ}
    (Bi1 : ∀ i, Fin (Ki1 i) → Set E) (Bi2 : ∀ i, Fin (Ki2 i) → Set E)
    (ci1 : ∀ i, Fin (Ki1 i) → Ω → ℝ) (ci2 : ∀ i, Fin (Ki2 i) → Ω → ℝ)
    (hBi1m : ∀ i k, MeasurableSet (Bi1 i k)) (hBi2m : ∀ i k, MeasurableSet (Bi2 i k))
    (hBi1f : ∀ i k, ν (Bi1 i k) ≠ ⊤) (hBi2f : ∀ i k, ν (Bi2 i k) ≠ ⊤)
    (hci1b : ∀ i k, ∃ M, ∀ ω, |ci1 i k ω| ≤ M) (hci2b : ∀ i k, ∃ M, ∀ ω, |ci2 i k ω| ≤ M)
    (hci1m : ∀ i k, Measurable (ci1 i k)) (hci2m : ∀ i k, Measurable (ci2 i k))
    (hci1a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T n i.castSucc)) (ci1 i k))
    (hci2a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T m i.castSucc)) (ci2 i k)) :
    ∫ ω, ((∑ i : Fin (2 ^ n), ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        ((∑ i : Fin (2 ^ n), (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci1 i k₀ ω * (Bi1 i k₀).indicator (fun _ => (1 : ℝ)) e)
          - ∑ i : Fin (2 ^ m), (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci2 i k₀ ω * (Bi2 i k₀).indicator (fun _ => (1 : ℝ)) e) ^ 2
        ∂volume ∂ν) ∂P := by
  -- diff isometry on (refined level-n family, level-m family) over the level-m partition.
  have hdiff := markStepIntegral_diff_isometry N ℱ hℱ (dyadicPartition T m)
    (dyadicPartition_zero T m) (dyadicPartition_strictMono hT m) (dyadicPartition_le_T hT m)
    (fun i' => Bi1 (dyadicCoarse n m hnm i')) Bi2
    (fun i' => ci1 (dyadicCoarse n m hnm i')) ci2
    (fun i' k => hBi1m _ k) hBi2m (fun i' k => hBi1f _ k) hBi2f
    (fun i' k => hci1b _ k) hci2b (fun i' k => hci1m _ k) hci2m
    (fun i' k => dyadic_refine_adapted N ℱ hT hnm ci1 hci1a i' k) hci2a
  have hrefI := stepIntegral_dyadic_refine_integral N hT hnm Bi1 ci1 hBi1m hBi1f
  have hrefE := stepIntegral_dyadic_refine_eval (E := E) hT hnm Bi1 ci1
  rw [show ∫ ω, ((∑ i : Fin (2 ^ n), ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, ((∑ i' : Fin (2 ^ m), ∑ k₀, ci1 (dyadicCoarse n m hnm i') k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc)
              (dyadicPartition T m i'.succ) ×ˢ Bi1 (dyadicCoarse n m hnm i') k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P from by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hrefI] with ω h
    rw [h]]
  rw [hdiff]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  refine congrArg _ (funext (fun e => ?_))
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [hrefE s ω e]

/-- **Euler-sum `L²(P)` Cauchy bound.** For dyadic levels `a ≤ b`, the squared
`L²(P)`-distance of the two Euler step integrals is bounded by `2·(L²-density error at a)
+ 2·(at b)`: chain the bridge `∫⁻‖·‖²=ofReal∫(·)²`, the cross-resolution diff isometry,
the triple real↔`ℝ≥0∞` bridge, a Tonelli swap, and the `2(a²+b²)` triangle against `φ`. -/
lemma eulerStepIntegral_cauchy_le
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) (φ
      : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤) {a b : ℕ} (hab : a ≤ b)
    {Kia : Fin (2 ^ a) → ℕ} {Kib : Fin (2 ^ b) → ℕ}
    (Bia : ∀ i, Fin (Kia i) → Set E) (Bib : ∀ i, Fin (Kib i) → Set E)
    (cia : ∀ i, Fin (Kia i) → Ω → ℝ) (cib : ∀ i, Fin (Kib i) → Ω → ℝ)
    (hBiam : ∀ i k, MeasurableSet (Bia i k)) (hBibm : ∀ i k, MeasurableSet (Bib i k))
    (hBiaS : ∀ i k, Bia i k ⊆ S) (hBibS : ∀ i k, Bib i k ⊆ S)
    (hciab : ∀ i k, ∃ M, ∀ ω, |cia i k ω| ≤ M) (hcibb : ∀ i k, ∃ M, ∀ ω, |cib i k ω| ≤ M)
    (hciam : ∀ i k, Measurable (cia i k)) (hcibm : ∀ i k, Measurable (cib i k))
    (hciaa : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T a i.castSucc)) (cia i k))
    (hciba : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T b i.castSucc)) (cib i k)) :
    ∫⁻ ω, (‖(∑ i : Fin (2 ^ a), ∑ k, cia i k ω
          * N.compensated (Set.Ioc (dyadicPartition T a i.castSucc)
              (dyadicPartition T a i.succ) ×ˢ Bia i k) ω)
        - ∑ i : Fin (2 ^ b), ∑ k, cib i k ω
          * N.compensated (Set.Ioc (dyadicPartition T b i.castSucc)
              (dyadicPartition T b i.succ) ×ˢ Bib i k) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e
            - ∑ i : Fin (2 ^ a), (Set.Ioc (dyadicPartition T a i.castSucc)
                (dyadicPartition T a i.succ)).indicator (fun _ => (1 : ℝ)) s
              * ∑ k, cia i k ω * (Bia i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
                ∂P)
        + 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e
            - ∑ i : Fin (2 ^ b), (Set.Ioc (dyadicPartition T b i.castSucc)
                (dyadicPartition T b i.succ)).indicator (fun _ => (1 : ℝ)) s
              * ∑ k, cib i k ω * (Bib i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
                ∂P) := by
  have hBiaf : ∀ i k, ν (Bia i k) ≠ ⊤ := fun i k => ne_top_of_le_ne_top hSfin (measure_mono (hBiaS
    i k))
  have hBibf : ∀ i k, ν (Bib i k) ≠ ⊤ := fun i k => ne_top_of_le_ne_top hSfin (measure_mono (hBibS
    i k))
  set ea : Ω → ℝ → E → ℝ := fun ω s e => ∑ i : Fin (2 ^ a),
    (Set.Ioc (dyadicPartition T a i.castSucc) (dyadicPartition T a i.succ)).indicator
      (fun _ => (1 : ℝ)) s * ∑ k, cia i k ω * (Bia i k).indicator (fun _ => (1 : ℝ)) e with hea
  set eb : Ω → ℝ → E → ℝ := fun ω s e => ∑ i : Fin (2 ^ b),
    (Set.Ioc (dyadicPartition T b i.castSucc) (dyadicPartition T b i.succ)).indicator
      (fun _ => (1 : ℝ)) s * ∑ k, cib i k ω * (Bib i k).indicator (fun _ => (1 : ℝ)) e with heb
  obtain ⟨Ca, hCa⟩ := markEval_bounded (dyadicPartition T a) Bia cia hciab
  obtain ⟨Cb, hCb⟩ := markEval_bounded (dyadicPartition T b) Bib cib hcibb
  have hh_bdd : ∀ ω s e, |ea ω s e - eb ω s e| ≤ Ca + Cb := fun ω s e =>
    (abs_sub _ _).trans (add_le_add (hCa ω s e) (hCb ω s e))
  have hh_supp : ∀ ω s e, e ∉ S → ea ω s e - eb ω s e = 0 := fun ω s e he => by
    simp only [hea, heb]
    rw [markEval_supp (dyadicPartition T a) Bia cia hBiaS ω s e he,
      markEval_supp (dyadicPartition T b) Bib cib hBibS ω s e he, sub_zero]
  have hh_meas : Measurable (fun p : Ω × ℝ × E => ea p.1 p.2.1 p.2.2 - eb p.1 p.2.1 p.2.2) :=
    (markEval_measurable (dyadicPartition T a) Bia cia hBiam hciam).sub
      (markEval_measurable (dyadicPartition T b) Bib cib hBibm hcibm)
  have hmemdiff : MeasureTheory.MemLp (fun ω => (∑ i : Fin (2 ^ a), ∑ k, cia i k ω
        * N.compensated (Set.Ioc (dyadicPartition T a i.castSucc)
            (dyadicPartition T a i.succ) ×ˢ Bia i k) ω)
      - ∑ i : Fin (2 ^ b), ∑ k, cib i k ω
        * N.compensated (Set.Ioc (dyadicPartition T b i.castSucc)
            (dyadicPartition T b i.succ) ×ˢ Bib i k) ω) 2 P :=
    (eulerStepIntegral_memLp N (dyadicPartition T a) Bia cia hBiam hBiaf hciab hciam).sub
      (eulerStepIntegral_memLp N (dyadicPartition T b) Bib cib hBibm hBibf hcibb hcibm)
  rw [lintegral_sq_eq_ofReal_integral hmemdiff,
    stepIntegral_crossres_diff_isometry N ℱ hℱ hT hab Bia Bib cia cib hBiam hBibm hBiaf hBibf
      hciab hcibb hciam hcibm hciaa hciba,
    triple_ofReal_integral_eq_lintegral (fun ω s e => ea ω s e - eb ω s e) hh_meas hh_bdd hS hSfin
      hh_supp]
  -- swap the `e` and `s` integrals to the density order.
  have hswap : ∀ ω, (∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖ea ω s e - eb ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂ν)
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖ea ω s e - eb ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    rw [MeasureTheory.lintegral_lintegral_swap]
    exact ((ENNReal.continuous_coe.measurable.comp
      (((hh_meas.comp (by fun_prop : Measurable fun q : E × ℝ =>
        ((ω, q.2, q.1) : Ω × ℝ × E)))).nnnorm)).pow_const 2).aemeasurable
  simp_rw [hswap]
  -- pointwise `2(a²+b²)` triangle against `φ`.
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖ea ω s e - eb ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (2 * (‖φ ω s e - ea ω s e‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ ω s e - eb ω s e‖₊ : ℝ≥0∞) ^ 2)
          ∂ν ∂volume ∂P := by
        refine lintegral_mono (fun ω => lintegral_mono (fun s => lintegral_mono (fun e => ?_)))
        have h := sq_nnnorm_add_le_two_mul (ea ω s e - φ ω s e) (φ ω s e - eb ω s e)
        rw [show ea ω s e - φ ω s e + (φ ω s e - eb ω s e) = ea ω s e - eb ω s e from by ring,
          show (‖ea ω s e - φ ω s e‖₊ : ℝ≥0∞) = ‖φ ω s e - ea ω s e‖₊ from by
            rw [show φ ω s e - ea ω s e = -(ea ω s e - φ ω s e) from by ring, nnnorm_neg],
          mul_add] at h
        exact h
      _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e - ea ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          + 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e - eb ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
        rw [lintegral_triple_add
          ((ENNReal.continuous_coe.measurable.comp
            ((h_meas.sub (markEval_measurable (dyadicPartition T a) Bia cia hBiam
              hciam)).nnnorm)).pow_const 2 |>.const_mul 2),
          lintegral_triple_const_mul 2 (by norm_num) _, lintegral_triple_const_mul 2 (by norm_num)
            _]

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊²`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {P : Measure Ω} (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g P) :
    MeasureTheory.eLpNorm g 2 P ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := (2 : ℝ≥0))
    (f := g) (by norm_num) hg
  rw [show ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
    show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl

/-- **Dissertation #2(B): the compensated Euler sums converge in `L²(P)`.** For a
bounded, progressively measurable `φ` with finite mark support, there is an
`L²(P)` random variable `F` (the L²-Itô-Lévy integral) such that the adapted Euler
step integrals `∑ᵢ∑ₖ ciₖⁿ·Ñ((pᵢⁿ,pᵢ₊₁ⁿ]×Biₖⁿ)` converge to `F` in `L²(P)`.
Assembles the density (`exists_markEval_L2_tendsto`), the cross-resolution Cauchy
bound (`eulerStepIntegral_cauchy_le`), and `Lp`-completeness
(`exists_L2_limit_of_memLp_cauchySeq`). -/
theorem compensated_eulerSum_L2_limit
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) (φ
      : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    ∃ (Ki : (n : ℕ) → Fin (2 ^ n) → ℕ)
      (Bi : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Set E)
      (ci : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Ω → ℝ) (F : Ω → ℝ),
      MeasureTheory.MemLp F 2 P ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        ((fun ω => ∑ i : Fin (2 ^ n), ∑ k, ci n i k ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi n i k) ω) - F) 2 P) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨Ki, Bi, ci, hBim, hBiS, hcia, hcib, htend⟩ :=
    exists_markEval_L2_tendsto N ℱ hT φ h_meas h_progMeas hM hS hSfin hSupp
  have hcim : ∀ n i k, Measurable (ci n i k) := fun n i k =>
    (hcia n i k).measurable.mono (ℱ.le _) le_rfl
  set I : ℕ → Ω → ℝ := fun n ω => ∑ i : Fin (2 ^ n), ∑ k, ci n i k ω
    * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
        (dyadicPartition T n i.succ) ×ˢ Bi n i k) ω with hI
  have hImem : ∀ n, MeasureTheory.MemLp (I n) 2 P := fun n =>
    eulerStepIntegral_memLp N (dyadicPartition T n) (Bi n) (ci n) (hBim n)
      (fun i k => ne_top_of_le_ne_top hSfin (measure_mono (hBiS n i k))) (hcib n) (hcim n)
  set Aφ : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e - ∑ i : Fin (2 ^ n),
      (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
        (fun _ => (1 : ℝ)) s * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e‖₊
      : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P with hAφ
  have hcauchy : CauchySeq (fun n => (hImem n).toLp (I n)) := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨0, fun m _ n _ => by rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)⟩
    set δ : ℝ≥0∞ := ε ^ (2 : ℝ) / 4 with hδ
    have hδ_pos : 0 < δ := ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (htend (Iio_mem_nhds hδ_pos))
    refine ⟨N0, fun m hm n hn => ?_⟩
    rw [MeasureTheory.Lp.edist_toLp_toLp]
    have hsq : MeasureTheory.eLpNorm (I m - I n) 2 P ^ (2 : ℝ) < ε ^ (2 : ℝ) := by
      rw [eLpNorm_two_rpow_eq_lintegral_sq _ ((hImem m).sub (hImem n)).aestronglyMeasurable]
      have hle : ∫⁻ ω, (‖(I m - I n) ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 2 * Aφ m + 2 * Aφ n := by
        change ∫⁻ ω, (‖I m ω - I n ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 2 * Aφ m + 2 * Aφ n
        rcases le_total m n with hmn | hnm
        · exact eulerStepIntegral_cauchy_le N ℱ hℱ hT φ h_meas hS hSfin hmn (Bi m) (Bi n) (ci m)
            (ci n)
            (hBim m) (hBim n) (hBiS m) (hBiS n) (hcib m) (hcib n) (hcim m) (hcim n)
            (hcia m) (hcia n)
        · rw [show (fun ω => (‖I m ω - I n ω‖₊ : ℝ≥0∞) ^ 2)
                = (fun ω => (‖I n ω - I m ω‖₊ : ℝ≥0∞) ^ 2) from funext (fun ω => by
              rw [show I m ω - I n ω = -(I n ω - I m ω) from by ring, nnnorm_neg]),
            add_comm (2 * Aφ m)]
          exact eulerStepIntegral_cauchy_le N ℱ hℱ hT φ h_meas hS hSfin hnm (Bi n) (Bi m) (ci n)
            (ci m)
            (hBim n) (hBim m) (hBiS n) (hBiS m) (hcib n) (hcib m) (hcim n) (hcim m)
            (hcia n) (hcia m)
      refine lt_of_le_of_lt hle ?_
      calc 2 * Aφ m + 2 * Aφ n = Aφ m * 2 + Aφ n * 2 := by ring
        _ < δ * 2 + δ * 2 :=
            ENNReal.add_lt_add
              (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) (hN0 m hm))
              (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) (hN0 n hn))
        _ = ε ^ (2 : ℝ) := by
            rw [show δ * 2 + δ * 2 = 4 * δ from by ring, hδ,
              ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hsq
  obtain ⟨F, hF_mem, hF_tend⟩ := exists_L2_limit_of_memLp_cauchySeq hImem hcauchy
  exact ⟨Ki, Bi, ci, F, hF_mem, hF_tend⟩

/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

/-- **Right-continuity of a monotone `ℝ≥0∞` function from sequential right-continuity.**
If `g` is monotone and `g (t + 1/(n+1)) → g t`, then `g` is right-continuous at `t`. -/
lemma monotone_tendsto_nhdsWithin_Ioi {g : ℝ → ℝ≥0∞} (hg : Monotone g) {t : ℝ}
    (hseq : Filter.Tendsto (fun n : ℕ => g (t + 1 / (n + 1))) Filter.atTop (nhds (g t))) :
    Filter.Tendsto g (nhdsWithin t (Set.Ioi t)) (nhds (g t)) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun s hs => ?_))
    exact hl.trans_le (hg (le_of_lt hs))
  · obtain ⟨N, hN⟩ := (hseq.eventually_lt_const hu).exists
    have hδ : t < t + 1 / ((N : ℝ) + 1) := lt_add_of_pos_right t (by positivity)
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [Iio_mem_nhds hδ] with s hs
    exact (hg (le_of_lt hs)).trans_lt hN

/-- **Left-limit existence for a monotone `ℝ≥0∞` function.** A monotone function has a
left limit at `t`, namely `⨆_{s<t} g s` (no continuity hypothesis needed). -/
lemma monotone_tendsto_nhdsWithin_Iio {g : ℝ → ℝ≥0∞} (hg : Monotone g) (t : ℝ) :
    Filter.Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (⨆ s : {s : ℝ // s < t}, g s.1)) := by
  set L : ℝ≥0∞ := ⨆ s : {s : ℝ // s < t}, g s.1 with hL
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · -- `l < L = ⨆ g s`, so some `s₀ < t` has `l < g s₀`; for `s ∈ (s₀, t)`, `g s ≥ g s₀ > l`.
    rw [hL, lt_iSup_iff] at hl
    obtain ⟨⟨s₀, hs₀t⟩, hs₀⟩ := hl
    refine Filter.eventually_inf_principal.mpr ?_
    filter_upwards [Ioi_mem_nhds hs₀t] with s hs _
    exact hs₀.trans_le (hg (le_of_lt hs))
  · -- `g s ≤ L < u` for all `s < t`.
    refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun s hs => ?_))
    exact lt_of_le_of_lt (le_iSup (fun s : {s : ℝ // s < t} => g s.1) ⟨s, hs⟩) hu

/-- The clamped time-rectangle base `(min a s, min b s]` grows with `s` (for `a ≤ b`):
when `s ≤ a` it is empty, and for `s > a` it is `(a, min b s]`, increasing in `s`. -/
lemma minIoc_subset {a b : ℝ} (hab : a ≤ b) {s s' : ℝ} (hss : s ≤ s') :
    Set.Ioc (min a s) (min b s) ⊆ Set.Ioc (min a s') (min b s') := by
  rintro x ⟨hx1, hx2⟩
  by_cases hsa : s ≤ a
  · rw [min_eq_right hsa] at hx1
    rw [min_eq_right (hsa.trans hab)] at hx2
    exact absurd (hx1.trans_le hx2) (lt_irrefl s)
  · push Not at hsa
    refine ⟨?_, hx2.trans (min_le_min (le_refl b) hss)⟩
    rw [min_eq_left (hsa.le.trans hss)]
    rwa [min_eq_left hsa.le] at hx1

/-- The clamped base `(min a s, min b s]` is always contained in `(a, b]` (for `a ≤ b`). -/
lemma minIoc_subset_Ioc {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Set.Ioc (min a s) (min b s) ⊆ Set.Ioc a b := by
  rintro x ⟨hx1, hx2⟩
  by_cases hsa : s ≤ a
  · rw [min_eq_right hsa] at hx1
    rw [min_eq_right (hsa.trans hab)] at hx2
    exact absurd (hx1.trans_le hx2) (lt_irrefl s)
  · push Not at hsa
    rw [min_eq_left hsa.le] at hx1
    exact ⟨hx1, hx2.trans (min_le_left b s)⟩

/-- **Count-part right-continuity.** For `a ≤ b`, a finite-mass mark set `A`, and a
measure `m` finite on `(a,b]×A`, the clamped count `s ↦ m((min a s, min b s]×A)` is
right-continuous (measure continuity from above along `t + 1/(n+1) ↓ t`). -/
lemma measure_minIoc_prod_rightCont (m : Measure (ℝ × E)) {a b : ℝ} (hab : a ≤ b)
    {A : Set E} (hA : MeasurableSet A) (hfin : m (Set.Ioc a b ×ˢ A) ≠ ⊤) (t : ℝ) :
    Filter.Tendsto (fun s => m (Set.Ioc (min a s) (min b s) ×ˢ A))
      (nhdsWithin t (Set.Ioi t)) (nhds (m (Set.Ioc (min a t) (min b t) ×ˢ A))) := by
  have hgmono : Monotone (fun s => m (Set.Ioc (min a s) (min b s) ×ˢ A)) := fun s s' hss =>
    measure_mono (Set.prod_mono (minIoc_subset hab hss) (le_refl A))
  refine monotone_tendsto_nhdsWithin_Ioi hgmono ?_
  set u : ℕ → ℝ := fun n => t + 1 / ((n : ℝ) + 1) with hu
  have htu : ∀ n, t ≤ u n := fun n => le_add_of_nonneg_right (by positivity)
  have hu_anti : Antitone u := by
    intro n n' hnn
    simp only [hu]
    have h : (1 : ℝ) / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn 1)
    linarith
  have hut : Filter.Tendsto u Filter.atTop (nhds t) := by
    have h0 : Filter.Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (t + 0)) :=
      Filter.Tendsto.const_add t tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hu] using h0
  have hset_anti : Antitone (fun n => Set.Ioc (min a (u n)) (min b (u n)) ×ˢ A) :=
    fun n n' hnn => Set.prod_mono (minIoc_subset hab (hu_anti hnn)) (le_refl A)
  have hInter : ⋂ n, Set.Ioc (min a (u n)) (min b (u n)) ×ˢ A
      = Set.Ioc (min a t) (min b t) ×ˢ A := by
    refine Set.Subset.antisymm (fun x hx => ?_)
      (Set.subset_iInter (fun n => Set.prod_mono (minIoc_subset hab (htu n)) (le_refl A)))
    rw [Set.mem_iInter] at hx
    refine Set.mem_prod.mpr ⟨⟨?_, ?_⟩, (Set.mem_prod.mp (hx 0)).2⟩
    · exact lt_of_le_of_lt (min_le_min (le_refl a) (htu 0)) (Set.mem_prod.mp (hx 0)).1.1
    · exact ge_of_tendsto' (tendsto_const_nhds.min hut)
        (fun n => (Set.mem_prod.mp (hx n)).1.2)
  have hfin0 : m (Set.Ioc (min a (u 0)) (min b (u 0)) ×ˢ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono (Set.prod_mono (minIoc_subset_Ioc hab (u 0)) (le_refl
      A)))
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (measurableSet_Ioc.prod hA).nullMeasurableSet) hset_anti ⟨0, hfin0⟩
  rw [hInter] at hlim
  exact hlim

end LevyStochCalc.Poisson.Compensated
