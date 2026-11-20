/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the measurability argument now
-- required by `eLpNorm_nnreal_pow_eq_lintegral` in Mathlib v4.35.0 (proof-only change).
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityRectSimple

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] in
/-- **Adapted mark-discretisation (per-time-piece).** A bounded `h : Ω → E → ℝ` that
is `m ⊗ E`-measurable (for a sub-σ-algebra `m ≤ m₀`) and supported on marks in a
finite-measure set `S` is approximated in `L²(P ⊗ ν)` by a finite mark-simple function
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` whose mark sets `Bₖ ⊆ S` and whose coefficients `cₖ` are bounded
and `m`-measurable (hence adapted). Runs `rectSimple_dense_L2` on the trimmed product
`(P.trim hm) ⊗ (ν|S)` to force `m`-measurable rectangle sides, then transfers the bound
back through `lintegral_prod_trim_left`. -/
lemma exists_markSimple_adapted_within
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} [@IsFiniteMeasure Ω m0 P]
    {ν : Measure E} [SigmaFinite ν]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (h : Ω → E → ℝ)
    (h_meas : @Measurable (Ω × E) ℝ (m.prod inferInstance) _ (fun q => h q.1 q.2))
    {C : ℝ} (h_bdd : ∀ ω e, |h ω e| ≤ C)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω e, e ∉ S → h ω e = 0)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (K : ℕ) (B : Fin K → Set E) (c : Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ S) ∧
      (∀ k, @Measurable Ω ℝ m _ (c k)) ∧
      (∀ k, ∃ M, ∀ ω, |c k ω| ≤ M) ∧
      ∫⁻ ω, ∫⁻ e, (‖h ω e
          - ∑ k, c k ω * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P ≤ δ := by
  classical
  -- finite product measure on the trimmed space.
  have hPt : IsFiniteMeasure (P.trim hm) := MeasureTheory.isFiniteMeasure_trim hm
  have hνS : IsFiniteMeasure (ν.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
  set μ : @Measure (Ω × E) (m.prod inferInstance) := (P.trim hm).prod (ν.restrict S) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set f : Ω × E → ℝ := fun q => h q.1 q.2 with hf
  -- `f ∈ L²(μ)`: bounded on a finite measure.
  have hmem : MeasureTheory.MemLp f 2 μ := by
    refine MeasureTheory.MemLp.mono_exponent ?_ (le_top)
    refine MeasureTheory.memLp_top_of_bound h_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs]; exact h_bdd q.1 q.2)
  -- tolerance `ε' = √δ`, so `ε'² = δ`.
  set ε' : ℝ≥0∞ := δ ^ (1 / 2 : ℝ) with hε'
  have hε'0 : ε' ≠ 0 := by
    rw [hε', Ne, ENNReal.rpow_eq_zero_iff]; push Not
    exact ⟨fun h0 => absurd h0 hδ, fun _ => by norm_num⟩
  obtain ⟨g, hg_rs, hg_err⟩ :=
    @rectSimple_dense_L2 Ω m E _ μ _ f hmem ε' hε'0
  obtain ⟨K, a, A, B, hA, hB, hgeq⟩ := @IsRectSimple.eq_finSum Ω m E _ g hg_rs
  -- repackage into a `Fin`-indexed mark-simple family (mark sides ∩ S).
  refine ⟨K, fun k => B k ∩ S, fun k ω => a k * (A k).indicator (fun _ => (1 : ℝ)) ω,
    fun k => (hB k).inter hS, fun k => Set.inter_subset_right, ?_, ?_, ?_⟩
  · intro k
    exact measurable_const.mul (Measurable.indicator measurable_const (hA k))
  · exact fun k => ⟨|a k|, fun ω => by
      rw [abs_mul]
      calc |a k| * |(A k).indicator (fun _ => (1 : ℝ)) ω|
          ≤ |a k| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [Set.indicator_apply]; split_ifs <;> simp
        _ = |a k| := mul_one _⟩
  -- the eval reproduces `g · 𝟙_S` in the mark.
  have heval : ∀ ω e, (∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
        * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e)
      = g (ω, e) * S.indicator (fun _ => (1 : ℝ)) e := by
    intro ω e
    rw [hgeq ω e, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (B k ∩ S).indicator (fun _ => (1 : ℝ)) e
          = (B k).indicator (fun _ => (1 : ℝ)) e * S.indicator (fun _ => (1 : ℝ)) e from by
      simp only [Set.indicator_apply, Set.mem_inter_iff]
      by_cases hk : e ∈ B k <;> by_cases hs : e ∈ S <;> simp [hk, hs]]
    ring
  -- transfer the `L²` bound through the trim bridge; the difference is supported on `S`.
  have hg_meas : @Measurable (Ω × E) ℝ (m.prod inferInstance) _ g :=
    @IsRectSimple.measurable Ω m E _ g hg_rs
  have hFmeas : @Measurable (Ω × E) ℝ≥0∞ (m.prod inferInstance) _
      (fun q => (‖f q - g q‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.sub hg_meas).nnNorm).pow_const 2
  have hpt : ∀ ω e, (‖h ω e - ∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
        * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
      = S.indicator (fun e' => (‖h ω e' - g (ω, e')‖₊ : ℝ≥0∞) ^ 2) e := by
    intro ω e
    rw [heval ω e]
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he, Set.indicator_of_mem he, mul_one]
    · rw [Set.indicator_of_notMem he, mul_zero, sub_zero, hsupp ω e he,
      Set.indicator_of_notMem he]
      simp
  calc ∫⁻ ω, ∫⁻ e, (‖h ω e - ∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
          * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
      = ∫⁻ ω, ∫⁻ e in S, (‖h ω e - g (ω, e)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := by
        refine lintegral_congr (fun ω => ?_)
        rw [← MeasureTheory.lintegral_indicator hS]
        exact lintegral_congr (fun e => hpt ω e)
    _ = ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂((P.trim hm).prod (ν.restrict S)) :=
        (lintegral_prod_trim_left hm hFmeas).symm
    _ ≤ δ := by
        rw [← hμ]
        have hsq : MeasureTheory.eLpNorm (f - g) 2 μ ^ (2 : ℝ)
            = ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
          have hL := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
            (μ := μ) (p := (2 : ℝ≥0)) (f := f - g) (by norm_num)
            (h_meas.sub hg_meas).aestronglyMeasurable
          rw [show ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
            show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num] at hL
          rw [hL]; refine lintegral_congr (fun q => ?_)
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
        calc ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂μ
            = MeasureTheory.eLpNorm (f - g) 2 μ ^ (2 : ℝ) := hsq.symm
          _ ≤ ε' ^ (2 : ℝ) := ENNReal.rpow_le_rpow hg_err (by norm_num)
          _ = δ := by
              rw [hε', ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 from by norm_num,
                ENNReal.rpow_one]

/-- **Adaptedness of the shifted dyadic average (mark-jointly).** Under progressive
measurability of `φ`, the coefficient `(ω, e) ↦ dyadicAvgShifted T φ n i ω e` is
`(ℱ_{pᵢ} ⊗ E)`-measurable, where `pᵢ = dyadicPartition T n i.castSucc`. (Integrates
out the time variable from the `ℱ_{pᵢ} ⊗ Borel ⊗ E`-measurable integrand `φ`.) -/
lemma dyadicAvg_shifted_adapted_prod
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (n : ℕ) (i : Fin (2 ^ n)) :
    @Measurable (Ω × E) ℝ
      ((ℱ (dyadicPartition T n i.castSucc)).prod inferInstance) _
      (fun q : Ω × E => dyadicAvgShifted T φ n i q.1 q.2) := by
  unfold dyadicAvgShifted
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceDIte]; exact measurable_const
  · simp only [hi, ↓reduceDIte, dyadicAvg]
    set j : Fin (2 ^ n) := ⟨i.val - 1, by omega⟩ with hj
    have hsucc : dyadicPartition T n j.succ = dyadicPartition T n i.castSucc := by
      congr 1
      ext
      simp only [Fin.val_succ, Fin.val_castSucc, hj]
      omega
    -- The average over `(p_{i-1}, p_i] ⊆ (-∞, p_i]` is `ℱ p_i ⊗ 𝓔`-measurable.
    have hint : @Measurable (Ω × E) ℝ
        ((ℱ (dyadicPartition T n i.castSucc)).prod inferInstance) _
        (fun q : Ω × E => ∫ s in Set.Ioc (dyadicPartition T n j.castSucc)
          (dyadicPartition T n j.succ), φ q.1 s q.2) :=
      (h_progMeas.stronglyMeasurable_setIntegral_prod (t := dyadicPartition T n i.castSucc)
        (S := Set.Ioc (dyadicPartition T n j.castSucc) (dyadicPartition T n j.succ))
        measurableSet_Ioc
        (Set.Ioc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr hsucc.le)) volume).measurable
    have hfin := hint.const_mul ((2 ^ n : ℕ) / T : ℝ)
    convert hfin using 1

/-- **Disjoint-interval collapse of a squared indicator sum.** The intervals
`(pᵢ, pᵢ₊₁]` are pairwise disjoint (`p` strictly monotone), so at any `s` at most one
indicator fires and the squared norm of the weighted sum equals the sum of indicators
of the squared weights. -/
lemma sq_nnnorm_disjoint_indicator_sum
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hpmono : StrictMono p) (g : Fin N₀ → ℝ) (s : ℝ) :
    (‖∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * g i‖₊
        : ℝ≥0∞) ^ 2
      = ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator
          (fun _ => (‖g i‖₊ : ℝ≥0∞) ^ 2) s := by
  by_cases hex : ∃ i : Fin N₀, s ∈ Set.Ioc (p i.castSucc) (p i.succ)
  · obtain ⟨i₀, hi₀⟩ := hex
    have huniq : ∀ j : Fin N₀, j ≠ i₀ → s ∉ Set.Ioc (p j.castSucc) (p j.succ) := by
      intro j hj hmem
      rcases lt_trichotomy j i₀ with hlt | heq | hgt
      · have hle := hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        exact absurd hi₀.1 (not_lt.mpr (le_trans hmem.2 hle))
      · exact hj heq
      · have hle := hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        exact absurd hmem.1 (not_lt.mpr (le_trans hi₀.2 hle))
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
        rw [Set.indicator_of_notMem (huniq j hj), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
      Set.indicator_of_mem hi₀, one_mul,
      Finset.sum_eq_single i₀ (fun j _ hj => Set.indicator_of_notMem (huniq j hj) _)
        (fun h => absurd (Finset.mem_univ _) h),
      Set.indicator_of_mem hi₀]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun i _ => by rw [Set.indicator_of_notMem (hex i), zero_mul]),
      Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hex i) _)]
    simp

/-- `(‖x + y‖₊)² ≤ 2((‖x‖₊)² + (‖y‖₊)²)` in `ℝ≥0∞` (the `2(a²+b²)` triangle bound). -/
lemma sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _),
      show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

/-- **Mark-discretisation error of the shifted dyadic eval.** For each level `n` and
tolerance `δ`, there is a per-piece adapted mark-simple family approximating the shifted
dyadic eval within `T·δ` in `L²(P ⊗ vol ⊗ ν)`: each time-piece coefficient
`dyadicAvgShifted T φ n i` is mark-discretised (via `exists_markSimple_adapted_within`)
to within `δ` in `L²(P ⊗ ν)`, and the disjoint-interval collapse pays a factor
`∑ᵢ vol(pᵢ, pᵢ₊₁] = T`. -/
lemma exists_markEval_close_dyadic
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0)
    (n : ℕ) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (Ki : Fin (2 ^ n) → ℕ) (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ),
      (∀ i k, MeasurableSet (Bi i k)) ∧ (∀ i k, Bi i k ⊆ S) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci i k)) ∧
      (∀ i k, ∃ C, ∀ ω, |ci i k ω| ≤ C) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖dyadicEvalShifted T φ n s ω e
          - ∑ i : Fin (2 ^ n),
              (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
                (fun _ => (1 : ℝ)) s
              * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P ≤ ENNReal.ofReal T * δ := by
  classical
  -- per-piece mark approximation of each shifted dyadic average.
  have hpiece : ∀ i : Fin (2 ^ n), ∃ (K : ℕ) (B : Fin K → Set E) (c : Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ S) ∧
      (∀ k, @Measurable Ω ℝ
        (ℱ (dyadicPartition T n i.castSucc)) _ (c k)) ∧
      (∀ k, ∃ C, ∀ ω, |c k ω| ≤ C) ∧
      ∫⁻ ω, ∫⁻ e, (‖dyadicAvgShifted T φ n i ω e
          - ∑ k, c k ω * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P ≤ δ := by
    intro i
    have hsupp_i : ∀ ω e, e ∉ S → dyadicAvgShifted T φ n i ω e = 0 := by
      intro ω e he
      unfold dyadicAvgShifted
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte, dyadicAvg]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (fun s _ => hSupp ω e he s)]
        simp
    exact exists_markSimple_adapted_within (ℱ.le _)
      (dyadicAvgShifted T φ n i) (dyadicAvg_shifted_adapted_prod N ℱ T φ h_progMeas n i)
      (dyadicAvg_shifted_bounded hT φ hM n i) hS hSfin hsupp_i hδ
  choose Ki Bi ci hBim hBiS hcim hcib hci_err using hpiece
  refine ⟨Ki, Bi, ci, hBim, hBiS, fun i k => (hcim i k).stronglyMeasurable, hcib, ?_⟩
  -- abbreviations.
  set p := dyadicPartition T n with hp
  set d : Fin (2 ^ n) → Ω → E → ℝ := fun i ω e => dyadicAvgShifted T φ n i ω e with hd
  set mk : Fin (2 ^ n) → Ω → E → ℝ :=
    fun i ω e => ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e with hmk
  set W : Fin (2 ^ n) → Ω → ℝ≥0∞ :=
    fun i ω => ∫⁻ e, (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hW
  -- joint `(ω,e)`-measurability of each piece's squared difference.
  have hd2 : ∀ i, Measurable (fun q : Ω × E => d i q.1 q.2) :=
    fun i => dyadicAvg_shifted_measurable T φ h_meas n i
  have hmk2 : ∀ i, Measurable (fun q : Ω × E => mk i q.1 q.2) := by
    intro i
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact (((hcim i k).mono (ℱ.le _) le_rfl).comp
      measurable_fst).mul ((measurable_const.indicator (hBim i k)).comp measurable_snd)
  have hjoint : ∀ i, Measurable (fun q : Ω × E => (‖d i q.1 q.2 - mk i q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => (ENNReal.continuous_coe.measurable.comp ((hd2 i).sub (hmk2 i)).nnNorm).pow_const 2
  have hW_meas : ∀ i, Measurable (W i) := fun i => (hjoint i).lintegral_prod_right'
  -- pointwise collapse of the squared difference.
  have hcollapse : ∀ s ω e,
      (‖dyadicEvalShifted T φ n s ω e
        - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * mk i ω e‖₊ : ℝ≥0∞) ^ 2
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) s := by
    intro s ω e
    have hDES : dyadicEvalShifted T φ n s ω e
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * d i ω e := by
      unfold dyadicEvalShifted
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Set.indicator_apply]
      by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · rw [ite_eq_left (Set.mem_Ioc.mp hsi), ite_eq_left hsi, one_mul]
      · rw [ite_eq_right (fun hc => hsi (Set.mem_Ioc.mpr hc)), ite_eq_right hsi, zero_mul]
    rw [hDES, ← Finset.sum_sub_distrib]
    rw [show (∑ i : Fin (2 ^ n), ((Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (1 : ℝ)) s * d i ω e
          - (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * mk i ω e))
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * (d i ω e - mk i ω e) from by
      refine Finset.sum_congr rfl (fun i _ => by ring)]
    exact sq_nnnorm_disjoint_indicator_sum p (dyadicPartition_strictMono hT n)
      (fun i => d i ω e - mk i ω e) s
  -- measurability of each per-piece integrand in `e`.
  have hmk_meas : ∀ i ω, Measurable (fun e => mk i ω e) := by
    intro i ω
    exact Finset.measurable_sum _ (fun k _ => (measurable_const.mul
      (measurable_const.indicator (hBim i k))))
  have hd_meas : ∀ i ω, Measurable (fun e => d i ω e) :=
    fun i ω => (hd2 i).comp measurable_prodMk_left
  have hgi_meas : ∀ i ω, Measurable (fun e => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) := by
    intro i ω
    exact (ENNReal.continuous_coe.measurable.comp
      ((hd_meas i ω).sub (hmk_meas i ω)).nnNorm).pow_const 2
  -- collapse the `e`-integral to `∑ᵢ 𝟙_{Iᵢ}(s)·Wᵢ(ω)`.
  have h_e : ∀ s ω, ∫⁻ e,
      (‖dyadicEvalShifted T φ n s ω e
        - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
          (fun _ => W i ω) s := by
    intro s ω
    rw [show (fun e => (‖dyadicEvalShifted T φ n s ω e
          - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
              * mk i ω e‖₊ : ℝ≥0∞) ^ 2)
        = fun e => ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) s
        from funext (fun e => hcollapse s ω e)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => by
      by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · simp only [Set.indicator_of_mem hsi]; exact hgi_meas i ω
      · simp only [Set.indicator_of_notMem hsi]; exact measurable_const)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
    · simp only [Set.indicator_of_mem hsi]; rfl
    · simp only [Set.indicator_of_notMem hsi, lintegral_zero]
  -- collapse the `s`-integral to `∑ᵢ vol(Iᵢ)·Wᵢ(ω)`.
  have h_s : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => W i ω) s)
      ∂volume
      = ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * W i ω := by
    intro ω
    rw [MeasureTheory.lintegral_finsetSum _ (fun i _ =>
      (measurable_const.indicator measurableSet_Ioc))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_indicator measurableSet_Ioc,
      MeasureTheory.setLIntegral_const, Measure.restrict_apply measurableSet_Ioc, mul_comm]
  -- assemble: integrate `ω`, factor the volumes, bound by `δ`.
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖dyadicEvalShifted T φ n s ω e
            - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
                (fun _ => (1 : ℝ)) s * mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * W i ω ∂P := by
        refine lintegral_congr (fun ω => ?_)
        rw [← h_s ω]
        refine lintegral_congr (fun s => ?_)
        exact h_e s ω
    _ = ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * ∫⁻ ω, W i ω ∂P := by
        rw [MeasureTheory.lintegral_finsetSum _
          (fun i _ => (hW_meas i).const_mul _)]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [MeasureTheory.lintegral_const_mul _ (hW_meas i)])
    _ ≤ ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * δ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_right (hci_err i) _
    _ = (∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T)) * δ := by
        rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal T * δ := by
        refine mul_le_mul_left ?_ δ
        calc ∑ i : Fin (2 ^ n),
              volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T)
            ≤ ∑ i : Fin (2 ^ n), volume (Set.Ioc (p i.castSucc) (p i.succ)) :=
              Finset.sum_le_sum (fun i _ => measure_mono Set.inter_subset_left)
          _ = ∑ _i : Fin (2 ^ n), ENNReal.ofReal (T / (2 ^ n : ℕ)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hp, Real.volume_Ioc, dyadicPartition_diff]
          _ = ENNReal.ofReal T := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have h2 : (2 ^ n : ℝ) ≠ 0 := by positivity
              push_cast
              field_simp

/-- Additivity of the nested `∫⁻ω∫⁻s∫⁻e` triple integral over jointly measurable
summands. -/
lemma lintegral_triple_add
    {P : Measure Ω} {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    {u v : Ω → ℝ → E → ℝ≥0∞}
    (hu : Measurable (fun p : Ω × ℝ × E => u p.1 p.2.1 p.2.2)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (u ω s e + v ω s e) ∂ν ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, v ω s e ∂ν ∂volume ∂P := by
  have hue : ∀ ω s, Measurable (fun e => u ω s e) :=
    fun ω s => hu.comp (measurable_prodMk_left.comp measurable_prodMk_left)
  have hus : ∀ ω, Measurable (fun s => ∫⁻ e, u ω s e ∂ν) :=
    fun ω => (hu.comp measurable_prodMk_left).lintegral_prod_right'
  have huω : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume) := by
    have h2 : Measurable (fun q : Ω × ℝ => ∫⁻ e, u q.1 q.2 e ∂ν) :=
      (hu.comp (by fun_prop : Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E)))
        |>.lintegral_prod_right'
    exact h2.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  rw [← MeasureTheory.lintegral_add_left huω]
  refine lintegral_congr (fun ω => ?_)
  rw [← MeasureTheory.lintegral_add_left (hus ω)]
  refine lintegral_congr (fun s => ?_)
  rw [← MeasureTheory.lintegral_add_left (hue ω s)]

/-- Pulling a finite constant out of the nested `∫⁻ω∫⁻s∫⁻e` triple integral. -/
lemma lintegral_triple_const_mul
    {P : Measure Ω} {ν : Measure E} {T : ℝ} (c : ℝ≥0∞) (hc : c ≠ ⊤) (u : Ω → ℝ → E → ℝ≥0∞) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, c * u ω s e ∂ν ∂volume ∂P
      = c * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume ∂P := by
  simp_rw [MeasureTheory.lintegral_const_mul' c _ hc]

/-- **`L²` density of the adapted step (Euler) approximants.** For a bounded,
progressively measurable `φ` with finite mark support, there is a sequence of adapted
mark-simple step approximants converging to `φ` in `L²(P ⊗ vol ⊗ ν)`. Diagonalises the
time-half (`dyadicEvalShifted_L2_tendsto`) against the mark-half
(`exists_markEval_close_dyadic` with tolerance `δₙ = (n+1)⁻¹`), via the `2(a²+b²)`
triangle bound and a squeeze. -/
lemma exists_markEval_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    ∃ (Ki : (n : ℕ) → Fin (2 ^ n) → ℕ)
      (Bi : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Set E)
      (ci : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Ω → ℝ),
      (∀ n i k, MeasurableSet (Bi n i k)) ∧ (∀ n i k, Bi n i k ⊆ S) ∧
      (∀ n i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci n i k)) ∧
      (∀ n i k, ∃ C, ∀ ω, |ci n i k ω| ≤ C) ∧
      Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - ∑ i : Fin (2 ^ n),
            (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
              (fun _ => (1 : ℝ)) s
            * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P) Filter.atTop (nhds 0) := by
  classical
  have hδne : ∀ n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun n =>
    ENNReal.inv_ne_zero.mpr (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
  choose Ki Bi ci hBim hBiS hcim hcib herr using fun n =>
    exists_markEval_close_dyadic N ℱ hT φ h_meas h_progMeas hM hS hSfin hSupp n (hδne n)
  refine ⟨Ki, Bi, ci, hBim, hBiS, hcim, hcib, ?_⟩
  -- the markEval step approximant and its triple-measurability.
  set mk : ℕ → Ω → ℝ → E → ℝ := fun n ω s e =>
    ∑ i : Fin (2 ^ n),
      (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e with hmkdef
  have hmkm : ∀ n, Measurable (fun p : Ω × ℝ × E => mk n p.1 p.2.1 p.2.2) := by
    intro n
    refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ ?_)
    · exact (measurable_const.indicator measurableSet_Ioc).comp
        (measurable_fst.comp measurable_snd)
    · refine Finset.measurable_sum _ (fun k _ => Measurable.mul ?_ ?_)
      · exact (((hcim n i k).measurable.mono
            (ℱ.le _) le_rfl)).comp measurable_fst
      · exact (measurable_const.indicator (hBim n i k)).comp
          (measurable_snd.comp measurable_snd)
  -- joint measurabilities of the two triangle summands.
  have hφm : ∀ n, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - dyadicEvalShifted T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (dyadicEvalShifted_measurable_triple φ h_meas n)).nnNorm).pow_const 2
  set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P with hAdef
  have htime : Filter.Tendsto A Filter.atTop (nhds 0) :=
    dyadicEvalShifted_L2_tendsto hT φ h_meas hM hS hSfin hSupp
  -- the markEval error is dominated by `2·Aₙ + 2·(T·δₙ)`.
  have hbound : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      ≤ 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹) := by
    intro n
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (2 * (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
              + 2 * (‖dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2)
            ∂ν ∂volume ∂P := by
          refine lintegral_mono (fun ω => lintegral_mono (fun s => lintegral_mono (fun e => ?_)))
          have h := sq_nnnorm_add_le_two_mul (φ ω s e - dyadicEvalShifted T φ n s ω e)
            (dyadicEvalShifted T φ n s ω e - mk n ω s e)
          rw [show φ ω s e - dyadicEvalShifted T φ n s ω e
                + (dyadicEvalShifted T φ n s ω e - mk n ω s e) = φ ω s e - mk n ω s e from by ring,
            mul_add] at h
          exact h
      _ = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * (‖dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
          lintegral_triple_add ((hφm n).const_mul 2)
      _ = 2 * A n + 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
          rw [lintegral_triple_const_mul 2 (by norm_num) _,
            lintegral_triple_const_mul 2 (by norm_num) _]
      _ ≤ 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹) := by
          gcongr
          exact herr n
  -- the dominating sequence tends to `0`; squeeze.
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  have hup : Filter.Tendsto (fun n => 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => 2 * A n) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul htime (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      simpa using this
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹))
        Filter.atTop (nhds 0) := by
      have ha : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹)
          Filter.atTop (nhds (ENNReal.ofReal T * 0)) :=
        ENNReal.Tendsto.const_mul hinv (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at ha
      have hb := ENNReal.Tendsto.const_mul ha (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      rwa [mul_zero] at hb
    have := h1.add h2
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) hbound

end LevyStochCalc.Poisson.Compensated
