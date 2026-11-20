/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use the v4.35.0
-- `eLpNorm`/`MemLp` API.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_sq_eq_lintegral_nnnorm_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionQuadVar

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The `ℱ.rightCont`-martingale property of the compensated square, the unified
existence theorem `itoIsometry_brownian_unified_existence` combining the martingale,
quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2 on `rightCont`: `(F)² − ∫₀ᵗH²` is a `rightCont`-martingale.**
The `ℱ`-martingale (`martingale_quadVar_stochasticIntegralBrownian`) lifts
via right-`L¹`-continuity: the `F²`-part is controlled by `F`'s right-`L²`-continuity
(`tendsto_eLpNorm_one_sq_sub`), the compensator part by the horizon slab
`∫⁻∫⁻_{(s,r]}‖H‖² → 0` (`tendsto_setLIntegral_Ioc_prod_zero`). -/
lemma martingale_rightCont_quadVar_stochasticIntegralBrownian :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_quadVar_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun s => ?_)
  set F := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hFdef
  -- `F²`-part: right-`L¹`-continuity of the square.
  have hF2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) 1 P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    tendsto_eLpNorm_one_sq_sub (l := nhdsWithin s (Set.Ioi s)) (a := fun r => F r) (b := F s)
      (fun r => (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global r).aestronglyMeasurable.aemeasurable)
      (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s).aestronglyMeasurable.aemeasurable
      (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s).eLpNorm_lt_top.ne
      (stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s)
  -- compensator part: right-`L¹`-continuity of `A_t = ∫₀ᵗ H²`.
  have hA : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
    rcases le_or_gt 0 s with hs | hs
    · have hslab := tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
        ((h_meas.nnNorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
        (h_sq_int_global (s + 1) (by linarith)).ne
      refine hslab.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsr : s ≤ r := le_of_lt hr
      have hrpos : 0 < r := lt_of_le_of_lt hs hr
      have hHr : ∀ᵐ ω ∂P, MeasureTheory.Integrable
          (fun u => (H ω u) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
        (compensatorH_memLp_prod H h_meas h_sq_int_global hrpos).integrable_sq.prod_right_ae
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_eNorm
        (f := fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume)
        (((compensatorH_adapted ℱ H h_progMeas r).mono (ℱ.le r)).aestronglyMeasurable.sub
          ((compensatorH_adapted ℱ H h_progMeas s).mono (ℱ.le s)).aestronglyMeasurable)]
      refine (lintegral_congr_ae ?_).symm
      filter_upwards [hHr] with ω hHrω
      have hHsω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Icc (0 : ℝ) s)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Icc_subset_Icc_right hsr)
          (le_refl _))
      have hHscω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Ioc s r)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)) (le_refl _))
      have hsplit : (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume
          = ∫ u in Set.Ioc s r, (H ω u) ^ 2 ∂volume := by
        have hdisjoint : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s r) :=
          (Set.Iic_disjoint_Ioc (c := r) (le_refl s)).mono Set.Icc_subset_Iic_self subset_rfl
        rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
          MeasureTheory.setIntegral_union hdisjoint measurableSet_Ioc hHsω hHscω]
        ring
      rw [hsplit, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun u => sq_nonneg _)),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHscω
          (Filter.Eventually.of_forall (fun u => sq_nonneg _))]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
      rw [show (‖H ω u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((H ω u) ^ 2) from by
        rw [show (‖H ω u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H ω u‖ from (ofReal_norm _).symm,
          ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr
      have hAr : (fun u => (H · u) ^ 2) = (fun u => (H · u) ^ 2) := rfl
      symm
      rw [show (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) from by
        funext ω
        rw [Set.Icc_eq_empty (not_le.mpr hr.2), Set.Icc_eq_empty (not_le.mpr hs)]
        simp]
      exact MeasureTheory.eLpNorm_zero
  -- combine the two parts.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Filter.Eventually.of_forall (fun r => bot_le)) (Filter.Eventually.of_forall (fun r => ?_))
  calc MeasureTheory.eLpNorm
        ((fun t ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) r
          - fun ω => (F s ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P
      = MeasureTheory.eLpNorm
          ((fun ω => (F r ω) ^ 2 - (F s ω) ^ 2)
            - fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
              - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P := by
        refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [Pi.sub_apply]; ring
    _ ≤ _ := MeasureTheory.eLpNorm_sub_le le_rfl

end MasterSequence

/-- **Unified L²-Itô integral with martingale + quadVar + isometry** (formerly cited
axiom #5, now a theorem).

For predictable square-integrable `H : Ω → ℝ → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t H² ds` is a martingale wrt `Filt` (quadVar identity),
* `∫⁻ ω, ‖F T‖₊² ∂P = ∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P`
  for every `T > 0`
  (L²-isometry).

The statement asserts existence of *some* process `F` with these three
properties for `Filt = ℱ.rightCont`; it does not name `F` or mention `W`. The
witness supplied by the proof is `stochasticIntegralBrownian`; the pinned
forms that name it directly are `isometry_stochasticIntegralBrownian`,
`martingale_rightCont_stochasticIntegralBrownian` and
`itoIsometry_diff_brownian`. The 3-conjunct strong existence consolidates
Karatzas–Shreve Thm 3.2.6.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** (unified martingale + quadratic variation +
L²-isometry of the L² Itô integral); Le Gall, J.-F. *Brownian Motion, Martingales
and Stochastic Calculus*, Springer 2016, **Theorem 5.4** + equation **(5.8)**.

**Construction**: `F := stochasticIntegralBrownian` is the coherent `L²`-limit of the
`masterApprox` simple integrals across growing horizons. Conjunct 1
(`martingale_rightCont_stochasticIntegralBrownian`) and conjunct 3
(`isometry_stochasticIntegralBrownian`) were proven directly; conjunct 2
(`martingale_rightCont_quadVar_stochasticIntegralBrownian`) is the set-level Itô
isometry at simple level lifted through the `L¹`-limit of the compensated squares and
the `rightCont` right-`L¹`-continuity. `Filt` is pinned to
`ℱ.rightCont`. -/
theorem itoIsometry_brownian_unified_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = ℱ.rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      (∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
  ⟨stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global,
    ℱ.rightCont, rfl,
    martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global,
    martingale_rightCont_quadVar_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global,
    fun _ hT => isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT⟩

/-- **`L²`-convergence ⇒ convergence of the squared mass.** If `gₙ → g` in `L²(μ)`
(with `‖g‖₂ < ⊤`), then `∫⁻ ‖gₙ‖₊² → ∫⁻ ‖g‖₊²`. The `L²`-norm is continuous under
`L²`-convergence (squeeze via the triangle inequality both ways), and `x ↦ x²` is
continuous on `ℝ≥0∞`. Underlies the per-difference Itô isometry (#17). -/
lemma tendsto_lintegral_nnnorm_sq_of_eLpNorm
    {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β}
    {ι : Type*} {l : Filter ι} {gₙ : ι → β → ℝ} {g : β → ℝ}
    (hgₙ : ∀ n, MeasureTheory.AEStronglyMeasurable (gₙ n) μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hgfin : MeasureTheory.eLpNorm g 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, (‖gₙ n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) l
      (nhds (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ)) := by
  -- `eLpNorm gₙ 2 → eLpNorm g 2` by the two-sided triangle bound.
  have hnorm : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n) 2 μ) l
      (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
    have hlo : Filter.Tendsto (fun n => MeasureTheory.eLpNorm g 2 μ
        - MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
        htend (Or.inl hgfin)
      simpa using this
    have hhi : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ
        + MeasureTheory.eLpNorm g 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := htend.add (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (Filter.Eventually.of_forall (fun n => ?_)) (Filter.Eventually.of_forall (fun n => ?_))
    · refine tsub_le_iff_left.mpr ?_
      calc MeasureTheory.eLpNorm g 2 μ
          = MeasureTheory.eLpNorm (gₙ n - (gₙ n - g)) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm (gₙ n) 2 μ := by
            refine le_trans (MeasureTheory.eLpNorm_sub_le (by norm_num)) ?_
            rw [add_comm]
    · calc MeasureTheory.eLpNorm (gₙ n) 2 μ
          = MeasureTheory.eLpNorm ((gₙ n - g) + g) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.add_apply, Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm g 2 μ :=
            MeasureTheory.eLpNorm_add_le (by norm_num)
  have hconv : ∀ x : β → ℝ, MeasureTheory.AEStronglyMeasurable x μ →
      MeasureTheory.eLpNorm x 2 μ * MeasureTheory.eLpNorm x 2 μ
        = ∫⁻ y, (‖x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    intro x hx
    rw [← eLpNorm_sq_eq_lintegral_nnnorm_sq x hx,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  rw [← hconv g hg]
  exact (ENNReal.Tendsto.mul hnorm (Or.inr hgfin) hnorm (Or.inr hgfin)).congr
    fun n => hconv (gₙ n) (hgₙ n)

/-- **Cross-integrand simple difference isometry.** For two integrands `H₁, H₂`, their
`masterApprox n` simple integrals satisfy `∫⁻‖Iₙ(H₁) − Iₙ(H₂)‖² = ∫⁻∫⁻‖evalₙ(H₁) −
evalₙ(H₂)‖²` at every `t ≥ 0`. Both `masterApprox · n` live on horizon `n+1`; extend
each to the common horizon `n+2` via `appendInterval` (which preserves `simpleIntegral`
and `eval`) and apply `simpleIntegral_intermediate_diff_isometry`. -/
theorem masterApprox_cross_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (n : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) t ω
        - simpleIntegral W (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
            - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n with hGn
  set Gm := masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (n : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (n : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (n : ℝ) + 1 := Gm.partition_le_T
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt ℱ hKn
    (masterApprox_adapt ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n)
  have ha_m := Gm.appendInterval_adapt ℱ hKm
    (masterApprox_adapt ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n)
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [Gn.appendInterval_simpleIntegral W hKn t ω, Gm.appendInterval_simpleIntegral W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [Gn.appendInterval_eval hKn s ω, Gm.appendInterval_eval hKm s ω]
  rw [hL, hR]; exact hiso

/-- **Per-difference L²-isometry of the Brownian Itô integral.**
`∫⁻‖∫₀ᵀ H₁ dW − ∫₀ᵀ H₂ dW‖² = ∫⁻∫⁻_{[0,T]}‖H₁ − H₂‖²`. Both the integral difference
and the integrand difference are realized as `L²`-limits of the same simple-integral
difference sequence (`masterApprox_cross_diff_isometry`); `tendsto_lintegral_nnnorm_sq_of_eLpNorm`
identifies each limit, and `tendsto_nhds_unique` equates them. -/
theorem isometry_diff_stochasticIntegralBrownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have ht_nn : (0 : ℝ) ≤ T := le_of_lt hT
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  -- abbreviations for the two simple-integral sequences and the two limits
  have hImeas : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (n : ℕ),
      Measurable (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hs n) T ω) := by
    intro H hm hp hs n
    unfold simpleIntegral
    exact Finset.measurable_sum _ (fun i _ =>
      ((masterApprox ℱ H hm hp hs n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _)))
  -- the bridge `∫⁻_{P⊗ν} ‖f‖² = ∫⁻∫⁻_{[0,T]} ‖f(ω,s)‖²`
  have hbridge : ∀ f : Ω × ℝ → ℝ, Measurable f →
      ∫⁻ p, (‖f p‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod ν)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [MeasureTheory.lintegral_prod _
      (((hf.nnNorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eval_n(H) → H` in `L²(P⊗ν)` for each integrand.
  have hevalL2 : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
    intro H hm hp hs
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν)
        ^ (2 : ℝ)) Filter.atTop (nhds 0) := by
      have he := masterApprox_eval_tendsto (t := T) ℱ H hm hp hs
      refine he.congr (fun n => ?_)
      rw [eLpNorm_sq_eq_lintegral_nnnorm_sq
          (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2)
          (((masterApprox ℱ H hm hp hs n).eval_jointly_measurable).sub hm).aestronglyMeasurable,
        hbridge (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2)
          (((masterApprox ℱ H hm hp hs n).eval_jointly_measurable).sub hm)]
      refine lintegral_congr (fun ω => ?_)
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
      rw [show (‖H ω s - (masterApprox ℱ H hm hp hs n).eval s ω‖₊ : ℝ≥0∞)
          = ‖(masterApprox ℱ H hm hp hs n).eval s ω - H ω s‖₊ from by
        rw [← nnNorm_neg]; congr 1; ring_nf]
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- LHS: `∫⁻‖Iₙ(H₁)−Iₙ(H₂)‖² → ∫⁻‖F₁−F₂‖²`
  have hLHS : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) T ω
        - simpleIntegral W (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds (∫⁻ ω,
        (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
          - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂
            h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) := by
    refine tendsto_lintegral_nnnorm_sq_of_eLpNorm
      (fun n => ((hImeas H₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
        (hImeas H₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
      ((stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
        h_sq₁ T).aestronglyMeasurable.sub
        (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ T).aestronglyMeasurable)
      (by
        refine (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le (by norm_num))
          (ENNReal.add_lt_top.mpr
            ⟨(stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁
                T).eLpNorm_lt_top,
              (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂
                T).eLpNorm_lt_top⟩)).ne)
      ?_
    have hsum := (masterApprox_tendsto_L2 W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ ht_nn).add
      (masterApprox_tendsto_L2 W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ ht_nn)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
      (Filter.Eventually.of_forall (fun n => bot_le))
      (Filter.Eventually.of_forall (fun n => ?_))
    refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le (by norm_num))
    exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun ω => by simp only [Pi.sub_apply]; ring)))
  -- RHS: `∫⁻∫⁻‖evalₙ(H₁)−evalₙ(H₂)‖² → ∫⁻∫⁻‖H₁−H₂‖²`
  have hHdfin : MeasureTheory.eLpNorm (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) 2 (P.prod ν)
      ≠ ⊤ :=
    (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le (by norm_num))
      (ENNReal.add_lt_top.mpr
        ⟨(compensatorH_memLp_prod H₁ h_meas₁ h_sq₁ hT).eLpNorm_lt_top,
          (compensatorH_memLp_prod H₂ h_meas₂ h_sq₂ hT).eLpNorm_lt_top⟩)).ne
  have hRHS' := tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (μ := P.prod ν)
    (gₙ := fun n p => (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval p.2 p.1
      - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval p.2 p.1)
    (g := fun p => H₁ p.1 p.2 - H₂ p.1 p.2)
    (fun n => (((masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((masterApprox ℱ H₂ h_meas₂ h_progMeas₂
        h_sq₂ n).eval_jointly_measurable)).aestronglyMeasurable)
    (h_meas₁.aestronglyMeasurable.sub h_meas₂.aestronglyMeasurable) hHdfin
    (by
      have hsum := (hevalL2 H₁ h_meas₁ h_progMeas₁ h_sq₁).add
        (hevalL2 H₂ h_meas₂ h_progMeas₂ h_sq₂)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le (by norm_num))
      exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
        (Filter.Eventually.of_forall (fun p => by simp only [Pi.sub_apply]; ring))))
  rw [hbridge (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) (h_meas₁.sub h_meas₂)] at hRHS'
  have hRHS : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
        - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
    refine hRHS'.congr' (Filter.Eventually.of_forall (fun n => ?_))
    exact (hbridge _ (((masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval_jointly_measurable)))
  -- the two sequences agree (cross diff isometry); equate the limits.
  refine tendsto_nhds_unique (hLHS.congr' (Filter.Eventually.of_forall (fun n => ?_))) hRHS
  exact masterApprox_cross_diff_isometry W ℱ hℱ H₁ H₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂
    h_sq₁ h_sq₂ n ht_nn

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

The **constructed** L²-limit process `stochasticIntegralBrownian` (the coherent
`L²`-limit of the `masterApprox` simple integrals), not a `Classical.choose`
witness — so it is genuinely linear-friendly (used by `itoIsometry_diff_brownian`). -/
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T

/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form.

Forwards to the L²-isometry conjunct of `itoIsometry_brownian_unified_existence`. -/
theorem itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT

/-- **Quadratic variation of the L² Itô integral.**

For predictable square-integrable `H`, the process `t ↦ (M_t)² − ∫_0^t |H_s|² ds`,
where `M_t = ∫_0^t H_s dW_s`, is a martingale with respect to some filtration
(the statement does not name it; the pinned form for `ℱ.rightCont` is
`martingale_rightCont_quadVar_stochasticIntegralBrownian`).

Extracts conjunct 2 (quadratic variation) of `itoIsometry_brownian_unified_existence`. -/
theorem quadVar_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2)
        F P := by
  unfold stochasticIntegral
  exact ⟨ℱ.rightCont,
    martingale_rightCont_quadVar_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global⟩

/-- **The L² Itô integral is a martingale.**

The Itô integral `M_t = ∫_0^t H_s dW_s` is a martingale with respect to some
filtration (the statement does not name it; the pinned form for `ℱ.rightCont`
is `martingale_rightCont_stochasticIntegralBrownian`).

Extracts conjunct 1 (martingale property) of `itoIsometry_brownian_unified_existence`. -/
theorem martingale_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) F P := by
  unfold stochasticIntegral
  exact ⟨ℱ.rightCont,
    martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global⟩

end LevyStochCalc.Brownian.Ito
