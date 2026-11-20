/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with source adaptations
-- (deprecated names, proof-context visibility, `continuous_abs.measurable.comp` for the no longer
-- reachable `Measurable.abs`) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Ito.VectorItoProcessDiff
public import LeanPool.KLS.LevyStochCalc.Probability.DoobContinuous

/-!
# The window supremum of the difference of two vector Itô versions

Two versions driven by different coefficients differ by a drift part, controlled pathwise by
Cauchy–Schwarz, and a martingale part, controlled by Doob's `L²` maximal inequality. Sampling the
paths on the dyadic points of the window turns the supremum into a countable one, which is all the
maximal inequality needs.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` — the second moment of the
  window supremum of the difference, in terms of the coefficients' energies.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Helpers

variable {Ω : Type u}

/-- The extended norm of a vector is at most the sum of the extended norms of its entries. -/
theorem enorm_pi_le_sum {m : ℕ} (x : Fin m → ℝ) :
    (‖x‖₊ : ℝ≥0∞) ≤ ∑ p, (‖x p‖₊ : ℝ≥0∞) := by
  have hreal : ‖x‖ ≤ ∑ p, ‖x p‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)).mpr fun p => ?_
    exact Finset.single_le_sum (f := fun q => ‖x q‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ p)
  have hnn : ‖x‖₊ ≤ ∑ p, ‖x p‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa using hreal
  calc (‖x‖₊ : ℝ≥0∞) ≤ ((∑ p, ‖x p‖₊ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = ∑ p, (‖x p‖₊ : ℝ≥0∞) := by rw [ENNReal.ofNNReal_finsetSum]

/-- The extended norm does not see the absolute value. -/
theorem nnnorm_abs_real (x : ℝ) : ‖|x|‖₊ = ‖x‖₊ := by
  rw [← Real.norm_eq_abs, nnNorm_norm]

/-- A squared sum of two terms, up to a constant. -/
theorem add_sq_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h := sq_sum_le_card_sq_mul (Finset.univ : Finset (Fin 2)) ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.card_univ, Fintype.card_fin] at h
  have h4 : ((2 : ℕ) : ℝ≥0∞) ^ 2 = 4 := by norm_num
  rwa [h4] at h

/-- The sampled running maximum only sees the values at the dyadic points. -/
theorem dyadicRunMax_congr {A B : ℝ → Ω → ℝ} {T : ℝ} {ω : Ω}
    (h : ∀ m k : ℕ, A (dyadicTime T m k) ω = B (dyadicTime T m k) ω) (m : ℕ) :
    dyadicRunMax A T m ω = dyadicRunMax B T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  rw [h m k]

/-- The sampled running maximum does not see the absolute value. -/
theorem dyadicRunMax_abs (A : ℝ → Ω → ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    dyadicRunMax (fun t ω => |A t ω|) T m ω = dyadicRunMax A T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  simp [Real.norm_eq_abs]

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (f : ι → ℝ → Ω → ℝ)
    (hf : ∀ i ∈ s, MeasureTheory.Martingale (f i) ℱ P) :
    MeasureTheory.Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun (t : ℝ) (ω : Ω) => ∑ i ∈ (∅ : Finset ι), f i t ω) = (0 : ℝ → Ω → ℝ) := by
        funext t ω
        simp
      rw [h0]
      exact MeasureTheory.martingale_zero ℝ ℱ P
  | insert i s hi ih =>
      have hsum : (fun t ω => ∑ j ∈ insert i s, f j t ω)
          = fun t ω => f i t ω + ∑ j ∈ s, f j t ω := by
        funext t ω
        rw [Finset.sum_insert hi]
      rw [hsum]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end Helpers

section SupBound

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in
/-- The martingale part of a vector Itô process is a martingale. -/
theorem martingale_vectorItoMartingale
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) :
    MeasureTheory.Martingale
      (fun t ω => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω) ℱ P := by
  have hrw : (fun (t : ℝ) (ω : Ω) => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω)
      = fun t ω => ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
          (hm p k) (hp p k) (hq p k) t ω := rfl
  rw [hrw]
  exact martingale_finsetSum Finset.univ _ fun k _ =>
    martingale_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hm p k) (hp p k) (hq p k)

private theorem lintegral_iSup_sq_drift_step_le
    {Ω : Type*}
    [MeasurableSpace Ω]
    {P : Measure Ω}
    {n : ℕ}
    {b₁ : Fin n → Ω → ℝ → ℝ}
    {b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ (p : Fin n), Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ (p : Fin n), Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ (ω : Ω), ∫⁻ (s : ℝ) in Set.Icc 0 T,
      ↑‖b₁ p ω s‖₊ ^ 2 ∂volume ∂P < ∞)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ (ω : Ω), ∫⁻ (s : ℝ) in Set.Icc 0 T,
      ↑‖b₂ p ω s‖₊ ^ 2 ∂volume ∂P < ∞)
    {T : ℝ}
    (hT : 0 < T)
    (p : Fin n)
    (D : ℝ → Ω → ℝ)
    (hDdef : D = fun t ω => (∫ (s : ℝ) in Set.Icc 0 t, b₂ p ω s) - ∫ (s : ℝ) in Set.Icc 0 t,
      b₁ p ω s)
    (hΔbfin : ∫⁻ (ω : Ω), ∫⁻ (s : ℝ) in Set.Icc 0 T, ↑‖|b₂ p ω s
      - b₁ p ω s|‖₊ ^ 2 ∂volume ∂P < ∞) : ∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
    ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  classical
  have hint₁ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₁ p ω) (Set.Icc (0 : ℝ) T) volume :=
    ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p T hT)
  have hint₂ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₂ p ω) (Set.Icc (0 : ℝ) T) volume :=
    ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p T hT)
  have hptw : ∀ᵐ ω ∂P, (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
      ≤ (‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) := by
    filter_upwards [hint₁, hint₂] with ω h1 h2
    refine iSup_dyadicRunMax_le_of_bound hT.le fun t ht => ?_
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
    have hDt : D t ω = ∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume := by
      simp only [hDdef]
      rw [MeasureTheory.integral_sub (h2.mono_set hsub) (h1.mono_set hsub)]
    have habs : |D t ω| ≤ ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume := by
      rw [hDt]
      exact MeasureTheory.abs_integral_le_integral_abs
    have hmono : ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume
        ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
      MeasureTheory.setIntegral_mono_set (h2.sub h1).abs
        (Filter.Eventually.of_forall fun s => abs_nonneg _) hsub.eventuallySubset
    have hnn : ‖D t ω‖₊ ≤ ‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnNorm, Real.norm_eq_abs]
      have hAnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun s => abs_nonneg _)
      rw [abs_of_nonneg hAnn]
      exact habs.trans hmono
    exact_mod_cast hnn
  calc ∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T,
          |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        MeasureTheory.lintegral_mono_ae (hptw.mono fun ω h => pow_le_pow_left' h 2)
    _ ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
          (f := fun ω s => |b₂ p ω s - b₁ p ω s|)
          (continuous_abs.measurable.comp ((hbm₂ p).sub (hbm₁ p))) hT.le hΔbfin
    _ = ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp

include hcoord in
/-- **The second moment of the window supremum of the difference of two vector Itô versions.**
The drift part is controlled pathwise by Cauchy–Schwarz and the martingale part by Doob's `L²`
maximal inequality. -/
theorem lintegral_iSup_sq_norm_version_sub_le
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k))}
    {hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k)}
    {hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k))}
    {hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k)}
    {hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X Y : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
    (hY : IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
          (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) := by
  classical
  set Zc : Fin n → ℝ → Ω → ℝ := fun p t ω => Y t ω p - X t ω p with hZcdef
  set Zabs : ℝ → Ω → ℝ := fun t ω => ∑ p : Fin n, |Zc p t ω| with hZabsdef
  have hZcm : ∀ (p : Fin n) (t : ℝ), Measurable (Zc p t) :=
    fun p t => (hY.measurable_coord t p).sub (hX.measurable_coord t p)
  have hZccont : ∀ (p : Fin n) (ω : Ω), Continuous fun t => Zc p t ω := by
    intro p ω
    exact ((continuous_apply p).comp (hY.continuous_path ω)).sub
      ((continuous_apply p).comp (hX.continuous_path ω))
  have hZabscont : ∀ ω : Ω, Continuous fun t => Zabs t ω :=
    fun ω => continuous_finsetSum _ fun p _ => (hZccont p ω).abs
  set S : Fin n → Ω → ℝ≥0∞ := fun p ω => ⨆ m : ℕ, (‖dyadicRunMax (Zc p) T m ω‖₊ : ℝ≥0∞)
    with hSdef
  have hSmeas : ∀ p : Fin n, Measurable (S p) :=
    fun p => Measurable.iSup fun m => measurable_enorm_dyadicRunMax (hZcm p) T m
  -- the window supremum is dominated by the coordinatewise dyadic suprema
  have hdom : ∀ ω : Ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
      ≤ ∑ p : Fin n, S p ω := by
    intro ω
    have hcad : ∀ t : ℝ, Filter.Tendsto (fun s => Zabs s ω) (nhdsWithin t (Set.Ioi t))
        (nhds (Zabs t ω)) := fun t => ((hZabscont ω).tendsto t).mono_left nhdsWithin_le_nhds
    have hstep1 : (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
        ≤ ⨆ t : Set.Icc (0 : ℝ) T, (‖Zabs (t : ℝ) ω‖₊ : ℝ≥0∞) := by
      refine iSup_le fun t => le_iSup_of_le t ?_
      have hnn : (0 : ℝ) ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| :=
        Finset.sum_nonneg fun q _ => abs_nonneg _
      have hreal : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖
          ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        refine (pi_norm_le_iff_of_nonneg hnn).mpr fun q => ?_
        have hq : |Y (t : ℝ) ω q - X (t : ℝ) ω q|
            ≤ ∑ r : Fin n, |Y (t : ℝ) ω r - X (t : ℝ) ω r| :=
          Finset.single_le_sum (f := fun r : Fin n => |Y (t : ℝ) ω r - X (t : ℝ) ω r|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
        simpa [Real.norm_eq_abs] using hq
      have hZ : ‖Zabs (t : ℝ) ω‖ = ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        simp only [hZabsdef, hZcdef]
        exact Real.norm_of_nonneg hnn
      have hle : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ ≤ ‖Zabs (t : ℝ) ω‖₊ := by
        rw [← NNReal.coe_le_coe]
        simpa only [coe_nnNorm, hZ] using hreal
      exact_mod_cast hle
    refine hstep1.trans ?_
    rw [iSup_enorm_eq_iSup_dyadicRunMax hT.le hcad]
    refine le_trans (iSup_dyadicRunMax_sum_le Finset.univ (fun p t ω => |Zc p t ω|) T ω) ?_
    exact le_of_eq (Finset.sum_congr rfl fun p _ => by
      simp only [hSdef, dyadicRunMax_abs])
  -- square, and split the integral over the coordinates
  have hsq : ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
    calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        ≤ ∫⁻ ω, ((n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, (S p ω) ^ 2) ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          refine le_trans (pow_le_pow_left' (hdom ω) 2) ?_
          simpa using sq_sum_le_card_sq_mul (Finset.univ : Finset (Fin n)) fun p => S p ω
      _ = (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun p _ => (hSmeas p).pow_const 2]
  refine hsq.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => ?_))
  -- the drift and martingale parts of the coordinate difference
  set D : ℝ → Ω → ℝ := fun t ω => (∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
    - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume with hDdef
  set M : ℝ → Ω → ℝ := fun t ω => vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
    - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω with hMdef
  have hDm : ∀ t : ℝ, Measurable (D t) := fun t =>
    (measurable_setIntegral (hbm₂ p) (Set.Icc (0 : ℝ) t)).sub
      (measurable_setIntegral (hbm₁ p) (Set.Icc (0 : ℝ) t))
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t =>
    (measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)
  have hsplit : ∀ᵐ ω ∂P, ∀ m k : ℕ,
      Zc p (dyadicTime T m k) ω = D (dyadicTime T m k) ω + M (dyadicTime T m k) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards [hX.ae_eq (dyadicTime T m k) (dyadicTime_nonneg hT.le m k),
      hY.ae_eq (dyadicTime T m k) (dyadicTime_nonneg hT.le m k)] with ω e1 e2
    simp only [hZcdef, hDdef, hMdef, e1, e2, vectorItoProcess]
    ring
  have hSbound : ∀ᵐ ω ∂P, (S p ω) ^ 2
      ≤ 4 * ((⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
        + (⨆ m : ℕ, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) := by
    filter_upwards [hsplit] with ω hω
    have hcongr : ∀ m : ℕ, dyadicRunMax (Zc p) T m ω
        = dyadicRunMax (fun t ω => D t ω + M t ω) T m ω :=
      fun m => dyadicRunMax_congr (fun m' k => hω m' k) m
    have hle : S p ω ≤ (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
        + ⨆ m : ℕ, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
      simp only [hSdef, hcongr]
      exact iSup_dyadicRunMax_add_le D M T ω
    exact le_trans (pow_le_pow_left' hle 2) (add_sq_le_four_mul _ _)
  -- the drift part, by Cauchy–Schwarz on the window
  have hΔbfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    have hbd : ∀ (ω : Ω) (s : ℝ), (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 + (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have := sq_nnnorm_sub_le_two_mul (b₂ p ω s) (b₁ p ω s)
      simpa [nnnorm_abs_real] using this
    exact lintegral_energy_lt_top_of_bound hbd (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) T hT
  have hDrift : ∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    lintegral_iSup_sq_drift_step_le hbm₁ hbm₂ hbq₁ hbq₂ hT p D hDdef hΔbfin
  -- the martingale part, by Doob's inequality
  have hMart : MeasureTheory.Martingale M ℱ P :=
    (martingale_vectorItoMartingale W ℱ hcoord hm₂ hp₂ hq₂ p).sub
      (martingale_vectorItoMartingale W ℱ hcoord hm₁ hp₁ hq₁ p)
  have hMT : ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hMTeq : ∀ ω : Ω, M T ω = ∑ k : Fin d,
        (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω) := by
      intro ω
      simp only [hMdef, vectorItoMartingale, coordItoIntegral]
      rw [Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      have h2 : Measurable (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T) :=
        ((stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T).mono (ℱ.le T)).measurable
      have h1 : Measurable (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T) :=
        ((stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T).mono (ℱ.le T)).measurable
      exact (((h2.sub h1).nnNorm).coe_nnreal_ennreal).pow_const 2
    calc ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ k : Fin d,
            (‖stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          rw [hMTeq ω]
          exact sq_enorm_finsetSum_le _
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k]
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          refine congrArg (fun x => (d : ℝ≥0∞) * x) (Finset.sum_congr rfl fun k _ => ?_)
          exact isometry_diff_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k)
            (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) hT
  have hDoob : ∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_iSup_dyadicRunMax_sq_le hMart hT.le
  calc ∫⁻ ω, (S p ω) ^ 2 ∂P
      ≤ ∫⁻ ω, 4 * ((⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m : ℕ, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae hSbound
    _ = 4 * (∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
          + ∫⁻ ω, (⨆ m : ℕ, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left
            ((Measurable.iSup fun m => measurable_enorm_dyadicRunMax hDm T m).pow_const 2)]
    _ ≤ 4 * (ENNReal.ofReal T * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
        mul_le_mul' le_rfl (add_le_add hDrift (hDoob.trans (mul_le_mul' le_rfl hMT)))
    _ = 4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
        rw [mul_add]

omit [IsProbabilityMeasure P] in
/-- The energy of a difference is controlled by the energies of the two differences with a common
third integrand. -/
theorem lintegral_energy_sub_le {f g h : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hh : Measurable (Function.uncurry h)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hptw : ∀ (ω : Ω) (s : ℝ), (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have hb := sq_nnnorm_sub_le_two_mul (f ω s - h ω s) (g ω s - h ω s)
    simpa [sub_sub_sub_cancel_right] using hb
  have hmfh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity (hf.sub hh) T
  have hmgh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity (hg.sub hh) T
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hptw ω s
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
        have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
              + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
          intro ω
          have hfhm : Measurable fun s : ℝ => (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 := by
            have h1 : Measurable fun s : ℝ => f ω s - h ω s :=
              (Measurable.of_uncurry_left hf).sub (Measurable.of_uncurry_left hh)
            exact ((h1.nnNorm).coe_nnreal_ennreal).pow_const 2
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_add_left hfhm]
        simp only [hinner]
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left hmfh]

end SupBound

end LevyStochCalc.Brownian.Ito
