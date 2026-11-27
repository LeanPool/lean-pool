/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolWeakLimit
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed measurable partitions from weak limits

The pool lemma needs one partition for each scanning rule, fixed before the
finite stage parameters are chosen.  Given the weak limits constructed in
`PoolWeakLimit`, take `H = {g = 1}` and `L = Hᶜ`.  These are measurable sets;
on Cantor space they are Borel sets.

Weak convergence makes the missed mass on `H` tend to zero.  On `L`, the mass
where `g` is arbitrarily close to one tends to zero.  A single positive rational
threshold works simultaneously for any prescribed finite list of limits.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open Filter MeasureTheory Set Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The high part of the fixed partition belonging to a weak limit. -/
def highSet (g : Lp ℝ 2 μ) : Set Ω := {x | g x = 1}

/-- The low part of the same fixed partition. -/
def lowSet (g : Lp ℝ 2 μ) : Set Ω := (highSet g)ᶜ

/-- Points in the low part whose weak-limit value is at least `1 - δ`. -/
def nearOneLowSet (g : Lp ℝ 2 μ) (δ : ℝ) : Set Ω :=
  lowSet g ∩ {x | 1 - δ ≤ g x}

theorem measurableSet_highSet (g : Lp ℝ 2 μ) : MeasurableSet (highSet g) :=
  (Lp.stronglyMeasurable g).measurableSet_eq_fun stronglyMeasurable_const

theorem measurableSet_lowSet (g : Lp ℝ 2 μ) : MeasurableSet (lowSet g) :=
  (measurableSet_highSet g).compl

theorem measurableSet_nearOneLowSet (g : Lp ℝ 2 μ) (δ : ℝ) :
    MeasurableSet (nearOneLowSet g δ) :=
  (measurableSet_lowSet g).inter
    (measurableSet_le measurable_const (Lp.stronglyMeasurable g).measurable)

theorem disjoint_highSet_lowSet (g : Lp ℝ 2 μ) : Disjoint (highSet g) (lowSet g) :=
  disjoint_compl_right

theorem highSet_union_lowSet (g : Lp ℝ 2 μ) : highSet g ∪ lowSet g = univ :=
  union_compl_self _

theorem setIntegral_highSet (g : Lp ℝ 2 μ) :
    ∫ x in highSet g, g x ∂μ = μ.real (highSet g) := by
  calc
    ∫ x in highSet g, g x ∂μ = ∫ _ in highSet g, (1 : ℝ) ∂μ :=
      setIntegral_congr_fun (measurableSet_highSet g) fun _ hx => hx
    _ = μ.real (highSet g) := by simp

variable [IsFiniteMeasure μ]

/-- On the high part, the set integral of `1 - uₙ` tends to zero. -/
theorem WeaklyConverges.high_deficit {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges u g) :
    Tendsto (fun n => μ.real (highSet g) - ∫ x in highSet g, u n x ∂μ)
      atTop (𝓝 0) := by
  simpa only [setIntegral_highSet, sub_self] using
    (tendsto_const_nhds (x := μ.real (highSet g))).sub
      (hu.setIntegral (measurableSet_highSet g))

/-- For indicator sequences, the deficit is exactly the high-set mass missed by
the corresponding event. -/
theorem high_deficit_indicator (g : Lp ℝ 2 μ) {A : Set Ω} (hA : MeasurableSet A) :
    μ.real (highSet g) -
        ∫ x in highSet g, indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) x ∂μ =
      μ.real (highSet g \ A) := by
  rw [setIntegral_indicatorConstLp (measurableSet_highSet g)]
  simp only [smul_eq_mul, mul_one, Set.inter_comm A]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := highSet g) hA
  linarith

/-- The missed mass on the one fixed high set tends to zero along the common
weakly convergent subsequence of query indicators. -/
theorem high_miss_tendsto_zero (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges
      (fun n => indicatorConstLp 2 (hA n) (measure_ne_top μ (A n)) (1 : ℝ)) g) :
    Tendsto (fun n => μ.real (highSet g \ A n)) atTop (𝓝 0) := by
  simpa only [high_deficit_indicator] using hu.high_deficit

/-- The low part has vanishing mass arbitrarily close to the value one.  The
upper bound on `g` is required only almost everywhere. -/
theorem tendsto_measure_nearOneLowSet (g : Lp ℝ 2 μ)
    (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    Tendsto (fun n : ℕ => μ (nearOneLowSet g ((1 / 2 : ℝ) ^ n))) atTop (𝓝 0) := by
  let s : ℕ → Set Ω := fun n => nearOneLowSet g ((1 / 2 : ℝ) ^ n)
  have hs : ∀ n, NullMeasurableSet (s n) μ :=
    fun n => (measurableSet_nearOneLowSet g _).nullMeasurableSet
  have hm : Antitone s := by
    intro n m hnm x hxm
    refine ⟨hxm.1, ?_⟩
    have hp : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
    exact (sub_le_sub_left hp 1).trans hxm.2
  have hz : μ (⋂ n, s n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hg1] with x hx1
    intro hx
    have hxlow : g x ≠ 1 := (mem_iInter.mp hx 0).1
    have hxnear : ∀ n, 1 - (1 / 2 : ℝ) ^ n ≤ g x := fun n => (mem_iInter.mp hx n).2
    have ht : Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
    exact hxlow (le_antisymm hx1 (le_of_tendsto' ht hxnear))
  simpa only [hz, Function.comp_def, s] using
    tendsto_measure_iInter_atTop hs hm ⟨0, measure_ne_top μ _⟩

theorem tendsto_measureReal_nearOneLowSet (g : Lp ℝ 2 μ)
    (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    Tendsto (fun n : ℕ => μ.real (nearOneLowSet g ((1 / 2 : ℝ) ^ n)))
      atTop (𝓝 0) := by
  simpa only [ENNReal.toReal_zero, Measure.real, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_measure_nearOneLowSet g hg1)

/-- A single positive rational margin works for finitely many fixed low sets.
It is chosen from the limits and the error tolerance, independently of any
eventual pool size. -/
theorem exists_rational_low_margin (g : ℕ → Lp ℝ 2 μ)
    (hg1 : ∀ i, ∀ᵐ x ∂μ, g i x ≤ 1) (ℓ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ i < ℓ, μ.real (nearOneLowSet (g i) (2 * (τ : ℝ))) < η := by
  have hev : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin ℓ, μ.real (nearOneLowSet (g i) ((1 / 2 : ℝ) ^ n)) < η := by
    exact Filter.eventually_all.mpr fun i =>
      (tendsto_measureReal_nearOneLowSet (g i) (hg1 i)).eventually (gt_mem_nhds hη)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop 2).and hev).exists
  refine ⟨(1 / 2 : ℚ) ^ (n + 1), by positivity, ?_, ?_⟩
  · have hp : (1 / 2 : ℚ) ^ (n + 1) ≤ (1 / 2 : ℚ) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp ⊢
    linarith
  · intro i hi
    have heq : 2 * (((1 / 2 : ℚ) ^ (n + 1) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ n := by
      push_cast
      rw [pow_succ]
      ring
    rw [heq]
    exact hsmall ⟨i, hi⟩

end Klr.Pool
