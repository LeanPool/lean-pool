/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

import LeanPool.PointwiseBirkhoff.Main
public import Mathlib.Dynamics.Ergodic.Function

public import LeanPool.MultiplicativeErgodic.Birkhoff.OscIO

/-!
# Convergence of the Birkhoff averages

An independent `L²` convergence proof and an adapter to the pool’s `L¹` Birkhoff theorem,
plus the comparison of `Aₙf(σx)` with `Aₙf(x)`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Finset

open scoped ENNReal

open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

variable {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}
/-- **The `L²` case of Birkhoff's theorem.** For a square-integrable observable the Birkhoff
averages converge a.e.

This is where the whole stage-4 apparatus meets: `exists_orthogonal_decomposition` splits the
`L²` element into an invariant part and a limit of coboundaries; the invariant part is handled by
`ae_tendsto_birkhoffAverage_of_invariant` (through `koopman_eq_self_iff`), the coboundary part by
`ae_tendsto_birkhoffAverage_of_dense` fed with `ae_tendsto_birkhoffAverage_of_coboundary`; and
`ae_tendsto_birkhoffAverage_add` recombines them, with `ae_tendsto_birkhoffAverage_congr` moving
between `Lp` elements and their representatives. -/
theorem ae_tendsto_birkhoffAverage_of_memLp_two [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving σ μ μ) (hσ : Measurable σ) (F : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (F : Ω → ℝ) n x) Filter.atTop (nhds L) := by
  obtain ⟨y, z, hy, hz, hF⟩ := exists_orthogonal_decomposition (koopman hmp) F
  -- The invariant summand.
  have hyconv : ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (y : Ω → ℝ) n x) Filter.atTop (nhds L) := by
    filter_upwards [ae_tendsto_birkhoffAverage_of_invariant hmp (y : Ω → ℝ)
      ((koopman_eq_self_iff hmp y).mp hy)] with x hx
    exact ⟨_, hx⟩
  -- The coboundary summand: approximate `z` by exact coboundaries in `L²`, hence in `L¹`.
  have hzconv : ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (z : Ω → ℝ) n x) Filter.atTop (nhds L) := by
    refine ae_tendsto_birkhoffAverage_of_dense hmp hσ (z : Ω → ℝ)
      (Lp.stronglyMeasurable z).measurable ?_
    intro η hη
    -- Pick a coboundary within `η` of `z` in the `L²` norm.
    have hmem : (z : Lp ℝ 2 μ) ∈ closure
        ((LinearMap.range ((koopman hmp).toLinearMap - LinearMap.id) : Submodule ℝ (Lp ℝ 2 μ)) :
          Set (Lp ℝ 2 μ)) := by
      rwa [← Submodule.topologicalClosure_coe]
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨k, hkmem, hkdist⟩ := hmem η hη
    obtain ⟨h, hh⟩ := hkmem
    refine ⟨(k : Ω → ℝ), (Lp.stronglyMeasurable k).measurable, ?_, ?_, ?_⟩
    · exact ((Lp.memLp z).integrable one_le_two).sub
        ((Lp.memLp k).integrable one_le_two) |>.abs
    · calc ∫ x, |(z : Ω → ℝ) x - (k : Ω → ℝ) x| ∂μ ≤ ‖z - k‖ := integral_abs_sub_le_norm z k
        _ = dist z k := by rw [dist_eq_norm]
        _ < η := hkdist
    · -- `k = U h - h = h ∘ σ - h`; the coboundary lemma is stated for `g - g ∘ σ`, so run it
      -- with `g = -h`, for which `g - g ∘ σ = h ∘ σ - h = k`.
      set g : Ω → ℝ := fun x => -((h : Ω → ℝ) x) with hgdef
      have hgm : Measurable g := ((Lp.stronglyMeasurable h).measurable).neg
      have hgsq : Integrable (fun x => (g x) ^ 2) μ := by
        have := memLp_two_iff_integrable_sq
          ((Lp.stronglyMeasurable h).measurable).aestronglyMeasurable |>.mp (Lp.memLp h)
        simpa [hgdef] using this
      refine ae_tendsto_birkhoffAverage_congr (f := fun x => g x - g (σ x)) hmp ?_ ?_
      · -- `(g - g ∘ σ) =ᵐ k`
        have h1 : ((koopman hmp) h - h : Lp ℝ 2 μ) = k := by rw [← hh]; rfl
        have h2 := Lp.coeFn_sub ((koopman hmp) h) h
        rw [h1] at h2
        have h3 : ((koopman hmp) h : Ω → ℝ) =ᵐ[μ] (h : Ω → ℝ) ∘ σ :=
          Lp.coeFn_compMeasurePreserving h hmp
        filter_upwards [h2, h3] with x hx2 hx3
        simp only [Pi.sub_apply] at hx2
        rw [hx2, hx3]
        simp only [hgdef, Function.comp_apply]
        ring
      · filter_upwards [ae_tendsto_birkhoffAverage_of_coboundary hmp g hgm hgsq] with x hx
        exact ⟨_, hx⟩
  -- Recombine.
  refine ae_tendsto_birkhoffAverage_congr hmp ?_ (ae_tendsto_birkhoffAverage_add hyconv hzconv)
  rw [hF]
  filter_upwards [Lp.coeFn_add y z] with x hx
  exact hx.symm

/-- **Birkhoff's pointwise ergodic theorem.** The averages of an integrable observable
converge almost everywhere. This adapter reuses the pool's conditional-expectation theorem;
the preceding maximal, density and square-integrable infrastructure remains independently usable. -/
theorem ae_tendsto_birkhoffAverage [IsProbabilityMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n x) Filter.atTop (nhds L) := by
  filter_upwards [LeanPool.PointwiseBirkhoff.birkhoffErgodicTheorem μ hmp hf hfm] with x hx
  exact ⟨_, hx⟩

/-!
### The ergodic case: identifying the limit

Birkhoff's theorem for an *ergodic* map says more than that a limit exists: the limit is
`∫ f ∂μ`. That identification is what every downstream consumer needs.
-/

omit [MeasurableSpace Ω] in
/-- Shifting the base point: `Sₙf(σω) = S_{n+1}f(ω) - f(ω)`. Pointwise, no hypotheses. -/
theorem birkhoffSum_comp_self (σ : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum σ f n (σ ω) = birkhoffSum σ f (n + 1) ω - f ω := by
  rw [congrFun (birkhoffSum_succ' σ f n) ω]
  simp only [Pi.add_apply, Function.comp_apply]
  ring

omit [MeasurableSpace Ω] in
/-- If the Birkhoff averages converge at `ω`, they converge at `σ ω` to the *same* limit.
Immediate from `birkhoffSum_comp_self`: `Aₙf(σω) = ((n+1)/n)·A_{n+1}f(ω) - f(ω)/n`, and
`(n+1)/n → 1` while `f(ω)/n → 0`. -/
theorem tendsto_birkhoffAverage_comp_self (σ : Ω → Ω) (f : Ω → ℝ) {ω : Ω} {L : ℝ}
    (hL : Filter.Tendsto (fun n : ℕ => birkhoffAverage ℝ σ f n ω) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℕ => birkhoffAverage ℝ σ f n (σ ω)) Filter.atTop (nhds L) := by
  simp only [birkhoffAverage_real] at hL ⊢
  have hratio : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) Filter.atTop (nhds 1) := by
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
    simpa [inv_div] using this
  -- `A_{n+1}f(ω) → L`
  have hshift : Filter.Tendsto (fun n : ℕ => birkhoffSum σ f (n + 1) ω / ((n : ℝ) + 1))
      Filter.atTop (nhds L) := by
    have := hL.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have hmain : Filter.Tendsto
      (fun n : ℕ => birkhoffSum σ f (n + 1) ω / ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ))
        - f ω / (n : ℝ)) Filter.atTop (nhds L) := by
    have hp := (hshift.mul hratio).sub (tendsto_const_div_atTop_nhds_zero_nat (f ω))
    simpa using hp
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [birkhoffSum_comp_self]
  field_simp

/-- Under ergodicity the a.e. limit of the Birkhoff averages is a.e. *constant*.

`limsup` of the averages is measurable and, by `tendsto_birkhoffAverage_comp_self`, invariant
under `σ`; Mathlib's `Ergodic.ae_eq_const_of_ae_eq_comp₀` then makes it a.e. constant. Where the
limit exists it agrees with the `limsup`, so the averages converge to that constant. -/
theorem exists_ae_tendsto_birkhoffAverage_const [IsProbabilityMeasure μ] (hσ : Ergodic σ μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∃ c : ℝ, ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n ω) Filter.atTop (nhds c) := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  set L : Ω → ℝ := fun ω => Filter.limsup (fun n : ℕ => birkhoffAverage ℝ σ f n ω) Filter.atTop
    with hLdef
  have hbm : ∀ n : ℕ, Measurable fun ω => birkhoffAverage ℝ σ f n ω := by
    intro n
    simp only [birkhoffAverage_real]
    exact (Finset.measurable_sum _ (fun i _ => hfm.comp (hmp.measurable.iterate i))).div_const _
  have hLm : Measurable L := Measurable.limsup hbm
  -- The averages converge a.e., and where they converge the limit is the `limsup`.
  have hconv := ae_tendsto_birkhoffAverage hmp f hfm hf
  have hLlim : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n ω) Filter.atTop (nhds (L ω)) := by
    filter_upwards [hconv] with ω hω
    obtain ⟨L', hL'⟩ := hω
    have : L ω = L' := hL'.limsup_eq
    rwa [this]
  -- `L` is `σ`-invariant, so ergodicity makes it a.e. constant.
  have hinv : L ∘ σ =ᵐ[μ] L := by
    have hσae : ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => birkhoffAverage ℝ σ f n (σ ω)) Filter.atTop (nhds (L ω)) := by
      filter_upwards [hLlim] with ω hω
      exact tendsto_birkhoffAverage_comp_self σ f hω
    filter_upwards [hσae] with ω hω
    exact hω.limsup_eq
  obtain ⟨c, hc⟩ := hσ.ae_eq_const_of_ae_eq_comp₀ hLm.nullMeasurable hinv
  refine ⟨c, ?_⟩
  filter_upwards [hLlim, hc] with ω hω hcω
  rwa [hcω] at hω

end MultiplicativeErgodic
