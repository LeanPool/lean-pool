/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Birkhoff.Mean

/-!
# The oscillation set

Stage 3: `oscIO σ f ε`, the set where the Birkhoff averages oscillate by at least `ε`
infinitely often. Its measure is controlled by the maximal inequality, which is what upgrades
convergence on a dense set to convergence a.e.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Finset

open scoped ENNReal

open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

variable {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}
/-- The "oscillates by at least `ε` infinitely often" set of `dyn.tex`:
`∀ N, ∃ m n ≥ N, |Aₘf(x) - Aₙf(x)| ≥ ε`. The Birkhoff averages converge at `x` exactly when `x`
avoids this set for every `ε = 1/(k+1)`, since `ℝ` is complete. -/
def oscIO (σ : Ω → Ω) (f : Ω → ℝ) (ε : ℝ) : Set Ω :=
  {x | ∀ N : ℕ, ∃ m n, N ≤ m ∧ N ≤ n ∧
        ε ≤ |birkhoffAverage ℝ σ f m x - birkhoffAverage ℝ σ f n x|}

omit [MeasurableSpace Ω] in
/-- The comparison at the heart of the transfer argument: if the averages of `f` oscillate by
`3ε` infinitely often, then either those of `f'` oscillate by `ε` infinitely often, or the
maximal function of `f - f'` exceeds `ε`.

This is the inclusion `dyn.tex` uses to run the `ε/3` estimate, and it is pure pointwise
algebra: `|Aₘf - Aₙf| ≤ |Aₘf' - Aₙf'| + |Aₘ(f-f')| + |Aₙ(f-f')|`, so if the left side is `≥ 3ε`
and the first right-hand term is `< ε`, one of the last two exceeds `ε`. -/
theorem oscIO_subset (σ : Ω → Ω) (f f' : Ω → ℝ) {ε : ℝ} :
    oscIO σ f (3 * ε) ⊆ oscIO σ f' ε
      ∪ {x | ∃ j, 1 ≤ j ∧ ε * j < birkhoffSum σ (fun y => |f y - f' y|) j x} := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- Failing the second set means every average of `|f - f'|` is at most `ε`.
  have hsmall : ∀ j : ℕ, 1 ≤ j → birkhoffSum σ (fun y => |f y - f' y|) j x ≤ ε * j := by
    intro j hj
    by_contra hc
    exact h2 ⟨j, hj, not_le.mp hc⟩
  -- Failing the first means the `f'` averages stop oscillating beyond some `N`.
  simp only [oscIO, Set.mem_ofPred_eq] at h1
  push Not at h1
  obtain ⟨N, hN⟩ := h1
  obtain ⟨m, n, hm, hn, hmn⟩ := hx (max N 1)
  have hmN : N ≤ m := le_trans (le_max_left N 1) hm
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hm1 : 1 ≤ m := le_trans (le_max_right N 1) hm
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hf'lt : |birkhoffAverage ℝ σ f' m x - birkhoffAverage ℝ σ f' n x| < ε := hN m n hmN hnN
  -- Each error term `|Aₖf - Aₖf'| ≤ Aₖ|f - f'| ≤ ε`.
  have herr : ∀ k : ℕ, 1 ≤ k →
      |birkhoffSum σ f k x / k - birkhoffSum σ f' k x / k| ≤ ε := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [← sub_div, abs_div, abs_of_pos hk0, div_le_iff₀ hk0]
    refine le_trans ?_ (hsmall k hk)
    have hdiff : birkhoffSum σ f k x - birkhoffSum σ f' k x
        = birkhoffSum σ (fun y => f y - f' y) k x := by
      simp [birkhoffSum, Finset.sum_sub_distrib]
    rw [hdiff]
    simpa [birkhoffSum] using
      Finset.abs_sum_le_sum_abs (fun i => f (σ^[i] x) - f' (σ^[i] x)) (Finset.range k)
  -- `|Aₘf - Aₙf| ≤ |Aₘf' - Aₙf'| + |Aₘf - Aₘf'| + |Aₙf - Aₙf'| < ε + ε + ε = 3ε`.
  have hchain : |birkhoffAverage ℝ σ f m x - birkhoffAverage ℝ σ f n x|
      ≤ |birkhoffAverage ℝ σ f' m x - birkhoffAverage ℝ σ f' n x|
        + |birkhoffSum σ f m x / m - birkhoffSum σ f' m x / m|
        + |birkhoffSum σ f n x / n - birkhoffSum σ f' n x / n| := by
    simp only [birkhoffAverage_real]
    set A := birkhoffSum σ f m x / m
    set B := birkhoffSum σ f n x / n
    set A' := birkhoffSum σ f' m x / m
    set B' := birkhoffSum σ f' n x / n
    calc |A - B| = |(A' - B') + (A - A') + -(B - B')| := by congr 1; ring
      _ ≤ |(A' - B') + (A - A')| + |-(B - B')| := abs_add_le _ _
      _ ≤ |A' - B'| + |A - A'| + |B - B'| := by
          rw [abs_neg]
          linarith [abs_add_le (A' - B') (A - A')]
  linarith [hmn, hf'lt, herr m hm1, herr n hn1, hchain]

/-- `oscIO` is measurable: it is a countable `⋂_N ⋃_m ⋃_n` of preimages of closed rays. -/
theorem measurableSet_oscIO (hσ : Measurable σ) (hfm : Measurable f) (ε : ℝ) :
    MeasurableSet (oscIO σ f ε) := by
  have hbs : ∀ k : ℕ, Measurable (birkhoffSum σ f k) := by
    intro k
    change Measurable fun x => ∑ i ∈ Finset.range k, f (σ^[i] x)
    exact Finset.measurable_sum _ (fun i _ => hfm.comp (hσ.iterate i))
  have hrw : oscIO σ f ε =
      ⋂ N : ℕ, ⋃ m : ℕ, ⋃ _ : N ≤ m, ⋃ n : ℕ, ⋃ _ : N ≤ n,
        {x | ε ≤ |birkhoffAverage ℝ σ f m x - birkhoffAverage ℝ σ f n x|} := by
    ext x
    simp only [oscIO, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h N
      obtain ⟨m, n, hm, hn, hlt⟩ := h N
      exact ⟨m, hm, n, hn, hlt⟩
    · intro h N
      obtain ⟨m, hm, n, hn, hlt⟩ := h N
      exact ⟨m, n, hm, hn, hlt⟩
  rw [hrw]
  refine MeasurableSet.iInter fun N => ?_
  refine MeasurableSet.iUnion fun m => ?_
  refine MeasurableSet.iUnion fun _ => ?_
  refine MeasurableSet.iUnion fun n => ?_
  refine MeasurableSet.iUnion fun _ => ?_
  simp only [birkhoffAverage_real]
  exact measurableSet_le measurable_const
    (((hbs m).div_const _).sub ((hbs n).div_const _)).abs

/-- **The transfer lemma.** If the Birkhoff averages of `f'` converge a.e. and `f'` approximates
`f` in `L¹`, the oscillation set of `f` at scale `3ε` is small — quantitatively,
`μ(oscIO f 3ε) ≤ ‖f - f'‖₁ / ε`.

This is the `ε/3` estimate of `dyn.tex` stage 4, and it is what lets a.e. convergence be
transported along an `L¹`-dense set. The retained independent `L²` proof uses it to pass
from exact coboundaries to `closure H`. The general `L¹` endpoint reuses the pool theorem. -/
theorem measureReal_oscIO_le [IsFiniteMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (f f' : Ω → ℝ) (hfm : Measurable f) (hf'm : Measurable f')
    (hdiff : Integrable (fun x => |f x - f' x|) μ) {ε : ℝ} (hε : 0 < ε)
    (hconv : μ.real (oscIO σ f' ε) = 0) :
    ε * μ.real (oscIO σ f (3 * ε)) ≤ ∫ x, |f x - f' x| ∂μ := by
  set D : Ω → ℝ := fun x => |f x - f' x| with hDdef
  have hDm : Measurable D := (hfm.sub hf'm).abs
  have hDabs : ∀ x, |D x| = D x := fun x => abs_of_nonneg (abs_nonneg _)
  -- The maximal set on the right of `oscIO_subset`.
  set M : Set Ω := {x | ∃ j, 1 ≤ j ∧ ε * j < birkhoffSum σ D j x} with hMdef
  have hsub := oscIO_subset σ f f' (ε := ε)
  -- `μ(oscIO f 3ε) ≤ μ(oscIO f' ε) + μ(M) = μ(M)`.
  have hle : μ.real (oscIO σ f (3 * ε)) ≤ μ.real M := by
    have h1 : μ.real (oscIO σ f (3 * ε)) ≤ μ.real (oscIO σ f' ε ∪ M) :=
      measureReal_mono hsub (by finiteness)
    have h2 : μ.real (oscIO σ f' ε ∪ M) ≤ μ.real (oscIO σ f' ε) + μ.real M :=
      measureReal_union_le _ _
    rw [hconv, zero_add] at h2
    linarith
  -- and `ε · μ(M) ≤ ‖D‖₁` is the global maximal inequality.
  have hglob := maximal_inequality_global (f := D) (ε := ε) hmp hdiff hDm
  simp only [hDabs] at hglob
  calc ε * μ.real (oscIO σ f (3 * ε)) ≤ ε * μ.real M := by
        exact mul_le_mul_of_nonneg_left hle hε.le
    _ ≤ ∫ x, D x ∂μ := hglob

omit [MeasurableSpace Ω] in
/-- Avoiding every oscillation set is exactly convergence, by completeness of `ℝ`. -/
theorem tendsto_of_notMem_oscIO (σ : Ω → Ω) (f : Ω → ℝ) (x : Ω)
    (hx : ∀ k : ℕ, x ∉ oscIO σ f (1 / (k + 1 : ℝ))) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n x) Filter.atTop (nhds L) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨k, hkgt⟩ := exists_nat_gt (1 / δ)
  have hk : 1 / ((k : ℝ) + 1) < δ := by
    have h0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : 1 / δ < (k : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ h0]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hxk := hx k
  simp only [oscIO, Set.mem_ofPred_eq] at hxk
  push Not at hxk
  obtain ⟨N, hN⟩ := hxk
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_lt_of_le (hN m n hm hn) hk.le

/-- **A.e. convergence transfers along an `L¹`-dense set.** If every `f'` in `D` has a.e.
convergent Birkhoff averages, and `f` can be approximated in `L¹` by members of `D` to arbitrary
accuracy, then `f` has a.e. convergent Birkhoff averages.

The independent `L²` proof applies this to pass from exact coboundaries to `closure H`.
The general `L¹` endpoint is supplied by the pool's existing theorem. -/
theorem ae_tendsto_birkhoffAverage_of_dense [IsFiniteMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (f : Ω → ℝ) (hfm : Measurable f)
    (happrox : ∀ η : ℝ, 0 < η → ∃ f' : Ω → ℝ, Measurable f' ∧
      Integrable (fun x => |f x - f' x|) μ ∧ (∫ x, |f x - f' x| ∂μ) < η ∧
      ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
        (fun n : ℕ => birkhoffAverage ℝ σ f' n x) Filter.atTop (nhds L)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n x) Filter.atTop (nhds L) := by
  -- Every oscillation set of `f` is null.
  have hnull : ∀ k : ℕ, μ.real (oscIO σ f (1 / (k + 1 : ℝ))) = 0 := by
    intro k
    set c : ℝ := 1 / (k + 1 : ℝ) with hcdef
    have hc : 0 < c := by rw [hcdef]; positivity
    -- Work at scale `ε = c/3`, so that `3ε = c`.
    set ε : ℝ := c / 3 with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    have h3 : 3 * ε = c := by rw [hεdef]; ring
    refine le_antisymm (le_of_forall_pos_le_add fun r hr => ?_) measureReal_nonneg
    rw [zero_add]
    -- Given `r > 0`, approximate to within `ε · r` and apply the transfer estimate.
    obtain ⟨f', hf'm, hdiff, hsmall, hf'conv⟩ := happrox (ε * r) (by positivity)
    have hf'null : μ.real (oscIO σ f' ε) = 0 := by
      -- `f'` converges a.e., so it avoids every oscillation set a.e.
      have : ∀ᵐ x ∂μ, x ∉ oscIO σ f' ε := by
        filter_upwards [hf'conv] with x hx
        obtain ⟨L, hL⟩ := hx
        intro hmem
        rw [Metric.tendsto_atTop] at hL
        obtain ⟨N, hNa⟩ := hL (ε / 2) (by positivity)
        obtain ⟨m, n, hm, hn, hlt⟩ := hmem N
        have h1 := hNa m hm
        have h2 := hNa n hn
        rw [Real.dist_eq] at h1 h2
        have hA := abs_lt.mp h1
        have hB := abs_lt.mp h2
        have hlt2 : |birkhoffAverage ℝ σ f' m x - birkhoffAverage ℝ σ f' n x| < ε :=
          abs_lt.mpr ⟨by linarith [hA.1, hA.2, hB.1, hB.2],
                      by linarith [hA.1, hA.2, hB.1, hB.2]⟩
        linarith
      simp [measureReal_def, measure_eq_zero_iff_ae_notMem.mpr this]
    have hkey := measureReal_oscIO_le hmp f f' hfm hf'm hdiff hε hf'null
    rw [h3] at hkey
    -- `ε · μ(oscIO f c) ≤ ‖f - f'‖₁ < ε · r`, so `μ(oscIO f c) < r`.
    have hlt : ε * μ.real (oscIO σ f c) < ε * r := lt_of_le_of_lt hkey hsmall
    exact le_of_lt (lt_of_mul_lt_mul_left hlt hε.le)
  -- Countably many null sets: a.e. `x` avoids all of them, hence converges.
  have hae : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∉ oscIO σ f (1 / (k + 1 : ℝ)) := by
    rw [ae_all_iff]
    intro k
    have h0 : μ (oscIO σ f (1 / (k + 1 : ℝ))) = 0 := by
      have := hnull k
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ _)] at this
    exact measure_eq_zero_iff_ae_notMem.mp h0
  filter_upwards [hae] with x hx
  exact tendsto_of_notMem_oscIO σ f x hx

/-- A.e. convergence of Birkhoff averages is additive in the observable. Needed to recombine the
two summands of the orthogonal decomposition `L² = closure H ⊕ Hᗮ`. -/
theorem ae_tendsto_birkhoffAverage_add {f g : Ω → ℝ}
    (hf : ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n x) Filter.atTop (nhds L))
    (hg : ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ g n x) Filter.atTop (nhds L)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (fun y => f y + g y) n x) Filter.atTop (nhds L) := by
  filter_upwards [hf, hg] with x hx hy
  obtain ⟨L₁, hL₁⟩ := hx
  obtain ⟨L₂, hL₂⟩ := hy
  refine ⟨L₁ + L₂, ?_⟩
  refine (hL₁.add hL₂).congr (fun n => ?_)
  simp only [birkhoffAverage_real]
  rw [← add_div]
  congr 1
  exact (birkhoffSum_add_apply σ f g n x).symm

/-- On a finite measure space, square-integrable implies integrable. This is the bridge that lets
`ae_tendsto_birkhoffAverage_of_dense` — whose approximation hypothesis is stated in `L¹` —
consume `L²`-density
facts. -/
theorem integrable_of_sq_integrable [IsFiniteMeasure μ] {h : Ω → ℝ} (hm : Measurable h)
    (hsq : Integrable (fun x => (h x) ^ 2) μ) :
    Integrable h μ := by
  have hmem : MemLp h 2 μ := by
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    exact hsq
  exact memLp_one_iff_integrable.mp (hmem.mono_exponent one_le_two)

/-- The orthogonal decomposition driving stage 4: every `g` in a Hilbert space splits as
`y + z` with `y` orthogonal to all coboundaries (hence `U`-invariant, by
`inner_sub_id_eq_zero_iff`) and `z` in the closure of the coboundary subspace.

Taking `K = Hᗮ` rather than `H` itself is what makes this immediate: orthogonal complements are
always closed, so `K.HasOrthogonalProjection` holds with no side condition, and
`Submodule.orthogonal_orthogonal_eq_closure` identifies `Kᗮ = Hᗮᗮ` with `closure H`. -/
theorem exists_orthogonal_decomposition {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) (g : H) :
    ∃ y z : H, U y = y ∧
      z ∈ (LinearMap.range (U.toLinearMap - LinearMap.id)).topologicalClosure ∧ g = y + z := by
  set K : Submodule ℝ H := (LinearMap.range (U.toLinearMap - LinearMap.id))ᗮ with hK
  obtain ⟨y, hy, z, hz, hg⟩ := K.exists_add_mem_mem_orthogonal g
  refine ⟨y, z, ?_, ?_, hg⟩
  · exact (inner_sub_id_eq_zero_iff U y).mp (fun f => hy _ ⟨f, by simp⟩)
  · rwa [hK, Submodule.orthogonal_orthogonal_eq_closure] at hz

/-- A.e.-equal observables have a.e.-equal Birkhoff sums, simultaneously for all `n`.
Indispensable for stage 4, where the decomposition happens at the level of `Lp` *elements* but
the conclusion is about their function representatives. -/
theorem birkhoffSum_congr_ae (hmp : MeasurePreserving σ μ μ) {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum σ f n x = birkhoffSum σ g n x := by
  have hiter : ∀ i : ℕ, ∀ᵐ x ∂μ, f (σ^[i] x) = g (σ^[i] x) := fun i =>
    (hmp.iterate i).quasiMeasurePreserving.ae_eq_comp h
  rw [← ae_all_iff] at hiter
  filter_upwards [hiter] with x hx n
  exact Finset.sum_congr rfl (fun i _ => hx i)

/-- A.e. convergence of Birkhoff averages only depends on the a.e.-class of the observable. -/
theorem ae_tendsto_birkhoffAverage_congr (hmp : MeasurePreserving σ μ μ) {f g : Ω → ℝ}
    (h : f =ᵐ[μ] g)
    (hf : ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n x) Filter.atTop (nhds L)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ g n x) Filter.atTop (nhds L) := by
  filter_upwards [hf, birkhoffSum_congr_ae hmp h] with x hx heq
  obtain ⟨L, hL⟩ := hx
  refine ⟨L, hL.congr (fun n => ?_)⟩
  simp only [birkhoffAverage_real, heq n]

/-- On a probability space, closeness in `L²` gives closeness in `L¹`: `‖u - v‖₁ ≤ ‖u - v‖₂`.
Cauchy–Schwarz, in the form `eLpNorm_le_eLpNorm_of_exponent_le`. -/
theorem integral_abs_sub_le_norm [IsProbabilityMeasure μ] (u v : Lp ℝ 2 μ) :
    ∫ x, |(u : Ω → ℝ) x - (v : Ω → ℝ) x| ∂μ ≤ ‖u - v‖ := by
  set w : Lp ℝ 2 μ := u - v with hw
  have hcoe : (w : Ω → ℝ) =ᵐ[μ] fun x => (u : Ω → ℝ) x - (v : Ω → ℝ) x := Lp.coeFn_sub u v
  have hint : Integrable (w : Ω → ℝ) μ := (Lp.memLp w).integrable one_le_two
  -- Replace the pointwise difference by the representative of `w`.
  have hEq : ∫ x, |(u : Ω → ℝ) x - (v : Ω → ℝ) x| ∂μ = ∫ x, ‖(w : Ω → ℝ) x‖ ∂μ := by
    refine (integral_congr_ae ?_).symm
    filter_upwards [hcoe] with x hx
    rw [hx, Real.norm_eq_abs]
  rw [hEq, integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable w),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable w), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top w)
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

end MultiplicativeErgodic
