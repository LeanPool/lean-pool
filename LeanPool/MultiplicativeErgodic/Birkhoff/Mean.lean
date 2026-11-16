/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Order.Group.Lattice

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.PSeries

public import LeanPool.MultiplicativeErgodic.Birkhoff.Maximal

/-!
# Coboundaries, orbit decay, and the mean ergodic theorem

Stage 2: Birkhoff sums of a coboundary telescope, `L²` orbit decay by Chebyshev plus
Borel–Cantelli, and the Hilbert-space input (`koopman`, the orthogonal decomposition).
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Finset

open scoped ENNReal

open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

variable {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}
/-!
### Stage 3: a.e. convergence on the coboundary subspace

For `g = h - h ∘ σ` the Birkhoff sums telescope, so `Aₙg = (h - h ∘ σⁿ)/n`. Convergence to `0`
therefore reduces entirely to **orbit decay**, `h(σⁿx)/n → 0`.

`dyn.tex` obtains this for `h ∈ L²` by Chebyshev: `μ(|h| > εn) ≤ ‖h‖₂²/(εn)²`, which is summable
in `n`, so Borel–Cantelli applies. Working in `L²` rather than `L¹` is exactly what makes the
tail sum converge without any layer-cake estimate — and the restriction costs nothing, since
stage 4 recovers all of `L¹` by density.
-/

omit [MeasurableSpace Ω] in
/-- The Birkhoff sums of a coboundary telescope. -/
theorem birkhoffSum_coboundary (σ : Ω → Ω) (h : Ω → ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum σ (fun y => h y - h (σ y)) n x = h x - h (σ^[n] x) := by
  simp only [birkhoffSum]
  have hstep : ∀ k, h (σ (σ^[k] x)) = h (σ^[k + 1] x) := by
    intro k; rw [← Function.iterate_succ_apply' σ k x]
  simp only [hstep]
  exact Finset.sum_range_sub' (fun k => h (σ^[k] x)) n

/-- Level sets along the orbit have the same measure as the original level set, since `σ^[n]`
preserves `μ`. This is what turns the tail estimate for `h` into one for `h ∘ σⁿ`. -/
theorem measure_orbit_level (hmp : MeasurePreserving σ μ μ) (h : Ω → ℝ) (hm : Measurable h)
    (n : ℕ) (t : ℝ) :
    μ {x | t < |h (σ^[n] x)|} = μ {x | t < |h x|} := by
  have hiter : MeasurePreserving (σ^[n]) μ μ := hmp.iterate n
  have hmeas : MeasurableSet {x | t < |h x|} :=
    measurableSet_lt measurable_const hm.abs
  rw [← hiter.measure_preimage hmeas.nullMeasurableSet]
  rfl

/-- Orbit decay for an `L²` observable: `h(σⁿx)/n → 0` a.e.

Chebyshev plus Borel–Cantelli, as in `dyn.tex` stage 3. This independent argument does not
use Birkhoff. The `L¹` orbit-decay theorem instead uses the pool’s general pointwise
Birkhoff theorem through `ae_tendsto_birkhoffAverage`; neither route depends on Kingman. -/
theorem orbit_decay_of_sq_integrable [IsFiniteMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (h : Ω → ℝ) (hm : Measurable h) (hsq : Integrable (fun x => (h x) ^ 2) μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => h (σ^[n] x) / n) Filter.atTop (nhds 0) := by
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal ((h x) ^ 2) ∂μ with hIdef
  have hIfin : I ≠ ⊤ := by
    rw [hIdef]
    have hfi := hsq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (by filter_upwards with x using sq_nonneg _)] at hfi
    exact hfi.ne
  -- Chebyshev: `t² · μ{|h| > t} ≤ ∫ h²` for `t > 0`.
  have hcheb : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ 2) * μ {x | t < |h x|} ≤ I := by
    intro t ht
    have hsub : {x | t < |h x|} ⊆ {x | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((h x) ^ 2)} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      refine ENNReal.ofReal_le_ofReal ?_
      have := sq_abs (h x)
      nlinarith [abs_nonneg (h x)]
    calc ENNReal.ofReal (t ^ 2) * μ {x | t < |h x|}
        ≤ ENNReal.ofReal (t ^ 2) * μ {x | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((h x) ^ 2)} :=
          by gcongr
      _ ≤ I := mul_meas_ge_le_lintegral₀ ((hm.pow_const 2).ennreal_ofReal.aemeasurable) _
  -- For each `ε = 1/(k+1)` the bad events are summable, so Borel–Cantelli applies.
  have key : ∀ k : ℕ, ∀ᵐ x ∂μ,
      ∀ᶠ n in Filter.atTop, |h (σ^[n] x)| ≤ (1 / (k + 1 : ℝ)) * n := by
    intro k
    set ε : ℝ := 1 / (k + 1 : ℝ) with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    set S : ℕ → Set Ω := fun n => {x | ε * n < |h (σ^[n] x)|} with hSdef
    have hSlevel : ∀ n, μ (S n) = μ {x | ε * n < |h x|} :=
      fun n => measure_orbit_level hmp h hm n (ε * n)
    -- Tail bound from Chebyshev, in real form to keep the series manipulation in `ℝ`.
    have hbound : ∀ n : ℕ,
        μ (S (n + 1)) ≤ ENNReal.ofReal (I.toReal / ε ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) := by
      intro n
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have ht : (0 : ℝ) < ε * (((n + 1 : ℕ)) : ℝ) := by rw [hcast]; positivity
      have hc := hcheb (ε * (((n + 1 : ℕ)) : ℝ)) ht
      rw [← hSlevel (n + 1)] at hc
      have hr := ENNReal.toReal_mono hIfin hc
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hcast] at hr
      have hle : (μ (S (n + 1))).toReal ≤ I.toReal / ε ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        have hD : (0 : ℝ) < ε ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
        rw [show I.toReal / ε ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)
              = I.toReal / (ε ^ 2 * ((n : ℝ) + 1) ^ 2) by field_simp,
          le_div_iff₀ hD]
        nlinarith [hr]
      calc μ (S (n + 1)) = ENNReal.ofReal (μ (S (n + 1))).toReal :=
            (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hle
    -- Summability of the bound, hence of the tail measures.
    have hsummable : Summable (fun n : ℕ => I.toReal / ε ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) := by
      refine Summable.mul_left _ ?_
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase
      simpa using this
    have hsum : ∑' n : ℕ, μ (S n) ≠ ⊤ := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      refine ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, ?_⟩
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
      exact ENNReal.ofReal_ne_top
    -- Borel–Cantelli.
    have hbc := measure_setOfPred_frequently_eq_zero
      (μ := μ) (p := fun n x => ε * n < |h (σ^[n] x)|) hsum
    have hae : ∀ᵐ x ∂μ, ¬ (∃ᶠ n in Filter.atTop, ε * n < |h (σ^[n] x)|) := by
      rw [ae_iff]; simpa only [not_not] using hbc
    filter_upwards [hae] with x hx
    rw [Filter.not_frequently] at hx
    filter_upwards [hx] with n hn
    exact not_lt.mp hn
  -- Assemble over the countably many `k`, then translate into the limit statement.
  rw [← ae_all_iff] at key
  filter_upwards [key] with x hx
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k, hkgt⟩ := exists_nat_gt (1 / δ)
  have hk : 1 / ((k : ℝ) + 1) < δ := by
    have h0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : 1 / δ < (k : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ h0]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hx k)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos]
  calc |h (σ^[n] x)| / n ≤ ((1 / (k + 1 : ℝ)) * n) / n := by gcongr; exact hN n hnN
    _ = 1 / (k + 1 : ℝ) := by field_simp
    _ < δ := hk

/-- **Stage 3.** On the coboundary subspace `{h - h ∘ σ}` the Birkhoff averages converge to `0`
a.e. Immediate from `birkhoffSum_coboundary` and `orbit_decay_of_sq_integrable`. -/
theorem ae_tendsto_birkhoffAverage_of_coboundary [IsFiniteMeasure μ]
    (hmp : MeasurePreserving σ μ μ) (h : Ω → ℝ)
    (hm : Measurable h) (hsq : Integrable (fun x => (h x) ^ 2) μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (fun y => h y - h (σ y)) n x) Filter.atTop (nhds 0) := by
  filter_upwards [orbit_decay_of_sq_integrable hmp h hm hsq] with x hx
  have hfirst : Filter.Tendsto (fun n : ℕ => h x / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (h x)
  have := hfirst.sub hx
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [birkhoffAverage_real, birkhoffSum_coboundary, sub_div]

/-!
### The mean-ergodic splitting

The abstract Hilbert-space input to stage 4: for a linear isometry `U`, a vector is orthogonal
to the coboundary subspace `range (U - id)` exactly when it is `U`-invariant.

**Relation to Mathlib.** Mathlib *does* have the von Neumann mean ergodic theorem,
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` in
`Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`, and its proof establishes exactly this
identification inline. What is missing there is a reusable *statement* of it, which is what this
section supplies. Note the mean ergodic theorem gives `L²`-norm convergence of the Birkhoff
averages; the pointwise a.e. convergence built in this file is a strictly stronger conclusion and
does not follow from it.

`dyn.tex` obtains this through the adjoint (`U* g = g`, then
`‖f - f ∘ T‖² = 2⟪f,f⟫ - 2⟪T*f,f⟫ = 0`). No adjoint is in fact needed: testing orthogonality
against the single vector `f = g` already pins `⟪Ug, g⟫ = ⟪g, g⟫`, and `LinearIsometry`'s
`inner_map_map` finishes it. That is the whole proof below.
-/

section Hilbert

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A vector is orthogonal to every coboundary `U f - f` iff it is `U`-invariant. -/
theorem inner_sub_id_eq_zero_iff (U : H →ₗᵢ[ℝ] H) (g : H) :
    (∀ f : H, ⟪U f - f, g⟫ = 0) ↔ U g = g := by
  constructor
  · intro hf
    -- Testing against `f = g` gives `⟪Ug, g⟫ = ⟪g, g⟫`.
    have hsym : ⟪U g, g⟫ = ⟪g, g⟫ := by
      have := hf g
      rw [inner_sub_left] at this
      linarith [this]
    -- Then `‖Ug - g‖² = ‖g‖² - 2⟪Ug,g⟫ + ‖g‖² = 0`, using that `U` preserves inner products.
    have hnorm : ⟪U g - g, U g - g⟫ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        U.inner_map_map, real_inner_comm (U g) g, hsym]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hnorm)
  · intro hg f
    rw [inner_sub_left, ← hg, U.inner_map_map, hg]
    ring

/-- The same statement in `Submodule.orthogonal` form: the orthogonal complement of the
coboundary subspace is the fixed-point set of `U`. Feeding this to
`Submodule.orthogonal_orthogonal` (for the closed subspace `closure (range (U - id))`) is what
gives the `L² = closure H ⊕ Hᗮ` decomposition stage 4 needs. -/
theorem mem_orthogonal_range_sub_id_iff (U : H →ₗᵢ[ℝ] H) (g : H) :
    g ∈ (LinearMap.range (U.toLinearMap - LinearMap.id))ᗮ ↔ U g = g := by
  rw [← inner_sub_id_eq_zero_iff U g]
  constructor
  · intro hg f
    exact hg _ ⟨f, by simp⟩
  · rintro hg _ ⟨f, rfl⟩
    simpa using hg f

end Hilbert

/-- **Global maximal ergodic inequality**: the same weak-type bound with the supremum taken over
*all* `j ≥ 1`, not just `j ≤ n`.

Obtained from `maximal_inequality` by continuity from below: the finite-horizon sets increase to
the global one. This is the form the transfer argument of stage 4 needs, since there the maximal
function is not truncated. -/
theorem maximal_inequality_global [IsFiniteMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (hf : Integrable f μ) (hfm : Measurable f) {ε : ℝ} :
    ε * μ.real {x | ∃ j, 1 ≤ j ∧ ε * j < birkhoffSum σ f j x} ≤ ∫ x, |f x| ∂μ := by
  set E : ℕ → Set Ω := fun n => {x | ∃ j, 1 ≤ j ∧ j ≤ n ∧ ε * j < birkhoffSum σ f j x} with hEdef
  have hmono : Monotone E := by
    intro m n hmn x hx
    obtain ⟨j, hj1, hjm, hjlt⟩ := hx
    exact ⟨j, hj1, hjm.trans hmn, hjlt⟩
  have hunion : ⋃ n, E n = {x | ∃ j, 1 ≤ j ∧ ε * j < birkhoffSum σ f j x} := by
    ext x
    simp only [hEdef, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, j, hj1, _, hjlt⟩; exact ⟨j, hj1, hjlt⟩
    · rintro ⟨j, hj1, hjlt⟩; exact ⟨j, j, hj1, le_rfl, hjlt⟩
  -- Continuity from below, transported to the real-valued measure (all sets have finite measure).
  have htend : Filter.Tendsto (fun n => μ (E n)) Filter.atTop (nhds (μ (⋃ n, E n))) :=
    tendsto_measure_iUnion_atTop (μ := μ) hmono
  have htendR : Filter.Tendsto (fun n => μ.real (E n)) Filter.atTop
      (nhds (μ.real (⋃ n, E n))) := by
    rw [measureReal_def]
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend
  rw [← hunion]
  -- Each finite-horizon bound passes to the limit.
  refine le_of_tendsto (htendR.const_mul ε) ?_
  filter_upwards with n
  exact maximal_inequality hmp hf hfm n

/-!
### Stage 4: extension to all of `L¹`

The remaining step. `dyn.tex` finishes by decomposing `L²` as `H ⊕ Hᗮ`, where
`H = {g - g ∘ σ : g ∈ L²}` is the coboundary subspace (stage 3 handles `closure H`) and `Hᗮ`
is the `σ`-invariant functions (handled by
`ae_tendsto_birkhoffAverage_of_invariant` below), then transfers a.e.
convergence to all of `L¹` by density, using `maximal_inequality` to control the error.
-/

/-- On the invariant part the Birkhoff averages are constant: if `h ∘ σ = h` a.e. then
`Aₙh → h` a.e. This is the `Hᗮ` half of stage 4. -/
theorem ae_tendsto_birkhoffAverage_of_invariant (hmp : MeasurePreserving σ μ μ) (h : Ω → ℝ)
    (hinv : (fun x => h (σ x)) =ᵐ[μ] h) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ h n x) Filter.atTop (nhds (h x)) := by
  -- `h ∘ σⁿ = h` a.e., for every `n`, by induction along the orbit.
  have hqmp := hmp.quasiMeasurePreserving
  have hiter : ∀ n : ℕ, ∀ᵐ x ∂μ, h (σ^[n] x) = h x := by
    intro n
    induction n with
    | zero => filter_upwards with x; simp
    | succ n ih =>
      have hcomp : (fun x => h (σ^[n] (σ x))) =ᵐ[μ] (fun x => h (σ x)) :=
        hqmp.ae_eq_comp ih
      filter_upwards [hcomp, hinv] with x h1 h2
      rw [Function.iterate_succ_apply]
      exact h1.trans h2
  -- Hence a.e. `x` has `h (σⁿ x) = h x` simultaneously for all `n`.
  rw [← ae_all_iff] at hiter
  filter_upwards [hiter] with x hx
  -- `Sₙh(x) = n · h(x)`, so the average is constantly `h x` from `n = 1` on.
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsum : birkhoffSum σ h n x = n * h x := by
    simp only [birkhoffSum]
    rw [Finset.sum_congr rfl (fun k _ => hx k), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [birkhoffAverage_real, hsum, mul_comm, mul_div_assoc, div_self hn0, mul_one]

/-- The **Koopman operator** `U g = g ∘ σ` on `L²(μ)`, as a linear isometry. This is where the
abstract `inner_sub_id_eq_zero_iff` gets instantiated. -/
noncomputable def koopman (hmp : MeasurePreserving σ μ μ) : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ σ hmp

/-- Being a fixed point of the Koopman operator is being a.e. `σ`-invariant as a function.
This is the bridge between the `Lp`-level statement and the pointwise one that
`ae_tendsto_birkhoffAverage_of_invariant` consumes. -/
theorem koopman_eq_self_iff (hmp : MeasurePreserving σ μ μ) (g : Lp ℝ 2 μ) :
    koopman hmp g = g ↔ (fun x => (g : Ω → ℝ) (σ x)) =ᵐ[μ] (g : Ω → ℝ) := by
  have hco : (koopman hmp g : Ω → ℝ) =ᵐ[μ] (g : Ω → ℝ) ∘ σ :=
    Lp.coeFn_compMeasurePreserving g hmp
  constructor
  · intro h
    rw [h] at hco
    exact hco.symm
  · intro h
    exact Lp.ext (hco.trans h)

/-- The `Hᗮ` half of stage 4, at the `L²` level: an element orthogonal to every coboundary has
a.e.-convergent Birkhoff averages. Combines `inner_sub_id_eq_zero_iff` (which identifies `Hᗮ`
with the Koopman fixed points), `koopman_eq_self_iff` (which turns that into a.e. invariance of
the representative) and `ae_tendsto_birkhoffAverage_of_invariant`. -/
theorem ae_tendsto_birkhoffAverage_of_orthogonal (hmp : MeasurePreserving σ μ μ)
    (g : Lp ℝ 2 μ) (hg : ∀ f : Lp ℝ 2 μ, inner ℝ (koopman hmp f - f) g = 0) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (g : Ω → ℝ) n x) Filter.atTop (nhds ((g : Ω → ℝ) x)) :=
  ae_tendsto_birkhoffAverage_of_invariant hmp _ ((koopman_eq_self_iff hmp g).mp
    ((inner_sub_id_eq_zero_iff (koopman hmp) g).mp hg))

end MultiplicativeErgodic
