/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.Setting

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Bielecki-weighted L² norm of a process `X : ℝ → Ω → (Fin n → ℝ)`
on `[0, T]`:

  `‖X‖_β,T := sup_{t ∈ [0, T]} e^{-βt} · (E[‖X_t‖²])^{1/2}`.

For `β = 0` this is the standard `S²` norm; for `β > 0` it is
equivalent to `S²` but absorbs the Grönwall constant in the Picard
contraction estimate. -/
noncomputable def bieleckiNorm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (β T : ℝ) (X : ℝ → Ω → (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (Real.exp (-β * t)) *
      (∫⁻ ω, (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ∂P) ^ (1/2 : ℝ)

/-- The space of jointly measurable, `ℱ`-progressively measurable, almost-surely càdlàg
processes on `[0, T]` with values in `Fin n → ℝ` and finite Bielecki norm at weight `0`.

One difference from the literature's `S²([0, T]; ℝⁿ)`, recorded in the section note "The
`IsRegular` hypothesis and the `S²` norm" of `Ito/PicardSpace.lean`: the norm here is
`bieleckiNorm`, the weighted supremum over `t` of the `L²` norms, rather than the `L²` norm of
the supremum. -/
structure SBoundedProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The path map. -/
  X : ℝ → Ω → (Fin n → ℝ)
  /-- Joint measurability in `(t, ω)`. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- Each coordinate is progressively measurable for `ℱ`. -/
  adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i)
  /-- Almost-sure càdlàg paths. -/
  cadlag_paths : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- Finite Bielecki-norm at the standard weight `β = 0`. -/
  sup_L2 : bieleckiNorm (P := P) 0 T X < ⊤

/-- Freezing a process at the horizon does not change its Bielecki norm on `[0, T]`, since the
supremum runs over times at which the two processes agree. -/
theorem bieleckiNorm_min {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (β T : ℝ)
    (X : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun s ω => X (min s T) ω) = bieleckiNorm (P := P) β T X := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  simp only [min_eq_left ht.2]

/-- The Bielecki norm at weight `0` bounds the `L²` slice energy at every time of the window,
for any path map. -/
theorem lintegral_sq_le_bieleckiNorm_sq_raw {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
  have hle : (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ bieleckiNorm (P := P) 0 T Z := by
    unfold bieleckiNorm
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal (Real.exp (-0 * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) u hu)
    simp
  calc (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ((∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := pow_le_pow_left' hle 2

/-- The doubly-integrated energy of a path map frozen at the horizon, over any window. -/
theorem lintegral_lintegral_sq_stopOf_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ)) (hZm : Measurable (Function.uncurry Z)) (hT : 0 ≤ T)
    (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
  have hZi : ∀ i : Fin n, Measurable fun p : Ω × ℝ => Z (min p.2 T) p.1 i := fun i =>
    (measurable_pi_apply i).comp
      (hZm.comp ((measurable_snd.min measurable_const).prodMk measurable_fst))
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      (ENNReal.continuous_coe.measurable.comp (hZi i).nnnorm).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
    (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T',
        (∫⁻ ω, ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T',
          (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc
          (fun s hs => lintegral_sq_le_bieleckiNorm_sq_raw Z ⟨le_min hs.1 hT, min_le_right s T⟩)
    _ = (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) * volume (Set.Icc (0 : ℝ) T') :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
        rw [Real.volume_Icc, sub_zero, mul_comm]

namespace SBoundedProcess

/-- **The deterministic-time freeze.** `X.stop` is `X` on `[0, T]` and constant at `X T`
afterwards. It has the same Bielecki norm on `[0, T]`, and its `L²` bounds hold at every
horizon, which is what the Picard step's integrand hypotheses need. -/
noncomputable def stop {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) : SBoundedProcess (n := n) P ℱ T where
  X s ω := X.X (min s T) ω
  measurable_path :=
    X.measurable_path.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  adapted i := (X.adapted i).minTime T
  cadlag_paths := by
    filter_upwards [X.cadlag_paths] with ω hω
    intro t
    refine ⟨?_, ?_⟩
    · rcases lt_or_ge t T with ht | ht
      · have hXt : X.X (min t T) ω = X.X t ω := by rw [min_eq_left ht.le]
        have hev : (fun s => X.X s ω) =ᶠ[nhdsWithin t (Set.Ioi t)]
            fun s => X.X (min s T) ω := by
          filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio ht)] with s hs
          rw [min_eq_left (le_of_lt hs)]
        rw [hXt]
        exact ((hω t).1).congr' hev
      · have hXt : X.X (min t T) ω = X.X T ω := by rw [min_eq_right ht]
        have hev : (fun _ : ℝ => X.X T ω) =ᶠ[nhdsWithin t (Set.Ioi t)]
            fun s => X.X (min s T) ω := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [min_eq_right (le_of_lt (lt_of_le_of_lt ht hs))]
        rw [hXt]
        exact tendsto_const_nhds.congr' hev
    · intro i
      rcases le_or_gt t T with ht | ht
      · obtain ⟨L, hL⟩ := (hω t).2 i
        refine ⟨L, hL.congr' ?_⟩
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [min_eq_left (le_of_lt (lt_of_lt_of_le hs ht))]
      · refine ⟨X.X T ω i, tendsto_const_nhds.congr' ?_⟩
        filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioi ht)] with s hs
        rw [min_eq_right (le_of_lt hs)]
  sup_L2 := by
    rw [bieleckiNorm_min]
    exact X.sup_L2

/-- The second moment at a single time of `[0, T]` is bounded by the squared Bielecki norm. -/
theorem lintegral_sq_le_bieleckiNorm_sq {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
  have hle : (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal (Real.exp (-0 * t))
          * (∫⁻ ω, ∑ i, (‖Y.X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) u hu)
    simp
  calc (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ((∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := pow_le_pow_left' hle 2

/-- **The frozen process is `L²`-bounded at every nonnegative time**, not only on `[0, T]` —
this is what the Picard step's integrand hypotheses need at horizons beyond `T`. -/
theorem lintegral_sq_stop_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ ω, ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) :=
  Y.lintegral_sq_le_bieleckiNorm_sq ⟨le_min hs hT, min_le_right s T⟩

@[simp] theorem stop_apply {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) (s : ℝ) (ω : Ω) :
    X.stop.X s ω = X.X (min s T) ω := rfl

/-- On `[0, T]` the frozen process agrees with the original. -/
theorem stop_eq_of_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) {s : ℝ} (hs : s ≤ T) (ω : Ω) :
    X.stop.X s ω = X.X s ω := by
  rw [stop_apply, min_eq_left hs]

end SBoundedProcess

/-- **The Picard map step.** Given a candidate process `X` and the
coefficients `(μ, σ, γ)`, the next iterate is

  `Φ X : t ↦ x_0 + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
      + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`.

This is the actual Picard map — not a placeholder. The integrands
require joint measurability + adaptedness hypotheses on `X` together
with measurability of the coefficient functions; these are bundled as
explicit hypotheses to keep the map well-typed.

For now we provide ONLY the drift component `∫_0^t μ(s, X_s) ds`; the
Brownian and compensated-Poisson integral components require
additional measurability bundling that is built up in subsequent
lemmas. -/
noncomputable def picardStep_drift
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  x₀ + fun i => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise drift difference identity.** For any two
candidates `X, Y`, the difference of drift components is the Bochner
integral of the per-component drift-coefficient difference:

  `(drift X x₀ t ω - drift Y x₀ t ω) i
    = ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i) ds`.

This is just the algebraic identity that `picardStep_drift` cancels the
common `x₀` and pulls the integral subtraction componentwise — no
analytic content yet, but a load-bearing intermediate. -/
lemma picardStep_drift_diff
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    -- Integrability of each side (needed for `integral_sub`):
    (h_X_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    (picardStep_drift (E := E) coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
      = ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  unfold picardStep_drift
  -- LHS = ((x₀ + (fun i => ∫ ... μ(X) i)) - (x₀ + (fun i => ∫ ... μ(Y) i))) i
  --     = (∫ ... μ(X) i - ∫ ... μ(Y) i)  by add_sub_add_cancel
  --     = ∫ ... (μ(X) i - μ(Y) i)        by integral_sub
  simp only [Pi.add_apply, Pi.sub_apply, add_sub_add_left_eq_sub]
  exact (MeasureTheory.integral_sub h_X_int h_Y_int).symm

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector form of the drift difference identity.** Bundles the per-component
identity into a `funext` over `i : Fin n`.

  `drift X x₀ t ω - drift Y x₀ t ω
    = fun i => ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i)`. -/
lemma picardStep_drift_diff_vec
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω
      = fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  funext i
  exact picardStep_drift_diff coeffs X Y x₀ t ω i (h_X_int i) (h_Y_int i)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise L¹ Lipschitz bound on the drift step.**

For Lipschitz μ with rate `L_μ` componentwise, the i-th component of
the drift-step difference is bounded by the time-integral of the
componentwise difference:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ ∫ s in [0, t], |μ s (X s ω) i - μ s (Y s ω) i|`. -/
lemma picardStep_drift_diff_componentwise_norm_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ ∫ s in Set.Icc (0 : ℝ) t,
          |coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i| := by
  rw [picardStep_drift_diff coeffs X Y x₀ t ω i h_X_int h_Y_int]
  -- |∫ f| ≤ ∫ |f| via MeasureTheory.norm_integral_le_integral_norm specialized to ℝ.
  have h_sub_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume := h_X_int.sub h_Y_int
  -- For ℝ-valued integrand, ‖x‖ = |x|, so norm_integral_le_integral_norm gives
  -- |∫ f| ≤ ∫ |f|. The lemma is stated for normed groups; |·| is the ℝ-norm.
  have h := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))
    (f := fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
  -- ‖·‖ on ℝ is |·|, so the goal matches after rewriting.
  simpa [Real.norm_eq_abs] using h

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component Lipschitz bound on the drift step.**

Using the per-component Lipschitz hypothesis on `μ`, the i-th component
of the drift difference is bounded by `L_μ * ∫_0^t ‖X_s - Y_s‖ ds`:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ L_μ · ∫ s in [0, t], ‖X s ω - Y s ω‖`.

This is the operator-level statement that feeds the Bielecki-norm
contraction. -/
lemma picardStep_drift_diff_lipschitz_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    -- Per-component Lipschitz on μ: |μ s x₁ i - μ s x₂ i| ≤ L_μ · ‖x₁ - x₂‖.
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    -- And the integrand ‖X_s - Y_s‖ must itself be integrable for the RHS
    -- bound's `mul_integral` rewrite to be valid:
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ := by
  -- Chain the two preceding bounds:
  -- |·| ≤ ∫ |μ(X) i - μ(Y) i|        (norm_integral_le_integral_norm)
  --     ≤ ∫ L_μ * ‖X - Y‖             (Lipschitz, integral monotonicity)
  --     = L_μ * ∫ ‖X - Y‖             (constant pull-out)
  refine (picardStep_drift_diff_componentwise_norm_bound
    coeffs X Y x₀ t ω i h_X_int h_Y_int).trans ?_
  -- Now goal: ∫ |μ(X) i - μ(Y) i| ≤ L_μ * ∫ ‖X - Y‖.
  -- Use integral_mono_of_nonneg or set_integral_mono after rewriting RHS as integral.
  rw [show L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖
        = ∫ s in Set.Icc (0 : ℝ) t, L_μ * ‖X s ω - Y s ω‖ from
      (MeasureTheory.integral_const_mul L_μ _).symm]
  -- Integral monotonicity. Need: integrability of both integrands + pointwise ≤.
  refine MeasureTheory.setIntegral_mono_on ?_ ?_
    measurableSet_Icc (fun s _ => h_μ_lip s (X s ω) (Y s ω) i)
  · -- LHS integrable: |μ(X) i - μ(Y) i| ∈ L¹.
    exact (h_X_int.sub h_Y_int).abs
  · -- RHS integrable: L_μ * ‖X - Y‖ ∈ L¹.
    exact h_XY_diff_int.const_mul L_μ

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **L² Cauchy-Schwarz on `[0, t]`.** For non-negative `L²` function `f`,

  `(∫ s in [0, t], f s)² ≤ t · ∫ s in [0, t], (f s)²`.

Derivation: view `f` and the constant `1` as elements of
`L²(volume.restrict [0,t])`. The `L²` inner product is `⟨f, 1⟩ = ∫ f`,
the `L²`-norms are `‖f‖_2 = √(∫ f²)` and `‖1‖_2 = √t`, and Cauchy-
Schwarz gives `(∫ f)² ≤ (∫ f²) · t`. -/
lemma integral_sq_le_mul_integral_sq_on_Icc
    (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ f s)
    (hf_L2 : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∫ s in Set.Icc (0 : ℝ) t, f s) ^ 2
      ≤ t * ∫ s in Set.Icc (0 : ℝ) t, (f s) ^ 2 := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)
  -- Constant function 1 ∈ L²(μ) since μ is finite.
  have h_one_L2 : MeasureTheory.MemLp (1 : ℝ → ℝ) 2 μ := MeasureTheory.memLp_const 1
  have h_one_nn : (0 : ℝ → ℝ) ≤ᵐ[μ] 1 :=
    Filter.Eventually.of_forall (fun _ => zero_le_one)
  have h2c : Real.HolderConjugate 2 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  -- Convert MemLp 2 to MemLp (ENNReal.ofReal 2) for Hölder API.
  have hf_L2' : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  have h_one_L2' : MeasureTheory.MemLp (1 : ℝ → ℝ) (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  -- Hölder: ∫ f · 1 ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  have h_holder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) h2c hf_nn h_one_nn hf_L2' h_one_L2'
  -- LHS simplification: ∫ f · 1 = ∫ f.
  have h_lhs_eq : ∫ a, f a * (1 : ℝ → ℝ) a ∂μ = ∫ a, f a ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change f a * (1 : ℝ → ℝ) a = f a
    rw [Pi.one_apply, mul_one]
  -- ∫ 1² = ∫ 1 = t.
  have h_one_sq_eq_one :
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = ∫ _a : ℝ, (1 : ℝ) ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change ((1 : ℝ → ℝ) a) ^ 2 = (1 : ℝ)
    rw [Pi.one_apply, one_pow]
  have h_one_int : ∫ _a : ℝ, (1 : ℝ) ∂μ = t := by
    rw [MeasureTheory.integral_const]
    change (μ Set.univ).toReal • (1 : ℝ) = t
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht, smul_eq_mul, mul_one]
  have h_int_one_sq_eq_t : ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = t :=
    h_one_sq_eq_one.trans h_one_int
  rw [h_lhs_eq] at h_holder
  -- h_holder : ∫ f ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  -- The `1 a ^ 2` in h_holder doesn't syntactically match my h_int_one_sq_eq_t LHS
  -- (Lean's elaboration of Pi.one_apply differs). Use calc directly with both.
  -- h_holder uses `^ (2 : ℝ)` (real exponent from HolderConjugate). Convert.
  have h_rpow_two_eq_sq : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have h_f_sq_conv : ∫ a, f a ^ (2 : ℝ) ∂μ = ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq (f a))
  have h_one_sq_conv : ∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ =
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq _)
  have h_holder' : (∫ a, f a ∂μ) ≤
      (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
    have h_step1 : (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by rw [h_f_sq_conv]
    have h_step2 : (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        t ^ ((1 : ℝ) / 2) := by
      rw [h_one_sq_conv, h_int_one_sq_eq_t]
    calc (∫ a, f a ∂μ)
        ≤ (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
            (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := h_holder
      _ = (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
            rw [h_step1, h_step2]
  clear h_holder
  have h_LHS_nn : 0 ≤ ∫ a, f a ∂μ := MeasureTheory.integral_nonneg_of_ae hf_nn
  have h_sq_int_nn : 0 ≤ ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae <| by
      filter_upwards [hf_nn] with s _ using sq_nonneg _
  have h_squared := mul_self_le_mul_self h_LHS_nn h_holder'
  have h_rpow_half_sq : ∀ a : ℝ, 0 ≤ a → a ^ ((1 : ℝ) / 2) * a ^ ((1 : ℝ) / 2) = a := by
    intro a ha
    rw [← Real.rpow_add_of_nonneg ha
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  calc (∫ a, f a ∂μ) ^ 2
      = (∫ a, f a ∂μ) * (∫ a, f a ∂μ) := by ring
    _ ≤ ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) *
        ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := h_squared
    _ = ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) *
        (t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := by ring
    _ = (∫ a, (f a) ^ 2 ∂μ) * t := by
        rw [h_rpow_half_sq _ h_sq_int_nn, h_rpow_half_sq _ ht]
    _ = t * ∫ a, (f a) ^ 2 ∂μ := by ring

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component L² Lipschitz bound on the drift step.**

Combining the L¹ Lipschitz bound `|drift X i - drift Y i| ≤
L_μ · ∫_0^t ‖X-Y‖` with the L² Cauchy-Schwarz `(∫ g)² ≤ t · ∫ g²`
applied to `g = ‖X - Y‖`:

  `|drift X i - drift Y i|² ≤ L_μ² · t · ∫_0^t ‖X_s - Y_s‖² ds`.

This is the per-(t, ω) bound. Taking `E[·]` over ω gives the L²-norm
Lipschitz bound, which is the ingredient for the Bielecki β-norm
contraction. -/
lemma picardStep_drift_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Step 1: L¹ Lipschitz bound (proven).
  have h_L1 := picardStep_drift_diff_lipschitz_componentwise
    coeffs hL_μ_nn h_μ_lip X Y x₀ t ω i h_X_int h_Y_int h_XY_diff_int
  -- The L¹ bound's |·| is the abs of the i-th component diff.
  -- Square both sides (LHS² = (|·|)² = (·)², RHS² = L² · (∫‖X-Y‖)²).
  have h_abs_sq : ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      = |(picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by
    rw [sq_abs]
  rw [h_abs_sq]
  -- |·|² ≤ (L_μ · ∫‖X-Y‖)² by squaring h_L1 (both sides nonneg).
  have h_abs_nn : 0 ≤ |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| := abs_nonneg _
  have h_int_nn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have h_RHS_nn : 0 ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    mul_nonneg hL_μ_nn h_int_nn
  have h_sq_bound := mul_self_le_mul_self h_abs_nn h_L1
  -- h_sq_bound: |·| * |·| ≤ (L_μ · ∫‖X-Y‖) * (L_μ · ∫‖X-Y‖)
  -- Convert ·*· to ·^2 on both sides:
  have h_LHS_sq_eq : |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| *
      |(picardStep_drift coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i|
      = |(picardStep_drift coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by ring
  have h_RHS_sq_eq : (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) *
      (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖)
      = L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := by ring
  rw [h_LHS_sq_eq, h_RHS_sq_eq] at h_sq_bound
  -- Apply Cauchy-Schwarz: (∫ ‖X-Y‖)² ≤ t · ∫ ‖X-Y‖².
  have h_CS := integral_sq_le_mul_integral_sq_on_Icc
    (fun s => ‖X s ω - Y s ω‖) t ht
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    h_XY_diff_sq_L2
  -- Chain: |·|² ≤ L_μ² · (∫‖X-Y‖)² ≤ L_μ² · t · ∫‖X-Y‖².
  have h_L_sq_nn : 0 ≤ L_μ ^ 2 := sq_nonneg _
  have h_CS_mul : L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2
      ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_CS h_L_sq_nn
  calc |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| ^ 2
      ≤ L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := h_sq_bound
    _ ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := h_CS_mul
    _ = L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring

end LevyStochCalc.Ito.Picard
