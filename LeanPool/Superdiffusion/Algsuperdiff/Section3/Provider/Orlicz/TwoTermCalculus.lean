/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# TwoTermCalculus

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Two-term weak-Orlicz calculus

Generic, unconditional A for the Section 3 two-term one-sided weak-Orlicz
relations `Algsuperdiff.Section3.Probability.IsTwoTermBigOWith` and
`Algsuperdiff.Section3.Probability.IsTwoTermBigOWithWitnesses`, together with
the `Γ_σ` scale calculus the Section 3.6 assembly consumes.

Every declaration here is a proved local helper of the `Provider` layer.

## Main results

* `isBigOWith_of_forall_add_pos`: a one-sided weak-Orlicz bound at scale `A`
  follows from the same bound at every strictly larger scale.
* `isTwoTermBigOWithWitnesses_mono_scales`, `isTwoTermBigOWith_mono_scales`:
  amplitude monotonicity, with and without the named witness pair.
* `isBigOWith_gammaSigma_tsum_of_nonneg_amplitude` and its majorant form
  `isBigOWith_gammaSigma_tsum_of_nonneg_amplitude_of_tsum_le`: the countable
  `Γ_σ` triangle inequality with *nonnegative* rather than positive
  amplitudes.
* `isBigOWith_gammaSigma_add`: the two-summand form of the same estimate.
* `isTwoTermBigOWithWitnesses_sqrt_of_sq`: the square-root buckle
  `F² ≤ O_{Γ_{σ₁}}(A) + O_{Γ_{σ₂}}(B)  ⟹  F ≤ O_{Γ_{2σ₁}}(√A) + O_{Γ_{2σ₂}}(√B)`,
  with the named output witnesses `√(Y ∨ 0)`, `√(Z ∨ 0)`.  Its call-site
  variants `isTwoTermBigOWithWitnesses_sqrt_of_sq_of_eq` and
  `isTwoTermBigOWithWitnesses_sqrt_of_sq_one_quarter` take the output exponents
  as equations `τᵢ = 2 σᵢ` rather than as literal products.
* `isBigOWith_gammaSigma_mono_exponent`: downgrading the stretched-exponential
  index of a one-sided display.
* `isTwoTermBigOWithWitnesses_mono_exponent`,
  `isTwoTermBigOWith_mono_exponent`: lane-wise exponent downgrade of a two-term
  display, witnesses and amplitudes preserved, no constant paid.
* `cstar_pos`, `sigmaBar_pos`, `neZero_of_model`, `dim_pos_of_model`: the named
  positivity facts of the standing model.

## References

* ABK26, Appendix (the two-term notation).
* ABK26, Lemma `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 1. Scale limits -/

/-- A one-sided weak-Orlicz upper-tail bound at scale `A` follows from the same
bound at every strictly larger scale.

The upper-tail events at the scales `A + 1/(n+1)` increase to the upper-tail
event at `A`, so continuity of the measure from below transfers the common
bound.  This is the device that removes strict positivity from amplitudes. -/
theorem isBigOWith_of_forall_add_pos [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {A : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → IsBigOWith μ Ψ X (A + ε)) :
    IsBigOWith μ Ψ X A := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hΨ_nonneg : (0 : ℝ) ≤ (Ψ t)⁻¹ :=
    le_trans measureReal_nonneg (h 1 one_pos ht)
  have hmono : Monotone fun n : ℕ =>
      upperTailEvent X ((A + 1 / ((n : ℝ) + 1)) * t) := by
    intro m n hmn
    refine upperTailEvent_mono_right ?_
    have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le hden (by exact_mod_cast Nat.add_le_add_right hmn 1)
    exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
  have hunion : upperTailEvent X (A * t)
      = ⋃ n : ℕ, upperTailEvent X ((A + 1 / ((n : ℝ) + 1)) * t) := by
    ext ω
    simp only [Set.mem_iUnion, mem_upperTailEvent]
    constructor
    · intro hω
      obtain ⟨n, hn⟩ :=
        exists_nat_one_div_lt (show (0 : ℝ) < (X ω - A * t) / t from
          div_pos (by linarith) ht0)
      refine ⟨n, ?_⟩
      have hstep : 1 / ((n : ℝ) + 1) * t < (X ω - A * t) / t * t :=
        mul_lt_mul_of_pos_right hn ht0
      have hcancel : (X ω - A * t) / t * t = X ω - A * t := by
        field_simp
      have hexp : (A + 1 / ((n : ℝ) + 1)) * t = A * t + 1 / ((n : ℝ) + 1) * t := by
        ring
      rw [hexp]
      linarith [hstep, hcancel]
    · rintro ⟨n, hn⟩
      have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      have hthr : A * t ≤ (A + 1 / ((n : ℝ) + 1)) * t :=
        mul_le_mul_of_nonneg_right (by linarith) ht0.le
      exact lt_of_le_of_lt hthr hn
  have hbound : ∀ n : ℕ,
      μ (upperTailEvent X ((A + 1 / ((n : ℝ) + 1)) * t))
        ≤ ENNReal.ofReal ((Ψ t)⁻¹) := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hΨ_nonneg).2
      (h (1 / ((n : ℝ) + 1)) (by positivity) ht)
  have hmeasure : μ (upperTailEvent X (A * t)) ≤ ENNReal.ofReal ((Ψ t)⁻¹) := by
    rw [hunion, hmono.measure_iUnion]
    exact iSup_le hbound
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rwa [ENNReal.toReal_ofReal hΨ_nonneg] at htoReal

/-! ## 2. Nonnegative normalization of a witness (consumed, not re-derived)

This section declares nothing.  The two scalar/tail facts the two-term displays
below need at this place are proved elsewhere and are consumed:

* the positive-part clamp of a one-sided tail at a strictly positive scale is
  `Algsuperdiff.Section3.Provider.Tail.isBigOWith_max_zero`
  (`Algsuperdiff/Section3/Provider/Tail/TailSqrt.lean`).  It is stated with the
  argument order `max 0 (Y ω)`; the displays below normalize witnesses as `max
  (Y ω) 0`, and the two are exchanged by `max_comm` at the point of use.
* subadditivity of `√` on the nonnegative reals is CoarseGraining's
  `Homogenization.sqrt_add_le_add_sqrt_of_nonneg`
  (`Homogenization/Deterministic/WeakNormInterfaces/Definitions.lean`), already
  in this file's import closure.

Both were previously re-derived here as private theorems; those private
re-derivations are deleted. -/

/-! ## 4. Amplitude monotonicity -/

/-- Amplitude monotonicity **preserving the witnesses**.  The two witnesses
`Y` and `Z` are untouched, so any side clause naming them -- for instance the
`s ≤ Cms * ε` refinement of the frozen multiscale conclusion -- survives the
enlargement verbatim.

Only `A₁ ≤ B₁` and `A₂ ≤ B₂` are needed: strict positivity of `B₁` and `B₂`
comes from the strict positivity of `A₁` and `A₂` already bundled in the
hypothesis. -/
theorem isTwoTermBigOWithWitnesses_mono_scales [IsFiniteMeasure μ]
    {Ψ₁ Ψ₂ : ℝ → ℝ} {X Y Z : Ω → ℝ} {A₁ A₂ B₁ B₂ : ℝ}
    (h : Probability.IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y Z A₁ A₂)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    Probability.IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y Z B₁ B₂ := by
  obtain ⟨hΨ₁, hΨ₂, hA₁, hA₂, hX, hY, hZ, hdom, hYt, hZt⟩ := h
  exact ⟨hΨ₁, hΨ₂, hA₁.trans_le h₁, hA₂.trans_le h₂, hX, hY, hZ, hdom,
    hYt.mono_scale h₁, hZt.mono_scale h₂⟩

/-- Amplitude monotonicity for the existential two-term relation. -/
theorem isTwoTermBigOWith_mono_scales [IsFiniteMeasure μ]
    {Ψ₁ Ψ₂ : ℝ → ℝ} {X : Ω → ℝ} {A₁ A₂ B₁ B₂ : ℝ}
    (h : Probability.IsTwoTermBigOWith μ Ψ₁ Ψ₂ X A₁ A₂)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    Probability.IsTwoTermBigOWith μ Ψ₁ Ψ₂ X B₁ B₂ := by
  obtain ⟨Y, Z, hw⟩ := h
  exact ⟨Y, Z, isTwoTermBigOWithWitnesses_mono_scales hw h₁ h₂⟩

/-! ## 6. The `Γ_σ` triangle inequality at nonnegative amplitudes -/

/-- Countable `Γ_σ` triangle inequality for nonnegative summands at
**nonnegative** amplitudes.

This is the proved positive-amplitude statement `isBigOWith_gammaSigma_tsum`
with `∀ k, 0 < a k` weakened to `∀ k, 0 ≤ a k`.  The positive statement is
consumed, never re-proved: the amplitudes are perturbed to `a k + δ 2^{-k}`,
which shifts the conclusion by `2 δ` `gammaTriangleConst σ`, and
`isBigOWith_of_forall_add_pos` removes the perturbation in the limit `δ ↓ 0`. -/
theorem isBigOWith_gammaSigma_tsum_of_nonneg_amplitude [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hX_meas : ∀ k, Measurable (X k))
    (ha : ∀ k, 0 ≤ a k)
    (ha_summable : Summable a)
    (hX : ∀ k, IsBigOWith μ (gammaSigma σ) (X k) (a k)) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑' k, X k ω)
      (gammaTriangleConst σ * ∑' k, a k) := by
  have hC : (0 : ℝ) < gammaTriangleConst σ := gammaTriangleConst_pos
  have hCne : gammaTriangleConst σ ≠ 0 := ne_of_gt hC
  refine isBigOWith_of_forall_add_pos ?_
  intro ε hε
  have hδ : 0 < ε / (2 * gammaTriangleConst σ) := div_pos hε (by linarith)
  set δ : ℝ := ε / (2 * gammaTriangleConst σ) with hδdef
  have hgeo : Summable fun k : ℕ => δ * ((1 : ℝ) / 2) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left δ
  have hperturb_pos : ∀ k : ℕ, (0 : ℝ) < δ * ((1 : ℝ) / 2) ^ k := by
    intro k; positivity
  have hpos' : ∀ k : ℕ, 0 < a k + δ * ((1 : ℝ) / 2) ^ k := by
    intro k; linarith [ha k, hperturb_pos k]
  have hsummable' : Summable fun k : ℕ => a k + δ * ((1 : ℝ) / 2) ^ k :=
    ha_summable.add hgeo
  have hX' : ∀ k : ℕ,
      IsBigOWith μ (gammaSigma σ) (X k) (a k + δ * ((1 : ℝ) / 2) ^ k) :=
    fun k => (hX k).mono_scale (by linarith [hperturb_pos k])
  have key :=
    isBigOWith_gammaSigma_tsum hσ hX_nonneg hX_meas hpos' hsummable' hX'
  have hgeoSum : (∑' k : ℕ, δ * ((1 : ℝ) / 2) ^ k) = δ * 2 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have htsum : (∑' k : ℕ, (a k + δ * ((1 : ℝ) / 2) ^ k))
      = (∑' k : ℕ, a k) + δ * 2 := by
    rw [ha_summable.tsum_add hgeo, hgeoSum]
  rw [htsum] at key
  refine key.mono_scale (le_of_eq ?_)
  rw [hδdef]
  field_simp

/-- The nonnegative-amplitude countable triangle inequality stated against an
arbitrary majorant `B` of the amplitude series, which is the form used at the
ABK26 call sites.  This is the nonnegative-amplitude twin of the proved
`isBigOWith_gammaSigma_tsum_of_tsum_le`
(`Algsuperdiff/Section3/Provider/Orlicz/TsumTriangle.lean`). -/
theorem isBigOWith_gammaSigma_tsum_of_nonneg_amplitude_of_tsum_le
    [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ B : ℝ}
    (hσ : 0 < σ)
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hX_meas : ∀ k, Measurable (X k))
    (ha : ∀ k, 0 ≤ a k)
    (ha_summable : Summable a)
    (hX : ∀ k, IsBigOWith μ (gammaSigma σ) (X k) (a k))
    (hB : ∑' k, a k ≤ B) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑' k, X k ω)
      (gammaTriangleConst σ * B) :=
  (isBigOWith_gammaSigma_tsum_of_nonneg_amplitude hσ hX_nonneg hX_meas ha
      ha_summable hX).mono_scale
    (mul_le_mul_of_nonneg_left hB gammaTriangleConst_pos.le)

/-- Two-summand `Γ_σ` triangle inequality for nonnegative observables at
nonnegative amplitudes.

The constant `gammaTriangleConst σ` is the cost of the *countable* engine this
statement is specialized from, and is carried here **by choice**, so that the
binary and the countable statement run on one engine.  It is **not** the only
possible constant, and the earlier claim in this docstring that it "cannot be
removed" was false and is withdrawn: cheaper proved binary publics are named in
the module header's constant-bookkeeping block (`ConclusionSeam3Closure.lean`
at `(1 + Real.log 2) ^ σ⁻¹ * (a + b)` with neither nonnegativity nor
measurability, `TailSqrt.lean`, and `BlockPayload.lean`), and ABK26's
`l.Gamma.sigma.triangle` prints factor `1` for `σ ≥ 1`. -/
theorem isBigOWith_gammaSigma_add [IsFiniteMeasure μ]
    {f g : Ω → ℝ} {a b σ : ℝ}
    (hσ : 0 < σ)
    (hf_nonneg : ∀ ω, 0 ≤ f ω) (hg_nonneg : ∀ ω, 0 ≤ g ω)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : IsBigOWith μ (gammaSigma σ) f a)
    (hg : IsBigOWith μ (gammaSigma σ) g b) :
    IsBigOWith μ (gammaSigma σ) (fun ω => f ω + g ω)
      (gammaTriangleConst σ * (a + b)) := by
  classical
  have hzero : IsBigOWith μ (gammaSigma σ) (fun _ : Ω => (0 : ℝ)) 0 := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have hΨ : (1 : ℝ) ≤ gammaSigma σ t := one_le_gammaSigma ht0
    have hΨinv : (0 : ℝ) ≤ (gammaSigma σ t)⁻¹ := by
      have : (0 : ℝ) < gammaSigma σ t := lt_of_lt_of_le zero_lt_one hΨ
      positivity
    have hempty : upperTailEvent (fun _ : Ω => (0 : ℝ)) (0 * t) = (∅ : Set Ω) := by
      ext ω
      simp [mem_upperTailEvent]
    rw [hempty]
    simpa using hΨinv
  have key :=
    isBigOWith_gammaSigma_tsum_of_nonneg_amplitude (μ := μ) (σ := σ)
      (X := fun k ω => if k = 0 then f ω else if k = 1 then g ω else 0)
      (a := fun k => if k = 0 then a else if k = 1 then b else 0) hσ
      (by
        intro k ω
        by_cases h0 : k = 0
        · simp [h0, hf_nonneg ω]
        · by_cases h1 : k = 1
          · simp [h1, hg_nonneg ω]
          · simp [h0, h1])
      (by
        intro k
        by_cases h0 : k = 0
        · simpa [h0] using hf_meas
        · by_cases h1 : k = 1
          · simpa [h0, h1] using hg_meas
          · simp [h0, h1])
      (by
        intro k
        by_cases h0 : k = 0
        · simpa [h0] using ha
        · by_cases h1 : k = 1
          · simpa [h0, h1] using hb
          · simp [h0, h1])
      (by
        refine summable_of_ne_finset_zero (s := Finset.range 2) ?_
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ite_eq_right (by omega), ite_eq_right (by omega)])
      (by
        intro k
        by_cases h0 : k = 0
        · simpa [h0] using hf
        · by_cases h1 : k = 1
          · simpa [h0, h1] using hg
          · simpa [h0, h1] using hzero)
  have hobs : (fun ω => ∑' k : ℕ,
      (if k = 0 then f ω else if k = 1 then g ω else 0)) = fun ω => f ω + g ω := by
    funext ω
    rw [tsum_eq_sum (s := Finset.range 2) ?_]
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hamp : (∑' k : ℕ, (if k = 0 then a else if k = 1 then b else 0)) = a + b := by
    rw [tsum_eq_sum (s := Finset.range 2) ?_]
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hobs, hamp] at key
  exact key

/-! ## 8. The square-root buckle -/

/-- The square-root transfer, **with named output witnesses**.

If a nonnegative observable `F` has `F²` dominated by the named witness pair
`Y`, `Z` at the exponents `σ₁`, `σ₂` and amplitudes `A`, `B`, then `F` itself is
dominated by the named pair `√(Y ∨ 0)`, `√(Z ∨ 0)` at the exponents `2σ₁`,
`2σ₂` and amplitudes `√A`, `√B`.  Naming the output witnesses is what lets a
caller keep a side clause about them across the buckle.

No constant is lost.  The pointwise step is `F = √(F²) ≤ √(Y ∨ 0 + Z ∨ 0) ≤ √(Y
∨ 0) + √(Z ∨ 0)`, whose last inequality is CoarseGraining's
`Homogenization.sqrt_add_le_add_sqrt_of_nonneg`.  Each lane's tail step is the
proved `Provider.Tail.isBigOWith_gammaSigma_sqrt`
(`Algsuperdiff/Section3/Provider/Tail/TailSqrt.lean`, the `p = 1/2` power rule),
applied to the clamped witness produced by `Provider.Tail.isBigOWith_max_zero`
(`ibid.:163`).

Measurability of `F` is not a premise: it follows from measurability of `F²`,
which the hypothesis carries, together with `F = √(F²)`. -/
theorem isTwoTermBigOWithWitnesses_sqrt_of_sq [IsFiniteMeasure μ]
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    {F Y Z : Ω → ℝ} {A B : ℝ}
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    (h : Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma σ₁) (gammaSigma σ₂)
      (fun ω => F ω ^ 2) Y Z A B) :
    Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma (2 * σ₁))
      (gammaSigma (2 * σ₂)) F
      (fun ω => Real.sqrt (max (Y ω) 0)) (fun ω => Real.sqrt (max (Z ω) 0))
      (Real.sqrt A) (Real.sqrt B) := by
  obtain ⟨-, -, hA, hB, hXm, hYm, hZm, hdom, hYt, hZt⟩ := h
  have hFmeas : Measurable F := by
    have hid : (fun ω => Real.sqrt (F ω ^ 2)) = F := by
      funext ω
      exact Real.sqrt_sq (hF_nonneg ω)
    rw [← hid]
    exact hXm.sqrt
  have hlane : ∀ {W : Ω → ℝ} {C τ : ℝ}, 0 < C →
      IsBigOWith μ (gammaSigma τ) W C →
      IsBigOWith μ (gammaSigma (2 * τ)) (fun ω => Real.sqrt (max (W ω) 0))
        (Real.sqrt C) := by
    intro W C τ hCpos hW
    have hc := Tail.isBigOWith_max_zero hCpos hW
    rw [show (fun ω => max 0 (W ω)) = fun ω => max (W ω) 0 from
      funext fun ω => max_comm 0 (W ω)] at hc
    exact Tail.isBigOWith_gammaSigma_sqrt hCpos.le (fun ω => le_max_right _ _) hc
  refine ⟨Probability.isAdmissibleTail_gammaSigma (by linarith),
    Probability.isAdmissibleTail_gammaSigma (by linarith),
    Real.sqrt_pos.2 hA, Real.sqrt_pos.2 hB, hFmeas,
    (hYm.max measurable_const).sqrt, (hZm.max measurable_const).sqrt, ?_,
    hlane hA hYt, hlane hB hZt⟩
  intro ω
  have hsq : F ω ^ 2 ≤ max (Y ω) 0 + max (Z ω) 0 :=
    le_trans (hdom ω) (add_le_add (le_max_left _ _) (le_max_left _ _))
  calc F ω = Real.sqrt (F ω ^ 2) := (Real.sqrt_sq (hF_nonneg ω)).symm
    _ ≤ Real.sqrt (max (Y ω) 0 + max (Z ω) 0) := Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (max (Y ω) 0) + Real.sqrt (max (Z ω) 0) :=
        HCPolySupport.sqrt_add_le_add_sqrt_of_nonneg (le_max_right _ _)
          (le_max_right _ _)

/-- The witness-level buckle with the output exponents supplied as *equations*
`τᵢ = 2 σᵢ` rather than as the literal terms `2 * σᵢ`.

This is pure call-site ergonomics: a consumer whose target display is stated at,
say, `gammaSigma (1/2)` does not have to rewrite `gammaSigma (2 * (1/4))` into
it, but discharges `(1/2 : ℝ) = 2 * (1/4)` by `norm_num`. -/
theorem isTwoTermBigOWithWitnesses_sqrt_of_sq_of_eq [IsFiniteMeasure μ]
    {σ₁ σ₂ τ₁ τ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hτ₁ : τ₁ = 2 * σ₁) (hτ₂ : τ₂ = 2 * σ₂)
    {F Y Z : Ω → ℝ} {A B : ℝ}
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    (h : Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma σ₁) (gammaSigma σ₂)
      (fun ω => F ω ^ 2) Y Z A B) :
    Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma τ₁) (gammaSigma τ₂) F
      (fun ω => Real.sqrt (max (Y ω) 0)) (fun ω => Real.sqrt (max (Z ω) 0))
      (Real.sqrt A) (Real.sqrt B) := by
  subst hτ₁
  subst hτ₂
  exact isTwoTermBigOWithWitnesses_sqrt_of_sq hσ₁ hσ₂ hF_nonneg h

theorem isTwoTermBigOWithWitnesses_sqrt_of_sq_one_quarter [IsFiniteMeasure μ]
    {F Y Z : Ω → ℝ} {A B : ℝ}
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    (h : Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma 1)
      (gammaSigma (1 / 4)) (fun ω => F ω ^ 2) Y Z A B) :
    Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma 2) (gammaSigma (1 / 2))
      F (fun ω => Real.sqrt (max (Y ω) 0)) (fun ω => Real.sqrt (max (Z ω) 0))
      (Real.sqrt A) (Real.sqrt B) :=
  isTwoTermBigOWithWitnesses_sqrt_of_sq_of_eq one_pos (by norm_num) (by norm_num)
    (by norm_num) hF_nonneg h

/-! ## 9. Downgrading the stretched-exponential index -/

/-- A `Γ_σ` upper tail at scale `A` is in particular a `Γ_{σ'}` upper tail at the
same scale whenever `σ' ≤ σ`.  No constant is paid.  The engine is
CoarseGraining's
`Homogenization.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent`, which is
consumed, not re-proved. -/
theorem isBigOWith_gammaSigma_mono_exponent {X : Ω → ℝ} {A σ σ' : ℝ}
    (hσσ' : σ' ≤ σ) (h : IsBigOWith μ (gammaSigma σ) X A) :
    IsBigOWith μ (gammaSigma σ') X A :=
  HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent hσσ' h

/-- **Lane-wise exponent downgrade of a two-term display, preserving the
witnesses.**  Both exponents may be lowered independently; the observable, the
two witnesses and the two amplitudes are untouched, and no constant is paid.

The engine is `isBigOWith_gammaSigma_mono_exponent` above, applied once per
lane.  The only positivity required is `0 < σ₁'` and `0 < σ₂'`, and only
because the carrier `IsTwoTermBigOWithWitnesses` bundles
`IsAdmissibleTail (gammaSigma σᵢ')`, which
`Probability.isAdmissibleTail_gammaSigma` supplies exactly from strict
positivity of the *target* exponent.  Positivity of `σ₁` and `σ₂` is not a
premise: it follows from `0 < σᵢ' ≤ σᵢ`. -/
theorem isTwoTermBigOWithWitnesses_mono_exponent {σ₁ σ₂ σ₁' σ₂' : ℝ}
    (hσ₁' : 0 < σ₁') (hσ₂' : 0 < σ₂') (h₁ : σ₁' ≤ σ₁) (h₂ : σ₂' ≤ σ₂)
    {X Y Z : Ω → ℝ} {A₁ A₂ : ℝ}
    (h : Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma σ₁) (gammaSigma σ₂)
      X Y Z A₁ A₂) :
    Probability.IsTwoTermBigOWithWitnesses μ (gammaSigma σ₁') (gammaSigma σ₂')
      X Y Z A₁ A₂ := by
  obtain ⟨-, -, hA₁, hA₂, hXm, hYm, hZm, hdom, hYt, hZt⟩ := h
  exact ⟨Probability.isAdmissibleTail_gammaSigma hσ₁',
    Probability.isAdmissibleTail_gammaSigma hσ₂', hA₁, hA₂, hXm, hYm, hZm, hdom,
    isBigOWith_gammaSigma_mono_exponent h₁ hYt,
    isBigOWith_gammaSigma_mono_exponent h₂ hZt⟩

/-- Lane-wise exponent downgrade for the existential two-term relation. -/
theorem isTwoTermBigOWith_mono_exponent {σ₁ σ₂ σ₁' σ₂' : ℝ}
    (hσ₁' : 0 < σ₁') (hσ₂' : 0 < σ₂') (h₁ : σ₁' ≤ σ₁) (h₂ : σ₂' ≤ σ₂)
    {X : Ω → ℝ} {A₁ A₂ : ℝ}
    (h : Probability.IsTwoTermBigOWith μ (gammaSigma σ₁) (gammaSigma σ₂)
      X A₁ A₂) :
    Probability.IsTwoTermBigOWith μ (gammaSigma σ₁') (gammaSigma σ₂') X A₁ A₂ := by
  obtain ⟨Y, Z, hw⟩ := h
  exact ⟨Y, Z, isTwoTermBigOWithWitnesses_mono_exponent hσ₁' hσ₂' h₁ h₂ hw⟩

end

/-! ## 10. Named positivity facts of the standing model -/

section Positivity

variable {d : ℕ}

/-- The J4 non-degeneracy constant of the standing model is positive.  This is the
first conjunct of the proved unique-choice characterization. -/
theorem cstar_pos (M : ABKModel d) : 0 < Disorder.cstar M :=
  (Disorder.cstar_characterization M).1

/-- The running diffusivity of the standing model is positive at every scale.  This
is the first conjunct of the proved unique-choice characterization. -/
theorem sigmaBar_pos (M : ABKModel d) (m : ℤ) :
    0 < (Annealed.sigmaBar M m : ℝ) :=
  (Annealed.sigmaBar_characterization M m).1

/-- The paper-wide standing assumption `2 ≤ d`, stored in the model, supplies
the nonzero-dimension fact.  This is a theorem and deliberately **not** an
instance: registering it would leak a `NeZero` instance into unrelated
typeclass searches. -/
theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The dimension of the standing model is positive. -/
theorem dim_pos_of_model (M : ABKModel d) : 0 < d :=
  lt_of_lt_of_le (by omega) M.shellPrefix.dimension

end Positivity

end Algsuperdiff.Section3.Provider.Orlicz
