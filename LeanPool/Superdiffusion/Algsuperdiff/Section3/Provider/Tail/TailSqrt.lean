/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower

/-!
# TailSqrt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Orlicz square root and the two-term witness upgrade

This module supplies the **model-free** probabilistic step of ABK26's
derivation of Proposition `p.tail.bounds` from Proposition
`p.cg.ellipticity.bounds`: the sentence

> Taking square roots, and specializing to `sigma = 1/4` and `s >= 4 gamma`, we
> get `e.tail.bounds`

Nothing in this file mentions the model, the cutoff, or the coarse-grained
ellipticity constants; it operates on an abstract nonnegative random variable
whose *square* has a three-term one-sided bound.

## The four moves

1. **The square root of a `Gamma_sigma` tail** (`isBigOWith_gammaSigma_sqrt`).
   `X <= O_{Gamma_sigma}(A)` with `X >= 0` gives `sqrt X <= O_{Gamma_{2
   sigma}}(sqrt A)`.  This is the `p = 1/2` case of the Appendix power rule
   `e.powerofGammasigma`, already proved as
   `Provider.Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg`; the index
   arithmetic is `sigma / (1/2) = 2 sigma`.  **This is where the manuscript's
   `sigma = 1/4` specialization lives**: the heavy leg of `e.cg.ellip.upper`
   sits at `Gamma_{(1 - sigma)/3}`, which at `sigma = 1/4` is `Gamma_{1/4}`,
   and `2 * (1/4) = 1/2` is the `Gamma_{1/2}` of `e.tail.bounds`.  The
   `Gamma_1` middle leg of `e.cg.ellip.upper` becomes the `Gamma_2` middle of
   `e.tail.bounds` by the same rule at `2 * 1 = 2`.

2. **The merge of two heavy legs** (`isBigOWith_gammaSigma_add_of_nonneg`).
   The manuscript's `ell^2` display has **three** terms, but `e.cg.ellip.lower`
   and `e.cg.ellip.upper` contribute **two** heavy terms, at `Gamma_{(1 -
   sigma)/2}` and `Gamma_{(1 - sigma)/3}` respectively.  The manuscript merges
   them silently.  The merge is not free: two `Gamma_sigma` tails at scales `A`
   and `B` sum to a `Gamma_sigma` tail at scale `2 (3 max{1, log 2})^{1/sigma}
   max{A, B}`, by the Appendix maximum lemma `l.maximums.Gamma.s`.

3. **The deterministic half** (`sqrt_le_add_of_sq_le_add_add`): the pointwise
   subadditivity `sqrt (D + Y + Z) <= sqrt D + sqrt Y + sqrt Z`.

4. **The witness upgrade** (`isTwoTermBigOWith_of_ae_le`).  ABK26's relations
   `X <= O_{Psi_1}(A_1) + O_{Psi_2}(A_2)` are formalized with a **pointwise**
   domination `forall omega, X omega <= Y omega + Z omega`
   (`Probability.IsTwoTermBigOWithWitnesses`), while a Section 3 observable may
   be known to satisfy the corresponding bound only almost everywhere (for
   instance when the bound itself is only an a.e. statement).  Modifying the
   two witnesses on the (measurable, null) set where the almost-everywhere
   inequality fails removes the mismatch without changing either tail.  On the
   centered cube the two observables reduce pointwise to the same literal, so
   the same witness transports there with no null-set surgery.
   Off centre, the translate identity `lambdaSq_cutoff_translateCutoffSample`
   is a pathwise equality read at a *different* sample, so no definitional
   identification bridges it.  Since the observable bodies are their literals
   clamped at `0`, however, the off-centre observable *is* its literal on the
   source range, and the pathwise covariance applies to it verbatim.  Composed
   with the law invariance
   `Cutoff.map_translateCutoffSample_cutoffSampleLaw`, this transports the
   whole `IsLowerIntegerFamilyOrliczWithWitness` package to every translate,
   with the witness composed with the translation
   (`Provider/BadEvents/ObservableSwapPayoff.lean`).  The transport is thus a
   consequence of covariance plus stationarity, not a definitional accident.
   `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is proved, so its
   centered instance is available to a downstream assembly; this helper still
   exposes that instance conditionally, and the `Lambda` (upper) leg has no
   proved translate covariance.  The lemma covers the two-term single-index
   case only.

## Main results

* `isBigOWith_of_ae_eq` --- `Gamma`-tails are invariant under almost-everywhere
  modification of the random variable.
* `isBigOWith_max_zero` --- clamping a witness at `0` preserves its tail.
* `isBigOWith_gammaSigma_sqrt` --- the Orlicz square root.
* `isBigOWith_gammaSigma_add_of_nonneg` --- the merge of two `Gamma_sigma` legs.
* `isTwoTermBigOWith_of_ae_le` --- the witness upgrade.
* `sqrt_le_add_of_sq_le_add_add` --- the deterministic half.
* `isDeterministicShiftTwoTermOneSidedOrlicz_of_sq_le` --- the packaged
  square-root step: an almost-everywhere three-term bound on `X ^ 2` becomes the
  source's two-term one-sided relation for `X`.

## References

* ABK26, `p.tail.bounds`; its derivation.
* ABK26, `e.powerofGammasigma`; `l.maximums.Gamma.s`; the Appendix tail
  conventions.
-/

namespace Algsuperdiff.Section3.Provider.Tail

open MeasureTheory
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Probability

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Almost-everywhere invariance and clamping -/

/-- A one-sided weak-Orlicz tail only sees the random variable through its
almost-everywhere class. -/
theorem isBigOWith_of_ae_eq {Ψ : ℝ → ℝ} {X Y : Ω → ℝ} {A : ℝ}
    (hXY : X =ᵐ[μ] Y) (hX : IsBigOWith μ Ψ X A) :
    IsBigOWith μ Ψ Y A := by
  intro t ht
  have hsets : upperTailEvent Y (A * t) =ᵐ[μ] upperTailEvent X (A * t) := by
    filter_upwards [hXY] with ω hω
    change (A * t < Y ω) = (A * t < X ω)
    rw [hω]
  rw [measureReal_congr hsets]
  exact hX ht

/-- Clamping a witness below at `0` does not change its one-sided tail, as long
as the scale is positive. -/
theorem isBigOWith_max_zero {Ψ : ℝ → ℝ} {Y : Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hY : IsBigOWith μ Ψ Y A) :
    IsBigOWith μ Ψ (fun ω => max 0 (Y ω)) A :=
  Algsuperdiff.Section3.Probability.isBigOWith_max_zero hA hY

/-! ## The Orlicz square root -/

/-- **The Orlicz square root.**  From `X <= O_{Gamma_sigma}(A)` for a
nonnegative `X` and a nonnegative scale `A`,
`sqrt X <= O_{Gamma_{2 sigma}}(sqrt A)`.

This is the `p = 1/2` instance of `e.powerofGammasigma`: the index arithmetic
of `Provider.Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg` is
`sigma / (1/2) = 2 sigma`, and `x ^ (1/2 : R) = sqrt x`. -/
theorem isBigOWith_gammaSigma_sqrt [IsFiniteMeasure μ]
    {X : Ω → ℝ} {A σ : ℝ} (hA : 0 ≤ A) (hXnn : ∀ ω, 0 ≤ X ω)
    (hX : IsBigOWith μ (gammaSigma σ) X A) :
    IsBigOWith μ (gammaSigma (2 * σ)) (fun ω => Real.sqrt (X ω)) (Real.sqrt A) := by
  have h :=
    (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg
      (μ := μ) (X := X) (K := A) (σ := σ) (p := 1 / 2)
      (by norm_num) hA hXnn).1 hX
  have hσ : σ / (1 / 2 : ℝ) = 2 * σ := by ring
  rw [hσ] at h
  simpa only [Real.sqrt_eq_rpow] using h

/-! ## The merge of two heavy legs -/

/-- The supremum of a two-element family is the binary maximum. -/
private theorem sup'_fin_two (f : Fin 2 → ℝ)
    (hs : (Finset.univ : Finset (Fin 2)).Nonempty) :
    (Finset.univ : Finset (Fin 2)).sup' hs f = max (f 0) (f 1) := by
  refine le_antisymm (Finset.sup'_le hs f ?_) (max_le ?_ ?_)
  · intro i _
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact Finset.le_sup' f (Finset.mem_univ 0)
  · exact Finset.le_sup' f (Finset.mem_univ 1)

/-- **The merge of two `Gamma_sigma` legs.**  The sum of two random variables
with `Gamma_sigma` tails at scales `A` and `B` has a `Gamma_sigma` tail at scale
`2 (3 max{1, log 2})^{1/sigma} max{A, B}`.

This is the step the manuscript performs silently between the two heavy terms
of `e.cg.ellip.lower` and `e.cg.ellip.upper` and the single heavy term of the
`ell^2` display.  The constant is the Appendix maximum lemma's, applied to `Y +
Z <= 2 max{Y, Z}`. -/
theorem isBigOWith_gammaSigma_add_of_nonneg [IsFiniteMeasure μ]
    {Y Z : Ω → ℝ} {A B σ : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hY : IsBigOWith μ (gammaSigma σ) Y A)
    (hZ : IsBigOWith μ (gammaSigma σ) Z B) :
    IsBigOWith μ (gammaSigma σ) (fun ω => Y ω + Z ω)
      (2 * ((3 * max 1 (Real.log 2)) ^ σ⁻¹ * max A B)) := by
  classical
  have hs : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hanonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (fun i : Fin 2 => if i = 0 then A else B) i := by
    intro i _
    fin_cases i
    · simpa using hA
    · simpa using hB
  have hWtail :
      ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        IsBigOWith μ (gammaSigma σ) ((fun i : Fin 2 => if i = 0 then Y else Z) i)
          ((fun i : Fin 2 => if i = 0 then A else B) i) := by
    intro i _
    fin_cases i
    · simpa using hY
    · simpa using hZ
  have hsup :=
    Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_scales_of_nonempty
      (μ := μ) (Finset.univ : Finset (Fin 2)) hs
      (X := fun i : Fin 2 => if i = 0 then Y else Z)
      (a := fun i : Fin 2 => if i = 0 then A else B) (σ := σ)
      hσ hanonneg hWtail
  have hcard : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  have hsupa :
      (Finset.univ : Finset (Fin 2)).sup' hs (fun i : Fin 2 => if i = 0 then A else B) =
        max A B := by
    rw [sup'_fin_two _ hs]
    norm_num
  have hsupW : ∀ ω : Ω,
      (Finset.univ : Finset (Fin 2)).sup' hs
          (fun i : Fin 2 => (if i = 0 then Y else Z) ω) = max (Y ω) (Z ω) := by
    intro ω
    rw [sup'_fin_two _ hs]
    norm_num
  rw [hcard, hsupa] at hsup
  have hmax : IsBigOWith μ (gammaSigma σ) (fun ω => max (Y ω) (Z ω))
      ((3 * max 1 (Real.log 2)) ^ σ⁻¹ * max A B) := by
    simpa only [hsupW] using hsup
  have hdouble :=
    IsBigOWith.const_mul (μ := μ) (Ψ := gammaSigma σ)
      (X := fun ω => max (Y ω) (Z ω))
      (A := (3 * max 1 (Real.log 2)) ^ σ⁻¹ * max A B) (c := 2)
      (by norm_num) hmax
  refine hdouble.of_le ?_
  intro ω
  show Y ω + Z ω ≤ 2 * max (Y ω) (Z ω)
  rcases le_total (Y ω) (Z ω) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-! ## The witness upgrade -/

/-- **The witness upgrade.**  An *almost-everywhere* two-term domination becomes
the source's *pointwise* one, by modifying the two witnesses on the measurable
null set where the inequality fails.  Neither tail changes, because a tail is an
almost-everywhere invariant (`isBigOWith_of_ae_eq`).

The Section 3 observables are measurable representatives of their literal
manuscript definitions, so every identification of an observable with an
analytic quantity is only almost-everywhere; without this lemma no such
identification can transport a `Probability.IsTwoTermBigOWith` conclusion. -/
theorem isTwoTermBigOWith_of_ae_le
    {Ψ₁ Ψ₂ : ℝ → ℝ} {X Y Z : Ω → ℝ} {A₁ A₂ : ℝ}
    (hΨ₁ : IsAdmissibleTail Ψ₁) (hΨ₂ : IsAdmissibleTail Ψ₂)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ Y ω + Z ω)
    (hYt : IsBigOWith μ Ψ₁ Y A₁) (hZt : IsBigOWith μ Ψ₂ Z A₂) :
    IsTwoTermBigOWith μ Ψ₁ Ψ₂ X A₁ A₂ := by
  classical
  set N : Set Ω := {ω | Y ω + Z ω < X ω} with hN
  have hNmeas : MeasurableSet N := measurableSet_lt (hY.add hZ) hX
  have hNnull : μ N = 0 := by
    have h := ae_iff.1 hle
    simpa [hN, not_le] using h
  refine ⟨fun ω => if ω ∈ N then 0 else Y ω, fun ω => if ω ∈ N then X ω else Z ω,
    hΨ₁, hΨ₂, hA₁, hA₂, hX, ?_, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite hNmeas measurable_const hY
  · exact Measurable.ite hNmeas hX hZ
  · intro ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · simp only [hω, ite_false]
      exact not_lt.1 (by simpa [hN] using hω)
  · refine isBigOWith_of_ae_eq (X := Y) ?_ hYt
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNnull] with ω hω
    simp [hω]
  · refine isBigOWith_of_ae_eq (X := Z) ?_ hZt
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNnull] with ω hω
    simp [hω]

/-! ## The deterministic half -/

/-- The deterministic half of the square-root step: a three-term bound on a
square becomes a three-term bound on the root, with no constant. -/
theorem sqrt_le_add_of_sq_le_add_add {x D Y Z : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hle : x ^ 2 ≤ D + Y + Z) :
    x ≤ Real.sqrt D + Real.sqrt Y + Real.sqrt Z := by
  have hsplit : Real.sqrt (D + Y + Z) ≤ Real.sqrt D + Real.sqrt Y + Real.sqrt Z := by
    have h1 : Real.sqrt (D + Y) ≤ Real.sqrt D + Real.sqrt Y := by
      have := Real.rpow_add_le_add_rpow hD hY (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 ≤ 1)
      simpa only [Real.sqrt_eq_rpow] using this
    have h2 : Real.sqrt (D + Y + Z) ≤ Real.sqrt (D + Y) + Real.sqrt Z := by
      have := Real.rpow_add_le_add_rpow (by linarith : (0 : ℝ) ≤ D + Y) hZ
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1)
      simpa only [Real.sqrt_eq_rpow] using this
    linarith
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (D + Y + Z) := Real.sqrt_le_sqrt hle
    _ ≤ Real.sqrt D + Real.sqrt Y + Real.sqrt Z := hsplit

/-! ## The packaged square-root step -/

/-- **The packaged square-root step.**

If a nonnegative measurable `X` satisfies, almost everywhere, a three-term
bound on its square

`X ^ 2 <= D + Y + Z`

with `Y <= O_{Gamma_{sigma_1}}(A_1)` and `Z <= O_{Gamma_{sigma_2}}(A_2)`
nonnegative witnesses, then `X` satisfies the source's two-term one-sided
relation

`X <= b + O_{Gamma_{2 sigma_1}}(B_1) + O_{Gamma_{2 sigma_2}}(B_2)`

for any deterministic shift `b >= sqrt D` and any positive scales
`B_1 >= sqrt A_1`, `B_2 >= sqrt A_2`. -/
theorem isDeterministicShiftTwoTermOneSidedOrlicz_of_sq_le [IsFiniteMeasure μ]
    {X Y Z : Ω → ℝ} {D A₁ A₂ σ₁ σ₂ b B₁ B₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (hZnn : ∀ ω, 0 ≤ Z ω)
    (hD : 0 ≤ D) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hsq : ∀ᵐ ω ∂μ, X ω ^ 2 ≤ D + Y ω + Z ω)
    (hYt : IsBigOWith μ (gammaSigma σ₁) Y A₁)
    (hZt : IsBigOWith μ (gammaSigma σ₂) Z A₂)
    (hb : Real.sqrt D ≤ b)
    (hB₁ : Real.sqrt A₁ ≤ B₁) (hB₁pos : 0 < B₁)
    (hB₂ : Real.sqrt A₂ ≤ B₂) (hB₂pos : 0 < B₂) :
    IsDeterministicShiftTwoTermOneSidedOrlicz μ (gammaSigma (2 * σ₁))
      (gammaSigma (2 * σ₂)) X b B₁ B₂ := by
  refine ⟨hX, ?_⟩
  have hYsqrt : IsBigOWith μ (gammaSigma (2 * σ₁))
      (fun ω => Real.sqrt (Y ω)) B₁ :=
    (isBigOWith_gammaSigma_sqrt hA₁ hYnn hYt).mono_scale hB₁
  have hZsqrt : IsBigOWith μ (gammaSigma (2 * σ₂))
      (fun ω => Real.sqrt (Z ω)) B₂ :=
    (isBigOWith_gammaSigma_sqrt hA₂ hZnn hZt).mono_scale hB₂
  refine isTwoTermBigOWith_of_ae_le
    (isAdmissibleTail_gammaSigma (by linarith : (0 : ℝ) < 2 * σ₁))
    (isAdmissibleTail_gammaSigma (by linarith : (0 : ℝ) < 2 * σ₂))
    hB₁pos hB₂pos (hX.sub measurable_const)
    (hY.sqrt) (hZ.sqrt) ?_ hYsqrt hZsqrt
  filter_upwards [hsq] with ω hω
  have h := sqrt_le_add_of_sq_le_add_add (hXnn ω) hD (hYnn ω) (hZnn ω) hω
  linarith

end

end Algsuperdiff.Section3.Provider.Tail
