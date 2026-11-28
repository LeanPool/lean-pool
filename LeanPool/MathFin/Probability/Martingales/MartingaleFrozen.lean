/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Martingale.Basic

/-!
# A martingale up to a horizon, frozen at the horizon

A process `S` that is a martingale only up to a horizon `T` (adapted and integrable on
`{t ≤ T}`, `S s = E[S t | 𝓕 s]` for `s ≤ t ≤ T`) is a martingale once it is frozen at `T`:
`t ↦ S (min t T)` is a martingale for the same filtration, and every martingale of that form
arises so (`martingale_min_iff`). Past the horizon the frozen process is constant, and the
constant `S T` is `𝓕 T ⊆ 𝓕 s`-measurable, so it is its own conditional expectation.

This is the vocabulary of the horizon-`T` equivalent martingale measure `MathFin.IsEMM`
(`EquivMartingaleMeasure.lean`), discrete and continuous: the hypothesis there is the
frozen martingale, and the three consequences read off it (adaptedness, integrability and the
martingale identity before the horizon) are the forward direction of `martingale_min_iff`. On
`ℕ` the identity need only be given one step at a time (`martingale_min_of_condExp_succ`).

A frozen process is `𝓕 T`-measurable at every time, so whether it is a martingale depends on the
measure only through its restriction to `𝓕 T`: two measures that agree on `𝓕 T` have the same
frozen martingales (`martingale_min_of_trim_eq`). This is why a pricing measure up to `T` need only
be equivalent to the reference measure on `𝓕 T` (`Market.IsPricingMeasure`).

## Main results

* `martingale_min_iff`: `t ↦ S (min t T)` is a martingale for `𝓕` iff `S` is adapted and
  integrable on `{t ≤ T}` and `S s = E[S t | 𝓕 s]` for `s ≤ t ≤ T` (finite measure).
* `martingale_min_of_condExp_succ`: on `ℕ`, adaptedness and integrability up to `T` and the
  one-step identity `S t = E[S (t+1) | 𝓕 t]` for `t < T` make `n ↦ S (min n T)` a martingale.
* `martingale_min_of_martingale`: a martingale frozen at any time is one.
* `martingale_min_of_trim_eq`: a frozen martingale stays one under any measure with the same
  restriction to `𝓕 T`.
* `MeasureTheory.Martingale.congr_ae`: an adapted process equal almost surely at each time to a
  martingale is one.

## Tags

martingale up to a horizon, stopped martingale, frozen process, equivalent martingale measure,
finite horizon martingale, MSC 60G44, MSC 60G48
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **An adapted process equal almost surely at each time to a martingale is a martingale**: the
conditional expectations see the process only up to null sets. -/
theorem _root_.MeasureTheory.Martingale.congr_ae {ι : Type*} [Preorder ι] {𝓕 : Filtration ι m0}
    {f g : ι → Ω → E} (hf : Martingale f 𝓕 μ) (hg : StronglyAdapted 𝓕 g)
    (hfg : ∀ i, f i =ᵐ[μ] g i) : Martingale g 𝓕 μ :=
  ⟨hg, fun i j hij ↦ (condExp_congr_ae (hfg j)).symm.trans ((hf.2 i j hij).trans (hfg i))⟩

section LinearOrder

variable {ι : Type*} [LinearOrder ι] {𝓕 : Filtration ι m0} {S : ι → Ω → E} {T : ι}

/-- **A martingale up to `T`, frozen at `T`, is a martingale; and conversely.** `t ↦ S (min t T)`
is a `μ`-martingale for `𝓕` iff `S` is adapted and integrable on `{t ≤ T}` and satisfies the
martingale identity `S s = E[S t | 𝓕 s]` for `s ≤ t ≤ T`. -/
theorem martingale_min_iff [IsFiniteMeasure μ] :
    Martingale (fun t ↦ S (min t T)) 𝓕 μ ↔
      (∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) ∧ (∀ t ≤ T, Integrable (S t) μ) ∧
        ∀ ⦃s t⦄, s ≤ t → t ≤ T → S s =ᵐ[μ] μ[S t | 𝓕 s] := by
  refine ⟨fun h ↦ ⟨fun t ht ↦ by simpa only [min_eq_left ht] using h.1 t,
    fun t ht ↦ by simpa only [min_eq_left ht] using h.integrable t,
    fun s t hst ht ↦ by
      simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using
        (h.condExp_ae_eq hst).symm⟩, fun ⟨hadapt, hint, hmart⟩ ↦
    ⟨fun s ↦ (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _)),
      fun i j hij ↦ ?_⟩⟩
  change μ[S (min j T) | 𝓕 i] =ᵐ[μ] S (min i T)
  rcases le_or_gt j T with hj | hj
  · simpa only [min_eq_left hj, min_eq_left (hij.trans hj)] using (hmart hij hj).symm
  rw [min_eq_right hj.le]
  rcases le_or_gt i T with hi | hi
  · simpa only [min_eq_left hi, min_eq_right hj.le] using (hmart hi le_rfl).symm
  · rw [min_eq_right hi.le]
    exact .of_eq (condExp_of_stronglyMeasurable (𝓕.le i)
      ((hadapt T le_rfl).mono (𝓕.mono hi.le)) (hint T le_rfl))

/-- **A martingale frozen at any time is a martingale.** -/
theorem martingale_min_of_martingale [IsFiniteMeasure μ] (hS : Martingale S 𝓕 μ) (T : ι) :
    Martingale (fun t ↦ S (min t T)) 𝓕 μ :=
  martingale_min_iff.mpr
    ⟨fun t _ ↦ hS.1 t, fun t _ ↦ hS.integrable t, fun _ _ hst _ ↦ (hS.condExp_ae_eq hst).symm⟩

/-- **A frozen martingale depends on the measure only up to the horizon.** If `t ↦ S (min t T)` is
a `μ`-martingale and `ν` agrees with `μ` on `𝓕 T`, it is a `ν`-martingale: before the horizon
every `S t` is `𝓕 T`-measurable, so its integrability and its integrals over the sets of
`𝓕 s ⊆ 𝓕 T` are the same under both measures. -/
theorem martingale_min_of_trim_eq {ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ.trim (𝓕.le T) = ν.trim (𝓕.le T)) (hS : Martingale (fun t ↦ S (min t T)) 𝓕 μ) :
    Martingale (fun t ↦ S (min t T)) 𝓕 ν := by
  obtain ⟨hadapt, hint, hmart⟩ := martingale_min_iff.mp hS
  have hT {t : ι} (ht : t ≤ T) : StronglyMeasurable[𝓕 T] (S t) := (hadapt t ht).mono (𝓕.mono ht)
  have hintν {t : ι} (ht : t ≤ T) : Integrable (S t) ν := by
    refine integrable_of_integrable_trim (𝓕.le T) ?_
    rw [← hμν]
    exact (hint t ht).trim (𝓕.le T) (hT ht)
  have hset {t : ι} (ht : t ≤ T) {A : Set Ω} (hA : MeasurableSet[𝓕 T] A) :
      ∫ ω in A, S t ω ∂ν = ∫ ω in A, S t ω ∂μ := by
    rw [setIntegral_trim (𝓕.le T) (hT ht) hA, setIntegral_trim (𝓕.le T) (hT ht) hA, hμν]
  refine martingale_min_iff.mpr ⟨hadapt, fun t ht ↦ hintν ht, fun s t hst ht ↦ ?_⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hintν ht)
    (fun _ _ _ ↦ (hintν (hst.trans ht)).integrableOn) (fun A hA _ ↦ ?_)
    (hadapt s (hst.trans ht)).aestronglyMeasurable
  have hAT : MeasurableSet[𝓕 T] A := 𝓕.mono (hst.trans ht) A hA
  rw [hset (hst.trans ht) hAT, hset ht hAT, ← setIntegral_condExp (𝓕.le s) (hint t ht) hA]
  exact setIntegral_congr_ae (𝓕.le s A hA) ((hmart hst ht).mono fun _ h _ ↦ h)

end LinearOrder

/-- **The one-step form on `ℕ`.** A process that is adapted and integrable up to `T` and satisfies
the one-step martingale identity `S t = E[S (t+1) | 𝓕 t]` for `t < T` is a martingale once frozen
at `T`. -/
theorem martingale_min_of_condExp_succ [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0}
    {S : ℕ → Ω → E} {T : ℕ} (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hint : ∀ t ≤ T, Integrable (S t) μ) (hmart : ∀ t < T, S t =ᵐ[μ] μ[S (t + 1) | 𝓕 t]) :
    Martingale (fun n ↦ S (min n T)) 𝓕 μ := by
  refine martingale_of_condExp_sub_eq_zero_nat
    (fun n ↦ (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _)))
    (fun n ↦ hint _ (min_le_right _ _)) fun n ↦ ?_
  show μ[S (min (n + 1) T) - S (min n T) | 𝓕 n] =ᵐ[μ] 0
  rcases lt_or_ge n T with hn | hn
  · rw [min_eq_left hn.le, min_eq_left (Nat.succ_le_of_lt hn)]
    filter_upwards [condExp_sub (hint (n + 1) hn) (hint n hn.le) (𝓕 n), hmart n hn]
      with ω h_sub h_mart
    rw [Pi.zero_apply, h_sub, Pi.sub_apply,
      condExp_of_stronglyMeasurable (𝓕.le n) (hadapt n hn.le) (hint n hn.le), ← h_mart, sub_self]
  · simp [min_eq_right hn, min_eq_right (hn.trans n.le_succ)]

end MathFin
