/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorDensityTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorArray

/-!
# ShiftedConcentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Re-basing the Appendix-D concentration engine at an arbitrary scale `m₀`

ABK26, Appendix D (`p.concentration.for.scales`) and §4.1.  The proved
Proposition `ScalesConcentration.p_concentration_for_scales_Cstar` is stated for
the window `{0,…,m}`; the manuscript's own reduction is "translate the array".
This module carries out that translation, once and generically, so that no lane
has to redo it.

## Contents

* `shiftArray m₀ X` — the re-based array `X'_{k,j} = X_{k+m₀, j+m₀}`.  **Both**
  indices move: the row index because the window moves, the column index
  because the Appendix-D weight `wt s k j = 3^{-s|k-j|}` is *difference-only*,
  so only the diagonal translation preserves the row sums.  (Translating the
  row index alone — the phrasing in the proved module docstring — does **not**
  preserve `Y_k`; see `Yk_shiftArray`.)
* `Yk_shiftArray` — `Y_k(X') = Y_{k+m₀}(X)`, by re-indexing the two-sided `tsum`
  with `Equiv.addRight m₀`.
* `columnsIndep_shiftArray` — `ColumnsIndep` transfers: the residue class `b` of
  the shifted array is the residue class `b + m₀` of the original, read through
  the measurable relabelling `g ↦ (k ↦ g (k + m₀))` of `ℤ → ℝ`.
* `ratioTail_of_concentration_shift` — the reusable endpoint: the proved
  `IndicatorDensity.ratioTail_of_concentration` at the window `{m₀,…,m₀+n}`.
  Its hypothesis list is *identical* to the base-`0` one except that the
  deterministic reduction is asked at every scale `m : ℤ` instead of only at `m
  ≥ 0` — which is what all three §4.1 lanes in fact prove (their `0 ≤ m`
  binders are unused).
* `scalePropFrom` and `scalePropFrom_eq_scaleProp` — the window re-index: the
  `Finset.range (Mw+1)`-indexed average of `Set.indicator`s at the scales `m₀ +
  k`, in which the frozen proportion display is written, is the proved
  `Finset.Icc`-indexed `scaleProp` of the shifted family.

## References

* ABK26, `p.concentration.for.scales`, (the `m₀` reduction);
  `p.independence.between.scales`.
* Also.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open MeasureTheory ProbabilityTheory
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {Ω : Type*}

/-! ## 1. The re-based array and its row sums -/

/-- **The Appendix-D array re-based at `m₀`**, `X'_{k,j} = X_{k+m₀, j+m₀}`. -/
def shiftArray (m0 : ℤ) (X : ℤ → ℤ → Ω → ℝ) : ℤ → ℤ → Ω → ℝ :=
  fun k j omega => X (k + m0) (j + m0) omega

@[simp] theorem shiftArray_apply (m0 : ℤ) (X : ℤ → ℤ → Ω → ℝ) (k j : ℤ) (omega : Ω) :
    shiftArray m0 X k j omega = X (k + m0) (j + m0) omega := rfl

/-- The Appendix-D index distance is translation invariant. -/
theorem idist_add_right (k j m0 : ℤ) : idist (k + m0) (j + m0) = idist k j := by
  simp only [idist]
  congr 1
  push_cast
  ring

/-- The Appendix-D weight `3^{-s|k-j|}` is difference-only, hence translation
invariant.  This is the fact that forces the *diagonal* shift. -/
theorem wt_add_right (s : ℝ) (k j m0 : ℤ) : wt s (k + m0) (j + m0) = wt s k j := by
  simp only [wt, idist_add_right]

/-- **The re-based row sum is the original row sum at the shifted scale.**  The
`tsum` over `ℤ` is re-indexed by `Equiv.addRight m₀`, and the weight is
translation invariant. -/
theorem Yk_shiftArray (X : ℤ → ℤ → Ω → ℝ) (s : ℝ) (m0 k : ℤ) (omega : Ω) :
    Yk (shiftArray m0 X) s k omega = Yk X s (k + m0) omega := by
  have h := (Equiv.addRight m0).tsum_eq
    (fun j : ℤ => wt s (k + m0) j * X (k + m0) j omega)
  simp only [Equiv.coe_addRight] at h
  rw [Yk, Yk, ← h]
  refine tsum_congr fun j => ?_
  simp only [shiftArray]
  rw [wt_add_right]

/-! ## 2. The window re-index

The frozen `§4.1` proportion display averages `Set.indicator`s of the events at
the scales `m₀ + k` over `k ∈ Finset.range (Mw+1)`.  The proved `scaleProp`
averages `if`-indicators over `m ∈ Finset.Icc (0:ℤ) (Mw:ℤ)`.  The two are the
same number. -/

private theorem Icc_zero_eq_map_range (n : ℕ) :
    Finset.Icc (0 : ℤ) (n : ℤ)
      = (Finset.range (n + 1)).map ⟨fun k : ℕ => (k : ℤ), Nat.cast_injective⟩ := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h0, hn⟩
    exact ⟨m.toNat, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

/-- **The integer window `{0,…,n}` re-indexed by `Finset.range (n+1)`.** -/
theorem sum_Icc_zero_eq_sum_range {A : Type*} [AddCommMonoid A] (f : ℤ → A) (n : ℕ) :
    ∑ m ∈ Finset.Icc (0 : ℤ) (n : ℤ), f m = ∑ k ∈ Finset.range (n + 1), f (k : ℤ) := by
  rw [Icc_zero_eq_map_range n, Finset.sum_map]
  rfl

/-- **The proportion of scales in the window `{m₀,…,m₀+Mw}`, in the frozen
display's own form**: the `Finset.range (Mw+1)`-indexed average of the
`Set.indicator`s of `Ev (m₀ + k)`. -/
def scalePropFrom (Ev : ℤ → Set Ω) (m0 : ℤ) (Mw : ℕ) (omega : Ω) : ℝ :=
  (1 / ((Mw : ℝ) + 1)) *
    ∑ k ∈ Finset.range (Mw + 1),
      (Ev (m0 + (k : ℤ))).indicator (fun _ => (1 : ℝ)) omega

/-- **The window re-index.**  The frozen display's `Finset.range`-indexed indicator
average at base `m₀` is the proved `Finset.Icc`-indexed `scaleProp` of the
shifted family. -/
theorem scalePropFrom_eq_scaleProp (Ev : ℤ → Set Ω) (m0 : ℤ) (Mw : ℕ) (omega : Ω) :
    scalePropFrom Ev m0 Mw omega = scaleProp (fun k => Ev (m0 + k)) Mw omega := by
  classical
  simp only [scalePropFrom, scaleProp]
  refine congrArg (fun z : ℝ => (1 / ((Mw : ℝ) + 1)) * z) ?_
  rw [sum_Icc_zero_eq_sum_range (fun m => if omega ∈ Ev (m0 + m) then (1 : ℝ) else 0) Mw]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Set.indicator_apply]

/-! ## 3. Transport of the independence hypothesis -/

variable [MeasurableSpace Ω]

/-- **`ColumnsIndep` is stable under the diagonal shift.**  The residue-`b` class
of the shifted array is the residue-`(b+m₀)` class of the original, composed with
the relabelling `g ↦ (k ↦ g (k+m₀))` of `ℤ → ℝ`, which is measurable; mutual
independence is preserved by `iIndepFun.comp`. -/
theorem columnsIndep_shiftArray {P : Measure Ω} {X : ℤ → ℤ → Ω → ℝ} {r : ℕ}
    (m0 : ℤ) (h : ColumnsIndep P X r) : ColumnsIndep P (shiftArray m0 X) r := by
  intro b
  have hb := (h (b + m0)).comp
    (g := fun (_ : ℤ) (x : ℤ → ℝ) => (fun (k : ℤ) => x (k + m0)))
    (fun _ => Measurable.of_eval fun k => measurable_pi_apply (k + m0))
  have hrw : ∀ j : ℤ, j * (r : ℤ) + (b + m0) = j * (r : ℤ) + b + m0 :=
    fun j => (add_assoc _ _ _).symm
  simp only [Function.comp_def, hrw] at hb
  exact hb

/-! ## 4. The re-based ratio-tail endpoint -/

/-- **The `§4.1` ratio-tail endpoint at an arbitrary base scale `m₀`.**

Given, for one array `X` and one event family `Ev`, the four Appendix-D
hypotheses, the parameter conditions of the proved
`IndicatorDensity.ratioTail_of_concentration`, and the deterministic reduction
`hreduce` **at every scale `m : ℤ`**, the density of scales in the window
`{m₀,…,m₀+n}` at which `Ev` fails obeys

```
ℙ[ θ < density of bad scales over {m₀,…,m₀+n} ] ≤ exp(−c₁n)/Q
```

for **every** `n : ℕ`, including the short windows `n < r` that
`p.concentration.for.scales` does not itself reach (covered inside the
proved `ratioTail_of_concentration`).

The proof is the diagonal translation of the array: `Y_k(X') = Y_{k+m₀}(X)`,
`ColumnsIndep` transports, and the three remaining Appendix-D hypotheses are
per-entry, hence transport entrywise. -/
theorem ratioTail_of_concentration_shift
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℤ → ℤ → Ω → ℝ)
    {p s' theta c1 Q : ℝ} {r : ℕ} (Ev : ℤ → Set Ω) (m0 : ℤ)
    (hp : 1 ≤ p) (hs' : 0 < s') (hs'1 : s' ≤ 1) (hsp : 1 ≤ s' * p) (hr1 : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hXnn : ∀ k j omega, 0 ≤ X k j omega)
    (hmomL : ∀ k j, ∫⁻ omega, ENNReal.ofReal ((X k j omega) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r)
    (hQ : 1 ≤ Q) (htheta0 : 0 < theta) (hthetar : theta * ((r : ℝ) + 1) < 1)
    (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ) ≤ s' * p * theta / (16 * (r : ℝ)))
    (hreduce : ∀ m : ℤ, ∀ omega ∈ (Ev m)ᶜ,
      9 * s'⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) < Yk X s' m omega)
    (n : ℕ) :
    P {omega | theta < scaleProp (fun k => (Ev (m0 + k))ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hconc : ∀ Mw : ℕ, (r : ℤ) ≤ (Mw : ℤ) →
      P (concEvent (shiftArray m0 X) p s' theta Cstar Mw)
        ≤ ENNReal.ofReal
            (Real.exp (-(s' * p * theta) / (16 * (r : ℝ)) * ((Mw : ℝ) + 1))) := by
    intro Mw hMw
    exact p_concentration_for_scales_Cstar P (shiftArray m0 X) hp hs' hs'1 hsp hr1
      (fun k j => hXmeas (k + m0) (j + m0))
      (fun k j omega => hXnn (k + m0) (j + m0) omega)
      (fun k j => hmomL (k + m0) (j + m0)) (columnsIndep_shiftArray m0 hindep)
      Mw theta hMw htheta0 htheta1
  refine ratioTail_of_concentration P (shiftArray m0 X) (fun k => Ev (m0 + k)) hr1 hQ
    htheta0 hthetar hc1 hrate hconc (fun m _hm omega homega => ?_) n
  have hshift : Yk (shiftArray m0 X) s' m omega = Yk X s' (m + m0) omega :=
    Yk_shiftArray X s' m0 m omega
  rw [hshift]
  have hmem : omega ∈ (Ev (m + m0))ᶜ := by rwa [add_comm m m0]
  exact hreduce (m + m0) omega hmem

end

end Algsuperdiff.Section4.Provider.Proportion
