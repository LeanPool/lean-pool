/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSelectionPackage

/-!
# RootAssemblyParameters

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` root assembly, part one: the parameter web and the single a.e. block

## The two defects this module clears

The proved outer chain is → → →, each layer re-exporting its predecessor.  Two
structural defects block the root assembly, and both are fixed here at Z
mathematical cost (no new estimate, no new hypothesis).

**(D1) The chain is lossy.**  The Step-3 window/budget endpoint drops
`GoodScaleWindows`, and the Step-7a selection endpoint drops in addition the
`ε_j` cap.  But `GoodScaleWindows` is *exactly* what's
`stepFiveConcreteOscillationResult_of_stepFourDecay` demands, at the same `ω`,
the same `(n,m)` and the same `X`-gate.  Because each layer re-derives its OWN
existential `Z` and its OWN `(C₁,γ₀,C)` cannot be invoked side by side and
their witnesses identified.  `rootAssembly_aePackage` below carries
`GoodScaleWindows`, the window/budget package AND the Step-7a selection in ONE
`∀ᵐ ω` block under ONE `Z` and ONE `(C₁,γ₀,C)`.

**(D2) `C₁` is opaque.**  The Step-1/3/7a producers export `C₁` as an
existential real with `2 ≤ C₁`, while the Step-6 endpoint needs it spelled out
as `stepOneC1 d Cedos Cann Citer k`, with `Cann` a further existential hidden
inside the `ε_j`-cap proof (`ae_stepOneEpsJ_le`).
`rootAssembly_aePackage` exports `Cann` and the defining identity, so the
produced `C₁` is consumable by the pointwise layer.

## Enlarging the produced constant

The frozen root uses ONE letter `C` in four roles: the tail prefactor, the tail
exponent (twice), the `α`-range `α ≤ 1 - C√γ`, and the prefactor of
`e.energy.density.estimate`.  The §4.4 chain produces its estimate constant
independently of the minimal-scale constant, so the assembly must take a
maximum.  `§3` proves that every role is MONOTONE-W in `C`: enlarging `C`
weakens the tail bound and shrinks the admissible `α`-range, so a single
maximum is legitimate.  This is the arithmetic behind "the single `C` in all
three roles", and it is proved here rather than asserted.

## References

* ABK26, `t.regularity`; Steps 1--3 and 7a.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-`ω` payload of the single a.e. block -/

/-- **The Step-1/3/7a payload at one window `[n,m]`**: the good-scale windows of
`p.minimal.scale.separation.sec4` (the input's Step-5 endpoint reads)'s window
family / bad set / budget / separation package's Step-7a selection at every
printed lattice centre.

Packaging the three together is what lets ONE `filter_upwards` serve the whole
per-`ω` chain. -/
def RootWindowPayload (M : ABKModel d) (C1 alpha : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha) stepOneSEighth_pos n m
      omega ∧
    (14 : ℤ) ≤ m - n ∧
    StepThreeWindowsAndBudget M (stepOneDelta C1 alpha) n m omega ∧
    ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
      ∃ (n' m' : ℤ) (zp zpp : Vec d),
        StepSevenSelectionData M (stepOneDelta C1 alpha) n m
          (Support.triadicLatticePoint n v) omega n' m' zp zpp

/-- The payload from the good-scale windows alone, at the gate.  Every component
beyond `GoodScaleWindows` is a proved pointwise consequence:'s
`stepThreeWindowsAndBudget_of_goodScaleWindows`'s
`exists_stepSevenSelectionData_of_stepThreeWindowsAndBudget`. -/
theorem rootWindowPayload_of_goodScaleWindows {M : ABKModel d} {C1 alpha : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d}
    (hdelta : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
      stepOneSEighth_pos n m omega) :
    RootWindowPayload M C1 alpha n m omega := by
  have hbudget : StepThreeWindowsAndBudget M (stepOneDelta C1 alpha) n m omega :=
    stepThreeWindowsAndBudget_of_goodScaleWindows (le_of_lt hdelta.1) hdelta.2 hwin hgood
  exact ⟨hgood, hwin, hbudget, fun v hv =>
    exists_stepSevenSelectionData_of_stepThreeWindowsAndBudget hbudget hv⟩

/-! ## 2. The single a.e. endpoint, with `C₁` transparent -/

/-- **`t.regularity` Steps 1--3 and 7a, as one a.e. theorem with a transparent
`C₁`.**

The frozen root's binder block with the minimal scale `X`, its measurability,
its tail, and a single `∀ᵐ ω` block whose payload is `RootWindowPayload` —
good-scale windows, the `14 ≤ m-n` gate consequence, the
window/bad-set/budget/separation package and the Step-7a selection at every
printed lattice centre, all at one `Z` and one `(C₁,γ₀,C)`.

`C₁` is produced spelled out as `stepOneC1 d Cedos Cann Citer k`, at a
caller-supplied `Cann` and a caller-supplied Step-1 index `k ≥ 11`, so the
pointwise §4.4 layer — whose statements name `stepOneC1` transparently — can be
applied at the produced constant.  The three floors travel with it.

`C_edos` is the abstract excess-decay one-step constant, `C_iter` the abstract
Step-6 iteration constant. -/
theorem rootAssembly_aePackage (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    (Cedos Citer Cann : ℝ) (k : ℕ) (hk : 11 ≤ k) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      2 ≤ stepOneC1 d Cedos Cann Citer k ∧
      2 * (d : ℝ) + 2 ≤ stepOneC1 d Cedos Cann Citer k ∧
      4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤
        stepOneC1 d Cedos Cann Citer k ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable (minimalScaleX Z k) ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ minimalScaleX Z k omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m →
                minimalScaleX Z k omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                  RootWindowPayload M
                    (stepOneC1 d Cedos Cann Citer k) alpha n m omega := by
  have hk10 : 10 ≤ k := by omega
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cedos Cann Citer k :=
    two_le_stepOneC1 d Cedos Cann Citer k
  obtain ⟨g0, C0, hg0pos, hC0pos, hRG1⟩ :=
    step_two_minimalScaleX d cstar hcstar k hk10
      (stepOneC1 d Cedos Cann Citer k) hC1two
  refine ⟨g0, C0, hg0pos, hC0pos, hC1two,
    two_mul_dim_le_stepOneC1 d Cedos Cann Citer k,
    step6_le_stepOneC1 d Cedos Cann Citer k, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have halpha1 : alpha < 1 := by
    have h : 0 < C0 * Real.sqrt M.gamma :=
      mul_pos hC0pos (Real.sqrt_pos.mpr hgpos)
    linarith only [halpha, h]
  have hdelta := stepOneDelta_mem hC1two halpha0 halpha1
  obtain ⟨Z, _, _, hXmeas, hXtail, hXgood⟩ := hRG1 M hcs hgamma alpha halpha0 halpha m
  refine ⟨Z, hXmeas, hXtail, ?_⟩
  filter_upwards [hXgood] with omega hgoodw
  intro n hn hgate
  have hwin : (14 : ℤ) ≤ m - n :=
    fourteen_le_window Z hk omega hgate
  exact rootWindowPayload_of_goodScaleWindows hdelta hwin (hgoodw n hn hgate)

/-! ## 3. Enlarging the produced constant -/

/-- **The tail bound is monotone-weakening in `C`.**

The frozen root prints ONE constant in the tail's three slots, so an assembly that
must also serve `e.energy.density.estimate` needs to enlarge it.  The enlargement is
free: with `0 < C₀ ≤ C` and `N ≥ 0`,

```text
  C₀·exp(−(1−α)²(N−C₀)/(C₀γ))  ≤  C·exp(−(1−α)²(N−C)/(Cγ)) .
```

The prefactor grows and the exponent rises (because `N/C ≤ N/C₀`), so the
right-hand side dominates. -/
theorem minimalScaleTail_mono_const {gamma alpha C0 C N : ℝ} (hC0 : 0 < C0)
    (hle : C0 ≤ C) (hgamma : 0 < gamma) (hN : 0 ≤ N) :
    C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C0)) / (C0 * gamma))
      ≤ C * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma)) := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le hC0 hle
  have hdiv : N / C ≤ N / C0 := by
    rw [div_le_div_iff₀ hCpos hC0]
    exact mul_le_mul_of_nonneg_left hle hN
  have hcoef : (0 : ℝ) ≤ (1 - alpha) ^ (2 : ℕ) / gamma :=
    div_nonneg (pow_two_nonneg _) (le_of_lt hgamma)
  have heqL : -((1 - alpha) ^ (2 : ℕ) * (N - C0)) / (C0 * gamma)
      = (1 - alpha) ^ (2 : ℕ) / gamma * (1 - N / C0) := by
    field_simp
    ring
  have heqR : -((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma)
      = (1 - alpha) ^ (2 : ℕ) / gamma * (1 - N / C) := by
    field_simp
    ring
  have hexp : -((1 - alpha) ^ (2 : ℕ) * (N - C0)) / (C0 * gamma)
      ≤ -((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma) := by
    rw [heqL, heqR]
    exact mul_le_mul_of_nonneg_left (by linarith only [hdiv]) hcoef
  have hstep1 : C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C0)) / (C0 * gamma))
      ≤ C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (le_of_lt hC0)
  have hstep2 : C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma))
      ≤ C * Real.exp (-((1 - alpha) ^ (2 : ℕ) * (N - C)) / (C * gamma)) :=
    mul_le_mul_of_nonneg_right hle (le_of_lt (Real.exp_pos _))
  linarith only [hstep1, hstep2]

/-- **The tail bound at an enlarged constant**, in the `ℝ≥0∞` shape the frozen root
prints. -/
theorem minimalScaleTail_ofReal_mono_const {gamma alpha C0 C : ℝ} {N : ℕ}
    (hC0 : 0 < C0) (hle : C0 ≤ C) (hgamma : 0 < gamma) :
    ENNReal.ofReal
        (C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C0)) / (C0 * gamma)))
      ≤ ENNReal.ofReal
        (C * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * gamma))) :=
  ENNReal.ofReal_le_ofReal
    (minimalScaleTail_mono_const hC0 hle hgamma (Nat.cast_nonneg N))

/-- **The `α`-range at an enlarged constant.**  Enlarging `C` shrinks the admissible
range, so the producer's own range hypothesis follows from the enlarged one —
the direction the assembly needs. -/
theorem alphaRange_of_mono_const {gamma alpha C0 C : ℝ} (hle : C0 ≤ C)
    (halpha : alpha ≤ 1 - C * Real.sqrt gamma) :
    alpha ≤ 1 - C0 * Real.sqrt gamma := by
  have hsqrt : (0 : ℝ) ≤ Real.sqrt gamma := Real.sqrt_nonneg gamma
  have h : C0 * Real.sqrt gamma ≤ C * Real.sqrt gamma :=
    mul_le_mul_of_nonneg_right hle hsqrt
  linarith only [halpha, h]

end

end Algsuperdiff.Section4.Provider.Regularity
