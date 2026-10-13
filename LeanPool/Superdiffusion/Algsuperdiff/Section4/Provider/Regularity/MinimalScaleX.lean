/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.MinimalScaleSeparation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.MinimalScaleShift

/-!
# MinimalScaleX

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 2: the minimal scale `X_m(α)`, its tail, and its
# good-scales clause

## The target

ABK26 `t.regularity` Step 2:

```
X_m(α) := Z_m(s/8, δ) + k + 3                                (e.def.X.m.alpha)
X_m(α)  = 𝒪_{Γ₁}( C c⋆^{-2} (1-α)^{-2} γ )        (e.X.m.stochastic.integrability)
```

at the Step-1 parameters `s := 1/4`, `δ := C₁⁻¹(1-α)` of
`e.parameter.choices.regularity`.

## What is delivered, and how it relates to the anchor's clause

`step_two_minimalScaleX` produces, for each `m`, a `Z` such that the four
Step-2 items hold for `X := minimalScaleX Z k` (`= Z + k + 3`):

* (a) the definition: `X` is literally `minimalScaleX Z k`, i.e.
  `fun omega => Z omega + (k : ℕ∞) + 3`, with `Z` the minimal scale delivered by
  `minimal_scale_separation`
  at `(s/8, δ) = (stepOneSEighth, stepOneDelta C₁ α)`.  The identification of
  `Z` is machine-visible: the first two conjuncts of the conclusion are the
  producer's own `Measurable Z` and its `a.s.` good-scales clause at the
  tighter gate `Z ω ≤ m - n`, both delivered verbatim;
* (b) `Measurable X`;
* (c) the tail, in the anchor's own shape: for every `N : ℕ`,
  `law {ω | N ≤ X ω} ≤.ofReal (C * exp (-((1-α)^2 * (N - C)) / (C * γ)))`.
  This conjunct is character-for-character the second conjunct of the
  minimal-scale block of the frozen `anomalous_regularity`
  (`Algsuperdiff/Frozen/Section4/AnomalousRegularity.lean`)
  with the anchor's bound `X` replaced by `minimalScaleX Z k` and the anchor's
  produced `C` by the one produced here;
* (d) the a.e. good-scales clause of `minimal_scale_separation`, transported
  from the gate `Z ω ≤ m - n` to the gate `X ω ≤ m - n` (`GoodScaleWindows`).
  The window family `U_j` and the bad set `B_z` of Step 3 are not formed here.

## Deviation from the printed text

Since `s` is the Step-1 numeral `1/4`, `s⁷ → s⁹` is a pure constant move: it is
absorbed into the produced `C` and the printed hypothesis `α ≤ 1 - C γ^{1/2}`
is preserved verbatim.

## References

* ABK26, `t.regularity` Steps 1--2.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## The good-scales window clause

`GoodScaleWindows` is the conclusion body of the frozen block of
`Algsuperdiff.Frozen.Section4.minimal_scale_separation`
(`MinimalScaleSeparation.lean`) spliced verbatim: the two Cesàro displays of
`e.scale.sep.clauses`, the flux-corrected error observable on the good event and
the complement-indicator density, each `≤.ofReal δ`, at the lattice centre
family `3^{n-1}ℤ^d ∩ □_m`.  Only the binder names for `(n, m, omega)` are
supplied; the body is unchanged. -/

/-- The two Cesàro good-scale displays of `p.minimal.scale.separation.sec4` at the
window `[n, m]`, spliced verbatim from the frozen block. -/
def GoodScaleWindows (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
      ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc n m,
          Set.indicator
            (Algsuperdiff.Frozen.Section4.goodEventAt M
              (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
              (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
              ⟨s, hs⟩ (s * Real.sqrt delta))
            (fun omega' =>
              Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSup M k
                ⟨s, hs⟩
                (Cutoff.translateCutoffSample
                  (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                  omega'))
            omega)) ≤
    ENNReal.ofReal delta ∧
  (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
      ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc n m,
          Set.indicator
            ((Algsuperdiff.Frozen.Section4.goodEventAt M
                (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
                (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                ⟨s, hs⟩ (s * Real.sqrt delta))ᶜ)
            (fun _ => (1 : ℝ≥0∞)) omega)) ≤
    ENNReal.ofReal delta

/-! ## The produced constants -/

/-- The produced `γ`-threshold: the first branch of the `min` in the `γ`-gate of
`p.minimal.scale.separation.sec4`, together with the `8γ ≤ s/8` gate. -/
noncomputable def stepTwoGamma0 (Cm cs : ℝ) : ℝ :=
  min ((Cm⁻¹) ^ (10 : ℕ) * cs ^ (10 : ℕ)) (1 / 256)

/-- The produced constant `C = C(d, c⋆)`: large enough (i) to dominate the
producer's prefactor, (ii) to exceed `k + 4` (the shift), (iii) to make the
producer's rate dominate the anchor's, and (iv) to make the theorem's own
hypothesis `α ≤ 1 - C γ^{1/2}` imply the producer's `γ`-gate. -/
noncomputable def stepTwoConst (Cm cs C1 : ℝ) (k : ℕ) : ℝ :=
  max (max Cm ((k : ℝ) + 4))
    (max (Cm * (stepOneSEighth ^ (9 : ℕ))⁻¹ * (cs ^ (2 : ℕ))⁻¹ * C1 ^ (2 : ℕ))
      (Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹))

private theorem stepTwoGamma0_pos {Cm cs : ℝ} (hCm : 0 < Cm) (hcs : 0 < cs) :
    0 < stepTwoGamma0 Cm cs :=
  lt_min (mul_pos (pow_pos (inv_pos.mpr hCm) 10) (pow_pos hcs 10)) (by norm_num)

private theorem stepTwoGamma0_le_left (Cm cs : ℝ) :
    stepTwoGamma0 Cm cs ≤ (Cm⁻¹) ^ (10 : ℕ) * cs ^ (10 : ℕ) :=
  min_le_left _ _

private theorem stepTwoGamma0_le_right (Cm cs : ℝ) : stepTwoGamma0 Cm cs ≤ 1 / 256 :=
  min_le_right _ _

private theorem le_stepTwoConst (Cm cs C1 : ℝ) (k : ℕ) :
    Cm ≤ stepTwoConst Cm cs C1 k :=
  le_trans (le_max_left _ _) (le_max_left _ _)

private theorem shift_le_stepTwoConst (Cm cs C1 : ℝ) (k : ℕ) :
    (k : ℝ) + 4 ≤ stepTwoConst Cm cs C1 k :=
  le_trans (le_max_right _ _) (le_max_left _ _)

private theorem stepTwoConst_pos {Cm cs C1 : ℝ} (hCm : 0 < Cm) (k : ℕ) :
    0 < stepTwoConst Cm cs C1 k :=
  lt_of_lt_of_le hCm (le_stepTwoConst Cm cs C1 k)

/-- The rate condition behind `rate_dom`. -/
private theorem stepTwoConst_rate {Cm cs C1 : ℝ} (hCm : 0 < Cm) (hcs : 0 < cs)
    (hC1 : 0 < C1) (k : ℕ) :
    Cm ≤ stepOneSEighth ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) *
      stepTwoConst Cm cs C1 k := by
  have hs : stepOneSEighth ≠ 0 := ne_of_gt stepOneSEighth_pos
  have hcs' : cs ≠ 0 := ne_of_gt hcs
  have hC1' : C1 ≠ 0 := ne_of_gt hC1
  have hid : stepOneSEighth ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) *
      (Cm * (stepOneSEighth ^ (9 : ℕ))⁻¹ * (cs ^ (2 : ℕ))⁻¹ * C1 ^ (2 : ℕ)) = Cm := by
    field_simp
  have hcoef : (0 : ℝ) ≤ stepOneSEighth ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (le_of_lt stepOneSEighth_pow_pos) (sq_nonneg cs))
      (sq_nonneg _)
  have hmem : Cm * (stepOneSEighth ^ (9 : ℕ))⁻¹ * (cs ^ (2 : ℕ))⁻¹ * C1 ^ (2 : ℕ) ≤
      stepTwoConst Cm cs C1 k :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  calc Cm = stepOneSEighth ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) *
        (Cm * (stepOneSEighth ^ (9 : ℕ))⁻¹ * (cs ^ (2 : ℕ))⁻¹ * C1 ^ (2 : ℕ)) := hid.symm
    _ ≤ stepOneSEighth ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) *
        stepTwoConst Cm cs C1 k := mul_le_mul_of_nonneg_left hmem hcoef

/-- The `γ`-gate condition behind `gate_of_sq_le`. -/
private theorem stepTwoConst_gate {Cm cs C1 : ℝ} (hCm : 0 < Cm) (hcs : 0 < cs)
    (hC1 : 0 < C1) (k : ℕ) :
    1 ≤ (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * stepOneSEighth ^ (9 : ℕ)) *
      stepTwoConst Cm cs C1 k ^ (2 : ℕ) := by
  have hs : stepOneSEighth ≠ 0 := ne_of_gt stepOneSEighth_pos
  have hcs' : cs ≠ 0 := ne_of_gt hcs
  have hC1' : C1 ≠ 0 := ne_of_gt hC1
  have hCm' : Cm ≠ 0 := ne_of_gt hCm
  have hid : (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * stepOneSEighth ^ (9 : ℕ)) *
      (Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹) ^ (2 : ℕ) =
      (stepOneSEighth ^ (9 : ℕ))⁻¹ := by
    field_simp
  have hdpos : (0 : ℝ) < Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹ :=
    mul_pos (mul_pos (mul_pos (pow_pos hCm 5) hC1) (inv_pos.mpr hcs))
      (inv_pos.mpr stepOneSEighth_pow_pos)
  have hmem : Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹ ≤
      stepTwoConst Cm cs C1 k :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hsq : (Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹) ^ (2 : ℕ) ≤
      stepTwoConst Cm cs C1 k ^ (2 : ℕ) :=
    pow_le_pow_left₀ (le_of_lt hdpos) hmem 2
  have hcoef : (0 : ℝ) ≤ (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * stepOneSEighth ^ (9 : ℕ)) :=
    mul_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hCm)) 10)
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg cs))
        (le_of_lt stepOneSEighth_pow_pos))
  calc (1 : ℝ) ≤ (stepOneSEighth ^ (9 : ℕ))⁻¹ :=
        (one_le_inv₀ stepOneSEighth_pow_pos).mpr stepOneSEighth_pow_le_one
    _ = (Cm⁻¹) ^ (10 : ℕ) *
        ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * stepOneSEighth ^ (9 : ℕ)) *
        (Cm ^ (5 : ℕ) * C1 * cs⁻¹ * (stepOneSEighth ^ (9 : ℕ))⁻¹) ^ (2 : ℕ) := hid.symm
    _ ≤ (Cm⁻¹) ^ (10 : ℕ) *
        ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * stepOneSEighth ^ (9 : ℕ)) *
        stepTwoConst Cm cs C1 k ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hsq hcoef

/-! ## The Step-2 endpoint -/

/-- **`t.regularity` Step 2: the minimal scale `X_m(α)`.**

For every `m` there is a minimal scale `Z` of `p.minimal.scale.separation.sec4`
at the Step-1 parameters `(s/8, δ) = (stepOneSEighth, stepOneDelta C₁ α)` --
measurable, and carrying the producer's `a.s.` good-scales clause -- such that
`X := minimalScaleX Z k = Z + k + 3` (`e.def.X.m.alpha`) is measurable, has the
shifted exponential tail in the shape printed in the minimal-scale clause of
`anomalous_regularity`, and carries the same a.e. good-scales clause at its
own (larger) gate `X ω ≤ m - n`, which is the form Steps 3--4 read. -/
theorem step_two_minimalScaleX (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    (k : ℕ) (hk : 10 ≤ k) (C1 : ℝ) (hC1 : 2 ≤ C1) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable Z ∧
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega) ∧
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
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega := by
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1]
  obtain ⟨Cm, hCm, hmss⟩ := Algsuperdiff.Frozen.Section4.minimal_scale_separation d
  refine ⟨stepTwoGamma0 Cm cstar, stepTwoConst Cm cstar C1 k,
    stepTwoGamma0_pos hCm hcstar, stepTwoConst_pos hCm k, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  subst hcs
  set Co := stepTwoConst Cm (Disorder.cstar M) C1 k with hCodef
  have hCopos : 0 < Co := stepTwoConst_pos hCm k
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hCok : (k : ℝ) + 4 ≤ Co := shift_le_stepTwoConst Cm (Disorder.cstar M) C1 k
  have hkR : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hCo1 : (1 : ℝ) ≤ Co := by linarith only [hCok, hkR]
  -- the theorem's own hypothesis, in the two forms the producer needs
  have hsqrtpos : 0 < Real.sqrt M.gamma := Real.sqrt_pos.mpr hgpos
  have halpha1 : alpha < 1 := by
    have hpos : 0 < Co * Real.sqrt M.gamma := mul_pos hCopos hsqrtpos
    linarith only [halpha, hpos]
  have hsq : Co ^ (2 : ℕ) * M.gamma ≤ (1 - alpha) ^ (2 : ℕ) := by
    have h1 : Co * Real.sqrt M.gamma ≤ 1 - alpha := by linarith only [halpha]
    have h2 : (Co * Real.sqrt M.gamma) ^ (2 : ℕ) ≤ (1 - alpha) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt (mul_pos hCopos hsqrtpos)) h1 2
    rwa [mul_pow, Real.sq_sqrt (le_of_lt hgpos)] at h2
  -- the producer's four gates
  have hgate : M.gamma ≤ (Cm⁻¹) ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (stepOneDelta C1 alpha ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
          stepOneSEighth ^ (9 : ℕ)) := by
    have hA : M.gamma ≤ (Cm⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) :=
      le_trans hgamma (stepTwoGamma0_le_left Cm (Disorder.cstar M))
    have hB : M.gamma ≤ (Cm⁻¹) ^ (10 : ℕ) *
        (stepOneDelta C1 alpha ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
          stepOneSEighth ^ (9 : ℕ)) :=
      gate_of_sq_le hgpos (le_of_lt stepOneSEighth_pos) hsq
        (stepTwoConst_gate hCm hcstar hC1pos k)
    rcases le_total (Disorder.cstar M ^ (10 : ℕ))
        (stepOneDelta C1 alpha ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
          stepOneSEighth ^ (9 : ℕ)) with hmin | hmin
    · rw [min_eq_left hmin]
      exact hA
    · rw [min_eq_right hmin]
      exact hB
  have h8 : 8 * M.gamma ≤ stepOneSEighth := by
    have hle : M.gamma ≤ 1 / 256 :=
      le_trans hgamma (stepTwoGamma0_le_right Cm (Disorder.cstar M))
    rw [stepOneSEighth_eq]
    linarith only [hle]
  obtain ⟨Z, hZmeas, hZtail, hZae⟩ :=
    hmss M stepOneSEighth (stepOneDelta C1 alpha) stepOneSEighth_mem
      (stepOneDelta_mem hC1 halpha0 halpha1) hgate h8 m stepOneSEighth_pos
  refine ⟨Z, hZmeas, hZae, measurable_minimalScaleX hZmeas k, ?_, ?_⟩
  · -- (c) the tail, in the anchor's shape
    intro N
    by_cases hN : k + 4 ≤ N
    · have hcast : ((N - (k + 3) : ℕ) : ℝ) = (N : ℝ) - ((k : ℝ) + 3) := by
        rw [Nat.cast_sub (by omega : k + 3 ≤ N)]
        push_cast
        ring
      have hNR : (k : ℝ) + 4 ≤ (N : ℝ) := by exact_mod_cast (by omega : k + 4 ≤ N)
      have ht : (0 : ℝ) ≤ ((N - (k + 3) : ℕ) : ℝ) - 1 := by
        rw [hcast]
        linarith only [hNR]
      have hvt : (N : ℝ) - Co ≤ ((N - (k + 3) : ℕ) : ℝ) - 1 := by
        rw [hcast]
        linarith only [hCok]
      refine le_trans (measure_mono (tail_minimalScaleX_subset Z k N)) ?_
      refine le_trans (hZtail (N - (k + 3))) (ENNReal.ofReal_le_ofReal ?_)
      rw [neg_div, neg_div]
      refine exp_tail_dom hCm (le_stepTwoConst Cm (Disorder.cstar M) C1 k) ?_
      exact rate_dom hgpos hCm hCopos ht hvt
        (stepTwoConst_rate hCm hcstar hC1pos k)
    · refine le_trans prob_le_one ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hNCo : (N : ℝ) ≤ Co := by
        have h1 : (N : ℝ) ≤ (k : ℝ) + 3 := by
          exact_mod_cast (by omega : N ≤ k + 3)
        linarith only [h1, hCok]
      exact one_le_shifted_exp hCo1 hgpos hNCo
  · -- (d) the a.e. good-scales clause, at the gate `X ≤ m - n`
    filter_upwards [hZae] with omega homega n hn hX
    exact homega n hn (le_trans (le_minimalScaleX Z k omega) hX)

end Algsuperdiff.Section4.Provider.Regularity
