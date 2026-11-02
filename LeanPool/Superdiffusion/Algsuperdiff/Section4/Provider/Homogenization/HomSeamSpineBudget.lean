/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradSpine

/-!
# HomSeamSpineBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The root display chain: the `|log γ|³` collapse and its free factor slot

## What this file supplies

The corrected statement enlarges the moment display of
Theorem B from `|log γ|²` to `|log γ|³` and assigns the new log to the
two machine-pinned costs of realizing Step 3 at the fixed exponent `p = 4d`.
This file is the display-side half of that assignment.

The seam display (`HomSeamStepOneDisplay.exists_ethmB_seam_moment_bound`) gives
the FIRST TWO logs and is untouched: `StepOneDisplayAt` is consumed here
verbatim, at `Real.log M.gamma ^ (2: ℕ)`.  What changes is the `K_abs` slot of
the real cut: it is no longer a model-free numeral but a per-model quantity
carrying an explicit BUDGET

```text
  0 ≤ K_abs   and   K_abs ≤ C_abs · |log γ|,
```

and the produced `E_B` moment display therefore gives at

```text
  C · (√p + √|log γ|) · √γ · |log γ|³,
```

which is the frozen statement's shape.  The budget is exactly what
`HomSeamBudgetArith.recut_geomBudget_le_absLog` certifies for `GEOM · CA`.

```text
  exists_spine_defect_witness_of_displayBudget    -- the real cut, at |log γ|³
  homogenization_spine_close_of_stepOneDisplayBudget
                                                  -- the spine, (C1) discharged
```

Passing from `|log γ|²` to `|log γ|³` at the level of these statements is a
one-log weakening (the printed gate gives `4 ≤ |log γ|`, so `|log γ|² ≤ |log
γ|³`); nothing here is stronger than the chain, and the extra log is spent, not
banked.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The real defect witness, at the budgeted `K_abs` -/

/-- **The real defect witness at the frozen display.**

The real defect witness at a free display, with the `K_abs` slot
moved INSIDE the model quantifier and gated by the budget
`K_abs ≤ C_abs · |log γ|`.  The Step-1 display hypothesis is unchanged, at
`|log γ|²`; the conclusion is the frozen moment display, at `|log γ|³`.

The one new inequality is
`K_abs · (C₀(1+C_gap) T |log γ|²) ≤ C · T · |log γ|³` — the free factor slot,
spent on the budget and on nothing else. -/
theorem exists_spine_defect_witness_of_displayBudget (d : ℕ) (cstar : ℝ)
    (_hcstar : 0 < cstar) {Cgap Cabs C0 : ℝ} (hCgap : 0 ≤ Cgap) (hCabs : 0 ≤ Cabs)
    (hC0 : 1 ≤ C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Kabs : ℝ, 0 ≤ Kabs → Kabs ≤ Cabs * |Real.log M.gamma| →
          ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
            ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
              StepOneDisplayAt M Cgap Y m sb C0 →
              ∃ EB : Cutoff.CutoffSample d → ℝ,
                (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
                (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
                  (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                    ENNReal.ofReal
                        (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
                (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ D : ℝ, 0 ≤ D →
                    ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) sb omega →
                      Kabs * D ≤ EB omega) := by
  have hC0pos : (0 : ℝ) < C0 := lt_of_lt_of_le zero_lt_one hC0
  set C : ℝ := Cabs * C0 * (1 + Cgap) + C0 + 1 with hCdef
  have hKC0 : (0 : ℝ) ≤ Cabs * C0 * (1 + Cgap) := by
    have h1 : (0 : ℝ) ≤ Cabs * C0 := mul_nonneg hCabs hC0pos.le
    have h2 : (0 : ℝ) ≤ 1 + Cgap := by linarith only [hCgap]
    exact mul_nonneg h1 h2
  have hCpos : 0 < C := by
    rw [hCdef]; linarith only [hKC0, hC0pos]
  have hCquart : (0 : ℝ) < ((4 * C)⁻¹) ^ (2 : ℕ) := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    exact pow_pos (inv_pos.mpr h4) 2
  refine ⟨min (1 / 81) (((4 * C)⁻¹) ^ (2 : ℕ)), C,
    lt_min (by norm_num) hCquart, hCpos, ?_⟩
  intro M _hcs hgamma Kabs hKabs hKbud Y hYmeas m sb hdisp
  /- ### the `γ`-consequences of the thresho -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_81 : M.gamma ≤ 1 / 81 := le_trans hgamma (min_le_left _ _)
  have hg_C : M.gamma ≤ ((4 * C)⁻¹) ^ (2 : ℕ) := le_trans hgamma (min_le_right _ _)
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hg1lt : M.gamma < 1 := by linarith only [hg_81]
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := (inv_pos.mpr hLpos).le
  /- ### `p = 1` lies inside the theorem's own ran -/
  have hsqrtC : Real.sqrt M.gamma ≤ (4 * C)⁻¹ := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    have hpow : Real.sqrt M.gamma ^ (2 : ℕ) ≤ ((4 * C)⁻¹) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hgpos.le]; exact hg_C
    exact le_of_pow_le_pow_left₀ (by norm_num) (inv_pos.mpr h4).le hpow
  have hprod : C * (M.gamma * |Real.log M.gamma|) ≤ 1 := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    have hstep := gamma_mul_absLog_le hgpos hg1lt
    have hmul : C * (M.gamma * |Real.log M.gamma|) ≤ C * (4 * Real.sqrt M.gamma) :=
      mul_le_mul_of_nonneg_left hstep hCpos.le
    have hfin : (4 * C) * Real.sqrt M.gamma ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hsqrtC h4.le
      rwa [mul_inv_cancel₀ (ne_of_gt h4)] at h
    linarith only [hmul, hfin]
  have hone : (1 : ℝ) ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
    have hppos : (0 : ℝ) < C * M.gamma * |Real.log M.gamma| :=
      mul_pos (mul_pos hCpos hgpos) hLpos
    have hid : (C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) *
        (C * M.gamma * |Real.log M.gamma|) = 1 := by
      field_simp
    have hle : 1 * (C * M.gamma * |Real.log M.gamma|) ≤
        (C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) *
          (C * M.gamma * |Real.log M.gamma|) := by
      rw [hid, one_mul, mul_assoc]
      exact hprod
    exact le_of_mul_le_mul_right hle hppos
  /- ### the display, on the theorem's own ran -/
  have hmom : ∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal
            (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p := by
    intro p hp hrange
    exact hdisp p hp
      (range_mono_of_le hC0pos (by rw [hCdef]; linarith only [hKC0]) hginv hLinv hrange)
  /- ### a.e. finiteness of the carrier, from the `p = 1` instan -/
  have hmeas : Measurable (ethmB M Cgap Y m (homN M m) sb) :=
    measurable_ethmB M Cgap hYmeas (homN_le M m) _
  have hfin : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ethmB M Cgap Y m (homN M m) sb omega ≠ ⊤ := by
    have h1 := hmom 1 le_rfl hone
    have hrw : (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ (1 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      refine lintegral_congr fun omega => ?_
      rw [ENNReal.rpow_one]
    have hne : (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≠ ⊤ := by
      rw [hrw]
      refine ne_top_of_le_ne_top ?_ h1
      rw [ENNReal.rpow_one]
      exact ENNReal.ofReal_ne_top
    exact (ae_lt_top' hmeas.aemeasurable hne).mono fun omega homega => homega.ne
  /- ### the real c -/
  refine ⟨fun omega => Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal,
    fun omega => mul_nonneg hKabs ENNReal.toReal_nonneg,
    hmeas.ennreal_toReal.const_mul Kabs, ?_, ?_⟩
  · /- the moment display, after the cut and the budget slot -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hpt : ∀ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal) ≤
          ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) sb omega := by
      intro omega
      rw [ENNReal.ofReal_mul hKabs]
      exact mul_le_mul' (le_refl _) ENNReal.ofReal_toReal_le
    have hmono : (∫⁻ omega,
        ENNReal.ofReal (Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal) ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ∫⁻ omega, (ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) sb omega) ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      lintegral_mono fun omega => ENNReal.rpow_le_rpow (hpt omega) hp0
    have hscale := ethmB_const_smul_moment M Cgap (Y := Y) (m := m) (n := homN M m)
      (s := sb) hp0 hKabs (hmom p hp hrange)
    refine (hmono.trans hscale).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    /- the free factor slot, spent -/
    have habs : Real.log M.gamma ^ (2 : ℕ) = |Real.log M.gamma| ^ (2 : ℕ) := (sq_abs _).symm
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma := by
      positivity
    have hTL : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (2 : ℕ) := by positivity
    have hcube : |Real.log M.gamma| ^ (3 : ℕ) =
        |Real.log M.gamma| ^ (2 : ℕ) * |Real.log M.gamma| := by ring
    have hbud : Kabs * (C0 * (1 + Cgap)) ≤ Cabs * |Real.log M.gamma| * (C0 * (1 + Cgap)) := by
      refine mul_le_mul_of_nonneg_right hKbud ?_
      have h2 : (0 : ℝ) ≤ 1 + Cgap := by linarith only [hCgap]
      exact mul_nonneg hC0pos.le h2
    have hCfac : Cabs * C0 * (1 + Cgap) ≤ C := by
      rw [hCdef]; linarith only [hC0pos]
    have hstep : Cabs * C0 * (1 + Cgap) *
        ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          |Real.log M.gamma| ^ (3 : ℕ)) ≤
        C * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          |Real.log M.gamma| ^ (3 : ℕ)) := by
      refine mul_le_mul_of_nonneg_right hCfac ?_
      positivity
    rw [habs]
    calc Kabs * (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * |Real.log M.gamma| ^ (2 : ℕ))
        = (Kabs * (C0 * (1 + Cgap))) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (2 : ℕ)) := by ring
      _ ≤ (Cabs * |Real.log M.gamma| * (C0 * (1 + Cgap))) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (2 : ℕ)) := mul_le_mul_of_nonneg_right hbud hTL
      _ = Cabs * C0 * (1 + Cgap) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (3 : ℕ)) := by rw [hcube]; ring
      _ ≤ C * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            |Real.log M.gamma| ^ (3 : ℕ)) := hstep
      _ = C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            |Real.log M.gamma| ^ (3 : ℕ) := by ring
  · /- the linka -/
    refine hfin.mono fun omega hne D hD hle => ?_
    have hreal : D ≤ (ethmB M Cgap Y m (homN M m) sb omega).toReal := by
      have h := ENNReal.toReal_mono hne hle
      rwa [ENNReal.toReal_ofReal hD] at h
    exact mul_le_mul_of_nonneg_left hreal hKabs

/-! ## 2. The spine at the frozen display, with (C1) discharged -/

/-- **The spine at a free `(Y, sb)` and the budgeted `K_abs`, at `|log γ|³`.**

`HomSeamGradSpine`'s gradient-threaded spine close with

* the `K_abs` slot moved inside the model quantifier and gated by the budget,
* the produced moment clause at the frozen factor `|log γ|³`,

and with clause (C1) discharged off the Section-3 anchor
`Algsuperdiff.Frozen.Section3.induction_bounds` at the genuine running
diffusivity `Annealed.sigmaBar M m`, exactly as in the original.  The Step-1
display hypothesis, the clause supplier and the root's own `HasGradientOn`
binder are unchanged, byte for byte. -/
theorem homogenization_spine_close_of_stepOneDisplayBudget (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) {Cgap Cabs C0 : ℝ} (hCgap : 0 ≤ Cgap) (hCabs : 0 ≤ Cabs)
    (hC0 : 1 ≤ C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Kabs : ℝ, 0 ≤ Kabs → Kabs ≤ Cabs * |Real.log M.gamma| →
          ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
            ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
              StepOneDisplayAt M Cgap Y m sb C0 →
              (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                HomSpineClauseSupplierAtGrad M Cgap Y m sb
                  ((Annealed.sigmaBar M m : ℝ)) Kabs omega) →
              ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
                |sigmaBar -
                    Real.sqrt (M.nu ^ (2 : ℕ) +
                      cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
                  C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar ∧
                ∃ EB : Cutoff.CutoffSample d → ℝ,
                  (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
                  (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
                    (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                      ENNReal.ofReal
                          (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                            Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
                  ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                    ∀ L : ℤ, m ≤ L →
                      ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                        (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                        IsDirichletSolutionOn
                            (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                            (originCube d m) u h g →
                        IsDirichletSolutionOn
                            (fun _ => sigmaBar • (1 : Mat d)) (originCube d m) v h g →
                        HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kg g →
                        HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kh h.grad →
                        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                        HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                        (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                          Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                            EB omega *
                              (sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                          |volumeAverage (openCubeSet (originCube d m))
                                (fun y => M.nu * vecNormSq (u.grad y)) -
                              volumeAverage (openCubeSet (originCube d m))
                                (fun y => sigmaBar * vecNormSq (v.grad y))| ≤
                            EB omega *
                              (Real.sqrt sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                  Real.sqrt sigmaBar *
                                    (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                                (2 : ℕ) := by
  obtain ⟨Cib, hCib, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hcinv : (0 : ℝ) ≤ cstar⁻¹ ^ (2 : ℕ) := pow_nonneg (inv_nonneg.mpr hcstar.le) 2
  have hCflow : (0 : ℝ) ≤ Cib * cstar⁻¹ ^ (2 : ℕ) := mul_nonneg hCib.le hcinv
  obtain ⟨g0, Cwit, hg0, hCwit, hwit⟩ :=
    exists_spine_defect_witness_of_displayBudget d cstar hcstar hCgap hCabs hC0
  have hreg0 : (0 : ℝ) < (Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) :=
    mul_pos (pow_pos (inv_pos.mpr hCib) 10) (pow_pos hcstar 10)
  refine ⟨min g0 ((Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ)), Cwit + Cib * cstar⁻¹ ^ (2 : ℕ),
    lt_min hg0 hreg0, by linarith only [hCwit, hCflow], ?_⟩
  intro M hcs hgamma Kabs hKabs hKbud Y hYm m sb hdisp hclauses
  have hg_wit : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hreg : M.gamma ≤ (Cib⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    rw [hcs]
    exact le_trans hgamma (min_le_right _ _)
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hC1 := (hbounds M hreg).2 m
  rw [hcs] at hC1
  obtain ⟨EB, hEB0, hEBm, hEBmom, hlink⟩ :=
    hwit M hcs hg_wit Kabs hKabs hKbud Y hYm m sb hdisp
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  refine ⟨(Annealed.sigmaBar M m : ℝ), hsig, ?_, EB, hEB0, hEBm, ?_, ?_⟩
  · /- (C1), re-based at the endpoint's own consta -/
    have hT : (0 : ℝ) ≤ Real.sqrt M.gamma * |Real.log M.gamma| *
        ((Annealed.sigmaBar M m : ℝ)) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hsig.le
    refine hC1.trans ?_
    calc Cib * cstar⁻¹ ^ (2 : ℕ) * Real.sqrt M.gamma * |Real.log M.gamma| *
          ((Annealed.sigmaBar M m : ℝ))
        = Cib * cstar⁻¹ ^ (2 : ℕ) *
            (Real.sqrt M.gamma * |Real.log M.gamma| * ((Annealed.sigmaBar M m : ℝ))) := by
          ring
      _ ≤ (Cwit + Cib * cstar⁻¹ ^ (2 : ℕ)) *
            (Real.sqrt M.gamma * |Real.log M.gamma| *
              ((Annealed.sigmaBar M m : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCwit]) hT
      _ = (Cwit + Cib * cstar⁻¹ ^ (2 : ℕ)) * Real.sqrt M.gamma * |Real.log M.gamma| *
            ((Annealed.sigmaBar M m : ℝ)) := by ring
  · /- (C2), re-based at the endpoint's own consta -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hsub : p ≤ Cwit⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
      range_mono_of_le hCwit (by linarith only [hCflow]) hginv hLinv hrange
    refine (hEBmom p hp hsub).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by positivity
    calc Cwit * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          |Real.log M.gamma| ^ (3 : ℕ)
        = Cwit * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            |Real.log M.gamma| ^ (3 : ℕ)) := by ring
      _ ≤ (Cwit + Cib * cstar⁻¹ ^ (2 : ℕ)) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCflow]) hT
      _ = (Cwit + Cib * cstar⁻¹ ^ (2 : ℕ)) *
            (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            |Real.log M.gamma| ^ (3 : ℕ) := by ring
  · /- (C3) and (C4), through the linka -/
    refine (hlink.and hclauses).mono ?_
    rintro omega ⟨hlk, hsupply⟩ L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
    obtain ⟨D, hD0, hDdom, hC3, hC4⟩ :=
      hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
    have hKD : Kabs * D ≤ EB omega := hlk D hD0 hDdom
    have hbr : 0 ≤ dataBracket ((Annealed.sigmaBar M m : ℝ))
        (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
    refine ⟨hC3.mono fun x hx => hx.trans ?_, hC4.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hKD hbr
    · exact mul_le_mul_of_nonneg_right hKD (sq_nonneg _)

end

end Algsuperdiff.Section4.Provider.Homogenization
