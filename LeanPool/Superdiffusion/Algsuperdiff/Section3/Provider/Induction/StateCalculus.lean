/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureFinalArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus

/-!
# StateCalculus

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The state calculus of the Section 3.6 induction

Support layer for the two induction roots `p.induction.step` and
`p.induction.bounds`.  The roots themselves are NOT declared here: they wait
on `Algsuperdiff.Frozen.Section3.multiscale_estimate`.  This module delivers
the surrounding calculus of `Algsuperdiff.Frozen.Section3.inductionState`:

* monotonicity in the budget `E`;
* the integer-iteration scaffold from a base scale to every scale;
* the `s^{-2}` to `s`-free absorption of the rare lane at the terminal display;
* the `epsilon`-fixing arithmetic of the multiscale conclusion; and
* the base-bridge arithmetic `Cstart c_star^{-1/2} <= C c_star^{-1}`.

## The frozen definition's `E`-occurrences

`inductionState M m0 E` is a conjunction of two `forall m <= m0` clauses.  The
first (the `sigmaBar` sandwich) does not mention `E` at all.  The second is a
`Probability.IsTwoTermBigOWith` display whose two amplitudes are

* `(E : R) * s^{-1} * sqrt gamma` -- increasing in `E`; and
* `(s^{-1})^2 * exp (-((E : R)^{-1})^3 * gamma^{-1})` -- also increasing in
  `E`, because `E >= 1 > 0` makes `E^{-1}` decreasing, hence `(E^{-1})^3`
  decreasing, hence the negated exponent increasing (`gamma > 0` is the
  standing `M.shellPrefix.gamma_pos`).

So *every* occurrence of `E` in the real definition is monotone and
`inductionState_mono_E` is unconditional.  No non-monotone occurrence exists.

## Sources

* ABK26, `d.mathcalS.def`, `p.induction.bounds`, `p.induction.step`, the
  induction proof, the `epsilon`-fixing, the terminal budget `E = C
  c_star^{-1}`.
* The gate does NOT fail at `C = 6`; it clears with margin (`64 * 6 = 384 >=
  324`).
-/

namespace Algsuperdiff.Section3.Provider.Induction

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Amplitude monotonicity of the two-term display -/

open Algsuperdiff.Section3.Provider.Orlicz

/-! ## 2. Monotonicity of the induction state in the budget `E` -/

/-- **The induction state is monotone in its budget.**

Both `E`-occurrences of the frozen definition are increasing in `E`: the
`Gamma_2` amplitude `E s^{-1} sqrt gamma` visibly, and the `Gamma_{1/2}`
amplitude `(s^{-1})^2 exp (-(E^{-1})^3 gamma^{-1})` because `1 <= E` makes
`(E^{-1})^3` decreasing.  Enlarging both amplitudes weakens the display, so no
hypothesis beyond `(E : R) <= (E' : R)` is needed. -/
theorem inductionState_mono_E {M : ABKModel d} {m0 : ℤ}
    {E E' : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (hEE : (E : ℝ) ≤ (E' : ℝ)) :
    Algsuperdiff.Frozen.Section3.inductionState M m0 E' := by
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hE'0 : (0 : ℝ) < (E' : ℝ) := lt_of_lt_of_le hE0 hEE
  have hinv : ((E' : ℝ))⁻¹ ≤ ((E : ℝ))⁻¹ := inv_anti₀ hE0 hEE
  have hcube : (((E' : ℝ))⁻¹) ^ 3 ≤ (((E : ℝ))⁻¹) ^ 3 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hE'0.le) hinv 3
  have hexpArg : -((((E : ℝ))⁻¹) ^ 3 * M.gamma⁻¹)
      ≤ -((((E' : ℝ))⁻¹) ^ 3 * M.gamma⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_right hcube (inv_nonneg.mpr hgamma.le)
    linarith only [hmul]
  refine ⟨hS.1, ?_⟩
  intro m hm s hsWindow
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma).trans_le hsWindow.1
  refine isTwoTermBigOWith_mono_scales (hS.2 m hm s hsWindow) ?_ ?_
  · have hnn : (0 : ℝ) ≤ s⁻¹ * Real.sqrt M.gamma :=
      mul_nonneg (inv_nonneg.mpr hs0.le) (Real.sqrt_nonneg _)
    calc (E : ℝ) * s⁻¹ * Real.sqrt M.gamma
        = (E : ℝ) * (s⁻¹ * Real.sqrt M.gamma) := by ring
      _ ≤ (E' : ℝ) * (s⁻¹ * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right hEE hnn
      _ = (E' : ℝ) * s⁻¹ * Real.sqrt M.gamma := by ring
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexpArg) (by positivity)

/-! ## 3. The integer-iteration scaffold -/

/-- **From a base scale and a one-scale step to every integer scale.**

Above the base scale this is `Int.leInduction`; below it the conclusion is
already contained in the base case, because both clauses of the frozen
definition are `forall m <= m0` (the proved
`...ApproximateRecurrence.Closure.inductionState_mono`). -/
theorem inductionState_of_base_of_step {M : ABKModel d} {mb : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (base : Algsuperdiff.Frozen.Section3.inductionState M mb E)
    (step : ∀ n : ℤ, Algsuperdiff.Frozen.Section3.inductionState M (n - 1) E →
      Algsuperdiff.Frozen.Section3.inductionState M n E) :
    ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E := by
  have hclimb : ∀ n : ℤ, mb ≤ n →
      Algsuperdiff.Frozen.Section3.inductionState M n E := by
    refine Int.leInduction base ?_
    intro n _ hPn
    have hstep := step (n + 1)
    rw [add_sub_cancel_right] at hstep
    exact hstep hPn
  intro m
  rcases le_total mb m with hm | hm
  · exact hclimb m hm
  · exact
      Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.inductionState_mono
        hm (hclimb mb le_rfl)

/-- **The `E`-enlarging iteration.**  The base case holds at the smaller budget and
the one-scale step at the larger budget `E`; the bridge is
`inductionState_mono_E`.  This is the manuscript's `C c_star^{-1/2} |-> C
c_star^{-1}` bump. -/
theorem inductionState_of_base_of_step_of_E_le {M : ABKModel d} {mb : ℤ}
    {E0 E : {E : ℝ // 1 ≤ E}}
    (base : Algsuperdiff.Frozen.Section3.inductionState M mb E0)
    (hE : (E0 : ℝ) ≤ (E : ℝ))
    (step : ∀ n : ℤ, Algsuperdiff.Frozen.Section3.inductionState M (n - 1) E →
      Algsuperdiff.Frozen.Section3.inductionState M n E) :
    ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E :=
  inductionState_of_base_of_step (inductionState_mono_E base hE) step

/-! ## 4. The `s^{-2}` to `s`-free absorption of the rare lane

The transcendental step is confined to `pow_three_le_const_mul_exp`; the
arithmetic core `inv_sq_le_of_regime` sees `exp` only as an opaque positive
real `X`. -/

/-- `y^3 <= 27 exp y` for `y >= 0`: the cube of `1 + z <= exp z` at `z = y/3`. -/
private theorem pow_three_le_const_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    y ^ 3 ≤ 27 * Real.exp y := by
  have h1 : y / 3 ≤ Real.exp (y / 3) := by
    have hx := Real.add_one_le_exp (y / 3)
    linarith only [hx]
  have h2 : (y / 3) ^ 3 ≤ (Real.exp (y / 3)) ^ 3 :=
    pow_le_pow_left₀ (by linarith only [hy]) h1 3
  have h3 : Real.exp y = (Real.exp (y / 3)) ^ 3 := by
    rw [pow_succ, pow_succ, pow_one, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← h3] at h2
  linarith only [h2]

/-- The manuscript's regime `gamma <= C^{-10} c_star^{10}` gives
`216 C^9 gamma <= 216 c_star^{10} / C`, and `c_star <= 3/2` turns that into
`324 c_star^9 / C`; the claim needs `<= 64 c_star^9`, i.e. `C >= 324/64 =
5.0625`.  The carried threshold `6 <= C` clears it. -/
private theorem regime_poly_gate {gamma cst C : ℝ}
    (hcs0 : 0 < cst) (hcs : cst ≤ 3 / 2) (hC : 6 ≤ C)
    (hreg : gamma ≤ (C⁻¹) ^ 10 * cst ^ 10) :
    216 * C ^ 9 * gamma ≤ 64 * cst ^ 9 := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hC10 : (0 : ℝ) < C ^ 10 := pow_pos hC0 10
  have hcs9 : (0 : ℝ) ≤ cst ^ 9 := pow_nonneg hcs0.le 9
  have e1 : 216 * C ^ 10 * gamma ≤ 216 * C ^ 10 * ((C⁻¹) ^ 10 * cst ^ 10) :=
    mul_le_mul_of_nonneg_left hreg (by positivity)
  have e2 : 216 * C ^ 10 * ((C⁻¹) ^ 10 * cst ^ 10) = 216 * cst ^ 10 := by
    field_simp
  rw [e2] at e1
  have e3 : 216 * cst ^ 10 ≤ 324 * cst ^ 9 := by
    have h := mul_le_mul_of_nonneg_left hcs
      (by linarith only [hcs9] : (0 : ℝ) ≤ 216 * cst ^ 9)
    linarith only [h]
  have e4 : 324 * cst ^ 9 ≤ 64 * cst ^ 9 * C := by
    have h := mul_le_mul_of_nonneg_left hC
      (by linarith only [hcs9] : (0 : ℝ) ≤ 64 * cst ^ 9)
    linarith only [h, hcs9]
  have hcomb : (216 * C ^ 9 * gamma) * C ≤ (64 * cst ^ 9) * C := by
    linarith only [e1, e3, e4]
  exact le_of_mul_le_mul_right hcomb hC0

/-- The arithmetic core of the absorption, with the exponential passed as an
opaque positive real `X` satisfying only the cubic minorant.  No numeric tactic
in this proof ever sees `Real.exp`. -/
private theorem inv_sq_le_of_regime {gamma cst C s X : ℝ} (hgamma : 0 < gamma)
    (hcs0 : 0 < cst) (hcs : cst ≤ 3 / 2) (hC : 6 ≤ C)
    (hreg : gamma ≤ (C⁻¹) ^ 10 * cst ^ 10) (hs8 : 8 * gamma ≤ s)
    (hXcube : ((C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹ / 2) ^ 3 ≤ 27 * X) :
    (s⁻¹) ^ 2 ≤ X := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hCne : C ≠ 0 := ne_of_gt hC0
  have hgne : gamma ≠ 0 := ne_of_gt hgamma
  have hpoly := regime_poly_gate hcs0 hcs hC hreg
  have hB3 : ((C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹ / 2) ^ 3 * (8 * C ^ 9 * gamma ^ 3)
      = cst ^ 9 := by
    field_simp
    ring
  have hpos8 : (0 : ℝ) < 8 * C ^ 9 * gamma ^ 3 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hC0 9)) (pow_pos hgamma 3)
  have hmul := mul_le_mul_of_nonneg_right hXcube hpos8.le
  rw [hB3] at hmul
  have hden : (0 : ℝ) < 216 * C ^ 9 * gamma :=
    mul_pos (mul_pos (by norm_num) (pow_pos hC0 9)) hgamma
  have hchain : (1 : ℝ) * (216 * C ^ 9 * gamma)
      ≤ (64 * X * gamma ^ 2) * (216 * C ^ 9 * gamma) := by
    linarith only [hpoly, hmul]
  have h1le : (1 : ℝ) ≤ 64 * X * gamma ^ 2 := le_of_mul_le_mul_right hchain hden
  have h64 : (0 : ℝ) < 64 * gamma ^ 2 := by positivity
  have hinvX : (64 * gamma ^ 2)⁻¹ ≤ X := by
    refine le_of_mul_le_mul_right ?_ h64
    rw [inv_mul_cancel₀ (ne_of_gt h64)]
    linarith only [h1le]
  have hsq : 64 * gamma ^ 2 ≤ s ^ 2 := by
    have h : (8 * gamma) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hgamma]) hs8 2
    linarith only [h]
  calc (s⁻¹) ^ 2 = (s ^ 2)⁻¹ := by rw [inv_pow]
    _ ≤ (64 * gamma ^ 2)⁻¹ := inv_anti₀ h64 hsq
    _ ≤ X := hinvX

/-- **The `s^{-2}` of the induction state's `Gamma_{1/2}` clause is absorbable
at the terminal display**, uniformly over the printed window `s >= 8 gamma`, at
the cost of one enlargement `C |-> 2 C^3` of the exponent constant. -/
theorem inv_sq_mul_exp_le_exp_of_regime {gamma cst C s : ℝ} (hgamma : 0 < gamma)
    (hcs0 : 0 < cst) (hcs : cst ≤ 3 / 2) (hC : 6 ≤ C)
    (hreg : gamma ≤ (C⁻¹) ^ 10 * cst ^ 10) (hs8 : 8 * gamma ≤ s) :
    (s⁻¹) ^ 2 * Real.exp (-((C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹))
      ≤ Real.exp (-((2 * C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹)) := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hCne : C ≠ 0 := ne_of_gt hC0
  set A : ℝ := (C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹ with hAdef
  have hA0 : 0 < A := by
    rw [hAdef]
    exact mul_pos (mul_pos (inv_pos.mpr (pow_pos hC0 3)) (pow_pos hcs0 3))
      (inv_pos.mpr hgamma)
  have hcube : (A / 2) ^ 3 ≤ 27 * Real.exp (A / 2) :=
    pow_three_le_const_mul_exp (by linarith only [hA0])
  have hcore : (s⁻¹) ^ 2 ≤ Real.exp (A / 2) :=
    inv_sq_le_of_regime hgamma hcs0 hcs hC hreg hs8 (by rw [← hAdef]; exact hcube)
  have hhalf : -((2 * C ^ 3)⁻¹ * cst ^ 3 * gamma⁻¹) = -(A / 2) := by
    rw [hAdef]
    field_simp
  have hsplit : Real.exp (A / 2) * Real.exp (-A) = Real.exp (-(A / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hhalf, ← hsplit]
  exact mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le

/-- **The consumer-facing `s`-free display.**

At the terminal budget `E = C c_star^{-1}` the induction state's `Gamma_2`
amplitude is already the printed `C c_star^{-1} s^{-1} sqrt gamma` and its
`Gamma_{1/2}` amplitude is `(s^{-1})^2 exp (-C^{-3} c_star^3 gamma^{-1})`.
Re-wrapping both at the single enlarged constant `Cp = 2 C^3` produces exactly
the first conclusion of `Algsuperdiff.Frozen.Section3.induction_bounds` (with
`C` there instantiated at `Cp`): amplitude `Cp c_star^{-1} s^{-1} sqrt gamma`
and the `s`-free `exp (-(Cp^{-1} c_star^3 gamma^{-1}))`.

No multiscale input is used: the whole content is the `E`-instantiation, the
absorption above, and amplitude monotonicity. -/
theorem inductionState_isTwoTermBigOWith_sFree (M : ABKModel d) {C : ℝ}
    {E : {E : ℝ // 1 ≤ E}} (hC : 6 ≤ C)
    (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hreg : M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10)
    {m0 : ℤ} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (m : ℤ) (hm : m ≤ m0) (s : ℝ)
    (hsWindow : s ∈ Set.Icc (8 * M.gamma) 1) :
    Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma 2)
      (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M m
        ⟨s,
          (mul_pos (by norm_num : (0 : ℝ) < 8)
            M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
      (2 * C ^ 3 * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)
      (Real.exp (-((2 * C ^ 3)⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))) := by
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma).trans_le hsWindow.1
  have hEcube : (((E : ℝ))⁻¹) ^ 3 * M.gamma⁻¹
      = (C ^ 3)⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ := by
    rw [hEval]
    field_simp
  refine isTwoTermBigOWith_mono_scales (hS.2 m hm s hsWindow) ?_ ?_
  · have hnn : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hcs0.le) (inv_nonneg.mpr hs0.le))
        (Real.sqrt_nonneg _)
    have hCle : C ≤ 2 * C ^ 3 := by
      have hsq : (6 : ℝ) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by norm_num) hC 2
      have hmul : C * 1 ≤ C * (2 * C ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hsq]) hC0.le
      linarith only [hmul]
    calc (E : ℝ) * s⁻¹ * Real.sqrt M.gamma
        = C * ((Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma) := by
          rw [hEval]; ring
      _ ≤ (2 * C ^ 3) * ((Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right hCle hnn
      _ = 2 * C ^ 3 * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma := by ring
  · rw [hEcube]
    exact inv_sq_mul_exp_le_exp_of_regime hgamma hcs0 hcs hC hreg hsWindow.1

/-! ## 5. The `epsilon`-fixing of the multiscale conclusion

The frozen `multiscale_estimate` conclusion carries
`Cms * E * s^{-1} * sqrt (epsilon * gamma)` and
`Cms * epsilon * (s^{-1})^2 * exp (...)`.  Fixing `epsilon := (2 Cms)^{-2}`
makes `Cms * sqrt epsilon = 1/2` and `Cms * epsilon = (4 Cms)^{-1} <= 1`, so
both amplitudes drop to the `inductionState` shape at the same `E`.

The enlargement is admissible because every `Cms`-occurrence in the frozen
conclusion is weakened by a larger constant, except the guard
`s <= Cms * epsilon` of the `Y`-refinement clause -- and at the fixed
`epsilon = ((2 Cms)^2)^{-1}` that guard's threshold `(4 Cms)^{-1}` tightens
with `Cms`. -/

/-- The fixed `epsilon = (2 Cms)^{-2}` lies in the admissible window
`Ioc 0 (1/2)` of `multiscale_estimate`, for every `Cms >= 1`. -/
theorem epsilonFix_mem_Ioc {Cms : ℝ} (hCms : 1 ≤ Cms) :
    ((2 * Cms) ^ 2)⁻¹ ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
  have h2 : (2 : ℝ) ≤ 2 * Cms := by linarith only [hCms]
  have hsq : (4 : ℝ) ≤ (2 * Cms) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
    linarith only [h]
  have hpos : (0 : ℝ) < (2 * Cms) ^ 2 := by linarith only [hsq]
  refine ⟨inv_pos.mpr hpos, ?_⟩
  calc ((2 * Cms) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hsq
    _ ≤ 1 / 2 := by norm_num

/-- The `epsilon`-fixing makes the multiscale `Gamma_2` loss coefficient exactly
`1/2`. -/
theorem mul_sqrt_epsilonFix {Cms : ℝ} (hCms : 0 < Cms) :
    Cms * Real.sqrt (((2 * Cms) ^ 2)⁻¹) = 2⁻¹ := by
  have hCne : Cms ≠ 0 := ne_of_gt hCms
  rw [Real.sqrt_inv, Real.sqrt_sq (by linarith only [hCms] : (0 : ℝ) ≤ 2 * Cms)]
  field_simp

/-- The fixed multiscale `Gamma_2` amplitude is at most the induction state's,
at the same budget `E`. -/
theorem multiscaleAmplitude_le_of_epsilonFix {Cms E s gamma : ℝ} (hCms : 0 < Cms)
    (hE : 0 ≤ E) (hs : 0 ≤ s⁻¹) :
    Cms * E * s⁻¹ * Real.sqrt (((2 * Cms) ^ 2)⁻¹ * gamma)
      ≤ E * s⁻¹ * Real.sqrt gamma := by
  have hnn : (0 : ℝ) ≤ E * s⁻¹ * Real.sqrt gamma :=
    mul_nonneg (mul_nonneg hE hs) (Real.sqrt_nonneg _)
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((2 * Cms) ^ 2)⁻¹)]
  calc Cms * E * s⁻¹ * (Real.sqrt (((2 * Cms) ^ 2)⁻¹) * Real.sqrt gamma)
      = (Cms * Real.sqrt (((2 * Cms) ^ 2)⁻¹)) * (E * s⁻¹ * Real.sqrt gamma) := by
        ring
    _ = 2⁻¹ * (E * s⁻¹ * Real.sqrt gamma) := by rw [mul_sqrt_epsilonFix hCms]
    _ ≤ 1 * (E * s⁻¹ * Real.sqrt gamma) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnn
    _ = E * s⁻¹ * Real.sqrt gamma := by ring

/-- The fixed multiscale `Gamma_{1/2}` amplitude is at most the induction
state's: `Cms * (2 Cms)^{-2} = (4 Cms)^{-1} <= 1`. -/
theorem multiscaleRareAmplitude_le_of_epsilonFix {Cms u v : ℝ} (hCms : 1 ≤ Cms)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Cms * ((2 * Cms) ^ 2)⁻¹ * u * v ≤ u * v := by
  have h2 : (2 : ℝ) ≤ 2 * Cms := by linarith only [hCms]
  have hsq : (4 : ℝ) ≤ (2 * Cms) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
    linarith only [h]
  have hpos : (0 : ℝ) < (2 * Cms) ^ 2 := by linarith only [hsq]
  have hcoeff : Cms * ((2 * Cms) ^ 2)⁻¹ ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ hpos
    have e : Cms * ((2 * Cms) ^ 2)⁻¹ * (2 * Cms) ^ 2 = Cms := by
      field_simp
    rw [e, one_mul]
    have hle : Cms * 1 ≤ Cms * (4 * Cms) :=
      mul_le_mul_of_nonneg_left (by linarith only [hCms]) (by linarith only [hCms])
    linarith only [hle]
  calc Cms * ((2 * Cms) ^ 2)⁻¹ * u * v
      = (Cms * ((2 * Cms) ^ 2)⁻¹) * (u * v) := by ring
    _ ≤ 1 * (u * v) := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hu hv)
    _ = u * v := by ring

/-! ## 6. The base bridge `Cstart c_star^{-1/2} <= C c_star^{-1}` -/

/-- The square-root-free core: `Cstart r^{-1} <= C (r r)^{-1}` whenever
`Cstart r <= C` and `r > 0`. -/
private theorem startBudget_core {r Cstart C : ℝ} (hr : 0 < r)
    (hC : Cstart * r ≤ C) :
    Cstart * r⁻¹ ≤ C * (r * r)⁻¹ := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrr : (0 : ℝ) < r * r := mul_pos hr hr
  refine le_of_mul_le_mul_right ?_ hrr
  have e1 : Cstart * r⁻¹ * (r * r) = Cstart * r := by field_simp
  have e2 : C * (r * r)⁻¹ * (r * r) = C := by field_simp
  rw [e1, e2]
  exact hC

/-- **The base bridge.**  Under the proved `c_star <= 3/2` the base case's budget
`Cstart c_star^{-1/2}` is below the induction budget `C c_star^{-1}` as soon as
`C >= Cstart sqrt (3/2)`.  The equivalence is `Cstart c_star^{-1/2} <= C
c_star^{-1}` iff `Cstart sqrt c_star <= C`. -/
theorem startBudget_le_of_sqrt {cst Cstart C : ℝ} (hcs0 : 0 < cst)
    (hcs : cst ≤ 3 / 2) (hCstart : 0 ≤ Cstart)
    (hC : Cstart * Real.sqrt (3 / 2) ≤ C) :
    Cstart * (Real.sqrt cst)⁻¹ ≤ C * cst⁻¹ := by
  have hr : 0 < Real.sqrt cst := Real.sqrt_pos.mpr hcs0
  have hrsq : Real.sqrt cst * Real.sqrt cst = cst := Real.mul_self_sqrt hcs0.le
  have hkey : Cstart * Real.sqrt cst ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcs) hCstart) hC
  have h := startBudget_core hr hkey
  rwa [hrsq] at h

end

end Algsuperdiff.Section3.Provider.Induction
