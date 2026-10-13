/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.DiffusivityAsymptotics
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.InductionStepAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.StateCalculus

/-!
# InductionBoundsAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The self-similar coarse-graining estimate: the Section 3 root

ABK26, `p.induction.bounds` (printed proof):

## Main result

* `induction_bounds_provided`: the body of the draft
  `Algsuperdiff.Frozen.Section3.induction_bounds`, with the identical binder
  list `(d : ℕ)` and the identical `∃ C`-statement.  The draft module is
  deliberately NOT in this file's import closure.

## The assembly

Three inputs, all of them proved or here, each consumed exactly once:

1. `Provider.Base.base_case d` (`Provider/Base/BaseCaseAssembly.lean`) -- its
   LAST clause `∃ Estart, (Estart: ℝ) = Cstart (sqrt c_star)^{-1} ∧
   inductionState M (mStarStar M) Estart` is the induction start `S(m**, Cstart
   c_star^{-1/2})`.  Its first three clauses (the all-scale error, the
   `m**`-window and the `m*`-window plateaus) are NOT consumed.
2. The draft root itself is never imported.
3. `Algsuperdiff.Frozen.Section3.diffusivity_asymptotics d`
   (`Frozen/Section3/DiffusivityAsymptotics.lean`, the frozen
   `p.propagate.diffusivity.lower.bound`) -- its conclusion, the sharp defect
   display `e.formula.for.shom` on the window `∀ m ≤ m0`, is the ingredient of
   the second root conjunct.  Its 2nd and 3rd conclusions (the `sigmaBar`
   sandwich at `m0`) are NOT consumed here; they are consumed inside input 2.

The exported constant is chosen B the universally quantified model.  Write
`Cstart`, `Cstep`, `Cflow` for the three inputs' own constants, and set

`K := max (max 6 (Cstart sqrt(3/2))) (max Cstep Cflow)`,  `C := 2 K^3`.

Each of the four demands on `K` is met by construction and is discharged where
it is used:

* `Cstart sqrt(3/2) ≤ K` -- the base bridge `startBudget_le_of_sqrt`
  (`StateCalculus.lean`): `Cstart c_star^{-1/2} ≤ K c_star^{-1}`, the budget
  bump, proved (not assumed) from the proved `cstar_le_three_halves`.
* `Cstep ≤ K` -- the gate `Cstep c_star^{-1} ≤ E` of the one-scale step.
* `Cflow ≤ K` -- the gate `Cflow c_star^{-1} ≤ E` of the diffusivity root, used
  for the second conjunct.

Per model `M` the terminal budget is `E := K c_star^{-1}`.  The root's own
premise `gamma ≤ (C^{-1})^{10} c_star^{10}` at `C = 2K^3` yields both regimes
actually needed, `gamma ≤ (K^{-1})^{10} c_star^{10}` (for the absorption) and
`gamma ≤ (E^{-1})^{10}` (for the two gates), because `K ≤ 2K^3` and
`(E^{-1})^{10} = (K^{-1})^{10} c_star^{10}`.  The iteration
`inductionState_of_base_of_step_of_E_le` (`StateCalculus.lean`) then gives `S(m,
E)` `m : ℤ`.

**Constant reconciliation.**  All four `C`-slots of the frozen root compose at
the single witness `C = 2K^3`: the regime is a, so the larger constant is the
stronger hypothesis (and it implies the regime at `K` since `K ≤ 2K^3` for `K ≥
6`); the `Gamma_2` amplitude, the `Gamma_{1/2}` exponent and the `sigmaBar`
defect bound are all U bounds, so the larger constant is the weaker conclusion.

## The gap in the printed proof that this module fills

The printed proof of `p.induction.bounds` proves exactly `S(m, C c_star^{-1})`
for every `m ∈ Z` and then stops.  The printed proof never performs that
extraction: `p.propagate.diffusivity.lower.bound` is invoked only for
`e.shom.h.bounds`, and its sharp first conclusion is dropped.  Section 9 below,
`exists_sigmaBar_formula`, supplies it: it re-invokes the
`diffusivity_asymptotics` at the auxiliary top scale `m0:= max m (mStar M + 1)`
(legal for every `m ∈ Z`, since the root's gate is `mStar M < m0` and its
defect conclusion is a `∀ m ≤ m0` window) and reads off the display at the
requested `m`.  No new mathematics is introduced: the whole content is the
landmark bookkeeping the print omits.

## References

* ABK26, (`p.induction.bounds`, with `e.induction.E.bounds` and
  `e.formula.for.shom`), (`d.mathcalS.def`), (`e.propagation.of.indyhyp`),
  (`p.propagate.diffusivity.lower.bound`), (the printed proof assembled and
  completed here), ("a possibly larger `C`"), (the base case citation), (the
  terminal budget `C c_star^{-1}`).
-/

namespace Algsuperdiff.Section3.Provider.Induction

/-! ## 1. The single induction constant

`K` is fixed before every model datum; it is the maximum of the four demands the
assembly makes, and the exported constant is `2 K^3`. -/

/-- A single real above `6` and above three given reals. -/
private theorem exists_inductionConst (a b c : ℝ) :
    ∃ K : ℝ, 6 ≤ K ∧ a ≤ K ∧ b ≤ K ∧ c ≤ K :=
  ⟨max (max 6 a) (max b c),
    le_trans (le_max_left 6 a) (le_max_left _ _),
    le_trans (le_max_right 6 a) (le_max_left _ _),
    le_trans (le_max_left b c) (le_max_right _ _),
    le_trans (le_max_right b c) (le_max_right _ _)⟩

/-! ## 2. The `K ↦ 2 K^3` enlargement

The two monotonicity facts that make the single exported witness work.  Both are
pure arithmetic in an opaque real `K ≥ 6`; no transcendental and no `c_star`
power appears, so the numeric tactics see only linear goals in the atoms
`K`, `K * K`. -/

/-- `K^2 ≤ 2 K^3` for `K ≥ 6`, since `1 ≤ 2 K`. -/
private theorem mul_self_le_two_mul_cube {K : ℝ} (hK : 6 ≤ K) :
    K * K ≤ 2 * K ^ 3 := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hKK : (0 : ℝ) ≤ K * K := mul_nonneg hK0.le hK0.le
  have h := mul_le_mul_of_nonneg_left (by linarith only [hK] : (1 : ℝ) ≤ 2 * K) hKK
  calc K * K = K * K * 1 := by ring
    _ ≤ K * K * (2 * K) := h
    _ = 2 * K ^ 3 := by ring

/-- `K ≤ 2 K^3` for `K ≥ 6`. -/
private theorem self_le_two_mul_cube {K : ℝ} (hK : 6 ≤ K) : K ≤ 2 * K ^ 3 :=
  le_trans
    (le_mul_of_one_le_left (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hK).le
      (by linarith only [hK]))
    (mul_self_le_two_mul_cube hK)

/-- **The regime transfer.**  The root's own premise at the exported constant
`2 K^3` implies the regime at `K`, which is what the `s^{-2}`-absorption needs.
The tenth powers are never expanded: the chain is `K ≤ 2 K^3`, then `inv_anti₀`,
then `pow_le_pow_left₀`. -/
private theorem regime_at_inductionConst {gamma K cst : ℝ} (hK : 6 ≤ K)
    (hcs : 0 ≤ cst) (hreg : gamma ≤ ((2 * K ^ 3)⁻¹) ^ 10 * cst ^ 10) :
    gamma ≤ (K⁻¹) ^ 10 * cst ^ 10 := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hCp0 : (0 : ℝ) < 2 * K ^ 3 := mul_pos (by norm_num) (pow_pos hK0 3)
  have hinv : (2 * K ^ 3)⁻¹ ≤ K⁻¹ := inv_anti₀ hK0 (self_le_two_mul_cube hK)
  have hpow : ((2 * K ^ 3)⁻¹) ^ 10 ≤ (K⁻¹) ^ 10 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hCp0.le) hinv 10
  exact hreg.trans (mul_le_mul_of_nonneg_right hpow (pow_nonneg hcs 10))

/-- **The terminal budget is admissible.**  `1 ≤ K c_star^{-1}` from `6 ≤ K` and
the proved `c_star ≤ 3/2`: the budget is at least `6 * (3/2)^{-1} = 4`. -/
private theorem one_le_terminalBudget {K cst : ℝ} (hK : 6 ≤ K) (hcs0 : 0 < cst)
    (hcs : cst ≤ 3 / 2) : (1 : ℝ) ≤ K * cst⁻¹ := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have ha : (6 : ℝ) * (3 / 2 : ℝ)⁻¹ ≤ K * (3 / 2 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hK (by norm_num)
  have hb : K * (3 / 2 : ℝ)⁻¹ ≤ K * cst⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ hcs0 hcs) hK0.le
  have hnum : (4 : ℝ) = 6 * (3 / 2 : ℝ)⁻¹ := by norm_num
  linarith only [ha, hb, hnum]

/-! ## 9. The sharp `sigmaBar` formula at every scale

The step the printed proof omits (see the module header).  The
`diffusivity_asymptotics` delivers its sharp defect display as a `∀ m ≤ m0`
window under the landmark gate `mStar M < m0`.  Both are satisfied at once, for
an arbitrary requested scale `m`, by the auxiliary top scale `m0:= max m (mStar
M + 1)`; the state at `m0 - 1` comes from the all-scale iteration supplied by
the caller. -/

/-- **`e.formula.for.shom` scale**, from the `p.propagate.diffusivity.lower.bound`
and the all-scale induction state.

The only device is the landmark bookkeeping: apply the root at `m0 = max m
(mStar M + 1) > mStar M` and read its first conclusion at `m ≤ m0`.  No
amplitude is changed, so the constant is the root's own. -/
private theorem exists_sigmaBar_formula (d : ℕ) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}),
        (∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E) →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ m : ℤ,
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ) := by
  obtain ⟨Cflow, hCflow0, hflow⟩ :=
    Algsuperdiff.Frozen.Section3.diffusivity_asymptotics d
  refine ⟨Cflow, hCflow0, ?_⟩
  intro M E hall hgate hgamma m
  obtain ⟨m0, hmle, hm0gt⟩ : ∃ m0 : ℤ, m ≤ m0 ∧ mStar M < m0 :=
    ⟨max m (mStar M + 1), le_max_left _ _,
      lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)⟩
  obtain ⟨hdefect, -, -⟩ := hflow M m0 E hm0gt (hall (m0 - 1)) hgate hgamma
  exact hdefect m hmle

/-! ## 10. The root -/

/-- **`p.induction.bounds`: the self-similar coarse-graining estimate.**

The exported constant is `C = 2 K^3` with `K = max (max 6 (Cstart sqrt(3/2)))
(max Cstep Cflow)`, chosen after the three inputs' own constants and before
every model datum.  Under the printed regime `gamma ≤ C^{-10} c_star^{10}` the
induction runs at the terminal budget `E = K c_star^{-1}` from the base scale
`m**` through the one-scale propagation, giving `S(m, E)` at every `m : ℤ`; the
first root conjunct is then the proved `s`-free re-wrapping of the state's
error clause, and the second is the sharp defect display of the diffusivity
root, read at every scale through §9.

This is a proved local Provider helper.  Its statement is the body of the draft
`Algsuperdiff.Frozen.Section3.induction_bounds`; the draft module is
deliberately NOT in this file's import closure. -/
theorem induction_bounds_provided
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        (∀ m : ℤ,
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M m
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              (C * (Disorder.cstar M)⁻¹ * s⁻¹ *
                Real.sqrt M.gamma)
              (Real.exp
                (-(C⁻¹ * (Disorder.cstar M) ^ 3 *
                  M.gamma⁻¹)))) ∧
        (∀ m : ℤ,
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ C * (Disorder.cstar M)⁻¹ ^ 2 *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) := by
  obtain ⟨_C0, Cstart, _hC00, hCstart0, hbase⟩ := Provider.Base.base_case d
  obtain ⟨Cstep, _hCstep0, hstep⟩ := induction_step_provided d
  obtain ⟨Cflow, _hCflow0, hsig⟩ := exists_sigmaBar_formula d
  obtain ⟨K, hK6, hKstart, hKstep, hKflow⟩ :=
    exists_inductionConst (Cstart * Real.sqrt (3 / 2)) Cstep Cflow
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK6
  have hCp0 : (0 : ℝ) < 2 * K ^ 3 := mul_pos (by norm_num) (pow_pos hK0 3)
  refine ⟨2 * K ^ 3, hCp0, ?_⟩
  intro M hreg
  -- the standing disorder data
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.mpr hcs0).le
  -- the terminal budget `E = K c_star^{-1}`
  obtain ⟨E, hEval⟩ :
      ∃ E : {E : ℝ // 1 ≤ E}, (E : ℝ) = K * (Disorder.cstar M)⁻¹ :=
    ⟨⟨K * (Disorder.cstar M)⁻¹, one_le_terminalBudget hK6 hcs0 hcs⟩, rfl⟩
  -- the two regimes, both from the root's single premise
  have hregK : M.gamma ≤ (K⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    regime_at_inductionConst hK6 hcs0.le hreg
  have hEinv : ((E : ℝ)⁻¹) ^ 10 = (K⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    rw [hEval, mul_inv, inv_inv, mul_pow]
  have hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 := by
    rw [hEinv]; exact hregK
  -- the three budget gates
  have hstepGate : Cstep * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    rw [hEval]; exact mul_le_mul_of_nonneg_right hKstep hcsinv
  have hflowGate : Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    rw [hEval]; exact mul_le_mul_of_nonneg_right hKflow hcsinv
  -- the base case at `m**` and the bridge to the terminal budget
  obtain ⟨-, -, -, Estart, hEstartVal, hEstartState⟩ := hbase M
  have hbridge : (Estart : ℝ) ≤ (E : ℝ) := by
    rw [hEstartVal, hEval]
    exact startBudget_le_of_sqrt hcs0 hcs hCstart0.le hKstart
  -- the iteration: the state at every scale
  have hall : ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E :=
    inductionState_of_base_of_step_of_E_le hEstartState hbridge
      fun n hn => hstep M n E hstepGate hgammaE hn
  refine ⟨?_, ?_⟩
  · -- conjunct 1: the `s`-free two-term display,
    intro m s hsWindow
    exact inductionState_isTwoTermBigOWith_sFree M hK6 hEval hregK (hall m) m
      le_rfl s hsWindow
  · -- conjunct 2: the sharp defect display,
    intro m
    refine (hsig M E hall hflowGate hgammaE m).trans ?_
    have hT : (0 : ℝ) ≤
        Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M m : ℝ) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        (Annealed.sigmaBar M m).2.le
    have hCK : Cflow * K ≤ 2 * K ^ 3 :=
      le_trans (mul_le_mul_of_nonneg_right hKflow hK0.le)
        (mul_self_le_two_mul_cube hK6)
    have hCoef : Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ)
        ≤ 2 * K ^ 3 * (Disorder.cstar M)⁻¹ ^ 2 := by
      rw [hEval]
      calc Cflow * (Disorder.cstar M)⁻¹ * (K * (Disorder.cstar M)⁻¹)
          = Cflow * K * (Disorder.cstar M)⁻¹ ^ 2 := by ring
        _ ≤ 2 * K ^ 3 * (Disorder.cstar M)⁻¹ ^ 2 :=
            mul_le_mul_of_nonneg_right hCK (sq_nonneg _)
    calc Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) * Real.sqrt M.gamma *
            |Real.log M.gamma| * (Annealed.sigmaBar M m : ℝ)
        = Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
            (Real.sqrt M.gamma * |Real.log M.gamma| *
              (Annealed.sigmaBar M m : ℝ)) := by ring
      _ ≤ 2 * K ^ 3 * (Disorder.cstar M)⁻¹ ^ 2 *
            (Real.sqrt M.gamma * |Real.log M.gamma| *
              (Annealed.sigmaBar M m : ℝ)) :=
          mul_le_mul_of_nonneg_right hCoef hT
      _ = 2 * K ^ 3 * (Disorder.cstar M)⁻¹ ^ 2 * Real.sqrt M.gamma *
            |Real.log M.gamma| * (Annealed.sigmaBar M m : ℝ) := by ring

end Algsuperdiff.Section3.Provider.Induction
