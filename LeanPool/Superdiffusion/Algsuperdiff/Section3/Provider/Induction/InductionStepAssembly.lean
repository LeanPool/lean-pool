/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.DiffusivityAsymptotics
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.MultiscaleEstimate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.BaseWindowDiffusivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.StateCalculus

/-!
# InductionStepAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-scale propagation of the induction hypothesis

ABK26, `e.propagation.of.indyhyp` under the condition `e.xi.delta1.condition`:

`S(m-1,E) ==> S(m,E)` whenever `E >= C c_star^{-1}` and `gamma <= E^{-10}`.

Below the top scale both clauses are already contained in `S(m-1,E)`, because
both are `forall m <= m0` clauses.

This module assembles exactly that proof at the two frozen roots.

## Main result

* `induction_step_provided`: the body of
  `Algsuperdiff.Frozen.Section3.induction_step`, with the identical binder list
  `(d : ℕ)` and the identical three premises.

## The assembly

Write `S(m0) := Algsuperdiff.Frozen.Section3.inductionState M m0 E`, a
conjunction of two `forall m <= m0` clauses.  Given `S(m-1)`, each clause at
`m' <= m` splits by integer bookkeeping into `m' <= m - 1`, discharged from
`S(m-1)`, and `m' = m`, the two new displays.

**Clause 1 (the `sigma_bar` sandwich) at `m' = m`**, split at the landmark `m*`
(`e.mstar`) exactly as the manuscript splits:

* `m <= m*`: the sibling `inductionState_diffusivity_of_le_mStar`
  (`Provider/Induction/BaseWindowDiffusivity.lean`) supplies the WHOLE
  clause `forall m' <= m` unconditionally, with no premise beyond the window
  and no dependence on `E`.  This materializes the diffusivity half.
* `m* < m`: the `Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`
  (`Frozen/Section3/DiffusivityAsymptotics.lean`, the frozen
  `p.propagate.diffusivity.lower.bound`) at `m0 := m`.  Its 2nd and 3rd
  conclusions are the sandwich AT `m0` on the nose -- the same two inequalities
  the frozen `inductionState` demands at the top scale, with the same `max`,
  the same `1/4` and `4`, and the same `3 ^ (2 * gamma * m)`.  Its 1st
  conclusion (the sharp defect `e.formula.for.shom`) is NOT consumed.  Its gate
  is `Cflow * c_star^{-1} <= E`, obtained from the root's own gate through
  `Cflow <= C`.

**Clause 2 (the error display) at `m' = m`**: the
`Algsuperdiff.Frozen.Section3.multiscale_estimate`
(`Frozen/Section3/MultiscaleEstimate.lean`) at the fixed `eps:= ((2
max{Cms,1})^2)^{-1}`, through the proved `epsilon`-fixing arithmetic of
`Provider/Induction/StateCalculus.lean` §5 (`epsilonFix_mem_Ioc`:478,
`multiscaleAmplitude_le_of_epsilonFix`:499,
`multiscaleRareAmplitude_le_of_epsilonFix`:516).  The root delivers the
witness-level display at amplitudes `Cms E s^{-1} sqrt(eps gamma)` and `Cms eps
(s^{-1})^2 exp(-(E^{-1})^3 gamma^{-1})`; the fixing sends the first to `<= E
s^{-1} sqrt gamma` (because `Cms sqrt eps <= 1/2`) and the second to `<=
(s^{-1})^2 exp(.)` (because `Cms eps <= (4 max{Cms,1})^{-1} <= 1`), which are
the frozen state's two amplitudes verbatim.  The state's clause is the
`Probability.IsTwoTermBigOWith`, so the root's named witnesses `Y`, `Z` are
re-packaged and enlarged by `Provider.Orlicz.isTwoTermBigOWith_mono_scales`
(`Provider/Orlicz/TwoTermCalculus.lean`).  The root's refinement clause (the `s
<= Cms eps` guard on `Y`) is NOT consumed.

Every `Cms`-occurrence of the frozen conclusion is weakened by the larger
constant except the guard of the unconsumed refinement clause, which this
module never touches.

**The `epsilon`-fixing differs from the print.**  The manuscript fixes
`eps := (2 C_{e.complete.wrapping})^{-1}`, linear in `eps`, because the printed
multiscale amplitude carries the factor `C eps`.  The frozen root's `Gamma_2`
amplitude carries `Cms sqrt(eps gamma)` instead, so the fixing must be
quadratic, `eps := (2 Cms)^{-2}`, to reach the same coefficient `1/2`.  The two
renderings agree on
the printed conclusion; only the numeric choice of `eps` differs, and `eps` is
universally quantified in the frozen root, so nothing outside this proof sees
the change.

**The window gate.**  The frozen multiscale root's budget condition is
`c_star^{-1} eps^{-Cms} <= E`, an `rpow` in `eps`.  Since `eps` depends only on
`Cms`, the quantity `Cgate := eps^{-Cms}` is a constant of `d`; it is kept O
throughout (positivity by `Real.rpow_pos_of_pos`, and the gate transfer is a
single `mul_comm` plus `Cgate <= C`).  No linear-arithmetic tactic is applied
to any goal containing it.

## Constant discipline

`Cflow` is the witness of the `diffusivity_asymptotics d` and `Cerr` is the
witness of `exists_errorDisplay_of_multiscale d`, itself obtained from
`multiscale_estimate d`; both are extracted B the exported constant is chosen,
and the exported constant

`C := max Cflow Cerr`

is chosen B the universally quantified model `M`, scale `m` and budget `E`.  `0
< C` follows from `0 < Cflow`.  No model datum enters any constant.

## References

* ABK26, (`d.mathcalS.def`), (`e.xi.delta1.condition`,
  `e.propagation.of.indyhyp`), (the proof assembled here), (the printed
  `eps`-fixing), (the printed split at `m*`).
-/

namespace Algsuperdiff.Section3.Provider.Induction

open _root_.Algsuperdiff.Section3.Provider.Orlicz

/-! ## The error clause at the top scale -/

/-- **The error display of the induction state at the top scale, with the
multiscale `epsilon` fixed.**

This is the frozen `inductionState` clause 2 AT the single scale `m`, produced
from the `Algsuperdiff.Frozen.Section3.multiscale_estimate` at `epsilon:= ((2
max{Cms,1})^2)^{-1}`.  The exported gate constant is the `rpow` `Cgate =
epsilon ^ (-Cms)`, which depends only on `d`; it is never touched by a
linear-arithmetic tactic.

Premises: the budget gate at the exported constant, the regime
`gamma <= (E^{-1})^10`, and `S(m-1,E)`.  Nothing else. -/
private theorem exists_errorDisplay_of_multiscale (d : ℕ) :
    ∃ Cerr : ℝ, 0 < Cerr ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        Cerr * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
          Probability.IsTwoTermBigOWith
            (Cutoff.cutoffSampleLaw M).toMeasure
            (HCPolySupport.IndependentSums.gammaSigma 2)
            (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
            (Observable.cutoffHomogenizationError M m
              ⟨s,
                (mul_pos (by norm_num : (0 : ℝ) < 8)
                  M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
            ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
            ((s⁻¹) ^ 2 *
              Real.exp
                (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by
  obtain ⟨Cms, hCms0, hms⟩ := Algsuperdiff.Frozen.Section3.multiscale_estimate d
  have hCms1 : (1 : ℝ) ≤ max Cms 1 := le_max_right Cms 1
  have hCmsle : Cms ≤ max Cms 1 := le_max_left Cms 1
  have heps : ((2 * max Cms 1) ^ 2)⁻¹ ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    epsilonFix_mem_Ioc hCms1
  refine ⟨((2 * max Cms 1) ^ 2)⁻¹ ^ (-Cms), Real.rpow_pos_of_pos heps.1 _, ?_⟩
  intro M m E hS hgate hgamma s hsWindow
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8)
      M.shellPrefix.gamma_pos).trans_le hsWindow.1
  have hsinv : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs0).le
  have hEgate :
      (Disorder.cstar M)⁻¹ * ((2 * max Cms 1) ^ 2)⁻¹ ^ (-Cms) ≤ (E : ℝ) :=
    (mul_comm ((Disorder.cstar M)⁻¹)
      (((2 * max Cms 1) ^ 2)⁻¹ ^ (-Cms))).trans_le hgate
  obtain ⟨Y, Z, hw, -⟩ :=
    hms M m E hS (((2 * max Cms 1) ^ 2)⁻¹) heps hEgate hgamma s hsWindow
  refine isTwoTermBigOWith_mono_scales ⟨Y, Z, hw⟩ ?_ ?_
  · calc Cms * (E : ℝ) * s⁻¹ *
          Real.sqrt (((2 * max Cms 1) ^ 2)⁻¹ * M.gamma)
      ≤ max Cms 1 * (E : ℝ) * s⁻¹ *
          Real.sqrt (((2 * max Cms 1) ^ 2)⁻¹ * M.gamma) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCmsle hE0.le) hsinv)
          (Real.sqrt_nonneg _)
    _ ≤ (E : ℝ) * s⁻¹ * Real.sqrt M.gamma :=
        multiscaleAmplitude_le_of_epsilonFix
          (lt_of_lt_of_le zero_lt_one hCms1) hE0.le hsinv
  · calc Cms * ((2 * max Cms 1) ^ 2)⁻¹ * (s⁻¹) ^ 2 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
      ≤ max Cms 1 * ((2 * max Cms 1) ^ 2)⁻¹ * (s⁻¹) ^ 2 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCmsle heps.1.le) (sq_nonneg _))
          (Real.exp_pos _).le
    _ ≤ (s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
        multiscaleRareAmplitude_le_of_epsilonFix hCms1 (sq_nonneg _)
          (Real.exp_pos _).le

/-! ## The one-scale propagation -/

/-- **`e.propagation.of.indyhyp`: `S(m-1,E)` implies `S(m,E)`.**

The exported constant is `C = max Cflow Cerr`, chosen after the two roots' own
constants and before every model datum.

This is a proved local Provider helper.  Its statement is the body of the
frozen draft `Algsuperdiff.Frozen.Section3.induction_step`; the frozen module
is deliberately NOT in this file's import closure. -/
theorem induction_step_provided
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        Algsuperdiff.Frozen.Section3.inductionState M m E := by
  obtain ⟨Cflow, hCflow0, hflow⟩ :=
    Algsuperdiff.Frozen.Section3.diffusivity_asymptotics d
  obtain ⟨Cerr, hCerr0, herr⟩ := exists_errorDisplay_of_multiscale d
  refine ⟨max Cflow Cerr, lt_of_lt_of_le hCflow0 (le_max_left Cflow Cerr), ?_⟩
  intro M m E hC hgamma hS
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.mpr hcs0).le
  have hflowGate : Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    le_trans
      (mul_le_mul_of_nonneg_right (le_max_left Cflow Cerr) hcsinv) hC
  have herrGate : Cerr * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    le_trans
      (mul_le_mul_of_nonneg_right (le_max_right Cflow Cerr) hcsinv) hC
  refine ⟨?_, ?_⟩
  · rcases le_or_gt m (mStar M) with hm | hm
    · exact inductionState_diffusivity_of_le_mStar M hm
    · obtain ⟨-, hlow, hup⟩ := hflow M m E hm hS hflowGate hgamma
      intro m' hm'
      rcases hm'.eq_or_lt with h | h
      · subst h
        exact ⟨hlow, hup⟩
      · exact hS.1 m' (by omega)
  · intro m' hm' s hsWindow
    rcases hm'.eq_or_lt with h | h
    · subst h
      exact herr M m' E hS herrGate hgamma s hsWindow
    · exact hS.2 m' (by omega) s hsWindow

end Algsuperdiff.Section3.Provider.Induction
