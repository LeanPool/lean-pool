/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsPrincipal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerFold

/-!
# SplitObligationsRegime

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Obligation (1) of `SplitScaleObligations`, at the closure's own families

ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.recurrence.params`.

## What this module supplies

Two things.

* `gamma_le_of_closureRegime` --- the standing translation of the manuscript's
  parameter block into a `cgamma`-threshold.  This is the *same* projection the
  proved `PrincipalResponseTerminal` performs; it is reproved here because it
  is `private` there.

* `exists_const_eventually_integrable_switchCubeEnergy_closureFamilies` ---
  the **first conjunct of `Closure.SplitProducerFold.SplitScaleObligations`**,
  at the closure's own corrector families, for all sufficiently large
  localization cubes, inside `Closure.ClosureRegime`.

The per-cell content is
`Closure.SplitObligationsPrincipal.integrable_switchCubeEnergy_of_integrable_switchEllipLoad_sq`,
fed by the proved
`PrincipalResponseGoodEnergy.exists_gamma0_integrable_switchEllipLoad_principalPz_sq`
transported from `M.P` to `Cutoff.cutoffSampleLaw M` along the measurable
embedding of `Cutoff.map_cutoffSampleLaw_val`, and by the proved measurability
`Closure.SplitProducerLoad.measurable_meshCellLoad`.

## Binders

Exactly `Closure.ClosureRegime` at the named threshold and the two direction
bounds `|e| <= 1`, `|e'| <= 1`.  The large-cube gate and the depth-naming
identity are produced internally as eventual statements in `K`.  Nothing else
is assumed; in particular no measurability, moment or selection property of the
corrector families occurs as a binder.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.recurrence.params`,
  `e.Pz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The `cgamma`-threshold carried by the regime -/

/-- **The manuscript's parameter block gives every `cgamma`-threshold.**

`ClosureRegime n h Ec` contains `C (cstar M)^{-1} <= Ec` and `cgamma <=
Ec^{-5}`.  Since `cstar M <= 3/2`, naming `C` above `(3/2) g^{-1}` forces
`cgamma <= g`.  Anchor-free. -/
theorem gamma_le_of_closureRegime {C g : ℝ} {M : ABKModel d} {n : ℤ} {h : ℕ}
    {Ec : {E : ℝ // 1 ≤ E}} (hg : 0 < g) (hC : (3 : ℝ) / 2 * g⁻¹ ≤ C)
    (hreg : ClosureRegime C M n h Ec) : M.gamma ≤ g := by
  obtain ⟨-, -, hCE, hgammaE, -, -⟩ := hreg
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
  have hEpos : (0 : ℝ) < (Ec : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 := Disorder.cstar_le_three_halves M
  have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
  have hcinv23 : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    linarith
  have hginv0 : (0 : ℝ) < g⁻¹ := inv_pos.2 hg
  have hstep : g⁻¹ ≤ (Ec : ℝ) := by
    have h1 : ((3 : ℝ) / 2 * g⁻¹) * (2 / 3) ≤
        ((3 : ℝ) / 2 * g⁻¹) * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_left hcinv23 (by positivity)
    have h2 : ((3 : ℝ) / 2 * g⁻¹) * (Disorder.cstar M)⁻¹ ≤ C * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_right hC hcinv0.le
    have h3 : ((3 : ℝ) / 2 * g⁻¹) * (2 / 3) = g⁻¹ := by ring
    linarith
  have hE5 : (Ec : ℝ) ≤ (Ec : ℝ) ^ (5 : ℕ) := le_self_pow₀ hE1 (by norm_num)
  have hgammaEc : M.gamma ≤ ((Ec : ℝ))⁻¹ := by
    have hEpow : (Ec : ℝ) ^ (-5 : ℤ) = ((Ec : ℝ) ^ (5 : ℕ))⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [hEpow] at hgammaE
    exact hgammaE.trans (inv_anti₀ hEpos hE5)
  have hEinv : (Ec : ℝ) ≤ M.gamma⁻¹ := (le_inv_comm₀ hEpos hgamma0).mpr hgammaEc
  have hfinal : g⁻¹ ≤ M.gamma⁻¹ := le_trans hstep hEinv
  rw [← inv_inv g, le_inv_comm₀ hgamma0 hginv0]
  exact hfinal

/-! ## The large-cube gate, as an eventual statement -/

/-- The gate `10^10 cgamma^{-1} <= K - (n+h)` of `e.recurrence.params` holds for
every large enough localization cube.  Unconditional. -/
theorem eventually_recurrenceParams_largeCube (M : ABKModel d) (n : ℤ) (h : ℕ) :
    ∀ᶠ K : ℕ in Filter.atTop,
      (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (((K : ℤ)) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    ((10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ))] with K hK
  push_cast at hK ⊢
  linarith

/-! ## Obligation (1) at the closure families -/

/-- **The first conjunct of `SplitScaleObligations`, produced inside the
manuscript's regime.**

For every mesoscopic cell of the closure mesh below a sufficiently large
localization cube, the Step-3 switch energy at `e.Pz.def`'s load is
sample-integrable under the genuine cutoff law.

exactly on `ClosureRegime` at the produced threshold and on the two direction
bounds. -/
theorem exists_const_eventually_integrable_switchCubeEnergy_closureFamilies
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Csplit : ℝ, 0 < Csplit ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d),
        Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 → ClosureRegime Csplit M n h Ec →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
            Integrable (fun omega : CutoffSample d =>
              switchCubeEnergy M (n + (h : ℤ)) R
                (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
                  (closureDirichletAlong M n h K e omega.val)
                  (closureNeumannAlong M n h K e' omega.val)) omega)
              (cutoffSampleLaw M).toMeasure := by
  classical
  obtain ⟨g, hgpos, -, hSqInt⟩ :=
    exists_gamma0_integrable_switchEllipLoad_principalPz_sq d hd
  refine ⟨(3 : ℝ) / 2 * g⁻¹, by positivity, ?_⟩
  intro M n h Ec e e' he he' hreg
  have hgamma : M.gamma ≤ g := gamma_le_of_closureRegime hgpos le_rfl hreg
  obtain ⟨hstate, hh, -, -, hhcap, -⟩ := hreg
  have hemb : MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)
  have hnh : n + (h : ℤ) - (h : ℤ) = n := by ring
  filter_upwards [eventually_recurrenceParams_largeCube M n h] with K hK
  intro R hR
  have hSq := hSqInt M hgamma (n + (h : ℤ) - 1) Ec hstate (n + (h : ℤ)) (K : ℤ) h hh
    (by omega) hhcap hK e e' he he' (closureMeshDepth M n h K) R hR
  rw [hnh] at hSq
  have hsh := hSq (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e')
  rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hsh
  exact integrable_switchCubeEnergy_of_integrable_switchEllipLoad_sq M
    (Annealed.sigmaBar M n) (n + (h : ℤ)) R
    (measurable_meshCellLoad M n h (K : ℤ) e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
      (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
      (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e') hR)
    hsh

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
