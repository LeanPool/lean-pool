/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureInteriorSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenDepthFluxOscillation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenDepthOscillation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorCellInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorGaugedEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsRegime

/-!
# GammaTenInteriorHosc

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `ClosureInteriorBesovEnvelopeInput`, produced

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.Fz.def`,
`e.recurrence.params`.

## What this module does

`Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput` is the
conditional A obligation the interior route of `Closure.ClosureInteriorSplit`
carries and does not prove.  This module discharges it, by the composition the
`ClosureInteriorSplit` header names:

* the **depth-indexed interior endpoints**
from `Closure.GammaTenDepthOscillation` for the Dirichlet and Neumann correctors
  supply the two per-depth grid roots, the Neumann one through the flux transport
`gridFourthMomentRoot_meshOscillationCell_neumannFluxField_cutoffSample_le`
  (cost: the explicit dimensional factor `2 d`);
* the **envelope device**
  `Closure.GammaTenStripEnvelopeTwoLeg.exists_besovEnvelope_two_legs_interiorMesoCubeGrid`,
  read through the gauge substitution of
  `Closure.GammaTenInteriorGaugedEnvelope`, turns them into one envelope for the
  two gauged legs of `bfF_z`;
* the **cellwise typing data** comes from `Closure.GammaTenInteriorCellInputs` and
  the octic layer
from `LocalizationFluctuationNumericOctic` for both corrector fields;
* the **scale bookkeeping** is the closure's own, exactly as
  `Closure.ClosureInteriorSplit.gammaTenBound_of_interiorEnvelope` computes it, and
  the boundary gate is
  `Closure.GammaTenInteriorGeometry.exists_gamma_threshold_mesh_boundary_half` at
  `p = closureMeshDepth`, `g = closureStripGap`.

Every threshold on `cgamma` is produced before the model and collected into the
single constant the obligation quantifies, through
`Closure.SplitObligationsRegime.gamma_le_of_closureRegime`; the only genuinely new
numerical threshold is the two-leg envelope's
`200 (4 . 2d . 4 . 3^9)^4 cgamma^4 <= 1`, which is dimension-only.

## What is proved

* `le_of_add_le_of_nonneg_right`,
  `integrable_pow_four_cutoffSample_of_memLp_two_rpow`,
  `integrable_rpow_four_cutoffSample_of_memLp_two_rpow` --- three small bridges.
* `exists_gamma0_octicCell_closureDirichlet`, `..._closureNeumann` --- the octic
  layer, read at the closure's own families.
* `exists_gamma0_depthRoot_closureDirichlet`, `..._closureNeumann` --- the two
  depth endpoints, read at the closure's own families and mesh scale.
* `exists_besovEnvelope_closureInterior_of_inputs` --- the body of the obligation
  at one localization cube and an **abstract** mesh scale, from those four inputs.
* `closureInteriorBesovEnvelopeInput_proved` --- the obligation itself.

## Binders

Of the terminal statement: the standing `2 <= d` alone.  Everything else --- the
five `cgamma` thresholds, the large-cube gate, the depth-naming identity and the
strip-gap bookkeeping --- is produced inside the manuscript's own parameter block
`ClosureRegime`.

## Scope

Internal Provider infrastructure.  There is no `sorry`, no `admit`, no custom
axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.Fz.def`,
  `e.recurrence.params`, `e.shom.h.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Three small bridges -/

/-- Dropping a nonnegative summand on the smaller side. -/
theorem le_of_add_le_of_nonneg_right {A B C : ℝ} (hB : 0 ≤ B) (h : A + B ≤ C) : A ≤ C := by
  linarith

/-- The octic layer's `L^2` membership of the fourth power of a shell observable
gives that fourth power's integrability on the closure's carrier, in the natural
power spelling the envelope's `hintcell` uses. -/
theorem integrable_pow_four_cutoffSample_of_memLp_two_rpow (M : ABKModel d)
    {F : ShellSeq d → ℝ}
    (hmem : MemLp (fun omega : ShellSeq d => F omega ^ (4 : ℝ)) 2 M.P.toMeasure) :
    Integrable (fun omega : CutoffSample d => F omega.val ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  have hint : Integrable (fun omega : ShellSeq d => F omega ^ (4 : ℝ)) M.P.toMeasure :=
    hmem.integrable (by norm_num)
  have hcongr : (fun omega : ShellSeq d => F omega ^ (4 : ℝ)) =
      fun omega : ShellSeq d => F omega ^ (4 : ℕ) := by
    funext omega
    exact rpow_four_eq_pow_four _
  rw [hcongr] at hint
  exact integrable_comp_val_cutoffSampleLaw M hint

/-- The same in the `rpow` spelling the grid Minkowski step uses. -/
theorem integrable_rpow_four_cutoffSample_of_memLp_two_rpow (M : ABKModel d)
    {F : ShellSeq d → ℝ}
    (hmem : MemLp (fun omega : ShellSeq d => F omega ^ (4 : ℝ)) 2 M.P.toMeasure) :
    Integrable (fun omega : CutoffSample d => F omega.val ^ (4 : ℝ))
      (cutoffSampleLaw M).toMeasure :=
  integrable_comp_val_cutoffSampleLaw M (hmem.integrable (by norm_num))

/-! ## The octic layer at the closure's families -/

/-- **The octic cell membership at the closure's Dirichlet family.**

The proved
`exists_gamma0_memLp_two_freshShellDirichlet_meshOscillationCell_rpow_four`,
with its six spatial side conditions discharged from the single `L^8`
membership of the closure's corrector gradient.

Proved from that producer and `memLp_eight_grad_closureDirichletAlong`. -/
theorem exists_gamma0_octicCell_closureDirichlet (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec → 0 < h →
          (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          ∀ K : ℕ, (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              (((K : ℕ) : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            ∀ e : Vec d, vecNorm e ≤ 1 →
            ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
              openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
              MemLp (fun omega : ShellSeq d => meshOscillationCell nn
                (closureDirichletAlong M n h K e omega).toH1Function.grad R ^ (4 : ℝ))
                2 M.P.toMeasure := by
  obtain ⟨gamma0, hg0, -, hmain⟩ :=
    exists_gamma0_memLp_two_freshShellDirichlet_meshOscillationCell_rpow_four d hd
  refine ⟨gamma0, hg0, ?_⟩
  intro M hMg n h Ec hstate hhpos hhcap K hK10 e he nn R hsc hsub
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (closureDirichletAlong M n h K e omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    memLp_eight_grad_closureDirichletAlong hd M n h K e omega
  have hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (closureDirichletAlong M n h K e omega)
        (fun x => -streamForcing
          ((Annealed.sigmaBar M (n + (h : ℤ) - (h : ℤ)) : ℝ))⁻¹ omega
          (n + (h : ℤ) - (h : ℤ)) (n + (h : ℤ)) e x) := by
    simp only [hcancel]
    exact fun omega =>
      isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega
  exact hmain M hMg (n + (h : ℤ) - 1) Ec hstate (n + (h : ℤ)) (K : ℤ) h hhpos
    (by omega) hhcap hK10 e e he he (closureDirichletAlong M n h K e) hsol
    (fun omega => memLp_vecNorm_eight_of_memLp_eight _ (hL8 omega))
    (fun omega k => integrableOn_openCubeSet_coord_of_memLp_eight _ (hL8 omega) k)
    (fun omega k => integrableOn_openCubeSet_coord_sq_of_memLp_eight _ (hL8 omega) k)
    (fun omega => integrableOn_openCubeSet_vecNormSq_of_memLp_eight _ (hL8 omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _ (hL8 omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_pow_four_of_memLp_eight _ (hL8 omega))
    nn R hsc hsub

/-- **The octic cell membership at the closure's Neumann family.**  The Neumann
mirror of the preceding statement.

Proved as above, through `memLp_eight_grad_closureNeumannAlong`. -/
theorem exists_gamma0_octicCell_closureNeumann (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec → 0 < h →
          (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          ∀ K : ℕ, (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              (((K : ℕ) : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            ∀ e' : Vec d, vecNorm e' ≤ 1 →
            ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
              openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
              MemLp (fun omega : ShellSeq d => meshOscillationCell nn
                (closureNeumannAlong M n h K e' omega).toH1Function.grad R ^ (4 : ℝ))
                2 M.P.toMeasure := by
  obtain ⟨gamma0, hg0, -, hmain⟩ :=
    exists_gamma0_memLp_two_freshShellNeumann_meshOscillationCell_rpow_four d hd
  refine ⟨gamma0, hg0, ?_⟩
  intro M hMg n h Ec hstate hhpos hhcap K hK10 e' he' nn R hsc hsub
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (closureNeumannAlong M n h K e' omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    memLp_eight_grad_closureNeumannAlong hd M n h K e' omega
  have hsol : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (closureNeumannAlong M n h K e' omega)
        (fun x => -streamForcing
          ((Annealed.sigmaBar M (n + (h : ℤ) - (h : ℤ)) : ℝ))⁻¹ omega
          (n + (h : ℤ) - (h : ℤ)) (n + (h : ℤ)) e' x) := by
    simp only [hcancel]
    exact fun omega =>
      isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega
  exact hmain M hMg (n + (h : ℤ) - 1) Ec hstate (n + (h : ℤ)) (K : ℤ) h hhpos
    (by omega) hhcap hK10 e' e' he' he' (closureNeumannAlong M n h K e') hsol
    (fun omega => memLp_vecNorm_eight_of_memLp_eight _ (hL8 omega))
    (fun omega k => integrableOn_openCubeSet_coord_of_memLp_eight _ (hL8 omega) k)
    (fun omega k => integrableOn_openCubeSet_coord_sq_of_memLp_eight _ (hL8 omega) k)
    (fun omega => integrableOn_openCubeSet_vecNormSq_of_memLp_eight _ (hL8 omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _ (hL8 omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_pow_four_of_memLp_eight _ (hL8 omega))
    nn R hsc hsub

/-! ## The two depth endpoints at the closure's families -/

/-- **The Dirichlet depth root at the closure's family**, with the additive
forcing gauge of the endpoint dropped.

Proved from
`exists_gamma0_freshShellDirichlet_meshOscillationDepth_le_gamma_pow_sixteen`.
-/
theorem exists_gamma0_depthRoot_closureDirichlet (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec → 0 < h →
          (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          ∀ K : ℕ, (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              (((K : ℕ) : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            ∀ e : Vec d, vecNorm e ≤ 1 →
            ∀ nmesh : ℤ, nmesh = recurrenceMesoScale recurrenceGapMultiplier M.gamma
                (n + (h : ℤ)) (h : ℤ) →
              ∀ i : ℕ,
                gridFourthMomentRoot M.P.toMeasure
                    (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
                    (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
                      (closureDirichletAlong M n h K e omega).toH1Function.grad R') ≤
                  M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
  obtain ⟨gamma0, hg0, -, hmain⟩ :=
    exists_gamma0_freshShellDirichlet_meshOscillationDepth_le_gamma_pow_sixteen d hd
  refine ⟨gamma0, hg0, ?_⟩
  intro M hMg n h Ec hstate hhpos hhcap K hK10 e he nmesh hnm i
  subst hnm
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (closureDirichletAlong M n h K e omega)
        (fun x => -streamForcing
          ((Annealed.sigmaBar M (n + (h : ℤ) - (h : ℤ)) : ℝ))⁻¹ omega
          (n + (h : ℤ) - (h : ℤ)) (n + (h : ℤ)) e x) := by
    simp only [hcancel]
    exact fun omega =>
      isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega
  have hep := hmain M hMg (n + (h : ℤ) - 1) Ec hstate (n + (h : ℤ)) (K : ℤ) h hhpos
    (by omega) hhcap hK10 e e he he (0 : Vec d) (closureDirichletAlong M n h K e) hsol i
  simp only [hcancel] at hep
  refine le_of_add_le_of_nonneg_right ?_ hep
  exact mul_nonneg (inv_nonneg.2 (Annealed.sigmaBar M n).2.le)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (shellDerivNormSum_nonneg _ _ _ _) _) _))

/-- **The Neumann depth endpoint at the closure's family**, in the exact shape the
flux transport's `hend` binder asks for --- gradient root plus forcing gauge, at
every base point.

Proved from
`exists_gamma0_freshShellNeumann_meshOscillationDepth_le_gamma_pow_sixteen`.
-/
theorem exists_gamma0_depthRoot_closureNeumann (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec → 0 < h →
          (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          ∀ K : ℕ, (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              (((K : ℕ) : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            ∀ e' : Vec d, vecNorm e' ≤ 1 →
            ∀ nmesh : ℤ, nmesh = recurrenceMesoScale recurrenceGapMultiplier M.gamma
                (n + (h : ℤ)) (h : ℤ) →
              ∀ (i : ℕ) (z0 : Vec d),
                gridFourthMomentRoot M.P.toMeasure
                    (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
                    (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
                      (closureNeumannAlong M n h K e' omega).toH1Function.grad R') +
                  ((Annealed.sigmaBar M n : ℝ))⁻¹ *
                    ((3 : ℝ) ^ (((nmesh - (i : ℤ)) : ℤ) : ℝ) *
                      (∫ omega : ShellSeq d,
                        shellDerivNormSum n (n + (h : ℤ)) z0 omega ^ (4 : ℝ)
                          ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                  M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
  obtain ⟨gamma0, hg0, -, hmain⟩ :=
    exists_gamma0_freshShellNeumann_meshOscillationDepth_le_gamma_pow_sixteen d hd
  refine ⟨gamma0, hg0, ?_⟩
  intro M hMg n h Ec hstate hhpos hhcap K hK10 e' he' nmesh hnm i z0
  subst hnm
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hsol : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (closureNeumannAlong M n h K e' omega)
        (fun x => -streamForcing
          ((Annealed.sigmaBar M (n + (h : ℤ) - (h : ℤ)) : ℝ))⁻¹ omega
          (n + (h : ℤ) - (h : ℤ)) (n + (h : ℤ)) e' x) := by
    simp only [hcancel]
    exact fun omega =>
      isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega
  have hep := hmain M hMg (n + (h : ℤ) - 1) Ec hstate (n + (h : ℤ)) (K : ℤ) h hhpos
    (by omega) hhcap hK10 e' e' he' he' z0 (closureNeumannAlong M n h K e') hsol i
  simp only [hcancel] at hep
  exact hep

/-! ## The eight inputs of the two-leg envelope, one theorem each -/

/-- A cell of an interior meso grid below the localization scale carries exactly
two pieces of spatial data: its scale, and its containment in `cu_K`. -/
theorem scale_and_subset_of_mem_interiorMesoCubeGrid {K nmesh outer : ℤ}
    (hnK : nmesh ≤ K) {R' : TriadicCube d}
    (hR' : R' ∈ interiorMesoCubeGrid d K nmesh outer) :
    R'.scale = nmesh ∧ openCubeSet R' ⊆ openCubeSet (originCube d K) :=
  ⟨scale_eq_of_mem_mesoCubeGrid (interiorMesoCubeGrid_subset hR'),
    openCubeSet_subset_originCube_of_mem_interiorMesoCubeGrid hnK hR'⟩

/-- `hmeascell` for the Dirichlet leg, at every depth-refined interior grid. -/
theorem measurable_oscCell_closureDirichlet_grid (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e : Vec d) {nmesh : ℤ}
    (hnK : nmesh ≤ (K : ℤ)) :
    ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Measurable fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad R' := by
  intro i R' hR'
  obtain ⟨hsc, hsub⟩ :=
    scale_and_subset_of_mem_interiorMesoCubeGrid (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR'
  exact measurable_meshOscillationCell_closureDirichlet_cutoffSample hd M n h K e R' hsc
    hsub

/-- `hmeascell` for the flux leg, at every depth-refined interior grid. -/
theorem measurable_oscCell_closureFlux_grid (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) {nmesh : ℤ}
    (hnK : nmesh ≤ (K : ℤ)) :
    ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Measurable fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) R' := by
  intro i R' hR'
  obtain ⟨hsc, hsub⟩ :=
    scale_and_subset_of_mem_interiorMesoCubeGrid (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR'
  exact measurable_meshOscillationCell_closureFlux_cutoffSample hd M n h K e' R' hsc hsub

/-- `hintcell` for a corrector gradient leg, at every depth-refined interior grid,
from the octic membership.  Stated for a general family so that both legs use it. -/
theorem integrable_oscCell_pow_four_grid_of_octic (M : ABKModel d) (n : ℤ) (K : ℕ)
    {nmesh : ℤ} (hnK : nmesh ≤ (K : ℤ)) (u : ShellSeq d → Vec d → Vec d)
    (hoct : ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
      openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (fun omega : ShellSeq d => meshOscillationCell nn (u omega) R ^ (4 : ℝ))
        2 M.P.toMeasure) :
    ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (u omega.val) R' ^ (4 : ℕ)) (cutoffSampleLaw M).toMeasure := by
  intro i R' hR'
  obtain ⟨hsc, hsub⟩ :=
    scale_and_subset_of_mem_interiorMesoCubeGrid (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR'
  exact integrable_pow_four_cutoffSample_of_memLp_two_rpow M (hoct _ R' hsc hsub)

/-- The `rpow` spelling of the same, which is what the flux transport asks for. -/
theorem integrable_oscCell_rpow_four_grid_of_octic (M : ABKModel d) (n : ℤ) (K : ℕ)
    {nmesh : ℤ} (hnK : nmesh ≤ (K : ℤ)) (u : ShellSeq d → Vec d → Vec d)
    (hoct : ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
      openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (fun omega : ShellSeq d => meshOscillationCell nn (u omega) R ^ (4 : ℝ))
        2 M.P.toMeasure) :
    ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (u omega.val) R' ^ (4 : ℝ)) (cutoffSampleLaw M).toMeasure := by
  intro i R' hR'
  obtain ⟨hsc, hsub⟩ :=
    scale_and_subset_of_mem_interiorMesoCubeGrid (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR'
  exact integrable_rpow_four_cutoffSample_of_memLp_two_rpow M (hoct _ R' hsc hsub)

/-- `hintcell` for the flux leg, at every depth-refined interior grid. -/
theorem integrable_oscCell_pow_four_closureFlux_grid (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) (hhpos : 0 < h) {nmesh : ℤ}
    (hnK : nmesh ≤ (K : ℤ)) (hnmn : nmesh ≤ n)
    (hgrad : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (closureNeumannAlong M n h K e' omega.val).toH1Function.grad R' ^ (4 : ℕ))
        (cutoffSampleLaw M).toMeasure) :
    ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) R' ^ (4 : ℕ))
        (cutoffSampleLaw M).toMeasure := by
  intro i R' hR'
  obtain ⟨hsc, hsub⟩ :=
    scale_and_subset_of_mem_interiorMesoCubeGrid (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR'
  exact integrable_meshOscillationCell_pow_four_closureFlux_cutoffSample hd M n h K e'
    hhpos (by omega : nmesh - (i : ℤ) ≤ n) R' hsc hsub (hgrad i R' hR')

/-- The Dirichlet per-depth grid root on the closure's carrier, at the common
constant `2 d`. -/
theorem depthRoot_cutoffSample_closureDirichlet (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e : Vec d) {nmesh : ℤ}
    (hdepD : ∀ i : ℕ,
      gridFourthMomentRoot M.P.toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureDirichletAlong M n h K e omega).toH1Function.grad R') ≤
        M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) :
    ∀ i : ℕ,
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureDirichletAlong M n h K e omega.val).toH1Function.grad R') ≤
        2 * (d : ℝ) * (M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) := by
  intro i
  have hA1 : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hR0 : (0 : ℝ) ≤ M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
    positivity
  have heq := gridFourthMomentRoot_val_cutoffSampleLaw M
    (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
    (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
      (closureDirichletAlong M n h K e omega).toH1Function.grad R')
  rw [heq]
  exact le_trans (hdepD i) (le_mul_of_one_le_left hR0 hA1)

/-- The flux per-depth grid root on the closure's carrier, at the constant `2 d`
the flux transport costs. -/
theorem depthRoot_cutoffSample_closureFlux (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) (he' : vecNorm e' ≤ 1)
    (hhpos : 0 < h) {nmesh : ℤ} (hnK : nmesh ≤ (K : ℤ)) (hnmn : nmesh ≤ n)
    (hoscInt : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (closureNeumannAlong M n h K e' omega.val).toH1Function.grad R' ^ (4 : ℝ))
        (cutoffSampleLaw M).toMeasure)
    (hdepN : ∀ (i : ℕ) (z0 : Vec d),
      gridFourthMomentRoot M.P.toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureNeumannAlong M n h K e' omega).toH1Function.grad R') +
        ((Annealed.sigmaBar M n : ℝ))⁻¹ *
          ((3 : ℝ) ^ (((nmesh - (i : ℤ)) : ℤ) : ℝ) *
            (∫ omega : ShellSeq d,
              shellDerivNormSum n (n + (h : ℤ)) z0 omega ^ (4 : ℝ) ∂M.P.toMeasure) ^
                ((4 : ℝ)⁻¹)) ≤
        M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) :
    ∀ i : ℕ,
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
              (closureNeumannAlong M n h K e' omega.val)) R') ≤
        2 * (d : ℝ) * (M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) := by
  intro i
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  refine gridFourthMomentRoot_meshOscillationCell_neumannFluxField_cutoffSample_le M
    (by omega : 1 ≤ d) (Annealed.sigmaBar M n) (by omega : n < n + (h : ℤ)) e' he'
    (closureNeumannAlong M n h K e') (by omega : nmesh - (i : ℤ) ≤ n) ?_ (hoscInt i)
    (hdepN i)
  intro R' hR'
  exact (scale_and_subset_of_mem_interiorMesoCubeGrid
    (by omega : nmesh - (i : ℤ) ≤ (K : ℤ)) hR').2

/-! ## The obligation's body at one localization cube -/

/-- **The body of `ClosureInteriorBesovEnvelopeInput` at one localization cube.**

Stated at an abstract mesh scale `nmesh` and abstract strip parameters `p`, `g`,
so that no arithmetic definition has to be unfolded.  The four named inputs are
exactly what the four producers above deliver.

Conditional on `hd`, `he'`, `hgamma0`, `hhpos`, the scale bookkeeping, the boundary gate
`hsmall`, the numerical threshold `hthr`, the gauge-ratio cap `hgauge`, and the
four named inputs. -/
theorem exists_besovEnvelope_closureInterior_of_inputs (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    (he' : vecNorm e' ≤ 1) (hgamma0 : 0 < M.gamma) (hhpos : 0 < h)
    {nmesh : ℤ} {p g : ℕ}
    (hKp : (K : ℤ) = nmesh + (p : ℤ)) (houter : n + 1 = nmesh + (g : ℤ)) (hgp : g ≤ p)
    (hno : nmesh ≤ n)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2)
    (hthr : 200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) *
      M.gamma ^ (4 : ℕ) ≤ 1)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n)
      (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ))
    (hoctD : ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
      openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (fun omega : ShellSeq d => meshOscillationCell nn
        (closureDirichletAlong M n h K e omega).toH1Function.grad R ^ (4 : ℝ))
        2 M.P.toMeasure)
    (hoctN : ∀ (nn : ℤ) (R : TriadicCube d), R.scale = nn →
      openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (fun omega : ShellSeq d => meshOscillationCell nn
        (closureNeumannAlong M n h K e' omega).toH1Function.grad R ^ (4 : ℝ))
        2 M.P.toMeasure)
    (hdepD : ∀ i : ℕ,
      gridFourthMomentRoot M.P.toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureDirichletAlong M n h K e omega).toH1Function.grad R') ≤
        M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))
    (hdepN : ∀ (i : ℕ) (z0 : Vec d),
      gridFourthMomentRoot M.P.toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureNeumannAlong M n h K e' omega).toH1Function.grad R') +
        ((Annealed.sigmaBar M n : ℝ))⁻¹ *
          ((3 : ℝ) ^ (((nmesh - (i : ℤ)) : ℤ) : ℝ) *
            (∫ omega : ShellSeq d,
              shellDerivNormSum n (n + (h : ℤ)) z0 omega ^ (4 : ℝ) ∂M.P.toMeasure) ^
                ((4 : ℝ)⁻¹)) ≤
        M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) :
    ∃ Bg : TriadicCube d → CutoffSample d → ℝ,
      (∀ R omega, 0 ≤ Bg R omega) ∧
      (∀ R ∈ interiorMesoCubeGrid d (K : ℤ) nmesh n,
        MemLp (Bg R) 4 (cutoffSampleLaw M).toMeasure) ∧
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) nmesh n) Bg ≤ M.gamma ^ (15 : ℕ) ∧
      (∀ R ∈ interiorMesoCubeGrid d (K : ℤ) nmesh n,
        ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
              (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
                ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
                  (closureDirichletAlong M n h K e omega.val)
                  (closureNeumannAlong M n h K e' omega.val)).eval x)).1) ≤
                Bg R omega) ∧
          (∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
              (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
                ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
                  (closureDirichletAlong M n h K e omega.val)
                  (closureNeumannAlong M n h K e' omega.val)).eval x)).2) ≤
                Bg R omega)) := by
  have hnK : nmesh ≤ (K : ℤ) := by omega
  exact exists_besovEnvelope_gaugedLocalizationFz_interiorMesoCubeGrid M n h K e e'
    hKp houter hgp hno hsmall hgamma0 hthr hgauge
    (fun omega S hS => memLp_two_gradH10_normalizedCubeMeasure_of_subset S hS
      (closureDirichletAlong M n h K e omega.val))
    (fun omega S hS => memLp_two_neumannFluxField_normalizedCubeMeasure
      (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' S hS
      (closureNeumannAlong M n h K e' omega.val))
    (measurable_oscCell_closureDirichlet_grid d hd M n h K e hnK)
    (integrable_oscCell_pow_four_grid_of_octic M n K hnK
      (fun omega => (closureDirichletAlong M n h K e omega).toH1Function.grad) hoctD)
    (measurable_oscCell_closureFlux_grid d hd M n h K e' hnK)
    (integrable_oscCell_pow_four_closureFlux_grid d hd M n h K e' hhpos hnK hno
      (integrable_oscCell_pow_four_grid_of_octic M n K hnK
        (fun omega => (closureNeumannAlong M n h K e' omega).toH1Function.grad) hoctN))
    (depthRoot_cutoffSample_closureDirichlet d hd M n h K e hdepD)
    (depthRoot_cutoffSample_closureFlux d hd M n h K e' he' hhpos hnK hno
      (integrable_oscCell_rpow_four_grid_of_octic M n K hnK
        (fun omega => (closureNeumannAlong M n h K e' omega).toH1Function.grad) hoctN)
      hdepN)

/-! ## The obligation -/

/-- **`Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput`, proved.**

Conditional on the standing `2 <= d` only, and otherwise proved from the
ingredients listed in the module docstring. -/
theorem closureInteriorBesovEnvelopeInput_proved (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ClosureInteriorBesovEnvelopeInput d := by
  classical
  obtain ⟨gOD, hgOD0, hOD⟩ := exists_gamma0_octicCell_closureDirichlet d hd
  obtain ⟨gON, hgON0, hON⟩ := exists_gamma0_octicCell_closureNeumann d hd
  obtain ⟨gDD, hgDD0, hDD⟩ := exists_gamma0_depthRoot_closureDirichlet d hd
  obtain ⟨gDN, hgDN0, hDN⟩ := exists_gamma0_depthRoot_closureNeumann d hd
  obtain ⟨gGeo, hgGeo0, -, hGeo⟩ := exists_gamma_threshold_mesh_boundary_half d
  have hCnum0 : (0 : ℝ) <
      200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) := by positivity
  have hgThr0 : (0 : ℝ) < min 1
      (200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹ :=
    lt_min one_pos (inv_pos.2 hCnum0)
  have hgmin0 : (0 : ℝ) < min (min gOD gON) (min (min gDD gDN) (min gGeo
      (min 1 (200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹))) :=
    lt_min (lt_min hgOD0 hgON0) (lt_min (lt_min hgDD0 hgDN0) (lt_min hgGeo0 hgThr0))
  refine ⟨3 / 2 * (min (min gOD gON) (min (min gDD gDN) (min gGeo
      (min 1 (200 * (4 * (2 * (d : ℝ)) *
        (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹))))⁻¹, ?_, ?_⟩
  · have hinv := inv_pos.2 hgmin0
    linarith
  intro M n h Ec e e' he he' hreg
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgmin : M.gamma ≤ min (min gOD gON) (min (min gDD gDN) (min gGeo
      (min 1 (200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹))) :=
    gamma_le_of_closureRegime hgmin0 le_rfl hreg
  have hgOD : M.gamma ≤ gOD :=
    le_trans hgmin (le_trans (min_le_left _ _) (min_le_left _ _))
  have hgON : M.gamma ≤ gON :=
    le_trans hgmin (le_trans (min_le_left _ _) (min_le_right _ _))
  have hgDD : M.gamma ≤ gDD :=
    le_trans hgmin (le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (min_le_left _ _))
  have hgDN : M.gamma ≤ gDN :=
    le_trans hgmin (le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (min_le_right _ _))
  have hgGeo : M.gamma ≤ gGeo :=
    le_trans hgmin (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_left _ _))
  have hgOne : M.gamma ≤ 1 :=
    le_trans hgmin (le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_right _ _)) (min_le_left _ _))
  have hgCnum : M.gamma ≤
      (200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹ :=
    le_trans hgmin (le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_right _ _)) (min_le_right _ _))
  have hthr : 200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) *
      M.gamma ^ (4 : ℕ) ≤ 1 := by
    have hp4 : M.gamma ^ (4 : ℕ) ≤ M.gamma :=
      pow_le_of_le_one hgamma0.le hgOne (by norm_num)
    have hstep : 200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) *
        M.gamma ^ (4 : ℕ) ≤
        200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) *
          (200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_left (le_trans hp4 hgCnum) hCnum0.le
    rwa [mul_inv_cancel₀ hCnum0.ne'] at hstep
  obtain ⟨hstate, hhpos, -, -, hhcap, -⟩ := id hreg
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hgauge : gaugeRatio (Annealed.sigmaBar M n)
      (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by
    have hb := gaugeRatio_sigmaBar_le_readingConst M hstate (m := n + (h : ℤ)) (h := h)
      hhpos (le_refl _) hhcap
    rwa [hcancel] at hb
  have hKge : ∀ᶠ K : ℕ in Filter.atTop, n + (h : ℤ) + 2 ≤ (K : ℤ) := by
    filter_upwards [Filter.eventually_ge_atTop (n + (h : ℤ) + 2).toNat] with K hK
    have hself := Int.self_le_toNat (n + (h : ℤ) + 2)
    have hKcast : ((n + (h : ℤ) + 2).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
    omega
  filter_upwards [eventually_recurrenceParams_largeCube M n h,
    eventually_closureMeshDepth_scale M n h, hKge] with K hK10 hscale hKn
  have hscale' : (K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) := hscale
  have hgapEq : (K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ) =
      n - ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℤ) := by
    rw [hscale']
    unfold recurrenceMesoScale
    ring
  have hgp : closureStripGap M ≤ closureMeshDepth M n h K := by
    unfold closureStripGap
    omega
  have houter : n + 1 = ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)) +
      ((closureStripGap M : ℕ) : ℤ) := by
    unfold closureStripGap
    omega
  have hKp : (K : ℤ) = ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)) +
      ((closureMeshDepth M n h K : ℕ) : ℤ) := by omega
  have hno : (K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ) ≤ n := by omega
  have hpg : ((closureMeshDepth M n h K : ℕ) : ℤ) - ((closureStripGap M : ℕ) : ℤ) =
      (K : ℤ) - n - 1 := by
    unfold closureStripGap
    omega
  have hsmall : (d : ℝ) * ((3 : ℝ) ^ (closureStripGap M) /
      (3 : ℝ) ^ (closureMeshDepth M n h K)) ≤ 1 / 2 := by
    refine hGeo M.gamma hgamma0 hgGeo (closureMeshDepth M n h K) (closureStripGap M) ?_
    have hcast : ((closureMeshDepth M n h K : ℕ) : ℝ) - ((closureStripGap M : ℕ) : ℝ) =
        ((K : ℕ) : ℝ) - ((n : ℤ) : ℝ) - 1 := by
      have hbase := congrArg (fun z : ℤ => (z : ℝ)) hpg
      push_cast at hbase
      linarith
    rw [hcast]
    have hK10' : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
        ((K : ℕ) : ℝ) - (((n : ℤ) : ℝ) + ((h : ℕ) : ℝ)) := by
      have hbase := hK10
      push_cast at hbase
      linarith
    have hh1R : (1 : ℝ) ≤ ((h : ℕ) : ℝ) := by exact_mod_cast hhpos
    linarith
  exact exists_besovEnvelope_closureInterior_of_inputs d hd M n h K e e' he' hgamma0
    hhpos hKp houter hgp hno hsmall hthr hgauge
    (hOD M hgOD n h Ec hstate hhpos hhcap K hK10 e he)
    (hON M hgON n h Ec hstate hhpos hhcap K hK10 e' he')
    (hDD M hgDD n h Ec hstate hhpos hhcap K hK10 e he _ hscale')
    (hDN M hgDN n h Ec hstate hhpos hhcap K hK10 e' he' _ hscale')

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
