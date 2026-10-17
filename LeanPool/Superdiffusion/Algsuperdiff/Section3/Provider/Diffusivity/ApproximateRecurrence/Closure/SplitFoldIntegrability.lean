/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitFoldCellMoments

/-!
# SplitFoldIntegrability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Conjuncts (1) and (2) of `SplitScaleObligations`, with no analytic binder

ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.recurrence.params`.

`Closure.SplitObligations.splitScaleObligations_integrability_of_regime`
produces the two integrability conjuncts of
`Closure.SplitProducerFold.SplitScaleObligations` from one analytic binder
`hmom`.  `Closure.SplitFoldCellMoments` proves both moments; this module chains
them and re-runs the same assembly *inside the regime*, so that the export

```
  splitScaleObligations_integrability_closureFamilies
```

carries exactly `Closure.ClosureRegime` at the produced threshold and the two
direction bounds --- no `hmom`, no measurability, no smallness.

After this module the residual of `SplitScaleObligations` at the closure's
families is **exactly** conjunct (3),

```
  fluctuationEnergyAverage M n h K (closureMeshDepth M n h K) e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
    <= M.gamma ^ 10 ,
```

which is Step 2 of the manuscript and is *not* proved here.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.recurrence.params`,
  Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two cell-energy moments, produced -/

/-- **`hmom` of `Closure.SplitObligations.splitScaleObligations_integrability_of_regime`,
as a theorem**, at the closure's own corrector families and in the parameter
range of `e.recurrence.params`.

For every mesoscopic cell of the closure mesh below a sufficiently large
localization cube: the *second* sample moment of the Step-2 background's
normalized potential cell energy, and the *first* sample moment of its flux cell
energy. -/
theorem exists_gamma0_closureCellMoments (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec →
          0 < h → (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 → Book.Ch02.vecNorm e' ≤ 1 →
            ∀ K : ℕ,
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
                (((K : ℤ)) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
              n + (h : ℤ) ≤ (K : ℤ) →
              ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
                Integrable
                    (fun omega : CutoffSample d =>
                      meshCellBackgroundPotentialEnergy M n h (K : ℤ) e e'
                          (closureDirichletAlong M n h K e)
                          (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
                    (cutoffSampleLaw M).toMeasure ∧
                  Integrable
                    (fun omega : CutoffSample d =>
                      meshCellBackgroundFluxEnergy M n h (K : ℤ) e e'
                        (closureDirichletAlong M n h K e)
                        (closureNeumannAlong M n h K e') R omega)
                    (cutoffSampleLaw M).toMeasure := by
  classical
  obtain ⟨g1, hg1pos, hg1q, hprodD⟩ :=
    exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four d hd
  obtain ⟨g2, hg2pos, hg2q, hprodN⟩ :=
    exists_gamma0_integrable_freshShellNeumann_meshEnergyCell_rpow_four d hd
  obtain ⟨Ckm, -, hkm⟩ := exists_integral_streamIncrementLpNorm_eight_pow_four_le d
  refine ⟨min g1 g2, lt_min hg1pos hg2pos, le_trans (min_le_left _ _) hg1q, ?_⟩
  intro M hMg n h Ec hstate hpos hhcap e e' he he' K hK10 hKn R hR
  have hnh : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hwin : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R :=
    openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have hwinsub : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale ⊆
      openCubeSet (originCube d (K : ℤ)) := by rw [hwin]; exact hsub
  have hm0 : n + (h : ℤ) - (h : ℤ) ≤ n + (h : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hpos
    omega
  -- the Dirichlet cell energy
  have hD := hprodD M (le_trans hMg (min_le_left _ _)) (n + (h : ℤ) - 1) Ec hstate
    (n + (h : ℤ)) (K : ℤ) h hpos hm0 hhcap hK10 e e' he he'
  rw [hnh] at hD
  have hcellD := hD (closureDirichletAlong M n h K e)
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
    (fun omega => memLp_vecNorm_eight_of_memLp_eight _
      (memLp_eight_grad_closureDirichletAlong hd M n h K e omega))
    (fun omega k => integrableOn_openCubeSet_coord_sq_of_memLp_eight _
      (memLp_eight_grad_closureDirichletAlong hd M n h K e omega) k)
    (fun omega => integrableOn_openCubeSet_vecNormSq_of_memLp_eight _
      (memLp_eight_grad_closureDirichletAlong hd M n h K e omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _
      (memLp_eight_grad_closureDirichletAlong hd M n h K e omega))
    R.scale R hwinsub
  -- the Neumann cell energy
  have hN := hprodN M (le_trans hMg (min_le_right _ _)) (n + (h : ℤ) - 1) Ec hstate
    (n + (h : ℤ)) (K : ℤ) h hpos hm0 hhcap hK10 e e' he he'
  rw [hnh] at hN
  have hcellN := hN (closureNeumannAlong M n h K e')
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e')
    (fun omega => memLp_vecNorm_eight_of_memLp_eight _
      (memLp_eight_grad_closureNeumannAlong hd M n h K e' omega))
    (fun omega k => integrableOn_openCubeSet_coord_sq_of_memLp_eight _
      (memLp_eight_grad_closureNeumannAlong hd M n h K e' omega) k)
    (fun omega => integrableOn_openCubeSet_vecNormSq_of_memLp_eight _
      (memLp_eight_grad_closureNeumannAlong hd M n h K e' omega))
    (fun omega => integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _
      (memLp_eight_grad_closureNeumannAlong hd M n h K e' omega))
    R.scale R hwinsub
  -- the fresh-shell `L^8` norm's second moment
  have hlt : n < n + (h : ℤ) := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hpos
    omega
  obtain ⟨hstream4, -⟩ := hkm M (K : ℤ) n (n + (h : ℤ)) hlt hKn
  have hstream2 : Integrable (fun omega : CutoffSample d =>
      Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ)) omega.val ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
    refine integrable_of_sq_integrable (fun omega => by positivity) ?_ ?_
    · exact (((measurable_streamIncrementLpNorm_eight (d := d) (K : ℤ) n
        (n + (h : ℤ))).comp measurable_subtype_coe).pow_const 2).aestronglyMeasurable
    · have hrw : (fun omega : CutoffSample d =>
          (Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ))
            omega.val ^ (2 : ℕ)) ^ (2 : ℕ)) =
          fun omega : CutoffSample d =>
            Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ))
              omega.val ^ (4 : ℕ) := by
        funext omega
        rw [← pow_mul]
      rw [hrw]
      exact hstream4
  exact ⟨integrable_meshCellBackgroundPotentialEnergy_sq_of_meshEnergyCell hd M n h K e e'
      hR hcellD,
    integrable_meshCellBackgroundFluxEnergy_of_legs hd M n h K e e' he' hR hcellN
      hstream2⟩

/-! ## Conjuncts (1) and (2), at the closure families, inside the regime -/

/-- **Obligations (1) and (2) of `Closure.SplitProducerFold.SplitScaleObligations`,
produced with no analytic binder.**

exactly on `Closure.ClosureRegime` at the produced threshold and the two
direction bounds `|e| <= 1`, `|e'| <= 1`.  This is
`Closure.SplitObligations.splitScaleObligations_integrability_of_regime` with
its binder `hmom` discharged by `exists_gamma0_closureCellMoments`. -/
theorem splitScaleObligations_integrability_closureFamilies (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ Csplit : ℝ, 0 < Csplit ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d),
        Book.Ch02.vecNorm e ≤ 1 → Book.Ch02.vecNorm e' ≤ 1 →
        ClosureRegime Csplit M n h Ec →
        ∀ᶠ K : ℕ in Filter.atTop,
          (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
              Integrable (fun omega : CutoffSample d =>
                switchCubeEnergy M (n + (h : ℤ)) R
                  (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
                    (closureDirichletAlong M n h K e omega.val)
                    (closureNeumannAlong M n h K e' omega.val)) omega)
                (cutoffSampleLaw M).toMeasure) ∧
            (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
              Integrable (fun omega : CutoffSample d =>
                Ch02.doubledMuValue (Ch02.cubeDomain R)
                    (meshCellCoeff M (n + (h : ℤ)) R omega)
                    (meshCellBackground M n h (K : ℤ) e e'
                      (closureDirichletAlong M n h K e)
                      (closureNeumannAlong M n h K e') R omega))
                (cutoffSampleLaw M).toMeasure) := by
  classical
  obtain ⟨Cs, hCs, hprin⟩ :=
    exists_const_eventually_integrable_switchCubeEnergy_closureFamilies d hd
  obtain ⟨g0, hg0pos, -, hmom⟩ := exists_gamma0_closureCellMoments d hd
  refine ⟨max Cs ((3 : ℝ) / 2 * g0⁻¹), lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro M n h Ec e e' he he' hreg
  have hregCs : ClosureRegime Cs M n h Ec := closureRegime_mono (le_max_left _ _) hreg
  have hgamma : M.gamma ≤ g0 :=
    gamma_le_of_closureRegime hg0pos (le_max_right _ _) hreg
  obtain ⟨hstate, hpos, -, -, hhcap, -⟩ := hreg
  have hKge : ∀ᶠ K : ℕ in Filter.atTop, n + (h : ℤ) ≤ (K : ℤ) := by
    filter_upwards [Filter.eventually_ge_atTop (n + (h : ℤ)).toNat] with K hK
    have hself := Int.self_le_toNat (n + (h : ℤ))
    have hKcast : ((n + (h : ℤ)).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
    omega
  filter_upwards [hprin M n h Ec e e' he he' hregCs,
    eventually_recurrenceParams_largeCube M n h, hKge] with K hK hK10 hKn
  refine ⟨hK, ?_⟩
  intro R hR
  let : MeasurableSpace (HilbertBlockL2 (openCubeSet (originCube d (K : ℤ)))) := borel _
  have : BorelSpace (HilbertBlockL2 (openCubeSet (originCube d (K : ℤ)))) := ⟨rfl⟩
  let : MeasurableSpace (HilbertBlockL2
      ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))) := borel _
  have : BorelSpace (HilbertBlockL2
      ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))) := ⟨rfl⟩
  obtain ⟨hpotSq, hfluxOne⟩ :=
    hmom M hgamma n h Ec hstate hpos hhcap e e' he he' K hK10 hKn R hR
  exact integrable_doubledMuValue_meshCellBackground_of_cellMoments M n h (K : ℤ) e e'
    (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e') hR hpotSq hfluxOne

/-! ## What is left of `SplitScaleObligations` -/

/-- **`SplitScaleObligations` from the two produced integrabilities and the
`cgamma^10` estimate.**

A repackaging with no content: after
`splitScaleObligations_integrability_closureFamilies` the residual of the three
obligations is exactly conjunct (3), Step 2 itself.  Anchor-free. -/
theorem splitScaleObligations_of_fluctuation [NeZero d] (M : ABKModel d) (n : ℤ)
    (h : ℕ) (K : ℕ) (e e' : Vec d)
    (hprin : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
      Integrable (fun omega : CutoffSample d =>
        switchCubeEnergy M (n + (h : ℤ)) R
          (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
            (closureDirichletAlong M n h K e omega.val)
            (closureNeumannAlong M n h K e' omega.val)) omega)
        (cutoffSampleLaw M).toMeasure)
    (hbg : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
      Integrable (fun omega : CutoffSample d =>
        Ch02.doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h (K : ℤ) e e' (closureDirichletAlong M n h K e)
            (closureNeumannAlong M n h K e') R omega))
        (cutoffSampleLaw M).toMeasure)
    (hfluct : fluctuationEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') ≤
      M.gamma ^ (10 : ℕ)) :
    SplitScaleObligations M n h K e e' :=
  ⟨hprin, hbg, hfluct⟩

/-! ## `ClosureSplitInput`, one estimate away -/

theorem vecNorm_zero_le_one_fold : Book.Ch02.vecNorm (0 : Vec d) ≤ 1 := by
  have h : Book.Ch02.vecNorm (0 : Vec d) = 0 := by
    rw [vecNorm_eq_sqrt_vecNormSq]
    have hz : vecNormSq (0 : Vec d) = 0 := by
      change (∑ i, (0 : Vec d) i * (0 : Vec d) i) = 0
      simp
    rw [hz, Real.sqrt_zero]
  rw [h]
  norm_num

/-- **`Closure.ClosureFinal.ClosureSplitInput` from the `cgamma^10` estimate
alone.**

Every other ingredient of the finite-grid half of Steps 1--3 at the closure's
own corrector families is discharged: the two integrability conjuncts by
`splitScaleObligations_integrability_closureFamilies`, and the whole Step-1--3
assembly by `Closure.SplitProducerFold.closureSplitInput_of_obligations`.  What
is left is verbatim Step 2 of the manuscript, at both direction pairs.

exactly on `hfluct`; the threshold is the maximum of the produced one and the
caller's `Cfl`. -/
theorem closureSplitInput_of_gammaTenBound (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {Cfl : ℝ}
    (hfluct : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d),
      Book.Ch02.vecNorm e ≤ 1 → Book.Ch02.vecNorm e' ≤ 1 →
      ClosureRegime Cfl M n h Ec →
      ∀ᶠ K : ℕ in Filter.atTop,
        fluctuationEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') ≤
          M.gamma ^ (10 : ℕ)) :
    ClosureSplitInput d := by
  classical
  obtain ⟨Cs, hCs, hint⟩ := splitScaleObligations_integrability_closureFamilies d hd
  refine closureSplitInput_of_obligations d
    (Csplit := max Cs Cfl) (lt_of_lt_of_le hCs (le_max_left _ _)) ?_
  intro M n h Ec e he hreg
  have hregCs : ClosureRegime Cs M n h Ec := closureRegime_mono (le_max_left _ _) hreg
  have hregCfl : ClosureRegime Cfl M n h Ec := closureRegime_mono (le_max_right _ _) hreg
  have hnorm : Book.Ch02.vecNorm e ≤ 1 :=
    le_of_eq (vecNorm_eq_one_of_vecNormSq_eq_one he)
  have hzero : Book.Ch02.vecNorm (0 : Vec d) ≤ 1 := vecNorm_zero_le_one_fold
  constructor
  · filter_upwards [hint M n h Ec 0 e hzero hnorm hregCs,
      hfluct M n h Ec 0 e hzero hnorm hregCfl] with K hK hKf
    exact splitScaleObligations_of_fluctuation M n h K 0 e hK.1 hK.2 hKf
  · filter_upwards [hint M n h Ec e 0 hnorm hzero hregCs,
      hfluct M n h Ec e 0 hnorm hzero hregCfl] with K hK hKf
    exact splitScaleObligations_of_fluctuation M n h K e 0 hK.1 hK.2 hKf

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
