/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootInterfaceGate

/-!
# StepSevenCaccBoundaryLattice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-7c display off the printed interior gate, at the lattice frame

## What is produced, and why the frame matters

`StepSevenCaccFinalInterior` produces `hcacc` and
`StepSevenCaccFinalDisplay` produces `e.gradient.with.shom` under the printed
indicator's own gate `z ∈ □_{m-1}` together with `n' ≤ m-1`.  Those two
hypotheses are used in exactly ONE way in the whole interior chain: through
`EdFinalInputs.image_add_subset_openCubeSet_of_mem_inner`, i.e. only to know

```text
  (GATE)      z + □_{n'} ⊆ □_m .
```

This module re-proves the same two theorems with `(GATE)` itself as the
hypothesis.  Nothing else changes: the frame stays at the printed lattice centre
`z`, so the coefficient family stays `𝐚_{L,mf}[Q_f](z + ·)` and the `hlambda`
slot is discharged by the same clause-(B) record on `□_{n'+1}` that the interior
branch uses, with no off-grid transport and no re-gate.  `hosc` is likewise
unmoved: the oscillation window is `U_{n'}`, not `U_{n'+1}`.

`(GATE)` is strictly weaker than the printed pair: for `n' ≤ m-1` and `z ∈
□_{m-1}` one has `|z_i| + ½·3^{n'} < ½·3^{m-1} + ½·3^{m-1} = 3^{m-1} ≤ ½·3^m`,
so the interior branch is the special case.  The centres it adds are genuine
boundary centres (`z ∉ □_{m-1}`) whenever `½·3^{n'} ≤ |z_i| ≤ ½·3^m − ½·3^{n'}`
for some coordinate — an ℓ^∞-shell of width `½·3^m − ½·3^{n'} − ½·3^{m-1}`.

## What is not produced

The centres with `z + □_{n'} ⊄ □_m` are not covered.  Reaching them requires
moving the Caccioppoli's outer cube off the printed lattice centre (the clamp
of `StepSevenCaccBoundary`), and then the coefficient family is read at an
off-lattice translate, where the proved clause-(B) producer
(`StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps`, whose null set is indexed
by the countable family of triadic lattice points) supplies no record.

## References

* ABK26, `e.gradient.with.shom`; Step 7a; `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The gate and its two immediate consequences -/

theorem image_add_subset_openCubeSet_of_gate_le {m j j' : ℤ} {z : Vec d}
    (hjj : j' ≤ j)
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    (fun y => z + y) '' openCubeSet (originCube d j') ⊆
      openCubeSet (originCube d m) :=
  (Set.image_mono (openCubeSet_originCube_subset_of_le hjj)).trans hgate

theorem mem_openCubeSet_of_gate {m j : ℤ} {z : Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    z ∈ openCubeSet (originCube d m) :=
  hgate ⟨0, zero_mem_openCubeSet_originCube d j, add_zero z⟩

theorem truncatedWindow_eq_translateSet_of_gate {m j : ℤ} {z : Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    truncatedWindow z m j = translateSet z (openCubeSet (originCube d j)) := by
  rw [truncatedWindow_eq_image_add_iff.mpr hgate, image_add_eq_translateSet]

/-! ## 2. The three identifications, at the gate -/

/-- **The `gradCore` identification at the gate.**

`StepSevenCaccFinalInterior.sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm`
with the printed pair replaced by the gate at scale `j - 2`. -/
theorem sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm_gate (M : ABKModel d)
    (L mf m j : ℤ) (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    (v : H1Function (Ch02.cubeDomain (originCube d j) : Set (Vec d)))
    (G : Vec d → Vec d) (hg : ∀ y, v.grad y = G (y + z))
    (hgate : (fun y => z + y) '' openCubeSet (originCube d (j - 2)) ⊆
      openCubeSet (originCube d m)) :
    Real.sqrt (localizedCoeffEnergyValue (caccioppoliCoreSet (originCube d j) 0)
        ((Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)).coeffOn (originCube d j)) v) =
      stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (j - 2)) G := by
  rw [stepSevenNuGradNorm]
  congr 1
  rw [localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq,
    caccioppoliCoreSet_originCube_zero]
  have hfun : (fun x => vecNormSq (v.grad x)) = fun x => vecNormSq (G (x + z)) := by
    funext x
    rw [hg x]
  have h1 := normalizedSetAverage_vecNormSq_translateSet z
    (openCubeSet (originCube d (j - 2))) G
  rw [truncatedWindow_eq_translateSet_of_gate hgate, hfun]
  exact congrArg (fun t : ℝ => (M.nu : ℝ) * t) h1.symm

/-- **The `oscLo` match at the gate.**

`StepSevenCaccFinalInterior.normalizedL2On_openCubeSet_sub_eq_truncatedWindow`
with the printed pair replaced by the gate. -/
theorem normalizedL2On_openCubeSet_sub_eq_truncatedWindow_gate {m j : ℤ} {z : Vec d}
    (w : Vec d → ℝ) (v : Vec d → ℝ) (hv : ∀ y, v y = w (y + z)) (c : ℝ)
    (hgate : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    normalizedL2On (openCubeSet (originCube d j)) (fun y => v y - c) =
      normalizedL2On (truncatedWindow z m j) (fun x => w x - c) := by
  have hfun : (fun y => v y - c) = fun x => w (x + z) - c := by
    funext y
    rw [hv y]
  have h1 := normalizedL2SqOnSet_translateSet z (openCubeSet (originCube d j))
    (fun x => w x - c)
  rw [truncatedWindow_eq_translateSet_of_gate hgate, hfun]
  exact congrArg Real.sqrt h1.symm

theorem forceBesovRegularity_stepSevenCacc_gate [NeZero d] {m n' : ℤ} {z : Vec d}
    {g : Vec d → Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m))
    (hgL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    ForceBesovRegularity (originCube d n') stepOneS (fun x => -g (x + z)) := by
  have hL2 := memLp_two_child_of_clause_iv hgate hgL2
  have hW := memLp_normalizedGagliardoMeasureOn_subset hgate
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero z (originCube d n')) hgW
  exact forceBesovRegularity_translated_neg (originCube d n') stepOneS_pos
    (by rw [stepOneS]; norm_num) hL2 hW

/-- **The Caccioppoli's solution object at the gate**, built from `t.regularity`'s
own Dirichlet datum and still framed at the printed lattice centre `z`. -/
theorem exists_stepSevenCaccGateSolution {m n' mf : ℤ} (M : ABKModel d) (L : ℤ)
    (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    {uglob hdat : H1Function (openCubeSet (originCube d m))} {gsrc : Vec d → Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m))
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) uglob hdat
      gsrc) :
    ∃ v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)),
      (∀ y, v.toFun y = uglob.toFun (y + z)) ∧
      (∀ y, v.grad y = uglob.grad (y + z)) ∧
      IsForcedEquation (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) v (fun x => -gsrc (x + z)) := by
  have hsub : translateSet z (openCubeSet (originCube d n')) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact hgate
  refine ⟨H1Function.untranslate z
      (uglob.restrict (isOpen_translateSet_openCubeSet z n') hsub), ?_, ?_, ?_⟩
  · intro y
    exact untranslate_restrict_toFun uglob hsub y
  · intro _
    rfl
  · exact isForcedEquation_fluxCorrected_freeFlux M L Qf z omega hsub hsol.2

/-! ## 3. The `hcacc` slot at the gate -/

/-- ** gap 2 (`hcacc`) at the gate `z + □_{n'} ⊆ □_m`.**

`StepSevenCaccFinalInterior.exists_stepSevenCaccHcacc_interior` V — same
constant, same windows, same frame, same coefficient family — with the printed
pair `z ∈ □_{m-1}`, `n' ≤ m-1` replaced by the single weaker gate. -/
theorem exists_stepSevenCaccHcacc_gate (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} (c : ℝ),
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        (fun y => z + y) '' openCubeSet (originCube d n') ⊆
          openCubeSet (originCube d m) →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n' - 2)) u.grad ≤
            Real.sqrt (caccioppoliWithRHSPrefactor C (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L mf Qf
                  (Cutoff.translateCutoffSample z omega))
                stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt (Ch02.lambdaS (originCube d n')
                    stepSevenCaccT
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega))) *
                  ((3 : ℝ) ^ (-n') *
                    normalizedL2On (truncatedWindow z m n') (fun x => u.toFun x - c))) +
              Real.sqrt (caccioppoliWithRHSPrefactor C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega))
                  stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt (stepSevenCaccForcingFactor *
                    (Ch02.lambdaS (originCube d n') stepSevenCaccT
                      (Support.fluxCorrectedCoeffFamily M L mf Qf
                        (Cutoff.translateCutoffSample z omega)))⁻¹) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n')
                    stepOneS g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCaccioppoliEnergyNorm d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n' Qf z omega u v g c hval hgrad hgate heq hforce
  have hbase := hC (x := (0 : Vec d)) v c heq (openCubeAtScale_zero_pred_subset n') hforce
  have hcore := sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm_gate M L mf m n' Qf
    omega v u.grad hgrad (image_add_subset_openCubeSet_of_gate_le (by omega) hgate)
  have hosc := normalizedL2On_openCubeSet_sub_eq_truncatedWindow_gate (m := m) (j := n')
    u.toFun v.toFun hval c hgate
  have hsc : (originCube d n').scale = n' := rfl
  rw [hcore, hsc, hosc] at hbase
  exact hbase

/-! ## 4. `e.gradient.with.shom` at the gate -/

/-- **`e.gradient.with.shom` at the gate, with `hvol` and `hcacc` discharged.**

`StepSevenCaccFinalDisplay.exists_stepSevenGradientWithShom_interior` at the
weaker geometric hypothesis.  Every carrier, every constant and every remaining
slot is unchanged — in particular `hlambda` is still asked at the family
`𝐚_{L,mf}[Q_f](z + ·)` framed at the printed lattice centre, and `hosc` is still
asked on `U_{n'}`. -/
theorem exists_stepSevenGradientWithShom_gate (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} {C1 alpha delta : ℝ} {B : ℕ}
        {Cosc Clam oscHi dataOsc shomNp : ℝ},
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        (fun y => z + y) '' openCubeSet (originCube d n') ⊆
          openCubeSet (originCube d m) →
        n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ Clam → 0 ≤ oscHi → 0 ≤ dataOsc →
        Ch02.lambdaS (originCube d n') stepSevenCaccT
            (Support.fluxCorrectedCoeffFamily M L mf Qf
              (Cutoff.translateCutoffSample z omega)) ≤ Clam * shomNp →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => u.toFun x -
                volumeAverage (truncatedWindow z m n') u.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * dataOsc) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt Clam + 1)) * Real.sqrt shomNp *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscHi +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt Clam + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt shomNp * dataOsc +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCaccHcacc_gate d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n n' Qf z omega u v g C1 alpha delta B Cosc Clam oscHi dataOsc shomNp
    hval hgrad hgate hcore heq hforce hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    hCosc hClam hoscHi hdataOsc hlambda hosc
  have hzm : z ∈ openCubeSet (originCube d m) := mem_openCubeSet_of_gate hgate
  have hvol := stepSevenNuGradNorm_le_volumeRatio d (nu := (M.nu : ℝ)) (n' := n')
    (le_of_lt M.nu_pos) hzm hnm hcore u
  have hcacc := hC M L mf m n' Qf omega u v
    (volumeAverage (truncatedWindow z m n') u.toFun) hval hgrad hgate heq hforce
  exact stepSevenGradientWithShom (d := d) (C1 := C1) (alpha := alpha)
    (delta := delta) (B := B) (n := n) (m := m) (n' := n')
    (Ccacc := stepSevenCaccConst C (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)))
    (Cosc := Cosc) (Clam := Clam)
    (gradLoc := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad)
    (gradCore := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n' - 2)) u.grad)
    (oscLo := (3 : ℝ) ^ (-n') *
      normalizedL2On (truncatedWindow z m n')
        (fun x => u.toFun x - volumeAverage (truncatedWindow z m n') u.toFun))
    (oscHi := oscHi) (dataOsc := dataOsc)
    (dataM := stepSevenCaccDataM (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)) g)
    (lamLo := Ch02.lambdaS (originCube d n') stepSevenCaccT
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)))
    (shomNp := shomNp)
    hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    (stepSevenCaccConst_nonneg _ _ _) hCosc hClam
    (stepSevenNuGradNorm_nonneg _ _ _)
    (mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (normalizedL2On_nonneg _ _))
    hoscHi hdataOsc (stepSevenCaccDataM_nonneg _ _ hforce) hvol hcacc hlambda hosc

/-- **`e.gradient.with.shom` at the gate, with `hlambda` wired in.**

The derived-slot table's row 2 at the parent cube `□_{n'+1}`, at the same frame
the interior branch uses, so the record is the same conclusion of
`StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps` at the printed lattice
centre.  The only surviving analytic input is `hosc`. -/
theorem exists_stepSevenGradientWithShom_gate_of_caps (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} {C1 alpha delta : ℝ} {B : ℕ}
        {Cosc CB sigma oscHi dataOsc : ℝ},
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        (fun y => z + y) '' openCubeSet (originCube d n') ⊆
          openCubeSet (originCube d m) →
        n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CB → 0 ≤ oscHi → 0 ≤ dataOsc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigma CB →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => u.toFun x -
                volumeAverage (truncatedWindow z m n') u.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * dataOsc) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt (256 / 63 * CB) + 1)) * Real.sqrt sigma *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscHi +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt (256 / 63 * CB) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt sigma * dataOsc +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenGradientWithShom_gate d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n n' Qf z omega u v g C1 alpha delta B Cosc CB sigma oscHi dataOsc
    hval hgrad hgate hcore heq hforce hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    hCosc hCB hoscHi hdataOsc hcaps hosc
  have hrow2 := stepSevenLambdaS_lower_le_of_caps (k := n' + 1) _ hcaps
  rw [show n' + 1 - 1 = n' by ring] at hrow2
  have hClam : (0 : ℝ) ≤ 256 / 63 * CB := by linarith only [hCB]
  exact hC M L mf m n n' Qf omega u v hval hgrad hgate hcore heq hforce hC1 halpha0
    halpha1 hnm hdelta hgap hbudget hCosc hClam hoscHi hdataOsc hrow2 hosc

end

end Algsuperdiff.Section4.Provider.Regularity
