/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCarrierBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit

/-!
# HomSpineEnergyDensity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube energy density at EVERY depth, from Theorem C

## What this file supplies

The §4.5 supplier's energy slot (`hS0`, `hS`, `hSbound`) needs the printed
per-cube energy `‖σ^{1/2}∇u‖_{L²(R)}` — this repository's `printedLocalEnergy`
at the cutoff coefficient field — bounded at EVERY depth `j ≤ m` below `□_m`.
Theorem C (`anomalous_regularity`) gives the display only on the deep range
`X_m(α) ≤ m - n`'s "Hence, for every `j ≤ m`" silently extends it.  This file
supplies both halves of that extension at the printed carriers:

* `ofReal_printedLocalEnergy_coefficientCutoff` — **the carrier identity**.  The
  printed per-cell energy of the cutoff field IS Theorem C's own left-hand side
  on the cube's own window: `symmPart(a_L) = ν Id`
  (`Cutoff.symmPart_coefficientCutoff`) turns `CoarseGraining`'s
  `localSymmetricEnergyENorm` into `√ν · ‖∇u‖_{L²(R)}` with no ellipticity
  ratio and no conversion.  This is an identity, not an estimate.
* `printedLocalEnergy_le_of_deep` — the deep range, by ONE application of the
  display at the descendant's own lattice centre
  (`latticeTranslate_of_mem_descendantsAtDepth`).
* `printedLocalEnergy_le_of_shallow` — **the sub-cube average step**, i.e.
 the shallow half at the energy carrier: a shallow cube's
  normalized energy is the volume-weighted average of its depth-`X` descendants'
  energies (`cubeAverage_le_of_descendants`, `CoarseGraining`'s exact partition identity),
  hence at most their maximum.  This is where the printed `3^{(1-α)X_m(α)}`
  factor is created.
* `printedLocalEnergy_le_of_display` — the two halves joined: ONE bound at every
  depth, at the majorant `C · 3^{(1-α)X} · 3^{(1-α)j}`.

## The display, sliced

`RegularityEnergyDisplay` is the root's FIRST conjunct with its three-term
bracket abstracted as one `[0,∞]` value `T`.  Nothing is added: the binder
shape, the window `((x+□_n) ∩ □_m)`, the measure, the integrand and the factor
`C·3^{(1-α)(m-n)}` are byte-for-byte the statement's.  The deep gate is written
`(X: ℤ) ≤ m - n` — at `n ≤ m` this is the `X ω ≤ (m-n).toNat` with a finite cut
of the `ℕ∞`-valued minimal scale.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The carrier identity -/

/-- The normalized volume measure of the OPEN cube is `CoarseGraining`'s normalized cube
measure: the two realizations of a triadic cube differ by a null set. -/
theorem normalizedVolumeMeasureOn_openCubeSet (R : TriadicCube d) :
    normalizedVolumeMeasureOn (openCubeSet R) = normalizedCubeMeasure R := by
  have hvol : volume (openCubeSet R) = volume (cubeSet R) :=
    (measure_congr (cubeSet_ae_eq_openCubeSet R)).symm
  rw [← normalizedVolumeMeasureOn_cubeSet R, normalizedVolumeMeasureOn_def,
    normalizedVolumeMeasureOn_def, hvol,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The `ν`-drop, pointwise.**  The symmetric part of the cutoff coefficient
field is `ν Id` (`Cutoff.symmPart_coefficientCutoff`), so the printed energy
density is literally `ν |∇u|²`.  An identity: no ellipticity ratio is spent. -/
theorem coefficientEnergyDensity_coefficientCutoff (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (x v : Vec d) :
    vecDot v (matVecMul (symmPart (Cutoff.coefficientCutoff M.nu L omega x)) v) =
      M.nu * vecNormSq v := by
  rw [Cutoff.symmPart_coefficientCutoff M.nu L omega x,
    show ((M.nu : ℝ) • (1 : Mat d)) = scalarMatrix (d := d) M.nu from rfl,
    matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]

/-- The `p = 2` `eLpNorm` of `|∇u|` against a measure, as a lower integral. -/
theorem eLpNorm_two_sqrt_vecNormSq (mu : Measure (Vec d)) (f : Vec d → Vec d)
    (hf : AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (f y))) mu) :
    eLpNorm (fun y => Real.sqrt (vecNormSq (f y))) 2 mu =
      (∫⁻ x, ENNReal.ofReal (vecNormSq (f x)) ∂mu) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (vecNormSq (f x)))
      (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact Real.sq_sqrt (vecNormSq_nonneg _)

/-- The Euclidean magnitude of an `H¹` gradient is a.e. strongly measurable for the
normalized volume measure of any subwindow of the domain. -/
theorem aestronglyMeasurable_sqrt_vecNormSq_grad {U A : Set (Vec d)} (u : H1Function U)
    (hAU : A ⊆ U) :
    AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (u.grad y)))
      (normalizedVolumeMeasureOn A) := by
  have hcont : Continuous fun v : Vec d => Real.sqrt (vecNormSq v) := by
    refine Real.continuous_sqrt.comp ?_
    show Continuous fun v : Vec d => ∑ i, v i * v i
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)
  rw [normalizedVolumeMeasureOn_def]
  exact ((hcont.comp_aestronglyMeasurable u.grad_memVectorL2.aestronglyMeasurable).mono_measure
    (Measure.restrict_mono hAU le_rfl)).smul_measure _

/-- **THE CARRIER IDENTITY.**

The printed per-cell energy of the cutoff field on a subcube `R` of `□_m` is
exactly Theorem C's left-hand side read on `R`'s own window:

```text
  ‖σ^{1/2}∇u‖_{L²(R)}  =  √ν · ‖∇u‖_{L²(R)}.
```

Both sides are `ENNReal.ofReal`-cut of the same finite quantity; the only step
is the pointwise `ν`-drop, which is an identity. -/
theorem ofReal_printedLocalEnergy_coefficientCutoff {Q R : TriadicCube d}
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
    (u : H1Function (openCubeSet Q)) (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    ENNReal.ofReal
        (printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega Q) u R) =
      ENNReal.ofReal (Real.sqrt M.nu) *
        eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
          (normalizedVolumeMeasureOn (openCubeSet R)) := by
  classical
  have hnu : (0 : ℝ) ≤ M.nu := M.nu_pos.le
  have hlocal : ENNReal.ofReal
      (printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega Q) u R) =
      localSymmetricEnergyENorm R
        ((Cutoff.coefficientCutoffCoeffOn M L omega Q).restrictToSubcube hRQ)
        (restrictH1ToSubcube u hRQ) := by
    rw [printedLocalEnergy, dite_eq_left hRQ,
      ENNReal.ofReal_toReal (localSymmetricEnergyENorm_ne_top _ _ _)]
  have hdensity : ∀ x : Vec d,
      ENNReal.ofReal
          (vecDot ((restrictH1ToSubcube u hRQ).grad x)
            (matVecMul
              (symmPart
                (((Cutoff.coefficientCutoffCoeffOn M L omega Q).restrictToSubcube
                    hRQ).toCoeffField x))
              ((restrictH1ToSubcube u hRQ).grad x))) =
        ENNReal.ofReal M.nu * ENNReal.ofReal (vecNormSq (u.grad x)) := by
    intro x
    rw [Book.Ch02.CoeffOn.restrictToSubcube_toCoeffField, restrictH1ToSubcube_grad,
      Cutoff.coefficientCutoffCoeffOn_toCoeffField]
    rw [coefficientEnergyDensity_coefficientCutoff M L omega x (u.grad x),
      ENNReal.ofReal_mul hnu]
  have hint : (∫⁻ x,
        ENNReal.ofReal
          (vecDot ((restrictH1ToSubcube u hRQ).grad x)
            (matVecMul
              (symmPart
                (((Cutoff.coefficientCutoffCoeffOn M L omega Q).restrictToSubcube
                    hRQ).toCoeffField x))
              ((restrictH1ToSubcube u hRQ).grad x)))
        ∂normalizedCubeMeasure R) =
      ENNReal.ofReal M.nu *
        ∫⁻ x, ENNReal.ofReal (vecNormSq (u.grad x)) ∂normalizedCubeMeasure R := by
    rw [lintegral_congr hdensity]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hsqrt : ENNReal.ofReal M.nu ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt M.nu) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hnu (by norm_num), ← Real.sqrt_eq_rpow]
  rw [hlocal, localSymmetricEnergyENorm, hint,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hsqrt,
    eLpNorm_two_sqrt_vecNormSq _ _ (aestronglyMeasurable_sqrt_vecNormSq_grad u hRQ),
    normalizedVolumeMeasureOn_openCubeSet]

/-! ## 2. The display, sliced at one sample -/

/-- **Theorem C's energy-density display, sliced.**

The FIRST conjunct of `anomalous_regularity` at one `ω`, one `L` and one
solution, with the printed three-term bracket abstracted as a single `[0,∞]`
value `T`.  The window, the measure, the integrand, the factor and the deep
gate are the statement's own; nothing is added.

`Creg` is the constant `C`, `alpha` the `α`, and `X` a finite cut of the
minimal scale `X_m(α)(ω)`. -/
def RegularityEnergyDisplay (M : ABKModel d) (m : ℤ) (X : ℕ)
    (u : H1Function (openCubeSet (originCube d m))) (Creg alpha : ℝ) (T : ℝ≥0∞) : Prop :=
  ∀ x ∈ openCubeSet (originCube d m), ∀ n : ℤ, n ≤ m → (X : ℤ) ≤ m - n →
    ENNReal.ofReal (Real.sqrt M.nu) *
        eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
          (normalizedVolumeMeasureOn
            (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
              openCubeSet (originCube d m))) ≤
      ENNReal.ofReal (Creg * Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) * T

/-! ## 3. The deep range -/

/-- **The deep range**, by one application of the display at the descendant's
own lattice centre.  `latticeTranslate_of_mem_descendantsAtDepth` identifies the
descendant with the printed translate `z + □_{m-j}`, and the intersection with
`□_m` is the descendant itself. -/
theorem printedLocalEnergy_le_of_deep {M : ABKModel d} {m : ℤ} {X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {Creg alpha : ℝ} {T : ℝ≥0∞}
    (hdisp : RegularityEnergyDisplay M m X u Creg alpha T) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {j : ℕ} (hj : X ≤ j) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    ENNReal.ofReal
        (printedLocalEnergy
          (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R) ≤
      ENNReal.ofReal (Creg * Real.rpow 3 ((1 - alpha) * (j : ℝ))) * T := by
  obtain ⟨hscale, hwindow, _hlattice, hcentre⟩ :=
    latticeTranslate_of_mem_descendantsAtDepth hR
  have hRQ : openCubeSet R ⊆ openCubeSet (originCube d m) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hset : ((fun y => triadicCubeShift R + y) '' openCubeSet (originCube d R.scale)) ∩
      openCubeSet (originCube d m) = openCubeSet R := by
    rw [← hwindow]
    exact Set.inter_eq_self_of_subset_left hRQ
  have hsc : R.scale = m - (j : ℤ) := hscale
  have hn : R.scale ≤ m := by rw [hsc]; omega
  have hgate : (X : ℤ) ≤ m - R.scale := by rw [hsc]; omega
  have hkey := hdisp (triadicCubeShift R) hcentre R.scale hn hgate
  rw [hset] at hkey
  have hpow : ((m : ℤ) : ℝ) - ((R.scale : ℤ) : ℝ) = (j : ℝ) := by
    rw [hsc]; push_cast; ring
  rw [ofReal_printedLocalEnergy_coefficientCutoff M L omega u hRQ]
  rw [hpow] at hkey
  exact hkey

/-! ## 4. The shallow range: the sub-cube average step -/

/-- **THE SUB-CUBE AVERAGE STEP** (at the energy carrier).

A shallow cube's normalized energy is the volume-weighted average of its
depth-`X` descendants' energies — `CoarseGraining`'s exact triadic partition
identity, routed through `cubeAverage_le_of_descendants` — hence at most their
maximum, each of which the deep display bounds.  No volume factor
`3^{(d/2)(m-j)}` is paid; the printed `3^{(1-α)X_m(α)}` is created exactly
here. -/
theorem printedLocalEnergy_le_of_shallow {M : ABKModel d} {m : ℤ} {X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {Creg alpha : ℝ} {T : ℝ≥0∞}
    (hdisp : RegularityEnergyDisplay M m X u Creg alpha T) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {j : ℕ} (hj : j ≤ X) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    ENNReal.ofReal
        (printedLocalEnergy
          (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R) ≤
      ENNReal.ofReal (Creg * Real.rpow 3 ((1 - alpha) * (X : ℝ))) * T := by
  classical
  have hnu2 : ENNReal.ofReal (Real.sqrt M.nu) ^ (2 : ℝ) = ENNReal.ofReal M.nu := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.sq_sqrt M.nu_pos.le
  /- the square of the printed energy on any subcu -/
  have hsq : ∀ S : TriadicCube d, openCubeSet S ⊆ openCubeSet (originCube d m) →
      ENNReal.ofReal
          (printedLocalEnergy
            (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u S) ^ (2 : ℝ) =
        ∫⁻ x, ENNReal.ofReal M.nu * ENNReal.ofReal (vecNormSq (u.grad x))
          ∂normalizedCubeMeasure S := by
    intro S hS
    rw [ofReal_printedLocalEnergy_coefficientCutoff M L omega u hS,
      normalizedVolumeMeasureOn_openCubeSet,
      eLpNorm_two_sqrt_vecNormSq _ _ (by
        rw [← normalizedVolumeMeasureOn_openCubeSet]
        exact aestronglyMeasurable_sqrt_vecNormSq_grad u hS),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hnu2, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  /- the deep descendants, at depth X below -/
  have hdeep : ∀ S ∈ descendantsAtDepth R (X - j),
      (∫⁻ x, ENNReal.ofReal M.nu * ENNReal.ofReal (vecNormSq (u.grad x))
          ∂normalizedCubeMeasure S) ≤
        (ENNReal.ofReal (Creg * Real.rpow 3 ((1 - alpha) * (X : ℝ))) * T) ^ (2 : ℝ) := by
    intro S hS
    have hmem : S ∈ descendantsAtDepth (originCube d m) (j + (X - j)) :=
      mem_descendantsAtDepth_add hR hS
    have hjj : j + (X - j) = X := by omega
    rw [hjj] at hmem
    have hSQ : openCubeSet S ⊆ openCubeSet (originCube d m) :=
      openCubeSet_subset_of_mem_descendantsAtDepth hmem
    have hbound := printedLocalEnergy_le_of_deep hdisp L omega (le_refl X) hmem
    rw [← hsq S hSQ]
    exact ENNReal.rpow_le_rpow hbound (by norm_num)
  have hRQ : openCubeSet R ⊆ openCubeSet (originCube d m) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hshallow := cubeAverage_le_of_descendants R (X - j)
    (fun x => ENNReal.ofReal M.nu * ENNReal.ofReal (vecNormSq (u.grad x))) hdeep
  rw [← hsq R hRQ] at hshallow
  have hmono := ENNReal.rpow_le_rpow hshallow (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one] at hmono

/-! ## 5. The two halves joined -/

/-- **THE DISPLAY AT EVERY DEPTH** ("Hence, for every
`j ≤ m`").

At every depth `j` below `□_m` — deep or shallow — the printed per-cube energy
obeys the same bound with the single extra factor `3^{(1-α)X}`, which is `≥ 1`
and is the manuscript's own minimal-scale factor. -/
theorem printedLocalEnergy_le_of_display {M : ABKModel d} {m : ℤ} {X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {Creg alpha : ℝ} {T : ℝ≥0∞}
    (hdisp : RegularityEnergyDisplay M m X u Creg alpha T) (halpha : alpha ≤ 1)
    (hCreg : 0 ≤ Creg) (L : ℤ) (omega : Cutoff.CutoffSample d) (j : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    ENNReal.ofReal
        (printedLocalEnergy
          (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R) ≤
      ENNReal.ofReal
          (Creg * Real.rpow 3 ((1 - alpha) * (X : ℝ)) *
            Real.rpow 3 ((1 - alpha) * (j : ℝ))) * T := by
  have h0 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha]
  have hX1 : (1 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * (X : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg h0 (Nat.cast_nonneg X))
  have hj1 : (1 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * (j : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg h0 (Nat.cast_nonneg j))
  have hX0 : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * (X : ℝ)) := by linarith only [hX1]
  have hj0 : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * (j : ℝ)) := by linarith only [hj1]
  rcases le_or_gt X j with hcase | hcase
  · refine (printedLocalEnergy_le_of_deep hdisp L omega hcase hR).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCreg hX1) hj0
  · refine (printedLocalEnergy_le_of_shallow hdisp L omega hcase.le hR).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact le_mul_of_one_le_right (mul_nonneg hCreg hX0) hj1

end

end Algsuperdiff.Section4.Provider.Homogenization
