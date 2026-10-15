/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementMassRepresentative
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.StationaryExpectations

/-!
# Shared normalized stream observables and law transport

The general observable and its stationary law are shared by both moment-boosted exponent regimes.
Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A one-sided tail bound pulls back along a measurable map. -/
theorem isBigOWith_comp_of_map
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {F : Omega → RegCoeffField d} (hF : Measurable F)
    {g : RegCoeffField d → ℝ} (hg : Measurable g) {Psi : ℝ → ℝ} {A : ℝ}
    (h : IsBigOWith (Measure.map F mu) Psi g A) :
    IsBigOWith mu Psi (fun omega => g (F omega)) A := by
  intro t ht
  have hset : MeasurableSet (upperTailEvent g (A * t)) :=
    measurableSet_lt measurable_const hg
  calc
    mu.real (upperTailEvent (fun omega => g (F omega)) (A * t)) =
        (Measure.map F mu).real (upperTailEvent g (A * t)) := by
          rw [Measure.real, Measure.real, Measure.map_apply hF hset]
          rfl
    _ ≤ (Psi t)⁻¹ := h ht

/-- Measurable real observables with the same law have equal integrals. -/
theorem integral_eq_of_map_eq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f mu = Measure.map g mu) :
    ∫ omega, f omega ∂mu = ∫ omega, g omega ∂mu := by
  calc
    ∫ omega, f omega ∂mu = ∫ x, x ∂Measure.map f mu := by
      symm
      change ∫ x, id x ∂Measure.map f mu = _
      rw [integral_map hf.aemeasurable aestronglyMeasurable_id]
      rfl
    _ = ∫ x, x ∂Measure.map g mu := by rw [hmap]
    _ = ∫ omega, g omega ∂mu := by
      change ∫ x, id x ∂Measure.map g mu = _
      rw [integral_map hg.aemeasurable aestronglyMeasurable_id]
      rfl

/-- Internal normalized centered cube-mass observable, reusable by both
moment-boosted exponent regimes. -/
def normalizedCenteredLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d) (p V : ℝ)
    (R : TriadicCube d) : RegCoeffField d → ℝ :=
  fun a => V⁻¹ *
    (regFieldLpMassRep p (cubeSet R) a -
      ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P)

/-- Measurability of the internal normalized centered cube-mass observable. -/
theorem measurable_normalizedCenteredLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d) (p V : ℝ)
    (R : TriadicCube d) :
    Measurable (normalizedCenteredLpMassRep P p V R) := by
  unfold normalizedCenteredLpMassRep
  exact measurable_const.mul ((measurable_regFieldLpMassRep p _).sub measurable_const)

/-- Locality of the internal normalized centered cube-mass observable. -/
theorem local_normalizedCenteredLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d) (p V : ℝ)
    (R : TriadicCube d) :
    Book.Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R)
      (normalizedCenteredLpMassRep P p V R) := by
  unfold normalizedCenteredLpMassRep
  exact Book.Ch04.IsRestrictionLocalRandomVariable.mul
    (Book.Ch04.IsRestrictionLocalRandomVariable.const _ _ V⁻¹)
    (Book.Ch04.IsRestrictionLocalRandomVariable.sub
      (isLocalRandomVariable_regFieldLpMassRep p (measurableSet_cubeSet R))
      (Book.Ch04.IsRestrictionLocalRandomVariable.const _ _ _))

/-- Stationarity gives every descendant of the normalized partition the same law as
the origin local variable.  This is the exact public-A rederivation of the
structural part of CoarseGraining's private partition-average proof. -/
theorem map_normalizedCenteredLpMassRep_descendant_eq_origin
    (M : ABKModel d) (p V : ℝ) (n m j : ℤ) (hj : 0 ≤ j)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d j) 0) :
    Measure.map (normalizedCenteredLpMassRep (partitionStreamIncrementLaw M n m) p V R)
        (partitionStreamIncrementLaw M n m) =
      Measure.map
        (normalizedCenteredLpMassRep (partitionStreamIncrementLaw M n m) p V
          (originCube d 0))
        (partitionStreamIncrementLaw M n m) := by
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let mu0 : ℝ := ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
    V⁻¹ * (regFieldLpMassRep p U a - mu0)
  have hY_cov : Book.Ch04.IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => V⁻¹ * (x - mu0))
      (isTranslationCovariantR_regFieldLpMassRep p U z a)
  have hY0_meas : Measurable (Y (cubeSet (originCube d 0))) := by
    exact measurable_const.mul ((measurable_regFieldLpMassRep p _).sub measurable_const)
  have hshift := Book.Ch04.cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
    (d := d) (by omega : (0 : ℤ) ≤ 0) hj hR
  have hmap := Book.Ch04.map_eq_map_translateReg_of_isRestrictionTranslationCovariant
    (P := P) (partitionStreamIncrementLaw_stationary M n m)
    (U := cubeSet (originCube d 0)) hY0_meas hY_cov (Book.Ch04.scaleTranslationShift 0 R)
  change Measure.map (Y (cubeSet R)) P = Measure.map (Y (cubeSet (originCube d 0))) P
  rw [hshift]
  exact hmap

end

end Algsuperdiff.Section3.Provider.Stream
