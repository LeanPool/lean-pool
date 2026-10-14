/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedColoring
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.StationaryExpectations

/-!
# MomentBoostedLargeTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Stream-specific transport for the sharp moment-boosted large-cube route

This module begins the application of the internal moment-boosted finite-family
endpoint to the actual partition-normalized stream increment.  It rederives the
stationarity transport for the centered local representative using only public
clean A.  In particular, no frozen declaration and no generic `Gamma_sigma`
coloring theorem is used.

The eventual public source theorem is assembled in a later focused provider;
the declarations here remain internal proof architecture.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Measurability needed by the final one-sided wrapper -/

theorem measurable_streamIncrementLpMass_for_momentBoosted
    {p : ℝ} (hp : 0 < p) (l n m : ℤ) :
    Measurable (streamIncrementLpMass (d := d) p l n m) :=
  Algsuperdiff.Section3.Provider.Stream.measurable_streamIncrementLpMass hp l n m

/-! ## Law transport for one-sided tails -/

private theorem isBigOWith_of_map_eq
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    {f : Omega → ℝ} {g : Omega' → ℝ} {Psi : ℝ → ℝ} {A : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f mu = Measure.map g mu')
    (hg_tail : IsBigOWith mu' Psi g A) :
    IsBigOWith mu Psi f A := by
  intro t ht
  let E : Set ℝ := {x | A * t < x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_id
  calc
    mu.real (upperTailEvent f (A * t)) = (Measure.map f mu).real E := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := mu) hf.aemeasurable hE)
      simpa [E, upperTailEvent] using! h.symm
    _ = (Measure.map g mu').real E := by rw [hmap]
    _ = mu'.real (upperTailEvent g (A * t)) := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := mu') hg.aemeasurable hE)
      simpa [E, upperTailEvent] using! h
    _ ≤ (Psi t)⁻¹ := hg_tail ht

private theorem isBigOWith_comp_of_map
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

private theorem integrable_of_map_eq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f mu = Measure.map g mu) (hg_int : Integrable g mu) :
    Integrable f mu := by
  have hint_map_g : Integrable id (Measure.map g mu) := by
    refine (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).mpr ?_
    simpa only [Function.comp_apply] using! hg_int
  have hint_map_f : Integrable id (Measure.map f mu) := by
    rw [hmap]
    exact hint_map_g
  refine (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mp ?_
  simpa only [Function.comp_apply] using hint_map_f

private theorem integral_eq_of_map_eq
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

private theorem map_abs_sq_eq_of_map_eq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f mu = Measure.map g mu) :
    Measure.map (fun omega => |f omega| ^ (2 : ℕ)) mu =
      Measure.map (fun omega => |g omega| ^ (2 : ℕ)) mu := by
  let phi : ℝ → ℝ := fun x => |x| ^ (2 : ℕ)
  have hphi : Measurable phi := continuous_abs.measurable.pow_const 2
  calc
    Measure.map (fun omega => |f omega| ^ (2 : ℕ)) mu =
        Measure.map phi (Measure.map f mu) := by
          simpa [phi, Function.comp_apply] using!
            (Measure.map_map hphi hf (μ := mu)).symm
    _ = Measure.map phi (Measure.map g mu) := by rw [hmap]
    _ = Measure.map (fun omega => |g omega| ^ (2 : ℕ)) mu := by
          simpa [phi, Function.comp_apply] using! Measure.map_map hphi hg (μ := mu)

/-! ## The actual centered local variable -/

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

/-- The normalized origin summand has unit strengthened one-sided control.
The scale is the actual all-real moment scale from `IncrementLp.lean`, not a
generic weak-Orlicz conversion constant. -/
theorem isBigOWith_normalizedCenteredLpMassRep_origin_momentBoosted
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let V : ℝ := streamIncrementLpMomentBoostScale M p n m
    IsBigOWith P (momentBoostedGammaSigma (2 / p))
      (normalizedCenteredLpMassRep P p V (originCube d 0)) 1 := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let V : ℝ := streamIncrementLpMomentBoostScale M p n m
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  let mu0 : ℝ := ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hV : 0 < V := streamIncrementLpMomentBoostScale_pos M hp hnm
  have hmu0 : mu0 =
      ∫ omega, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega
        ∂M.P.toMeasure := by
    simpa [P, mu0] using integral_regFieldLpMassRep_originCube_zero M hp0 n m
  have hraw := isBigOWith_centered_streamIncrementLpMass_momentBoosted M hp hnm
    (m + (incrementPartitionShift d : ℤ))
  have hmeas : Measurable (fun a : RegCoeffField d =>
      regFieldLpMassRep p (cubeSet (originCube d 0)) a - mu0) :=
    (measurable_regFieldLpMassRep p _).sub measurable_const
  have hcomp : (fun omega : ShellSeq d =>
      regFieldLpMassRep p (cubeSet (originCube d 0)) (F omega) - mu0) =
      fun omega => streamIncrementLpMass p
        (m + (incrementPartitionShift d : ℤ)) n m omega -
          ∫ omega', streamIncrementLpMass p
            (m + (incrementPartitionShift d : ℤ)) n m omega' ∂M.P.toMeasure := by
    funext omega
    rw [show F omega =
      smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m) by rfl,
      regFieldLpMassRep_originCube_zero_partitionIncrement hp0 n m omega, hmu0]
  have hPraw : IsBigOWith P (momentBoostedGammaSigma (2 / p))
      (fun a : RegCoeffField d =>
        regFieldLpMassRep p (cubeSet (originCube d 0)) a - mu0) V := by
    have h := isBigOWith_map_of_isBigOWith_comp
      (mu := M.P.toMeasure) (F := F)
      (show Measurable F by
        exact measurable_partitionIncrementField (d := d) n m) hmeas
      (by rw [hcomp]; exact hraw)
    simpa [P, F] using! h
  have hscaled := hPraw.const_mul (inv_nonneg.mpr hV.le)
  have hfun : (fun a : RegCoeffField d =>
      V⁻¹ * (regFieldLpMassRep p (cubeSet (originCube d 0)) a - mu0)) =
      normalizedCenteredLpMassRep P p V (originCube d 0) := by
    funext a
    unfold normalizedCenteredLpMassRep
    rfl
  rw [hfun] at hscaled
  simpa [P, V, hV.ne', inv_mul_cancel₀] using hscaled

/-- The same normalized origin summand is centered, integrable, and has a
unit second-moment proxy.  This consumes the genuine variance estimate from
the moment-growth proof; it does not assume a second-moment premise. -/
theorem normalizedCenteredLpMassRep_origin_moments
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let V : ℝ := streamIncrementLpMomentBoostScale M p n m
    let Y := normalizedCenteredLpMassRep P p V (originCube d 0)
    Integrable Y P ∧
      Integrable (fun a => |Y a| ^ (2 : ℕ)) P ∧
      (∫ a, Y a ∂P) = 0 ∧
      (∫ a, |Y a| ^ (2 : ℕ) ∂P) ≤ 1 := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let V : ℝ := streamIncrementLpMomentBoostScale M p n m
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  let mu0 : ℝ := ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P
  let Z : RegCoeffField d → ℝ := fun a =>
    regFieldLpMassRep p (cubeSet (originCube d 0)) a - mu0
  let Zshell : ShellSeq d → ℝ := fun omega =>
    streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega -
      ∫ omega', streamIncrementLpMass p
        (m + (incrementPartitionShift d : ℤ)) n m omega' ∂M.P.toMeasure
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hV : 0 < V := streamIncrementLpMomentBoostScale_pos M hp hnm
  have hmu0 : mu0 =
      ∫ omega, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega
        ∂M.P.toMeasure := by
    simpa [P, mu0] using integral_regFieldLpMassRep_originCube_zero M hp0 n m
  have hZcomp : (fun omega : ShellSeq d => Z (F omega)) = Zshell := by
    funext omega
    dsimp [Z, F, Zshell]
    rw [regFieldLpMassRep_originCube_zero_partitionIncrement hp0 n m omega, hmu0]
  have hmass_int := integrable_streamIncrementLpMass M hp hnm
    (m + (incrementPartitionShift d : ℤ))
  have hZshell_int : Integrable Zshell M.P.toMeasure := by
    exact hmass_int.sub (integrable_const _)
  have hZ_int : Integrable Z P := by
    rw [show P = Measure.map F M.P.toMeasure by rfl]
    refine (integrable_map_measure (show AEStronglyMeasurable Z P from
      ((measurable_regFieldLpMassRep p _).sub measurable_const).aestronglyMeasurable)
      (show AEMeasurable F M.P.toMeasure from
        (measurable_partitionIncrementField (d := d) n m).aemeasurable)).mpr ?_
    change Integrable (fun omega => Z (F omega)) M.P.toMeasure
    rw [hZcomp]
    exact hZshell_int
  have hZmean : (∫ a, Z a ∂P) = 0 := by
    have hZmean_map : (∫ a, Z a ∂P) = ∫ omega, Z (F omega) ∂M.P.toMeasure := by
      rw [show P = Measure.map F M.P.toMeasure by rfl]
      exact integral_map (measurable_partitionIncrementField (d := d) n m).aemeasurable
        ((measurable_regFieldLpMassRep p _).sub measurable_const).aestronglyMeasurable
    rw [hZmean_map]
    change (∫ omega, Z (F omega) ∂M.P.toMeasure) = 0
    rw [hZcomp]
    change (∫ omega, streamIncrementLpMass p
      (m + (incrementPartitionShift d : ℤ)) n m omega -
        ∫ omega', streamIncrementLpMass p
          (m + (incrementPartitionShift d : ℤ)) n m omega' ∂M.P.toMeasure
      ∂M.P.toMeasure) = 0
    rw [integral_sub hmass_int (integrable_const _)]
    simp
  have hZsqcomp : (fun omega => Z (F omega) ^ (2 : ℕ)) =
      fun omega => Zshell omega ^ (2 : ℕ) := by
    funext omega
    exact congrArg (fun x : ℝ => x ^ (2 : ℕ)) (congrFun hZcomp omega)
  have hsecond := integrable_and_integral_centered_streamIncrementLpMass_sq_le
    M hp hnm (m + (incrementPartitionShift d : ℤ))
  have hZsq_int : Integrable (fun a => Z a ^ (2 : ℕ)) P := by
    rw [show P = Measure.map F M.P.toMeasure by rfl]
    refine (integrable_map_measure (show AEStronglyMeasurable (fun a => Z a ^ (2 : ℕ)) P from
      ((measurable_regFieldLpMassRep p _).sub measurable_const).pow_const 2 |>.aestronglyMeasurable)
      (show AEMeasurable F M.P.toMeasure from
        (measurable_partitionIncrementField (d := d) n m).aemeasurable)).mpr ?_
    change Integrable (fun omega => Z (F omega) ^ (2 : ℕ)) M.P.toMeasure
    rw [hZsqcomp]
    exact hsecond.1
  have hZsq : (∫ a, Z a ^ (2 : ℕ) ∂P) ≤ V ^ (2 : ℕ) := by
    have hZsq_map : (∫ a, Z a ^ (2 : ℕ) ∂P) = ∫ omega, Z (F omega) ^ (2 : ℕ) ∂M.P.toMeasure := by
      rw [show P = Measure.map F M.P.toMeasure by rfl]
      exact integral_map (measurable_partitionIncrementField (d := d) n m).aemeasurable
        (((measurable_regFieldLpMassRep p _).sub measurable_const).pow_const 2
          |>.aestronglyMeasurable)
    rw [hZsq_map]
    change (∫ omega, Z (F omega) ^ (2 : ℕ) ∂M.P.toMeasure) ≤ V ^ (2 : ℕ)
    rw [hZsqcomp]
    exact hsecond.2
  let Y : RegCoeffField d → ℝ := fun a => V⁻¹ * Z a
  have hY_int : Integrable Y P := by
    simpa [Y] using hZ_int.const_mul V⁻¹
  have hYsq_fun : (fun a => |Y a| ^ (2 : ℕ)) =
      fun a => (V⁻¹) ^ (2 : ℕ) * Z a ^ (2 : ℕ) := by
    funext a
    dsimp [Y]
    rw [sq_abs]
    ring
  have hYsq_int : Integrable (fun a => |Y a| ^ (2 : ℕ)) P := by
    rw [hYsq_fun]
    exact hZsq_int.const_mul _
  have hYmean : (∫ a, Y a ∂P) = 0 := by
    rw [show Y = fun a => V⁻¹ * Z a by rfl, integral_const_mul, hZmean, mul_zero]
  have hYsq : (∫ a, |Y a| ^ (2 : ℕ) ∂P) ≤ 1 := by
    rw [hYsq_fun, integral_const_mul]
    calc
      (V⁻¹) ^ (2 : ℕ) * ∫ a, Z a ^ (2 : ℕ) ∂P ≤
          (V⁻¹) ^ (2 : ℕ) * V ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hZsq (pow_nonneg (inv_nonneg.mpr hV.le) _)
      _ = 1 := by field_simp [hV.ne']
  refine ⟨?_, ?_, ?_, hYsq⟩
  · simpa [normalizedCenteredLpMassRep, P, V, mu0, Z, Y] using! hY_int
  · simpa [normalizedCenteredLpMassRep, P, V, mu0, Z, Y] using hYsq_int
  · simpa [normalizedCenteredLpMassRep, P, V, mu0, Z, Y] using hYmean

/-- The sharp finite-color theorem applied to the genuine centered descendant
average of the partition-normalized stream increment.  All its moment, mean,
locality, and stationarity inputs are discharged locally in this proof. -/
private theorem isBigOWith_gammaSigma_centeredDescendantAverage_momentBoosted
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let sigma : ℝ := 2 / p
    let V : ℝ := streamIncrementLpMomentBoostScale M p n m
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    IsBigOWith P (gammaSigma sigma)
      (Book.Ch04.restrictionCenteredDescendantAverage P 0 j (regFieldLpMassRep p))
      (16 *
        (((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card : ℝ) *
        (((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card : ℝ) ^
          (1 / sigma) *
        Real.sqrt (momentBoostedIndependentVariance sigma) * V *
        Book.Ch04.partitionCardinalityScale (d := d) 0 j) := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let sigma : ℝ := 2 / p
  let V : ℝ := streamIncrementLpMomentBoostScale M p n m
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
  let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
  let Y : TriadicCube d → RegCoeffField d → ℝ :=
    normalizedCenteredLpMassRep P p V
  have hj : 0 ≤ j := by
    dsimp [j]
    omega
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    positivity
  have hsigma_one : sigma < 1 := by
    dsimp [sigma]
    rw [div_lt_one (by positivity : (0 : ℝ) < p)]
    linarith
  have hV : 0 < V := streamIncrementLpMomentBoostScale_pos M hp hnm
  have hS : S.Nonempty := by
    dsimp [S]
    exact descendantsAtScale_nonempty (originCube d j) hj
  have horigin_tail := isBigOWith_normalizedCenteredLpMassRep_origin_momentBoosted
    M hp hnm
  have horigin_moments := normalizedCenteredLpMassRep_origin_moments M hp hnm
  have hmap : ∀ R ∈ S, Measure.map (Y R) P =
      Measure.map (Y (originCube d 0)) P := by
    intro R hR
    simpa [Y, P, V, j, S] using
      map_normalizedCenteredLpMassRep_descendant_eq_origin M p V n m j hj R hR
  have hlocal : ∀ R ∈ S,
      Book.Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R)
        (Y R) := by
    intro R _
    exact local_normalizedCenteredLpMassRep P p V R
  have hmeas : ∀ R : TriadicCube d, Measurable (Y R) := by
    intro R
    exact measurable_normalizedCenteredLpMassRep P p V R
  have hint : ∀ R ∈ S, Integrable (Y R) P := by
    intro R hR
    exact integrable_of_map_eq (hmeas R) (hmeas (originCube d 0)) (hmap R hR)
      horigin_moments.1
  have hsq : ∀ R ∈ S, Integrable (fun a => |Y R a| ^ (2 : ℕ)) P := by
    intro R hR
    exact integrable_of_map_eq
      ((continuous_abs.measurable.comp (hmeas R)).pow_const 2)
      ((continuous_abs.measurable.comp (hmeas (originCube d 0))).pow_const 2)
      (map_abs_sq_eq_of_map_eq (hmeas R) (hmeas (originCube d 0)) (hmap R hR))
      horigin_moments.2.1
  have htail : ∀ R ∈ S,
      IsBigOWith P (momentBoostedGammaSigma sigma) (Y R) 1 := by
    intro R hR
    exact isBigOWith_of_map_eq (hmeas R) (hmeas (originCube d 0)) (hmap R hR)
      (by simpa [P, sigma, V, Y] using horigin_tail)
  have hmean : ∀ R ∈ S, ∫ a, Y R a ∂P = 0 := by
    intro R hR
    calc
      ∫ a, Y R a ∂P = ∫ a, Y (originCube d 0) a ∂P :=
        integral_eq_of_map_eq (hmeas R) (hmeas (originCube d 0)) (hmap R hR)
      _ = 0 := by simpa [P, V, Y] using horigin_moments.2.2.1
  have hsecond : ∀ R ∈ S, ∫ a, |Y R a| ^ (2 : ℕ) ∂P ≤ 1 := by
    intro R hR
    calc
      ∫ a, |Y R a| ^ (2 : ℕ) ∂P =
          ∫ a, |Y (originCube d 0) a| ^ (2 : ℕ) ∂P :=
        integral_eq_of_map_eq ((continuous_abs.measurable.comp (hmeas R)).pow_const 2)
          ((continuous_abs.measurable.comp (hmeas (originCube d 0))).pow_const 2)
          (map_abs_sq_eq_of_map_eq (hmeas R) (hmeas (originCube d 0)) (hmap R hR))
      _ ≤ 1 := by simpa [P, V, Y] using horigin_moments.2.2.2
  have hcolored := isBigOWith_gammaSigma_finset_sum_momentBoosted_colored
    (mu := P) (X := Y) (s := S) (color := color) (sigma := sigma) hS
    (fun c hc => by
      exact
        Book.Ch04.iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
        (Q := originCube d j) (k := 0) (c := c) (P := P)
        (partitionStreamIncrementLaw_unitRangeDependent M n m)
        (fun R => hlocal R.1 (Finset.mem_filter.mp R.2).1))
    hmeas hint hsq hsigma hsigma_one htail hmean hsecond
  let N : ℝ := S.card
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hS.card_pos
  have hscaled := hcolored.const_mul (mul_nonneg hV.le (inv_nonneg.mpr hN.le))
  have hfun :
      (fun a => (V * N⁻¹) * ∑ R ∈ S, Y R a) =
        Book.Ch04.restrictionCenteredDescendantAverage P 0 j (regFieldLpMassRep p) := by
    funext a
    unfold Book.Ch04.restrictionCenteredDescendantAverage
    change (V * N⁻¹) * ∑ R ∈ S,
        V⁻¹ * (regFieldLpMassRep p (cubeSet R) a -
          ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P) =
      N⁻¹ * ∑ R ∈ S,
        (regFieldLpMassRep p (cubeSet R) a -
          ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b ∂P)
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    field_simp [hV.ne']
  rw [hfun] at hscaled
  have hscale :
      (V * N⁻¹) *
          (16 * ((S.image color).card : ℝ) * ((S.image color).card : ℝ) ^ (1 / sigma) *
            Real.sqrt (momentBoostedIndependentVariance sigma) * Real.sqrt N) =
        16 * ((S.image color).card : ℝ) * ((S.image color).card : ℝ) ^ (1 / sigma) *
          Real.sqrt (momentBoostedIndependentVariance sigma) * V *
          Book.Ch04.partitionCardinalityScale (d := d) 0 j := by
    rw [Book.Ch04.partitionCardinalityScale]
    dsimp [N, S]
    ring
  rw [hscale] at hscaled
  simpa [P, sigma, V, j, S, color, N] using hscaled

/-- The sharp centered-average estimate transported back to the shell-sequence
law.  It is still an internal large-partition lemma; the deterministic head
and the final dimension-only envelope are assembled separately. -/
theorem isBigOWith_gammaSigma_streamIncrementLpMass_sub_originMean_momentBoosted
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    let sigma : ℝ := 2 / p
    let V : ℝ := streamIncrementLpMomentBoostScale M p n m
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => streamIncrementLpMass p l n m omega -
        ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure)
      (16 *
        (((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card : ℝ) *
        (((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card : ℝ) ^
          (1 / sigma) *
        Real.sqrt (momentBoostedIndependentVariance sigma) * V *
        Book.Ch04.partitionCardinalityScale (d := d) 0 j) := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let sigma : ℝ := 2 / p
  let V : ℝ := streamIncrementLpMomentBoostScale M p n m
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  have hmain := isBigOWith_gammaSigma_centeredDescendantAverage_momentBoosted
    M hp hp_two hnm hsl
  have hmeas : Measurable (Book.Ch04.restrictionCenteredDescendantAverage P 0 j
      (regFieldLpMassRep p)) := by
    unfold Book.Ch04.restrictionCenteredDescendantAverage
    exact (Finset.measurable_sum _ fun R _ =>
      (measurable_regFieldLpMassRep p (cubeSet R)).sub measurable_const).const_mul _
  have htrans := isBigOWith_comp_of_map
    (mu := M.P.toMeasure) (F := F)
    (show Measurable F by
      exact measurable_partitionIncrementField (d := d) n m) hmeas
    (by simpa [P, sigma, V, j] using! hmain)
  have hfun : (fun omega : ShellSeq d =>
      Book.Ch04.restrictionCenteredDescendantAverage P 0 j (regFieldLpMassRep p)
        (F omega)) =
      fun omega => streamIncrementLpMass p l n m omega -
        ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure := by
    funext omega
    rw [show F omega =
      smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m) by rfl,
      centeredDescendantAverage_regFieldLpMassRep_apply M
        (lt_of_lt_of_le zero_lt_one hp) hsl omega,
      integral_regFieldLpMassRep_originCube_zero M
        (lt_of_lt_of_le zero_lt_one hp) n m]
  rw [hfun] at htrans
  simpa [sigma, V, j] using htrans

end

end Algsuperdiff.Section3.Provider.Stream
