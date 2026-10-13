/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLowPowerColoring
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.StationaryExpectations

/-!
# MomentBoostedLowPowerTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Stream transport for the low-power moment-boosted route

This module applies the deterministic two-regime colored Bernstein endpoint to
the actual stream increment.  The only comparison between exponents is the
pointwise Jensen inequality on the cube: for `1 ≤ p ≤ 2`, the `p`-mass is at
most the `p / 2` power of the two-mass.  No such comparison is exposed as a
new premise of a source-facing declaration.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory Filter
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The low-power cube-mass comparison used internally by the two-regime
transport. -/
theorem streamIncrementLpMass_le_streamIncrementLpMass_two_rpow {p : ℝ}
    (hp : 0 < p) (hp_two : p ≤ 2) (l n m : ℤ) (omega : ShellSeq d) :
    streamIncrementLpMass p l n m omega ≤
      (streamIncrementLpMass 2 l n m omega) ^ (p / 2) := by
  let r : ℝ := 2 / p
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hp]
    linarith
  have hpr : p * r = 2 := by
    dsimp [r]
    field_simp
  have hmass := streamIncrementLpMass_rpow_le hp hr l n m omega
  rw [hpr] at hmass
  have hnonneg := streamIncrementLpMass_nonneg p l n m omega
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hinv : r⁻¹ = p / 2 := by
    dsimp [r]
    field_simp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hnonneg r) hmass
    (inv_nonneg.mpr hrpos.le)
  rw [← Real.rpow_mul hnonneg, hinv] at hpow
  have hrinv : r * (p / 2) = 1 := by
    dsimp [r]
    field_simp
  rw [hrinv, Real.rpow_one] at hpow
  exact hpow

/-- The centered, scale-two partition summand normalized by its actual mass
scale.  It is internal data for the low-power coloring application. -/
def normalizedLowPowerLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d) (V : ℝ)
    (R : TriadicCube d) : RegCoeffField d → ℝ :=
  fun a => V⁻¹ *
    (regFieldLpMassRep 2 (cubeSet R) a -
      ∫ b, regFieldLpMassRep 2 (cubeSet (originCube d 0)) b ∂P)

theorem measurable_normalizedLowPowerLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d)
    (V : ℝ) (R : TriadicCube d) :
    Measurable (normalizedLowPowerLpMassRep P V R) := by
  unfold normalizedLowPowerLpMassRep
  exact measurable_const.mul ((measurable_regFieldLpMassRep 2 _).sub measurable_const)

theorem local_normalizedLowPowerLpMassRep (P : Book.Ch04.RestrictionCoeffLaw d)
    (V : ℝ) (R : TriadicCube d) :
    Book.Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R)
      (normalizedLowPowerLpMassRep P V R) := by
  unfold normalizedLowPowerLpMassRep
  exact Book.Ch04.IsRestrictionLocalRandomVariable.mul
    (Book.Ch04.IsRestrictionLocalRandomVariable.const _ _ V⁻¹)
    (Book.Ch04.IsRestrictionLocalRandomVariable.sub
      (isLocalRandomVariable_regFieldLpMassRep 2 (measurableSet_cubeSet R))
      (Book.Ch04.IsRestrictionLocalRandomVariable.const _ _ _))

/-- Stationarity makes every scale-zero descendant have the origin law for
the normalized scale-two summand. -/
theorem map_normalizedLowPowerLpMassRep_descendant_eq_origin
    (M : ABKModel d) (V : ℝ) (n m j : ℤ) (hj : 0 ≤ j)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d j) 0) :
    Measure.map (normalizedLowPowerLpMassRep (partitionStreamIncrementLaw M n m) V R)
        (partitionStreamIncrementLaw M n m) =
      Measure.map
        (normalizedLowPowerLpMassRep (partitionStreamIncrementLaw M n m) V
          (originCube d 0))
        (partitionStreamIncrementLaw M n m) := by
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let mu0 : ℝ := ∫ b, regFieldLpMassRep 2 (cubeSet (originCube d 0)) b ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
    V⁻¹ * (regFieldLpMassRep 2 U a - mu0)
  have hY_cov : Book.Ch04.IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => V⁻¹ * (x - mu0))
      (isTranslationCovariantR_regFieldLpMassRep 2 U z a)
  have hY_meas : Measurable (Y (cubeSet (originCube d 0))) := by
    exact measurable_const.mul ((measurable_regFieldLpMassRep 2 _).sub measurable_const)
  have hshift := Book.Ch04.cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
    (d := d) (by omega : (0 : ℤ) ≤ 0) hj hR
  have hmap := Book.Ch04.map_eq_map_translateReg_of_isRestrictionTranslationCovariant
    (P := P) (partitionStreamIncrementLaw_stationary M n m)
    (U := cubeSet (originCube d 0)) hY_meas hY_cov (Book.Ch04.scaleTranslationShift 0 R)
  change Measure.map (Y (cubeSet R)) P = Measure.map (Y (cubeSet (originCube d 0))) P
  rw [hshift]
  exact hmap

private theorem lowPower_isBigO_of_map_eq
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    {f : Omega → ℝ} {g : Omega' → ℝ} {Psi : ℝ → ℝ} {A : ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure mu']
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f mu = Measure.map g mu')
    (hg_tail : IsBigO mu' Psi g A) :
    IsBigO mu Psi f A := by
  intro t ht
  let E : Set ℝ := {x | A * t < |x|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const continuous_abs.measurable
  calc
    mu.real (absTailEvent f (A * t)) = (Measure.map f mu).real E := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := mu) hf.aemeasurable hE)
      simpa [E, absTailEvent] using! h.symm
    _ = (Measure.map g mu').real E := by rw [hmap]
    _ = mu'.real (absTailEvent g (A * t)) := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := mu') hg.aemeasurable hE)
      simpa [E, absTailEvent] using! h
    _ ≤ (Psi t)⁻¹ := hg_tail ht

private theorem lowPower_integral_eq_of_map_eq
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

private theorem isBigOWith_normalizedLowPowerLpMassRep_origin
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let V : ℝ := streamIncrementLpMassScale M 2 n m
    IsBigO P (gammaSigma 1)
      (normalizedLowPowerLpMassRep P V (originCube d 0)) 1 := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let V : ℝ := streamIncrementLpMassScale M 2 n m
  have hV : 0 < V := streamIncrementLpMassScale_pos M (by norm_num) hnm
  have hraw := isBigO_gammaSigma_centeredOriginObservable_regFieldLpMassRep M
    (p := 2) (by norm_num) hnm
  have hscaled := hraw.const_mul (inv_nonneg.mpr hV.le)
  have hfun :
      (fun a : RegCoeffField d =>
        V⁻¹ * Book.Ch04.restrictionCenteredOriginObservable P 0 (regFieldLpMassRep 2) a) =
        normalizedLowPowerLpMassRep P V (originCube d 0) := by
    funext a
    simp only [normalizedLowPowerLpMassRep, Book.Ch04.restrictionCenteredOriginObservable]
  rw [hfun] at hscaled
  simpa [P, V, hV.ne', inv_mul_cancel₀] using hscaled

private theorem integral_normalizedLowPowerLpMassRep_origin_eq_zero
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let V : ℝ := streamIncrementLpMassScale M 2 n m
    (∫ a, normalizedLowPowerLpMassRep P V (originCube d 0) a ∂P) = 0 := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let V : ℝ := streamIncrementLpMassScale M 2 n m
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  let U : RegCoeffField d → ℝ := fun a =>
    regFieldLpMassRep 2 (cubeSet (originCube d 0)) a
  let mu0 : ℝ := ∫ a, U a ∂P
  have hU_meas : Measurable U := measurable_regFieldLpMassRep 2 _
  have hUcomp : (fun omega : ShellSeq d => U (F omega)) =
      streamIncrementLpMass 2 (m + (incrementPartitionShift d : ℤ)) n m := by
    funext omega
    dsimp [U]
    rw [show F omega =
      smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m) by rfl,
      regFieldLpMassRep_originCube_zero_partitionIncrement (by norm_num) n m omega]
  have hmass_int := integrable_streamIncrementLpMass M (by norm_num : (1 : ℝ) ≤ 2)
    hnm (m + (incrementPartitionShift d : ℤ))
  have hU_int : Integrable U P := by
    rw [show P = Measure.map F M.P.toMeasure by rfl]
    refine (integrable_map_measure hU_meas.aestronglyMeasurable
      (measurable_partitionIncrementField (d := d) n m).aemeasurable).mpr ?_
    have hcomp : U ∘ F =
        streamIncrementLpMass 2 (m + (incrementPartitionShift d : ℤ)) n m := by
      simpa only [Function.comp_apply] using! hUcomp
    rw [hcomp]
    exact hmass_int
  unfold normalizedLowPowerLpMassRep
  change ∫ a, V⁻¹ * (U a - mu0) ∂P = 0
  rw [integral_const_mul, integral_sub hU_int (integrable_const _)]
  simp [mu0]

private theorem isBigOWith_gammaSigma_lowPower_descendantAverage
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : p ≤ 2)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
    let K : ℝ := streamIncrementLpMassScale M 2 n m
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
    let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
    IsBigOWith P (gammaSigma (2 / p))
      (fun a => Book.Ch04.restrictionDescendantAverage 0 j (regFieldLpMassRep p) a - K ^ (p / 2))
      (momentBoostedLowPowerColorConst ((S.image color).card : ℝ) * K ^ (p / 2) /
        Real.sqrt (S.card : ℝ)) := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let K : ℝ := streamIncrementLpMassScale M 2 n m
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
  let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    normalizedLowPowerLpMassRep P K
  let Y : RegCoeffField d → ℝ :=
    Book.Ch04.restrictionDescendantAverage 0 j (regFieldLpMassRep 2)
  let Z : RegCoeffField d → ℝ :=
    Book.Ch04.restrictionDescendantAverage 0 j (regFieldLpMassRep p)
  let r : ℝ := p / 2
  let mu0 : ℝ := ∫ a, regFieldLpMassRep 2 (cubeSet (originCube d 0)) a ∂P
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hK : 0 < K := streamIncrementLpMassScale_pos M (by norm_num) hnm
  have hj : 0 ≤ j := by dsimp [j]; omega
  have hS : S.Nonempty := by
    dsimp [S]
    exact descendantsAtScale_nonempty (originCube d j) hj
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hr_half : (1 : ℝ) / 2 ≤ r := by dsimp [r]; linarith
  have hr_one : r ≤ 1 := by dsimp [r]; linarith
  have hX_origin := isBigOWith_normalizedLowPowerLpMassRep_origin M hnm
  have hX_mean := integral_normalizedLowPowerLpMassRep_origin_eq_zero M hnm
  have hmap : ∀ R ∈ S, Measure.map (X R) P =
      Measure.map (X (originCube d 0)) P := by
    intro R hR
    simpa [X, P, K, j, S] using
      map_normalizedLowPowerLpMassRep_descendant_eq_origin M K n m j hj R hR
  have hX_meas : ∀ R, Measurable (X R) := fun R =>
    measurable_normalizedLowPowerLpMassRep P K R
  have hX_tail : ∀ R ∈ S, IsBigO P (gammaSigma 1) (X R) 1 := by
    intro R hR
    exact lowPower_isBigO_of_map_eq (hX_meas R) (hX_meas (originCube d 0))
      (hmap R hR) (by simpa [P, K, X] using hX_origin)
  have hX_mean_all : ∀ R ∈ S, ∫ a, X R a ∂P = 0 := by
    intro R hR
    calc
      ∫ a, X R a ∂P = ∫ a, X (originCube d 0) a ∂P :=
        lowPower_integral_eq_of_map_eq (hX_meas R) (hX_meas (originCube d 0))
          (hmap R hR)
      _ = 0 := by simpa [P, K, X] using hX_mean
  have h_indep : ∀ c ∈ S.image color,
      iIndepFun (fun R : {R // R ∈ S.filter (fun T => color T = c)} => X R.1) P := by
    intro c hc
    exact Book.Ch04.iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
      (Q := originCube d j) (k := 0) (c := c) (P := P)
      (partitionStreamIncrementLaw_unitRangeDependent M n m)
      (fun R => local_normalizedLowPowerLpMassRep P K R.1)
  have hmu0 : mu0 ≤ K := by
    have hmu0_eq : mu0 =
        ∫ omega, streamIncrementLpMass 2
          (m + (incrementPartitionShift d : ℤ)) n m omega ∂M.P.toMeasure := by
      simpa [P, mu0] using integral_regFieldLpMassRep_originCube_zero M
        (by norm_num : (0 : ℝ) < 2) n m
    rw [hmu0_eq]
    exact integral_streamIncrementLpMass_le_massScale M (by norm_num) hnm _
  have hY_decomp : ∀ a,
      Y a = mu0 + (K / (S.card : ℝ)) * ∑ R ∈ S, X R a := by
    intro a
    dsimp [Y, X, normalizedLowPowerLpMassRep, mu0]
    unfold Book.Ch04.restrictionDescendantAverage
    change ((S.card : ℝ)⁻¹ *
        ∑ R ∈ S, regFieldLpMassRep 2 (cubeSet R) a) =
      mu0 + (K / (S.card : ℝ)) *
        ∑ R ∈ S, K⁻¹ * (regFieldLpMassRep 2 (cubeSet R) a - mu0)
    have hsum :
        (∑ R ∈ S, K⁻¹ * (regFieldLpMassRep 2 (cubeSet R) a - mu0)) =
          K⁻¹ * ((∑ R ∈ S, regFieldLpMassRep 2 (cubeSet R) a) -
            (S.card : ℝ) * mu0) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    rw [hsum]
    field_simp [hK.ne', hN.ne']
    ring
  have hYsum : Y ≤ᵐ[P] fun a =>
      K + (K / (S.card : ℝ)) * ∑ R ∈ S, X R a := by
    filter_upwards [] with a
    rw [hY_decomp a]
    gcongr
  have hYmeas : Measurable Y := by
    unfold Y Book.Ch04.restrictionDescendantAverage
    exact measurable_const.mul
      (Finset.measurable_sum _ fun R _ => measurable_regFieldLpMassRep 2 _)
  have hZmeas : Measurable Z := by
    unfold Z Book.Ch04.restrictionDescendantAverage
    exact measurable_const.mul
      (Finset.measurable_sum _ fun R _ => measurable_regFieldLpMassRep p _)
  have hYF : ∀ omega, Y (F omega) = streamIncrementLpMass 2 l n m omega := by
    intro omega
    dsimp [Y, F, j]
    exact descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass (by norm_num) hsl
      (incrementPartitionScale_ne_zero d m) rfl n m omega
  have hZF : ∀ omega, Z (F omega) = streamIncrementLpMass p l n m omega := by
    intro omega
    dsimp [Z, F, j]
    exact descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass hp0 hsl
      (incrementPartitionScale_ne_zero d m) rfl n m omega
  have hY_nonneg : 0 ≤ᵐ[P] Y := by
    rw [show P = Measure.map F M.P.toMeasure by rfl]
    apply (ae_map_iff (measurable_partitionIncrementField (d := d) n m).aemeasurable
      (hYmeas measurableSet_Ici)).2
    filter_upwards [] with omega
    rw [hYF omega]
    exact streamIncrementLpMass_nonneg 2 l n m omega
  have hZY : Z ≤ᵐ[P] fun a => (Y a) ^ r := by
    have hYpow_meas : Measurable fun a => (Y a) ^ r :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ r)).measurable.comp hYmeas
    rw [show P = Measure.map F M.P.toMeasure by rfl]
    have hmapAE := (ae_map_iff
      (μ := M.P.toMeasure)
      (measurable_partitionIncrementField (d := d) n m).aemeasurable
      ((hZmeas.sub hYpow_meas) measurableSet_Iic)).2
      (Filter.Eventually.of_forall fun omega => by
        change Z (F omega) - Y (F omega) ^ r ≤ 0
        rw [hZF omega, hYF omega]
        exact sub_nonpos.mpr
          (streamIncrementLpMass_le_streamIncrementLpMass_two_rpow hp0 hp_two l n m omega))
    filter_upwards [hmapAE] with a ha
    exact sub_nonpos.mp ha
  have hmain := sub_rpow_isBigOWith_gammaSigma_of_momentBoostedColoredBernstein
    (mu := P) (X := X) (s := S) (color := color) (Y := Y) (Z := Z)
    (r := r) (H := K) (K := K) hS h_indep hX_meas hX_tail hX_mean_all
    hr_half hr_one hK hK le_rfl hY_nonneg hZY hYsum
  simpa [P, K, j, S, color, Y, Z, r] using hmain

private theorem lowPower_isBigOWith_comp_of_map
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

/-- The low-power two-regime colored concentration bound, transported to the
actual stream mass in the genuine large-partition regime. -/
theorem isBigOWith_gammaSigma_streamIncrementLpMass_lowPower_partition
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : p ≤ 2)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    let K : ℝ := streamIncrementLpMassScale M 2 n m
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
    let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
    IsBigOWith M.P.toMeasure (gammaSigma (2 / p))
      (fun omega => streamIncrementLpMass p l n m omega - K ^ (p / 2))
      (momentBoostedLowPowerColorConst ((S.image color).card : ℝ) * K ^ (p / 2) /
        Real.sqrt (S.card : ℝ)) := by
  dsimp
  let P : Book.Ch04.RestrictionCoeffLaw d := partitionStreamIncrementLaw M n m
  let K : ℝ := streamIncrementLpMassScale M 2 n m
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
  let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
      (finiteShellIncrement omega n m)
  let g : RegCoeffField d → ℝ := fun a =>
    Book.Ch04.restrictionDescendantAverage 0 j (regFieldLpMassRep p) a - K ^ (p / 2)
  have hmain := isBigOWith_gammaSigma_lowPower_descendantAverage M hp hp_two hnm hsl
  have hg : Measurable g := by
    unfold g Book.Ch04.restrictionDescendantAverage
    exact (measurable_const.mul
      (Finset.measurable_sum _ fun R _ => measurable_regFieldLpMassRep p _)).sub
        measurable_const
  have htrans := lowPower_isBigOWith_comp_of_map
    (mu := M.P.toMeasure) (F := F) (g := g)
    (show Measurable F by exact measurable_partitionIncrementField (d := d) n m) hg
    (by simpa [P, K, j, S, color, g] using! hmain)
  have hfun : (fun omega : ShellSeq d => g (F omega)) =
      fun omega => streamIncrementLpMass p l n m omega - K ^ (p / 2) := by
    funext omega
    dsimp [g, F, j]
    rw [descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass
      (lt_of_lt_of_le zero_lt_one hp) hsl
      (incrementPartitionScale_ne_zero d m) rfl n m omega]
  rw [hfun] at htrans
  simpa [K, j, S, color] using htrans

end

end Algsuperdiff.Section3.Provider.Stream
