/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationWeakLimit
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationEnergyLimit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive-order energy at the rounded affine iteration limit

Right-associated finite tails of the geometric increments have a uniform
continuous-K energy bound: the factor two from each addition is absorbed by
the much faster geometric contraction.  The continuous K-functional is
Lipschitz with respect to the base Hilbert `L²` distance.  Pointwise
convergence of its weighted integrand and Fatou's lemma therefore pass the
uniform positive-order bound to the identified zero-trace weak limit.
-/

namespace HCPolySupport
namespace HighContrast

open _root_.Filter MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator Topology

noncomputable section

variable {d : ℕ}

private theorem unitCubeEuclideanL2Field_ext_energyLimit
    (F G : UnitCubeEuclideanL2Field d) (hFG : F.toField = G.toField) : F = G := by
  cases F with
  | mk F hF =>
      cases G with
      | mk G hG =>
          dsimp only at hFG
          subst G
          rfl

/-- A right-associated nonempty tail of consecutive rounded iteration
increments.  Index `n` represents the `n + 1` increments beginning at `k`. -/
@[expose]
noncomputable def roundedUnitCubeDirichletContinuousKIterationIncrementTail
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (k : ℕ) : ℕ →
      UnitCubeEuclideanL2Field d
  | 0 => roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h k
  | n + 1 =>
      unitCubeEuclideanL2FieldAdd
        (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h k)
        (roundedUnitCubeDirichletContinuousKIterationIncrementTail
          abar hS h (k + 1) n)

/-- A right-associated increment tail telescopes to the literal difference
of its endpoint iteration gradients. -/
theorem roundedUnitCubeDirichletContinuousKIterationIncrementTail_apply
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (k n : ℕ) (x : Vec d) :
    roundedUnitCubeDirichletContinuousKIterationIncrementTail
        abar hS h k n x =
      (roundedUnitCubeDirichletContinuousKIteration abar hS h
          (k + n + 1)).toH1Function.grad x -
        (roundedUnitCubeDirichletContinuousKIteration abar hS h
          k).toH1Function.grad x := by
  induction n generalizing k with
  | zero =>
      change
        (roundedUnitCubeDirichletContinuousKIteration abar hS h (k + 1) -
            roundedUnitCubeDirichletContinuousKIteration abar hS h k).toH1Function.grad x =
          (roundedUnitCubeDirichletContinuousKIteration abar hS h
            (k + 1)).toH1Function.grad x -
            (roundedUnitCubeDirichletContinuousKIteration abar hS h
              k).toH1Function.grad x
      exact congrFun
        (H1Function.sub_grad
          (roundedUnitCubeDirichletContinuousKIteration abar hS h
            (k + 1)).toH1Function
          (roundedUnitCubeDirichletContinuousKIteration abar hS h
            k).toH1Function) x
  | succ n ih =>
      change
        (roundedUnitCubeDirichletContinuousKIteration abar hS h (k + 1) -
            roundedUnitCubeDirichletContinuousKIteration abar hS h k).toH1Function.grad x +
          roundedUnitCubeDirichletContinuousKIterationIncrementTail
              abar hS h (k + 1) n x = _
      rw [show
          (roundedUnitCubeDirichletContinuousKIteration abar hS h (k + 1) -
              roundedUnitCubeDirichletContinuousKIteration abar hS h k).toH1Function.grad x =
            (roundedUnitCubeDirichletContinuousKIteration abar hS h
              (k + 1)).toH1Function.grad x -
              (roundedUnitCubeDirichletContinuousKIteration abar hS h
                k).toH1Function.grad x from
          congrFun
            (H1Function.sub_grad
              (roundedUnitCubeDirichletContinuousKIteration abar hS h
                (k + 1)).toH1Function
              (roundedUnitCubeDirichletContinuousKIteration abar hS h
                k).toH1Function) x,
        ih (k + 1)]
      have hindex : (k + 1) + n + 1 = k + (n + 1) + 1 := by omega
      rw [hindex]
      abel

/-- Starting the right-associated tail at zero gives exactly the packaged
gradient of the corresponding positive iterate. -/
theorem roundedUnitCubeDirichletContinuousKIterationIncrementTail_zero_eq_gradient
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (n : ℕ) :
    roundedUnitCubeDirichletContinuousKIterationIncrementTail
        abar hS h 0 n =
      unitCubeGradientEuclideanL2Field
        (roundedUnitCubeDirichletContinuousKIteration abar hS h (n + 1)) := by
  apply unitCubeEuclideanL2Field_ext_energyLimit
  funext x
  rw [roundedUnitCubeDirichletContinuousKIterationIncrementTail_apply]
  simp only [zero_add, unitCubeGradientEuclideanL2Field_apply,
    roundedUnitCubeDirichletContinuousKIteration_zero]
  change _ - (0 : H1Function (openCubeSet (originCube d 0))).grad x = _
  rw [H1Function.zero_grad]
  simp only [Pi.zero_apply, sub_zero]

/-- Right association turns the factor-two addition estimate into a uniform
bound because the next tail starts one geometric power later. -/
theorem roundedUnitCubeDirichletContinuousKIterationIncrementTail_energy_le
    [NeZero d] (s : FractionalOrder)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (q E0 : ℝ≥0∞)
    (hq : q ≤ ENNReal.ofReal ((1 : ℝ) / 4))
    (hincrements : ∀ j : ℕ,
      unitCubeNormalizedContinuousKEnergy s
          (roundedUnitCubeDirichletContinuousKIterationIncrement
            abar hS h j) ≤ q ^ j * E0) :
    ∀ k n : ℕ,
      unitCubeNormalizedContinuousKEnergy s
          (roundedUnitCubeDirichletContinuousKIterationIncrementTail
            abar hS h k n) ≤
        4 * (q ^ k * E0) := by
  intro k n
  induction n generalizing k with
  | zero =>
      calc
        unitCubeNormalizedContinuousKEnergy s
            (roundedUnitCubeDirichletContinuousKIterationIncrementTail
              abar hS h k 0) ≤ q ^ k * E0 := hincrements k
        _ ≤ 4 * (q ^ k * E0) := by
          exact le_mul_of_one_le_left (by norm_num) (by norm_num)
  | succ n ih =>
      have hq' : q ≤ (1 : ℝ≥0∞) / 4 := by
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hq
      have hfourMul : (4 : ℝ≥0∞) * q ≤ 1 := by
        calc
          (4 : ℝ≥0∞) * q ≤ 4 * ((1 : ℝ≥0∞) / 4) := by
            simpa only [mul_comm] using mul_le_mul_left hq' 4
          _ = 1 := by
            rw [div_eq_mul_inv, one_mul,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      have heightMul : (8 : ℝ≥0∞) * q ≤ 2 := by
        calc
          (8 : ℝ≥0∞) * q = 2 * (4 * q) := by ring
          _ ≤ 2 * 1 := by
            simpa only [mul_comm] using mul_le_mul_left hfourMul 2
          _ = 2 := by norm_num
      have hcoefficient : (2 : ℝ≥0∞) + 8 * q ≤ 4 := by
        calc
          (2 : ℝ≥0∞) + 8 * q ≤ 2 + 2 := by
            simpa only [add_comm] using add_le_add_left heightMul 2
          _ = 4 := by norm_num
      calc
        unitCubeNormalizedContinuousKEnergy s
            (roundedUnitCubeDirichletContinuousKIterationIncrementTail
              abar hS h k (n + 1)) ≤
          2 * unitCubeNormalizedContinuousKEnergy s
              (roundedUnitCubeDirichletContinuousKIterationIncrement
                abar hS h k) +
            2 * unitCubeNormalizedContinuousKEnergy s
              (roundedUnitCubeDirichletContinuousKIterationIncrementTail
                abar hS h (k + 1) n) :=
          unitCubeNormalizedContinuousKEnergy_add_le s
            (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h k)
            (roundedUnitCubeDirichletContinuousKIterationIncrementTail
              abar hS h (k + 1) n)
        _ ≤ 2 * (q ^ k * E0) + 2 * (4 * (q ^ (k + 1) * E0)) := by
          exact add_le_add
            (by simpa only [mul_comm] using
              mul_le_mul_left (hincrements k) 2)
            (by simpa only [mul_comm] using
              mul_le_mul_left (ih (k + 1)) 2)
        _ = (2 + 8 * q) * (q ^ k * E0) := by
          rw [pow_succ]
          ring
        _ ≤ 4 * (q ^ k * E0) := by
          simpa only [mul_comm] using
            mul_le_mul_right hcoefficient (q ^ k * E0)

private theorem continuousKGradientNorm_default_eq_zero_energyLimit :
    continuousKGradientNorm (default : ContinuousKCompetitor d) = 0 := by
  unfold continuousKGradientNorm
  calc
    (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun x => matrixFrobeniusMagnitude
          ((default : ContinuousKCompetitor d).gradient x))
        (default : ContinuousKCompetitor d).gradientFrobeniusMemL2 =
      (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun _ => (0 : ℝ)) MeasureTheory.MemLp.zero' := by
          apply BoundedMeasurableDomain.normalizedLpNorm_congr_ae
          filter_upwards [] with x
          rw [show (default : ContinuousKCompetitor d).gradient x = 0 by
            ext i j
            rfl]
          exact matrixFrobeniusMagnitude_zero
    _ = 0 := by
      unfold BoundedMeasurableDomain.normalizedLpNorm
        BoundedMeasurableDomain.normalizedLpFiniteENorm
        BoundedMeasurableDomain.normalizedLpENorm
      simp

private theorem ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm_energyLimit
    (F : UnitCubeEuclideanL2Field d) :
    ENNReal.ofReal
        (continuousKResidualNorm F (default : ContinuousKCompetitor d)) =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F := by
  have hresidual :
      (fun x => euclideanNorm
        (F x - (default : ContinuousKCompetitor d).toField x)) =
        fun x => euclideanNorm (F x) := by
    funext x
    rw [show (default : ContinuousKCompetitor d).toField x = 0 by
      ext i
      rfl]
    exact congrArg euclideanNorm (sub_zero (F x))
  unfold continuousKResidualNorm
    BoundedMeasurableDomain.normalizedEuclideanLpNorm
    BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change ENNReal.ofReal
      (MeasureTheory.eLpNorm
        (fun x => euclideanNorm
          (F x - (default : ContinuousKCompetitor d).toField x))
        (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume).toReal =
    MeasureTheory.eLpNorm (fun x => euclideanNorm (F x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume
  rw [hresidual,
    ENNReal.ofReal_toReal F.euclideanMagnitudeMemL2.eLpNorm_ne_top]

private theorem continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm_toReal
    (F : UnitCubeEuclideanL2Field d) :
    continuousKResidualNorm F (default : ContinuousKCompetitor d) =
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F).toReal := by
  have h := congrArg ENNReal.toReal
    (ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm_energyLimit F)
  simpa only [ENNReal.toReal_ofReal
    (continuousKResidualNorm_nonneg F default)] using h

/-- The continuous K-functional is bounded by the base Hilbert `L²` norm,
using the zero competitor. -/
theorem continuousKFunctional_le_norm_unitCubeEuclideanL2FieldHilbertL2
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F ≤
      ‖unitCubeEuclideanL2FieldHilbertL2 F‖ := by
  calc
    continuousKFunctional t F ≤
        continuousKFunctionalCompetitorValue t F default :=
      continuousKFunctional_le_competitor t F default
    _ = continuousKResidualNorm F default := by
      unfold continuousKFunctionalCompetitorValue
      rw [continuousKGradientNorm_default_eq_zero_energyLimit]
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
        Real.sqrt_sq_eq_abs,
        abs_of_nonneg (continuousKResidualNorm_nonneg F default)]
    _ = ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F).toReal :=
      continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm_toReal F
    _ = ‖unitCubeEuclideanL2FieldHilbertL2 F‖ :=
      (norm_unitCubeEuclideanL2FieldHilbertL2 F).symm

private theorem unitCubeEuclideanL2FieldAdd_sub_eq_left
    (F G : UnitCubeEuclideanL2Field d) :
    unitCubeEuclideanL2FieldAdd G (unitCubeEuclideanL2FieldSub F G) = F := by
  apply unitCubeEuclideanL2Field_ext_energyLimit
  funext x
  simp only [unitCubeEuclideanL2FieldAdd_apply,
    unitCubeEuclideanL2FieldSub_apply]
  abel

/-- The continuous K-functional is one-Lipschitz with respect to the base
Hilbert `L²` distance. -/
theorem abs_continuousKFunctional_sub_le_dist_hilbertL2
    (t : ContinuousKScale) (F G : UnitCubeEuclideanL2Field d) :
    |continuousKFunctional t F - continuousKFunctional t G| ≤
      dist (unitCubeEuclideanL2FieldHilbertL2 F)
        (unitCubeEuclideanL2FieldHilbertL2 G) := by
  have hFG : continuousKFunctional t F ≤
      continuousKFunctional t G +
        dist (unitCubeEuclideanL2FieldHilbertL2 F)
          (unitCubeEuclideanL2FieldHilbertL2 G) := by
    calc
      continuousKFunctional t F =
          continuousKFunctional t
            (unitCubeEuclideanL2FieldAdd G
              (unitCubeEuclideanL2FieldSub F G)) := by
            rw [unitCubeEuclideanL2FieldAdd_sub_eq_left]
      _ ≤ continuousKFunctional t G +
          continuousKFunctional t (unitCubeEuclideanL2FieldSub F G) :=
        continuousKFunctional_add_le t G (unitCubeEuclideanL2FieldSub F G)
      _ ≤ continuousKFunctional t G +
          ‖unitCubeEuclideanL2FieldHilbertL2
            (unitCubeEuclideanL2FieldSub F G)‖ := by
        exact add_le_add_right
          (continuousKFunctional_le_norm_unitCubeEuclideanL2FieldHilbertL2
            t (unitCubeEuclideanL2FieldSub F G)) _
      _ = continuousKFunctional t G +
          dist (unitCubeEuclideanL2FieldHilbertL2 F)
            (unitCubeEuclideanL2FieldHilbertL2 G) := by
        rw [unitCubeEuclideanL2FieldHilbertL2_sub, dist_eq_norm]
  have hGF : continuousKFunctional t G ≤
      continuousKFunctional t F +
        dist (unitCubeEuclideanL2FieldHilbertL2 F)
          (unitCubeEuclideanL2FieldHilbertL2 G) := by
    calc
      continuousKFunctional t G =
          continuousKFunctional t
            (unitCubeEuclideanL2FieldAdd F
              (unitCubeEuclideanL2FieldSub G F)) := by
            rw [unitCubeEuclideanL2FieldAdd_sub_eq_left]
      _ ≤ continuousKFunctional t F +
          continuousKFunctional t (unitCubeEuclideanL2FieldSub G F) :=
        continuousKFunctional_add_le t F (unitCubeEuclideanL2FieldSub G F)
      _ ≤ continuousKFunctional t F +
          ‖unitCubeEuclideanL2FieldHilbertL2
            (unitCubeEuclideanL2FieldSub G F)‖ := by
        exact add_le_add_right
          (continuousKFunctional_le_norm_unitCubeEuclideanL2FieldHilbertL2
            t (unitCubeEuclideanL2FieldSub G F)) _
      _ = continuousKFunctional t F +
          dist (unitCubeEuclideanL2FieldHilbertL2 F)
            (unitCubeEuclideanL2FieldHilbertL2 G) := by
        rw [unitCubeEuclideanL2FieldHilbertL2_sub, dist_comm, dist_eq_norm]
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr hFG, sub_le_iff_le_add'.mpr hGF⟩

/-- Base Hilbert `L²` convergence implies convergence of every fixed-scale
continuous K-functional value. -/
theorem tendsto_continuousKFunctional_of_tendsto_hilbertL2
    (t : ContinuousKScale) (F : ℕ → UnitCubeEuclideanL2Field d)
    (G : UnitCubeEuclideanL2Field d)
    (hFG : Tendsto (fun n ↦ unitCubeEuclideanL2FieldHilbertL2 (F n))
      atTop (nhds (unitCubeEuclideanL2FieldHilbertL2 G))) :
    Tendsto (fun n ↦ continuousKFunctional t (F n)) atTop
      (nhds (continuousKFunctional t G)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist := tendsto_iff_dist_tendsto_zero.mp hFG
  exact squeeze_zero
    (fun n ↦ dist_nonneg)
    (fun n ↦ by
      rw [Real.dist_eq]
      exact abs_continuousKFunctional_sub_le_dist_hilbertL2 t (F n) G)
    hdist

/-- Base Hilbert `L²` convergence gives pointwise convergence of the weighted
continuous-K seminorm integrands. -/
theorem tendsto_continuousKSeminormIntegrand_of_tendsto_hilbertL2
    (sigma : ℝ) (F : ℕ → UnitCubeEuclideanL2Field d)
    (G : UnitCubeEuclideanL2Field d)
    (hFG : Tendsto (fun n ↦ unitCubeEuclideanL2FieldHilbertL2 (F n))
      atTop (nhds (unitCubeEuclideanL2FieldHilbertL2 G))) (t : ℝ) :
    Tendsto (fun n ↦ continuousKSeminormIntegrand sigma (F n) t)
      atTop (nhds (continuousKSeminormIntegrand sigma G t)) := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · let tau : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hK : Tendsto (fun n ↦ continuousKFunctional tau (F n)) atTop
        (nhds (continuousKFunctional tau G)) :=
      tendsto_continuousKFunctional_of_tendsto_hilbertL2 tau F G hFG
    have hKsq : Tendsto (fun n ↦ continuousKFunctional tau (F n) ^ 2) atTop
        (nhds (continuousKFunctional tau G ^ 2)) := hK.pow 2
    have hofReal : Tendsto
        (fun n ↦ ENNReal.ofReal (continuousKFunctional tau (F n) ^ 2)) atTop
        (nhds (ENNReal.ofReal (continuousKFunctional tau G ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hKsq
    simp only [continuousKSeminormIntegrand,
      continuousKFunctionalOnOpenScale, dite_eq_left ht]
    have hleft : Tendsto
        (fun n ↦ ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (continuousKFunctional tau (F n) ^ 2)) atTop
        (nhds (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (continuousKFunctional tau G ^ 2))) :=
      ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal (Real.rpow t (-2 * sigma))) hofReal
        (Or.inr ENNReal.ofReal_ne_top)
    exact ENNReal.Tendsto.mul_const
      (b := ENNReal.ofReal t⁻¹) hleft (Or.inr ENNReal.ofReal_ne_top)
  · simp only [continuousKSeminormIntegrand,
      continuousKFunctionalOnOpenScale, dite_eq_right ht, zero_pow (by norm_num : 2 ≠ 0),
      ENNReal.ofReal_zero, mul_zero]
    exact tendsto_const_nhds

/-- A uniform continuous-K energy bound is closed under base Hilbert `L²`
convergence.  Separating the endpoint and continuum terms costs only the
displayed factor two. -/
theorem unitCubeNormalizedContinuousKEnergy_limit_le_two_mul
    (s : FractionalOrder) (F : ℕ → UnitCubeEuclideanL2Field d)
    (G : UnitCubeEuclideanL2Field d) (M : ℝ≥0∞)
    (hFG : Tendsto (fun n ↦ unitCubeEuclideanL2FieldHilbertL2 (F n))
      atTop (nhds (unitCubeEuclideanL2FieldHilbertL2 G)))
    (hbound : ∀ n : ℕ, unitCubeNormalizedContinuousKEnergy s (F n) ≤ M) :
    unitCubeNormalizedContinuousKEnergy s G ≤ 2 * M := by
  let L : UnitCubeEuclideanL2Field d → ℝ≥0∞ := fun H ↦
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) H
  let I : UnitCubeEuclideanL2Field d → ℝ≥0∞ := fun H ↦
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 H t
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  have hpPos : 0 < p := by
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (by norm_num) (FractionalOrder.pos s))
  have hpZero : p ≠ 0 := ne_of_gt hpPos
  have hpTop : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hLformula : ∀ H : UnitCubeEuclideanL2Field d,
      L H = ENNReal.ofReal ‖unitCubeEuclideanL2FieldHilbertL2 H‖ := by
    intro H
    rw [norm_unitCubeEuclideanL2FieldHilbertL2]
    exact (ENNReal.ofReal_toReal
      H.euclideanMagnitudeMemL2.eLpNorm_ne_top).symm
  have hnorm : Tendsto
      (fun n ↦ ‖unitCubeEuclideanL2FieldHilbertL2 (F n)‖) atTop
      (nhds ‖unitCubeEuclideanL2FieldHilbertL2 G‖) :=
    continuous_norm.continuousAt.tendsto.comp hFG
  have hLtendsto : Tendsto (fun n ↦ L (F n)) atTop (nhds (L G)) := by
    simp_rw [hLformula]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hnorm
  have hLsqTendsto : Tendsto (fun n ↦ (L (F n)) ^ 2) atTop
      (nhds ((L G) ^ 2)) := ENNReal.Tendsto.pow hLtendsto
  have hLbound : ∀ n : ℕ, (L (F n)) ^ 2 ≤ M := by
    intro n
    exact
      (unitCubeNormalizedEuclideanLpENorm_sq_le_continuousKEnergy s (F n)).trans
        (hbound n)
  have hLlimit : (L G) ^ 2 ≤ M :=
    isClosed_Iic.mem_of_tendsto hLsqTendsto
      (_root_.Filter.Eventually.of_forall hLbound)
  have hItendsto : ∀ t : ℝ,
      Tendsto (fun n ↦ continuousKSeminormIntegrand s.1 (F n) t) atTop
        (nhds (continuousKSeminormIntegrand s.1 G t)) :=
    tendsto_continuousKSeminormIntegrand_of_tendsto_hilbertL2 s.1 F G hFG
  have hIfatou : I G ≤ liminf (fun n ↦ I (F n)) atTop := by
    calc
      I G = ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          liminf (fun n ↦ continuousKSeminormIntegrand s.1 (F n) t) atTop := by
            apply lintegral_congr_ae
            filter_upwards [] with t
            exact (hItendsto t).liminf_eq.symm
      _ ≤ liminf (fun n ↦ I (F n)) atTop := by
        exact lintegral_liminf_le' fun n ↦
          continuousKSeminormIntegrand_aemeasurable s.1 (F n)
  have hpIbound : ∀ n : ℕ, p * I (F n) ≤ M := by
    intro n
    calc
      p * I (F n) ≤ (L (F n)) ^ 2 + p * I (F n) :=
        self_le_add_left _ _
      _ = unitCubeNormalizedContinuousKEnergy s (F n) := by
        rfl
      _ ≤ M := hbound n
  have hIbound : ∀ n : ℕ, I (F n) ≤ p⁻¹ * M := by
    intro n
    calc
      I (F n) = p⁻¹ * (p * I (F n)) := by
        rw [ENNReal.inv_mul_cancel_left hpZero hpTop]
      _ ≤ p⁻¹ * M := by
        simpa only [mul_comm] using mul_le_mul_left (hpIbound n) p⁻¹
  have hIlimit : I G ≤ p⁻¹ * M :=
    hIfatou.trans
      (liminf_le_of_frequently_le' (_root_.Filter.Frequently.of_forall hIbound))
  have hpIlimit : p * I G ≤ M := by
    calc
      p * I G ≤ p * (p⁻¹ * M) := by
        simpa only [mul_comm] using mul_le_mul_left hIlimit p
      _ = M := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hpZero hpTop, one_mul]
  change (L G) ^ 2 + p * I G ≤ 2 * M
  calc
    (L G) ^ 2 + p * I G ≤ M + M := add_le_add hLlimit hpIlimit
    _ = 2 * M := by ring

/-- The rounded-reference weak limit inherits a finite selected-order
continuous-K energy, with all membership and finiteness asserted as
conclusions. -/
theorem exists_roundedUnitCubeDirichletContinuousKIterationEnergyLimit
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∃ s : FractionalOrder,
        s.1 < (1 : ℝ) / 12 ∧
          (ENNReal.ofReal A) ^ (2 * s.1) <
            ENNReal.ofReal ((101 : ℝ) / 100) ∧
          (ENNReal.ofReal A) ^ (2 * s.1) *
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) <
            ENNReal.ofReal ((101 : ℝ) / 1000000) ∧
          (ENNReal.ofReal A) ^ (2 * s.1) *
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) < 1 ∧
          ∃ B : ℝ, 1 ≤ B ∧
            ∀ (abar : Mat d) (hS : (symmPart abar).PosDef)
              (h : UnitCubeEuclideanL2Field d),
              unitCubeNormalizedContinuousKEnergy s h < ∞ →
                ∃ u : H10Function (openCubeSet (originCube d 0)),
                  Tendsto
                    (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
                      abar hS h) atTop
                    (nhds u.toH1Function.gradToHilbertVectorL2) ∧
                  IsZeroTraceDirichletRhsWeakSolution
                    (constantCoeffField (roundedReferenceMatrix abar hS))
                    (openCubeSet (originCube d 0)) u (fun x ↦ -h x) ∧
                  unitCubeNormalizedContinuousKEnergy s
                      (unitCubeGradientEuclideanL2Field u) ≤
                    8 * ((ENNReal.ofReal B) ^ (2 * s.1) *
                      unitCubeNormalizedContinuousKEnergy s h) ∧
                  unitCubeNormalizedContinuousKEnergy s
                      (unitCubeGradientEuclideanL2Field u) < ∞ := by
  rcases exists_roundedUnitCubeDirichletContinuousKIterationWeakLimit d with
    ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient,
      B, honeB, hlimit⟩
  refine ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient,
    B, honeB, ?_⟩
  intro abar hS h hhFinite
  rcases hlimit abar hS h hhFinite with
    ⟨hfirst, hfirstFinite, hincrements, u, hlim, hweak⟩
  let q : ℝ≥0∞ :=
    (ENNReal.ofReal A) ^ (2 * s.1) *
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)
  let E0 : ℝ≥0∞ :=
    unitCubeNormalizedContinuousKEnergy s
      (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h 0)
  let F : ℕ → UnitCubeEuclideanL2Field d := fun n ↦
    unitCubeGradientEuclideanL2Field
      (roundedUnitCubeDirichletContinuousKIteration abar hS h (n + 1))
  let G : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field u
  let M : ℝ≥0∞ := 4 * E0
  have hqQuarter : q ≤ ENNReal.ofReal ((1 : ℝ) / 4) := by
    calc
      q ≤ ENNReal.ofReal ((101 : ℝ) / 1000000) :=
        (by simpa only [q] using hcoefficient.le)
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 4) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
  have hincrements' : ∀ n : ℕ,
      unitCubeNormalizedContinuousKEnergy s
          (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h n) ≤
        q ^ n * E0 := by
    intro n
    simpa only [q, E0] using (hincrements n).1
  have hFbound : ∀ n : ℕ,
      unitCubeNormalizedContinuousKEnergy s (F n) ≤ M := by
    intro n
    rw [show F n =
        roundedUnitCubeDirichletContinuousKIterationIncrementTail
          abar hS h 0 n by
          exact
            (roundedUnitCubeDirichletContinuousKIterationIncrementTail_zero_eq_gradient
              abar hS h n).symm]
    have htail :=
      roundedUnitCubeDirichletContinuousKIterationIncrementTail_energy_le
        s abar hS h q E0 hqQuarter hincrements' 0 n
    simpa only [M, pow_zero, one_mul] using htail
  have hFG : Tendsto
      (fun n ↦ unitCubeEuclideanL2FieldHilbertL2 (F n)) atTop
      (nhds (unitCubeEuclideanL2FieldHilbertL2 G)) := by
    have hshift := hlim.comp (tendsto_add_atTop_nat 1)
    simpa only [F, G,
      roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2,
      unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2]
      using! hshift
  have hlimitEnergy :
      unitCubeNormalizedContinuousKEnergy s G ≤ 2 * M :=
    unitCubeNormalizedContinuousKEnergy_limit_le_two_mul
      s F G M hFG hFbound
  have henergy :
      unitCubeNormalizedContinuousKEnergy s
          (unitCubeGradientEuclideanL2Field u) ≤
        8 * ((ENNReal.ofReal B) ^ (2 * s.1) *
          unitCubeNormalizedContinuousKEnergy s h) := by
    calc
      unitCubeNormalizedContinuousKEnergy s
          (unitCubeGradientEuclideanL2Field u) ≤ 2 * M := by
            simpa only [G] using hlimitEnergy
      _ = 8 * E0 := by
        simp only [M]
        ring
      _ ≤ 8 * ((ENNReal.ofReal B) ^ (2 * s.1) *
          unitCubeNormalizedContinuousKEnergy s h) :=
        (by
          have hE0 : E0 ≤
              (ENNReal.ofReal B) ^ (2 * s.1) *
                unitCubeNormalizedContinuousKEnergy s h := by
            simpa only [E0] using hfirst
          simpa only [mul_comm] using mul_le_mul_left hE0 8)
  have hBfinite : (ENNReal.ofReal B) ^ (2 * s.1) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg
      (mul_nonneg (by norm_num) s.2.1.le) ENNReal.ofReal_ne_top
  have hrightFinite :
      8 * ((ENNReal.ofReal B) ^ (2 * s.1) *
        unitCubeNormalizedContinuousKEnergy s h) < ∞ :=
    ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top hBfinite hhFinite)
  refine ⟨u, hlim, hweak, henergy, ?_⟩
  exact henergy.trans_lt hrightFinite

end

end HighContrast
end HCPolySupport
