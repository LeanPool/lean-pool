/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationL2Limit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.H10Graph

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationWeakLimit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Zero-trace weak limit of the rounded affine iteration

The geometric continuous-K increment estimates are kept together with the
base Hilbert `L²` convergence.  Closedness of the zero-trace gradient range
recovers an honest `H10Function` at the limit.  The affine identity equations
then pass to the limit against each fixed zero-trace test gradient and give
the rounded constant-coefficient weak equation.
-/

namespace HCPolySupport
namespace HighContrast

open _root_.Filter MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator Topology

noncomputable section

variable {d : ℕ}

/-- The Hilbert representative of a packaged unit-cube gradient is the
standard Hilbert `L²` realization of that weak gradient. -/
theorem unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2
    (u : H10Function (openCubeSet (originCube d 0))) :
    unitCubeEuclideanL2FieldHilbertL2
        (unitCubeGradientEuclideanL2Field u) =
      u.toH1Function.gradToHilbertVectorL2 := by
  unfold unitCubeEuclideanL2FieldHilbertL2
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (unitCubeEuclideanL2Field_memVectorL2
          (unitCubeGradientEuclideanL2Field u)),
        H1Function.coeFn_gradToHilbertVectorL2 u.toH1Function]
    with x hx hgrad
  rw [hx, hgrad]
  rfl

/-- A matrix-transposed test gradient, packaged in the Hilbert `L²` space so
that pairing it with a solution gradient represents the coefficient weak
form. -/
@[expose]
noncomputable def unitCubeMatrixGradientTestHilbertL2
    (A : Mat d) (φ : H10Function (openCubeSet (originCube d 0))) :
    HilbertVectorL2 (openCubeSet (originCube d 0)) :=
  toHilbertVectorL2OfVecField
    (memVectorL2_constMatrix_mul (matTranspose A)
      φ.toH1Function.grad_memVectorL2)

/-- Pairing with the transposed matrix test gradient is exactly the weak
constant-coefficient bilinear form. -/
theorem inner_unitCubeMatrixGradientTestHilbertL2_eq_integral
    (A : Mat d) (φ u : H10Function (openCubeSet (originCube d 0))) :
    inner ℝ (unitCubeMatrixGradientTestHilbertL2 A φ)
        u.toH1Function.gradToHilbertVectorL2 =
      ∫ x in openCubeSet (originCube d 0),
        vecDot (matVecMul A (u.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume := by
  let htest : MemVectorL2 (openCubeSet (originCube d 0))
      (fun x ↦ matVecMul (matTranspose A) (φ.toH1Function.grad x)) :=
    memVectorL2_constMatrix_mul (matTranspose A)
      φ.toH1Function.grad_memVectorL2
  change u.toH1Function.gradientHilbertPairing htest = _
  rw [H1Function.gradientHilbertPairing_eq_integral]
  refine setIntegral_congr_fun (measurableSet_openCubeSet (originCube d 0)) ?_
  intro x _hx
  calc
    vecDot (matVecMul (matTranspose A) (φ.toH1Function.grad x))
        (u.toH1Function.grad x) =
        vecDot (u.toH1Function.grad x)
          (matVecMul (matTranspose A) (φ.toH1Function.grad x)) := by
          rw [vecDot_comm]
    _ = vecDot (matVecMul A (u.toH1Function.grad x))
          (φ.toH1Function.grad x) := by
          rw [vecDot_matVecMul_transpose]

private theorem matVecMul_one_iterationWeakLimit (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem matVecMul_eq_add_defect_iterationWeakLimit
    (A : Mat d) (x : Vec d) :
    matVecMul A x = x + matVecMul (A - 1) x := by
  rw [sub_matVecMul, matVecMul_one_iterationWeakLimit]
  abel

/-- A Hilbert `L²` limit of honest zero-trace gradients is again the gradient
of an honest zero-trace function on the open unit cube. -/
theorem exists_h10Function_of_tendsto_roundedIterationGradientHilbertL2
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d)
    (G : HilbertVectorL2 (openCubeSet (originCube d 0)))
    (hG : Tendsto
      (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
        abar hS h) atTop (nhds G)) :
    ∃ u : H10Function (openCubeSet (originCube d 0)),
      u.toH1Function.gradToHilbertVectorL2 = G := by
  let U : Set (Vec d) := openCubeSet (originCube d 0)
  have hU : IsOpenBoundedConvexDomain U := by
    simpa only [U] using
      isOpenBoundedConvexDomain_openCubeSet (originCube d 0)
  have hclosed : IsClosed
      (Set.range (H10GraphClosed.gradientCLM (d := d) (U := U))) :=
    H10GraphClosed.isClosed_range_gradientCLM (U := U) hU
  have hrange : ∀ n : ℕ,
      roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
          abar hS h n ∈
        Set.range (H10GraphClosed.gradientCLM (d := d) (U := U)) := by
    intro n
    let w : H10Function U :=
      roundedUnitCubeDirichletContinuousKIteration abar hS h n
    let zval : ScalarL2 U × HilbertVectorL2 U :=
      (w.toH1Function.toScalarL2,
        w.toH1Function.gradToHilbertVectorL2)
    have hzval : zval ∈ (h10GraphClosedSubmodule U).toSubmodule := by
      change zval ∈ (h10GraphSubmodule U).closure
      exact subset_closure
        (h10_pair_mem_h10GraphSubmodule (U := U) w)
    let z : H10GraphClosedSpace (d := d) U := ⟨zval, hzval⟩
    refine ⟨z, ?_⟩
    change w.toH1Function.gradToHilbertVectorL2 =
      roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
        abar hS h n
    exact
      (unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2
        w).symm
  have hGmem : G ∈
      Set.range (H10GraphClosed.gradientCLM (d := d) (U := U)) :=
    hclosed.mem_of_tendsto hG (_root_.Filter.Eventually.of_forall hrange)
  rcases hGmem with ⟨z, hzG⟩
  rcases exists_h10Function_of_mem_h10GraphClosedSubmodule (U := U) hU z.2 with
    ⟨u, _huVal, huGrad⟩
  refine ⟨u, ?_⟩
  calc
    u.toH1Function.gradToHilbertVectorL2 = z.1.2 := huGrad
    _ = H10GraphClosed.gradientCLM (d := d) (U := U) z := rfl
    _ = G := hzG

/-- Passing the affine identity problems to an identified zero-trace gradient
limit gives the rounded constant-coefficient Dirichlet equation. -/
theorem roundedIteration_isZeroTraceDirichletRhsWeakSolution_of_tendsto
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d)
    (u : H10Function (openCubeSet (originCube d 0)))
    (hlim : Tendsto
      (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
        abar hS h) atTop
      (nhds u.toH1Function.gradToHilbertVectorL2)) :
    IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField (roundedReferenceMatrix abar hS))
      (openCubeSet (originCube d 0)) u (fun x ↦ -h x) := by
  intro φ
  let U : Set (Vec d) := openCubeSet (originCube d 0)
  let B : Mat d := roundedReferenceMatrix abar hS
  let D : Mat d := B - 1
  let P : Vec d → Vec d := fun x ↦ φ.toH1Function.grad x
  let HB : HilbertVectorL2 U := unitCubeMatrixGradientTestHilbertL2 B φ
  let HI : HilbertVectorL2 U := unitCubeMatrixGradientTestHilbertL2 1 φ
  let Hforce : ℝ := ∫ x in U, vecDot (h x) (P x) ∂volume
  let g : ℕ → HilbertVectorL2 U :=
    roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2 abar hS h
  have hP : MemVectorL2 U P := by
    simpa only [U, P] using φ.toH1Function.grad_memVectorL2
  have hh : MemVectorL2 U h := by
    simpa only [U] using unitCubeEuclideanL2Field_memVectorL2 h
  have hHI : Tendsto (fun n ↦ inner ℝ HI (g n)) atTop
      (nhds (inner ℝ HI u.toH1Function.gradToHilbertVectorL2)) :=
    _root_.Filter.Tendsto.inner tendsto_const_nhds hlim
  have hHIsucc : Tendsto (fun n ↦ inner ℝ HI (g (n + 1))) atTop
      (nhds (inner ℝ HI u.toH1Function.gradToHilbertVectorL2)) :=
    hHI.comp (tendsto_add_atTop_nat 1)
  have hHB : Tendsto (fun n ↦ inner ℝ HB (g n)) atTop
      (nhds (inner ℝ HB u.toH1Function.gradToHilbertVectorL2)) :=
    _root_.Filter.Tendsto.inner tendsto_const_nhds hlim
  have hsequence : ∀ n : ℕ,
      inner ℝ HB (g n) =
        -Hforce + inner ℝ HI (g n) - inner ℝ HI (g (n + 1)) := by
    intro n
    let w : H10Function U :=
      roundedUnitCubeDirichletContinuousKIteration abar hS h n
    let wnext : H10Function U :=
      roundedUnitCubeDirichletContinuousKIteration abar hS h (n + 1)
    have hg : MemVectorL2 U (fun x ↦ w.toH1Function.grad x) :=
      w.toH1Function.grad_memVectorL2
    have hDg : MemVectorL2 U
        (fun x ↦ matVecMul D (w.toH1Function.grad x)) :=
      memVectorL2_constMatrix_mul D hg
    have hgP : IntegrableOn
        (fun x ↦ vecDot (w.toH1Function.grad x) (P x)) U :=
      integrableOn_vecDot_of_memVectorL2 hg hP
    have hDgP : IntegrableOn
        (fun x ↦ vecDot (matVecMul D (w.toH1Function.grad x)) (P x)) U :=
      integrableOn_vecDot_of_memVectorL2 hDg hP
    have hhP : IntegrableOn (fun x ↦ vecDot (h x) (P x)) U :=
      integrableOn_vecDot_of_memVectorL2 hh hP
    have hweak :=
      (roundedUnitCubeDirichletContinuousKIteration_succ_problem
        abar hS h n) φ
    have hweak' :
        (∫ x in U,
            vecDot (wnext.toH1Function.grad x) (P x) ∂volume) =
          -(Hforce + ∫ x in U,
            vecDot (matVecMul D (w.toH1Function.grad x)) (P x) ∂volume) := by
      calc
        (∫ x in U,
            vecDot (wnext.toH1Function.grad x) (P x) ∂volume) =
            -∫ x in U,
              vecDot
                (h x + matVecMul D (w.toH1Function.grad x))
                (P x) ∂volume := by
              simpa only [U, B, D, P, w, wnext,
                unitCubeEuclideanL2FieldAdd_apply,
                unitCubeEuclideanL2FieldConstMatrixMul_apply] using! hweak
        _ = -(Hforce + ∫ x in U,
              vecDot (matVecMul D (w.toH1Function.grad x)) (P x) ∂volume) := by
              rw [show (fun x ↦ vecDot
                    (h x + matVecMul D (w.toH1Function.grad x)) (P x)) =
                  (fun x ↦ vecDot (h x) (P x)) +
                    fun x ↦ vecDot (matVecMul D (w.toH1Function.grad x))
                      (P x) by
                    funext x
                    rw [Pi.add_apply, vecDot_add_left],
                show (fun x ↦ vecDot (h x) (P x)) +
                    (fun x ↦ vecDot (matVecMul D (w.toH1Function.grad x))
                      (P x)) =
                  fun x ↦ vecDot (h x) (P x) +
                    vecDot (matVecMul D (w.toH1Function.grad x)) (P x) by
                      funext x
                      rfl,
                integral_add hhP hDgP]
    have hBsplit :
        (∫ x in U,
            vecDot (matVecMul B (w.toH1Function.grad x)) (P x) ∂volume) =
          (∫ x in U, vecDot (w.toH1Function.grad x) (P x) ∂volume) +
            ∫ x in U,
              vecDot (matVecMul D (w.toH1Function.grad x)) (P x) ∂volume := by
      rw [← integral_add hgP hDgP]
      refine setIntegral_congr_fun (measurableSet_openCubeSet (originCube d 0)) ?_
      intro x _hx
      change vecDot (matVecMul B (w.toH1Function.grad x)) (P x) =
        vecDot (w.toH1Function.grad x) (P x) +
          vecDot (matVecMul D (w.toH1Function.grad x)) (P x)
      rw [show matVecMul B (w.toH1Function.grad x) =
          w.toH1Function.grad x + matVecMul D (w.toH1Function.grad x) by
            simpa only [D] using
              matVecMul_eq_add_defect_iterationWeakLimit B
                (w.toH1Function.grad x),
        vecDot_add_left]
    rw [show inner ℝ HB (g n) =
        ∫ x in U,
          vecDot (matVecMul B (w.toH1Function.grad x)) (P x) ∂volume by
          simpa only [HB, g, U, B, P, w,
            unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2]
            using! inner_unitCubeMatrixGradientTestHilbertL2_eq_integral B φ w]
    rw [show inner ℝ HI (g n) =
        ∫ x in U, vecDot (w.toH1Function.grad x) (P x) ∂volume by
          have hinner :=
            inner_unitCubeMatrixGradientTestHilbertL2_eq_integral
              (1 : Mat d) φ w
          simpa only [HI, g, U, P, w,
            unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2,
            matVecMul_one_iterationWeakLimit] using! hinner]
    rw [show inner ℝ HI (g (n + 1)) =
        ∫ x in U, vecDot (wnext.toH1Function.grad x) (P x) ∂volume by
          have hinner :=
            inner_unitCubeMatrixGradientTestHilbertL2_eq_integral
              (1 : Mat d) φ wnext
          simpa only [HI, g, U, P, wnext,
            unitCubeGradientEuclideanL2FieldHilbertL2_eq_gradToHilbertVectorL2,
            matVecMul_one_iterationWeakLimit] using! hinner]
    rw [hBsplit, hweak']
    ring
  have hright : Tendsto
      (fun n ↦ -Hforce + inner ℝ HI (g n) - inner ℝ HI (g (n + 1)))
      atTop (nhds (-Hforce)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (-Hforce : ℝ)) atTop
        (nhds (-Hforce)) := tendsto_const_nhds
    have h := (hconst.add hHI).sub hHIsucc
    simpa only [add_sub_cancel_right] using h
  have hHBnegative : Tendsto (fun n ↦ inner ℝ HB (g n)) atTop
      (nhds (-Hforce)) :=
    hright.congr' (_root_.Filter.Eventually.of_forall fun n ↦ (hsequence n).symm)
  have hpair : inner ℝ HB u.toH1Function.gradToHilbertVectorL2 = -Hforce :=
    tendsto_nhds_unique hHB hHBnegative
  change
    (∫ x in U,
        vecDot (matVecMul B (u.toH1Function.grad x)) (P x) ∂volume) =
      ∫ x in U, vecDot (-h x) (P x) ∂volume
  rw [← inner_unitCubeMatrixGradientTestHilbertL2_eq_integral B φ u]
  change inner ℝ HB u.toH1Function.gradToHilbertVectorL2 = _
  rw [hpair]
  rw [show (fun x ↦ vecDot (-h x) (P x)) =
      fun x ↦ -vecDot (h x) (P x) by
        funext x
        rw [vecDot_neg_left],
    integral_neg]

private theorem real_half_pow_sq_iterationWeakLimit (n : ℕ) :
    (((1 : ℝ) / 2) ^ n) ^ 2 = ((1 : ℝ) / 4) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

/-- The dimension-first order, geometric increment bounds, and their
zero-trace rounded-reference weak limit are selected in one package.  This
keeps the exact same witnesses available to the subsequent positive-order
closure argument. -/
theorem exists_roundedUnitCubeDirichletContinuousKIterationWeakLimit
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
                unitCubeNormalizedContinuousKEnergy s
                    (roundedUnitCubeDirichletContinuousKIterationIncrement
                      abar hS h 0) ≤
                  (ENNReal.ofReal B) ^ (2 * s.1) *
                    unitCubeNormalizedContinuousKEnergy s h ∧
                unitCubeNormalizedContinuousKEnergy s
                    (roundedUnitCubeDirichletContinuousKIterationIncrement
                      abar hS h 0) < ∞ ∧
                (∀ n : ℕ,
                  unitCubeNormalizedContinuousKEnergy s
                      (roundedUnitCubeDirichletContinuousKIterationIncrement
                        abar hS h n) ≤
                    (((ENNReal.ofReal A) ^ (2 * s.1) *
                        ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)) ^ n) *
                      unitCubeNormalizedContinuousKEnergy s
                        (roundedUnitCubeDirichletContinuousKIterationIncrement
                          abar hS h 0) ∧
                  unitCubeNormalizedContinuousKEnergy s
                      (roundedUnitCubeDirichletContinuousKIterationIncrement
                        abar hS h n) < ∞) ∧
                ∃ u : H10Function (openCubeSet (originCube d 0)),
                  Tendsto
                    (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
                      abar hS h) atTop
                    (nhds u.toH1Function.gradToHilbertVectorL2) ∧
                  IsZeroTraceDirichletRhsWeakSolution
                    (constantCoeffField (roundedReferenceMatrix abar hS))
                    (openCubeSet (originCube d 0)) u (fun x ↦ -h x) := by
  rcases
      exists_roundedUnitCubeDirichletContinuousKIterationIncrementGeometricBound d with
    ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient,
      B, honeB, hgeometric⟩
  refine ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient,
    B, honeB, ?_⟩
  intro abar hS h hhFinite
  rcases hgeometric abar hS h hhFinite with
    ⟨hfirst, hfirstFinite, hincrements⟩
  let q : ℝ≥0∞ :=
    (ENNReal.ofReal A) ^ (2 * s.1) *
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)
  let E0 : ℝ≥0∞ :=
    unitCubeNormalizedContinuousKEnergy s
      (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h 0)
  have hqQuarter : q ≤ ENNReal.ofReal ((1 : ℝ) / 4) := by
    calc
      q ≤ ENNReal.ofReal ((101 : ℝ) / 1000000) :=
        (by simpa only [q] using hcoefficient.le)
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 4) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
  have hdistGeometric : ∀ n : ℕ,
      dist
          (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
            abar hS h n)
          (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
            abar hS h (n + 1)) ≤
        Real.sqrt E0.toReal * ((1 : ℝ) / 2) ^ n := by
    intro n
    let L : ℝ≥0∞ :=
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞)
        (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h n)
    have henergy :
        unitCubeNormalizedContinuousKEnergy s
            (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h n) ≤
          q ^ n * E0 := by
      simpa only [q, E0] using (hincrements n).1
    have hLsq : L ^ 2 ≤ q ^ n * E0 :=
      (unitCubeNormalizedEuclideanLpENorm_sq_le_continuousKEnergy s
        (roundedUnitCubeDirichletContinuousKIterationIncrement abar hS h n)).trans
        henergy
    have hLsqQuarter :
        L ^ 2 ≤ (ENNReal.ofReal ((1 : ℝ) / 4)) ^ n * E0 := by
      calc
        L ^ 2 ≤ q ^ n * E0 := hLsq
        _ ≤ (ENNReal.ofReal ((1 : ℝ) / 4)) ^ n * E0 := by
          have hp : q ^ n ≤ (ENNReal.ofReal ((1 : ℝ) / 4)) ^ n := by
            gcongr
          simpa only [mul_comm] using mul_le_mul_right hp E0
    have hquarterPowFinite :
        (ENNReal.ofReal ((1 : ℝ) / 4)) ^ n < ∞ :=
      ENNReal.pow_lt_top ENNReal.ofReal_lt_top
    have hrightFinite :
        (ENNReal.ofReal ((1 : ℝ) / 4)) ^ n * E0 < ∞ :=
      ENNReal.mul_lt_top hquarterPowFinite
        (by simpa only [E0] using hfirstFinite)
    have hreal := ENNReal.toReal_mono hrightFinite.ne hLsqQuarter
    rw [ENNReal.toReal_mul] at hreal
    simp only [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hreal
    apply (sq_le_sq₀ (dist_nonneg)
      (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by norm_num) n))).mp
    calc
      dist
          (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
            abar hS h n)
          (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
            abar hS h (n + 1)) ^ 2 = L.toReal ^ 2 := by
        rw [dist_roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2_succ]
      _ ≤ ((1 : ℝ) / 4) ^ n * E0.toReal := by
        simpa only [ENNReal.toReal_pow] using hreal
      _ = (Real.sqrt E0.toReal * ((1 : ℝ) / 2) ^ n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg,
          real_half_pow_sq_iterationWeakLimit]
        ring
  have hcauchy : CauchySeq
      (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
        abar hS h) :=
    cauchySeq_of_le_geometric ((1 : ℝ) / 2) (Real.sqrt E0.toReal)
      (by norm_num) hdistGeometric
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨G, hG⟩
  rcases exists_h10Function_of_tendsto_roundedIterationGradientHilbertL2
      abar hS h G hG with ⟨u, huG⟩
  have hlim : Tendsto
      (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
        abar hS h) atTop
      (nhds u.toH1Function.gradToHilbertVectorL2) := by
    simpa only [huG] using hG
  refine ⟨hfirst, hfirstFinite, hincrements, u, hlim, ?_⟩
  exact roundedIteration_isZeroTraceDirichletRhsWeakSolution_of_tendsto
    abar hS h u hlim

end

end HighContrast
end HCPolySupport
