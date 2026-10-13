/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.ConstantBesov
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.TransposeGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BesovCongr
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.UnitCubeValue
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.BesovPairing

/-!
# GradientSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The negative Besov budget of the zero-trace witness gradient

Source: ABK26 (`e.split.besov.stuff.begin`).  The Term BC multiplicand of the
`D_h` split is the zero-trace witness `u` with

```
∇u = ∇w + ∇w^* + ℓ_p' = ½ (∇v(·,□₀,p,q;a) + ∇v(·,□₀,p,-q;aᵗ)) + p ,
```

and every Besov estimate for `u` is fed by the concrete negative Besov
seminorm of `∇u` at the gauge exponent `3/8`.  This module produces that
budget, in the frozen shape

```
[∇u]_{B^{-3/8}_{2,2}(□₀)} ≤ C λ_{3/8,2}^{-1/2} ( J^{1/2} + |p·q|^{1/2} ) .
```

The three summands are handled by

* the coarse Poincaré inequality (`Assembly.GaugeBridge`) for `∇v`;
* the same inequality for `∇v^*` at the transposed coefficient, combined with
  the transpose invariance of the gauge (`Discharge.TransposeGauge`) and the
  adjoint response identity (`Discharge.AdjointResponse`);
* the constant-field bound (`Discharge.ConstantBesov`) together with the
  ellipticity chain (`Discharge.EllipticityOrdered`) for the affine piece `p`.

The elementary negative-Besov calculus (`a.e.` congruence and scalar
homogeneity at finite depth) is not available upstream and is proved here.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Almost-everywhere congruence for the negative `q = 2` quantities -/

theorem cubeBesovNegativeVectorDepthAverage_congr_ae (Q : TriadicCube d) (j : ℕ)
    {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovNegativeVectorDepthAverage Q f j =
      cubeBesovNegativeVectorDepthAverage Q g j := by
  have hpt : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R f) = vecNormSq (cubeAverageVec R g) := by
    intro R hR
    rw [cubeAverageVec_congr_ae R (ae_eq_on_descendant hR h)]
  unfold cubeBesovNegativeVectorDepthAverage
  refine le_antisymm ?_ ?_
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).le
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).ge

theorem cubeBesovNegativeVectorDepthSeminorm_congr_ae (Q : TriadicCube d) (s : ℝ)
    (j : ℕ) {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovNegativeVectorDepthSeminorm Q s f j =
      cubeBesovNegativeVectorDepthSeminorm Q s g j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_congr_ae Q j h]

theorem cubeBesovNegativeVectorPartialSeminormTwo_congr_ae (Q : TriadicCube d)
    (s : ℝ) (N : ℕ) {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N f =
      cubeBesovNegativeVectorPartialSeminormTwo Q s N g := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => ?_)
  rw [cubeBesovNegativeVectorDepthSeminorm_congr_ae Q s j h]

/-! ## Scalar homogeneity of the negative `q = 2` quantities -/

theorem cubeAverageVec_const_smul (Q : TriadicCube d) (c : ℝ)
    (f : Vec d → Vec d) :
    cubeAverageVec Q (fun x => c • f x) = c • cubeAverageVec Q f := by
  funext i
  show cubeAverage Q (fun x => (c • f x) i) = c * cubeAverage Q (fun x => f x i)
  simpa [Pi.smul_apply, smul_eq_mul] using
    cubeAverage_const_mul Q c (fun x => f x i)

theorem descendantsAverage_const_mul (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) = c * descendantsAverage Q j F := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun R => c * F R) =
    c * (((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum F)
  rw [← Finset.mul_sum]
  ring

theorem cubeBesovNegativeVectorDepthAverage_const_smul (Q : TriadicCube d)
    (c : ℝ) (f : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (fun x => c • f x) j =
      c ^ 2 * cubeBesovNegativeVectorDepthAverage Q f j := by
  have hpt : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R (fun x => c • f x)) =
        c ^ 2 * vecNormSq (cubeAverageVec R f) := by
    intro R _
    rw [cubeAverageVec_const_smul, vecNormSq_smul]
  unfold cubeBesovNegativeVectorDepthAverage
  rw [← descendantsAverage_const_mul Q j (c ^ 2)
    (fun R => vecNormSq (cubeAverageVec R f))]
  refine le_antisymm ?_ ?_
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).le
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).ge

theorem cubeBesovNegativeVectorDepthSeminorm_const_smul (Q : TriadicCube d)
    (s c : ℝ) (f : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • f x) j =
      |c| * cubeBesovNegativeVectorDepthSeminorm Q s f j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_const_smul,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  ring

theorem cubeBesovNegativeVectorPartialSeminormTwo_const_smul (Q : TriadicCube d)
    (s : ℝ) (N : ℕ) (c : ℝ) (f : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • f x) =
      |c| * cubeBesovNegativeVectorPartialSeminormTwo Q s N f := by
  have hsum :
      (∑ j ∈ Finset.range (N + 1),
          (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • f x) j) ^ 2) =
        ∑ j ∈ Finset.range (N + 1),
          (|c| * cubeBesovNegativeVectorDepthSeminorm Q s f j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      rw [cubeBesovNegativeVectorDepthSeminorm_const_smul]
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  rw [hsum]
  exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) |c|
    (fun j => cubeBesovNegativeVectorDepthSeminorm Q s f j) (abs_nonneg c)

/-! ## `L²` bookkeeping on the closed unit cube -/

theorem isFiniteMeasure_volumeMeasureOn_cubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
  let : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  change IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
  infer_instance

/-! ## The two maximizer-gradient budgets -/

/-- The negative Besov budget of a response-maximizer gradient at the frozen
unit cube, in the concrete `q = 2` spelling. -/
theorem cubeBesovNegativeVectorSeminormTwo_maximizerGrad_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) {p q : Vec d}
    {v : Solution (cubeDomain (originCube d 0)) a}
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v) :
    cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
        (fun x => v.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q)) := by
  classical
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  have hmain :=
    scaleNormalizedNegativeBesovVectorNorm_solutionGradient_unitCube_le
      (d := d) a F hF (v := Solution.ofAEEq hF.symm v) (hv.ofAEEq hF.symm)
  rw [Ch03.solutionGradientField, Solution.toH1_ofAEEq,
    Ch03.scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm]
    at hmain
  exact hmain

/-- The negative Besov partial seminorms of any `H¹` gradient on a cube are
bounded above. -/
theorem bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad [NeZero d]
    (Q : TriadicCube d)
    (w : H1Function ((cubeDomain Q : Domain d) : Set (Vec d))) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
        (fun x => w.grad x)) := by
  refine ⟨Ch03.scaleNormalizedNegativeBesovVectorNorm Q (3 / 8)
    (.finite 2) (fun x => w.grad x), ?_⟩
  rintro _ ⟨N, rfl⟩
  exact cubeBesovNegativeVectorPartialSeminormTwo_le_scaleNormalizedNegativeBesovVectorNorm
    Q (by norm_num) _ (memVectorL2_cubeSet_grad w) N

/-- The adjoint budget: the transposed gauge equals the frozen one, and the
transposed response is shifted by `2 p·q`. -/
theorem cubeBesovNegativeVectorSeminormTwo_adjointGrad_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) {p q : Vec d}
    {vAdj : Solution (cubeDomain (originCube d 0)) a.transpose}
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q)
      vAdj) :
    cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
        (fun x => vAdj.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
        (2 * Real.sqrt 2 *
          (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
            Real.sqrt |vecDot p q|)) := by
  classical
  have hbase :=
    cubeBesovNegativeVectorSeminormTwo_maximizerGrad_le a.transpose hvAdj
  rw [unitCubeLambda_transpose] at hbase
  refine hbase.trans ?_
  have hfactor : (0 : ℝ) ≤ Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
      Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) :=
    mul_nonneg poincareDiscountFactor_sensitivity_pos.le (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ hfactor
  -- the response shift
  have hshift := responseJ_transpose_neg_right (cubeDomain (originCube d 0)) a p q
  have hJnn : 0 ≤ responseJ (cubeDomain (originCube d 0)) a p q :=
    Ch02.responseJ_nonneg _ a p q
  have habs : vecDot p q ≤ |vecDot p q| := le_abs_self _
  have hmono : Real.sqrt (responseJ (cubeDomain (originCube d 0)) a.transpose p (-q)) ≤
      Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q + 2 * |vecDot p q|) := by
    rw [hshift]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsplit :
      Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q + 2 * |vecDot p q|) ≤
        Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
          Real.sqrt (2 * |vecDot p q|) :=
    sqrt_add_le_add_sqrt_of_nonneg hJnn (by positivity)
  have hroot : Real.sqrt (2 * |vecDot p q|) =
      Real.sqrt 2 * Real.sqrt |vecDot p q| :=
    Real.sqrt_mul (by norm_num) _
  have hone : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hJs : 0 ≤ Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) :=
    Real.sqrt_nonneg _
  have hqs : 0 ≤ Real.sqrt |vecDot p q| := Real.sqrt_nonneg _
  have hfinal : Real.sqrt (responseJ (cubeDomain (originCube d 0)) a.transpose p (-q)) ≤
      Real.sqrt 2 *
        (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
          Real.sqrt |vecDot p q|) := by
    refine (hmono.trans hsplit).trans ?_
    rw [hroot]
    nlinarith
  nlinarith [hfinal, Real.sqrt_nonneg 2]

/-! ## The witness-gradient budget -/

/-- The explicit constant of the witness-gradient negative Besov budget. -/
def gradSplitConst : ℝ :=
  Real.sqrt 2 *
    (2⁻¹ * Real.sqrt 2 *
        (2 * Real.sqrt 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) +
          2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)) +
      constantFieldBesovConst (3 / 8) * Real.sqrt 2)

theorem gradSplitConst_nonneg : 0 ≤ gradSplitConst := by
  have := poincareDiscountFactor_sensitivity_pos.le
  have := constantFieldBesovConst_nonneg (3 / 8 : ℝ)
  have h2 := Real.sqrt_nonneg (2 : ℝ)
  unfold gradSplitConst
  positivity

/-- **The negative Besov budget of the zero-trace witness gradient.** -/
theorem cubeBesovNegativeVectorSeminormTwo_witnessGrad_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (p q : Vec d)
    {vAdj : Solution (cubeDomain (originCube d 0)) a.transpose}
    {v : Solution (cubeDomain (originCube d 0)) a}
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q)
      vAdj)
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂ volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
        (fun x => u.toH1Function.grad x) ≤
      gradSplitConst *
        (Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
            Real.sqrt |vecDot p q|)) := by
  classical
  set X : ℝ := Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
    (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
      Real.sqrt |vecDot p q|) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  set PD : ℝ := Ch03.poincareDiscountFactor (3 / 8) (.finite 2) with hPD
  have hPDnn : 0 ≤ PD := poincareDiscountFactor_sensitivity_pos.le
  -- the three summand budgets
  have hAdj : cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
      (fun x => vAdj.toH1.grad x) ≤ (2 * Real.sqrt 2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_adjointGrad_le a hvAdj).trans
      (le_of_eq ?_)
    rw [hX, hPD]; ring
  have hPrimal : cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
      (fun x => v.toH1.grad x) ≤ (2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_maximizerGrad_le a hv).trans ?_
    have hle : Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) ≤
        Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
          Real.sqrt |vecDot p q| := by
      have := Real.sqrt_nonneg |vecDot p q|; linarith
    have hfac : (0 : ℝ) ≤ PD * Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) :=
      mul_nonneg hPDnn (Real.sqrt_nonneg _)
    have hstep := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)) hfac
    refine hstep.trans (le_of_eq ?_)
    rw [hX, hPD]; ring
  have hConst : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
          (fun _ => p) ≤ (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * X := by
    intro N
    refine (cubeBesovNegativeVectorPartialSeminormTwo_const_le (originCube d 0)
      (by norm_num) N p).trans ?_
    have hp := vecNorm_le_sqrt_two_mul_sqrt_unitCubeLambda_inv_mul_add a p q
    have hstep := mul_le_mul_of_nonneg_left hp
      (constantFieldBesovConst_nonneg (3 / 8 : ℝ))
    refine hstep.trans (le_of_eq ?_)
    rw [hX]; ring
  -- the a.e. identification of the witness gradient
  have hae : (fun x => u.toH1Function.grad x)
      =ᵐ[normalizedCubeMeasure (originCube d 0)]
      fun x => ((2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) + (fun _ => p) x := by
    refine ae_frozen_carrier_iff_normalizedCubeMeasure ?_
    filter_upwards [hu] with x hx using hx
  -- `L²` data
  have hL2Adj : MemVectorL2 (cubeSet (originCube d 0)) (fun x => vAdj.toH1.grad x) :=
    memVectorL2_cubeSet_grad vAdj.toH1
  have hL2v : MemVectorL2 (cubeSet (originCube d 0)) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_grad v.toH1
  have hL2sum : MemVectorL2 (cubeSet (originCube d 0))
      (fun x => vAdj.toH1.grad x + v.toH1.grad x) := hL2Adj.add hL2v
  have hL2smul : MemVectorL2 (cubeSet (originCube d 0))
      (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) :=
    hL2sum.const_smul ((2 : ℝ)⁻¹)
  have hL2const : MemVectorL2 (cubeSet (originCube d 0)) (fun _ : Vec d => p) := by
    let := isFiniteMeasure_volumeMeasureOn_cubeSet (originCube d 0)
    exact memVectorL2_const p
  -- the bounded-above data
  have hBddAdj := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
    (originCube d 0) vAdj.toH1
  have hBddv := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
    (originCube d 0) v.toH1
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound _ _ _ ?_
  intro N
  rw [cubeBesovNegativeVectorPartialSeminormTwo_congr_ae (originCube d 0) (3 / 8) N hae]
  have hadd := cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    (originCube d 0) (3 / 8)
    (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x))
    (fun _ => p) hL2smul hL2const N
  refine hadd.trans ?_
  have hsmul := cubeBesovNegativeVectorPartialSeminormTwo_const_smul
    (originCube d 0) (3 / 8) N ((2 : ℝ)⁻¹)
    (fun x => vAdj.toH1.grad x + v.toH1.grad x)
  have habs2 : |((2 : ℝ)⁻¹)| = (2 : ℝ)⁻¹ := by norm_num
  rw [habs2] at hsmul
  have hinner := cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    (originCube d 0) (3 / 8) (fun x => vAdj.toH1.grad x) (fun x => v.toH1.grad x)
    hL2Adj hL2v N
  have hAdjN : cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
      (fun x => vAdj.toH1.grad x) ≤ (2 * Real.sqrt 2 * PD) * X := by
    refine le_trans ?_ hAdj
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddAdj ⟨N, rfl⟩
  have hvN : cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
      (fun x => v.toH1.grad x) ≤ (2 * PD) * X := by
    refine le_trans ?_ hPrimal
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddv ⟨N, rfl⟩
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hleft :
      cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
          (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) ≤
        2⁻¹ * Real.sqrt 2 * ((2 * Real.sqrt 2 * PD) * X + (2 * PD) * X) := by
    rw [hsmul]
    have := hinner.trans (mul_le_mul_of_nonneg_left (add_le_add hAdjN hvN) hs2)
    linarith
  have hright := hConst N
  have hgoal :
      Real.sqrt 2 *
          (2⁻¹ * Real.sqrt 2 * ((2 * Real.sqrt 2 * PD) * X + (2 * PD) * X) +
            (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * X) =
        gradSplitConst * X := by
    unfold gradSplitConst
    rw [hPD]; ring
  calc
    Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
            (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) +
          cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
            (fun _ => p))
        ≤ Real.sqrt 2 *
            (2⁻¹ * Real.sqrt 2 * ((2 * Real.sqrt 2 * PD) * X + (2 * PD) * X) +
              (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * X) :=
          mul_le_mul_of_nonneg_left (add_le_add hleft hright) hs2
    _ = gradSplitConst * X := hgoal

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
