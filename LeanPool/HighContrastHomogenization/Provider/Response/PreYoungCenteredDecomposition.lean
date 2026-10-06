/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungGapAPartial
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates
public import LeanPool.HighContrastHomogenization.Provider.Response.SplitReadoutAdjointIntegrability

/-!
# High-contrast homogenization: Provider.Response.PreYoungCenteredDecomposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centered terminal-response decomposition

The annealed terminal response is split into a cutoff-weighted centered
product, the cutoff-energy defect, and the two cutoff-defect means.  The
measurability of the centered product and the localized readouts is recovered
from the measurable optimizer energy and coordinate-readout maps; quantitative
domination is kept explicit.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem volumeAverage_weighted_centered_vecDot
    {U : Set (Vec d)} {eta : Vec d → ℝ} {G F : Vec d → Vec d}
    {Pcen Qcen : Vec d}
    (henergy : IntegrableOn
      (fun x ↦ eta x * ((1 / 2 : ℝ) * vecDot (G x) (F x))) U)
    (hG : ∀ i, IntegrableOn (fun x ↦ eta x * G x i) U)
    (hF : ∀ i, IntegrableOn (fun x ↦ eta x * F x i) U)
    (heta : IntegrableOn eta U) :
    volumeAverage U (fun x ↦ eta x * ((1 / 2 : ℝ) *
        vecDot (G x - Pcen) (F x - Qcen))) =
      volumeAverage U (fun x ↦ eta x * ((1 / 2 : ℝ) * vecDot (G x) (F x))) -
        (1 / 2 : ℝ) * vecDot Qcen
          (fun i ↦ volumeAverage U (fun x ↦ eta x * G x i)) -
        (1 / 2 : ℝ) * vecDot Pcen
          (fun i ↦ volumeAverage U (fun x ↦ eta x * F x i)) +
        (1 / 2 : ℝ) * vecDot Pcen Qcen * volumeAverage U eta := by
  let A := fun x ↦ eta x * ((1 / 2 : ℝ) * vecDot (G x) (F x))
  let B := fun x ↦ eta x * ((1 / 2 : ℝ) * vecDot Qcen (G x))
  let C := fun x ↦ eta x * ((1 / 2 : ℝ) * vecDot Pcen (F x))
  let K := fun x ↦ ((1 / 2 : ℝ) * vecDot Pcen Qcen) * eta x
  have hBeq : B = (1 / 2 : ℝ) • fun x ↦
      vecDot Qcen (fun i ↦ eta x * G x i) := by
    funext x
    dsimp only [B, vecDot, Pi.smul_apply, smul_eq_mul]
    calc
      eta x * ((1 / 2 : ℝ) * ∑ i, Qcen i * G x i) =
          ((1 / 2 : ℝ) * eta x) * ∑ i, Qcen i * G x i := by ring
      _ = ∑ i, ((1 / 2 : ℝ) * eta x) * (Qcen i * G x i) :=
        Finset.mul_sum _ _ _
      _ = ∑ i, (1 / 2 : ℝ) * (Qcen i * (eta x * G x i)) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (1 / 2 : ℝ) * ∑ i, Qcen i * (eta x * G x i) :=
        (Finset.mul_sum _ _ _).symm
  have hCeq : C = (1 / 2 : ℝ) • fun x ↦
      vecDot Pcen (fun i ↦ eta x * F x i) := by
    funext x
    dsimp only [C, vecDot, Pi.smul_apply, smul_eq_mul]
    calc
      eta x * ((1 / 2 : ℝ) * ∑ i, Pcen i * F x i) =
          ((1 / 2 : ℝ) * eta x) * ∑ i, Pcen i * F x i := by ring
      _ = ∑ i, ((1 / 2 : ℝ) * eta x) * (Pcen i * F x i) :=
        Finset.mul_sum _ _ _
      _ = ∑ i, (1 / 2 : ℝ) * (Pcen i * (eta x * F x i)) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (1 / 2 : ℝ) * ∑ i, Pcen i * (eta x * F x i) :=
        (Finset.mul_sum _ _ _).symm
  have hB : IntegrableOn B U := by
    have hsum := (integrable_finsetSum Finset.univ fun i _ ↦
      (hG i).const_mul (Qcen i)).const_mul (1 / 2 : ℝ)
    exact hsum.congr
      (_root_.Filter.Eventually.of_forall fun x ↦ (congrFun hBeq x).symm)
  have hC : IntegrableOn C U := by
    have hsum := (integrable_finsetSum Finset.univ fun i _ ↦
      (hF i).const_mul (Pcen i)).const_mul (1 / 2 : ℝ)
    exact hsum.congr
      (_root_.Filter.Eventually.of_forall fun x ↦ (congrFun hCeq x).symm)
  have hK : IntegrableOn K U := heta.const_mul _
  have hpoint : (fun x ↦ eta x * ((1 / 2 : ℝ) *
      vecDot (G x - Pcen) (F x - Qcen))) =
      fun x ↦ A x - B x - C x + K x := by
    funext x
    dsimp only [A, B, C, K]
    rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right,
      vecDot_comm (G x) Qcen]
    ring
  have hAB : volumeAverage U (fun x ↦ A x - B x) =
      volumeAverage U A - volumeAverage U B :=
    volumeAverage_sub henergy hB
  have hABC : volumeAverage U (fun x ↦ (A x - B x) - C x) =
      volumeAverage U (fun x ↦ A x - B x) - volumeAverage U C :=
    volumeAverage_sub (henergy.sub hB) hC
  have hABCK : volumeAverage U (fun x ↦ (A x - B x - C x) + K x) =
      volumeAverage U (fun x ↦ A x - B x - C x) + volumeAverage U K :=
    volumeAverage_add ((henergy.sub hB).sub hC) hK
  rw [hpoint, hABCK, hABC, hAB]
  have hBavg : volumeAverage U B = (1 / 2 : ℝ) * vecDot Qcen
      (fun i ↦ volumeAverage U (fun x ↦ eta x * G x i)) := by
    rw [hBeq, volumeAverage_smul, volumeAverage_vecDot_left Qcen _ hG]
  have hCavg : volumeAverage U C = (1 / 2 : ℝ) * vecDot Pcen
      (fun i ↦ volumeAverage U (fun x ↦ eta x * F x i)) := by
    rw [hCeq, volumeAverage_smul, volumeAverage_vecDot_left Pcen _ hF]
  have hKavg : volumeAverage U K =
      (1 / 2 : ℝ) * vecDot Pcen Qcen * volumeAverage U eta := by
    rw [show K = ((1 / 2 : ℝ) * vecDot Pcen Qcen) • eta by
      funext x; simp only [K, Pi.smul_apply, smul_eq_mul], volumeAverage_smul]
  rw [hBavg, hCavg, hKavg]

private theorem integral_vecDot_const
    {P : Measure (CoeffSpace d)} (c : Vec d) {F : CoeffSpace d → Vec d}
    (hF : ∀ i, Integrable (fun a ↦ F a i) P) :
    ∫ a, vecDot c (F a) ∂P = vecDot c (fun i ↦ ∫ a, F a i ∂P) := by
  simp only [vecDot]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (hF i).const_mul (c i))]
  exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul (c i) (fun a ↦ F a i)

private theorem centered_integral_identity
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {C D J : CoeffSpace d → ℝ} {G F : CoeffSpace d → Vec d}
    {Pcen Qcen Mgrad Mflux : Vec d}
    (hD : Integrable D P) (hJ : Integrable J P)
    (hG : ∀ i, Integrable (fun a ↦ G a i) P)
    (hF : ∀ i, Integrable (fun a ↦ F a i) P)
    (hGmean : ∀ i, ∫ a, G a i ∂P = Pcen i + Mgrad i)
    (hFmean : ∀ i, ∫ a, F a i ∂P = Qcen i + Mflux i)
    (hpoint : ∀ a, C a = D a + J a - (1 / 2 : ℝ) * vecDot Qcen (G a) -
      (1 / 2 : ℝ) * vecDot Pcen (F a) +
        (1 / 2 : ℝ) * vecDot Pcen Qcen) :
    (∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Pcen Qcen =
      (∫ a, C a ∂P) - (∫ a, D a ∂P) +
        (1 / 2 : ℝ) * (vecDot Qcen Mgrad + vecDot Pcen Mflux) := by
  have hQG : Integrable (fun a ↦ vecDot Qcen (G a)) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ
      (fun i _ ↦ (hG i).const_mul (Qcen i))
  have hPF : Integrable (fun a ↦ vecDot Pcen (F a)) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ
      (fun i _ ↦ (hF i).const_mul (Pcen i))
  have hconst : Integrable
      (fun _ : CoeffSpace d ↦ (1 / 2 : ℝ) * vecDot Pcen Qcen) P :=
    integrable_const _
  have hright : Integrable (fun a ↦
      D a + J a - (1 / 2 : ℝ) * vecDot Qcen (G a) -
        (1 / 2 : ℝ) * vecDot Pcen (F a) +
          (1 / 2 : ℝ) * vecDot Pcen Qcen) P :=
    (((hD.add hJ).sub (hQG.const_mul (1 / 2 : ℝ))).sub
      (hPF.const_mul (1 / 2 : ℝ))).add hconst
  have hCeq : ∫ a, C a ∂P = ∫ a,
      D a + J a - (1 / 2 : ℝ) * vecDot Qcen (G a) -
        (1 / 2 : ℝ) * vecDot Pcen (F a) +
          (1 / 2 : ℝ) * vecDot Pcen Qcen ∂P :=
    integral_congr_ae (_root_.Filter.Eventually.of_forall hpoint)
  have hDJ : ∫ a, D a + J a ∂P =
      (∫ a, D a ∂P) + ∫ a, J a ∂P := integral_add hD hJ
  have hDJQ : ∫ a, (D a + J a) -
      (1 / 2 : ℝ) * vecDot Qcen (G a) ∂P =
      (∫ a, D a + J a ∂P) -
        ∫ a, (1 / 2 : ℝ) * vecDot Qcen (G a) ∂P :=
    integral_sub (hD.add hJ) (hQG.const_mul (1 / 2 : ℝ))
  have hDJQPF : ∫ a, ((D a + J a) -
      (1 / 2 : ℝ) * vecDot Qcen (G a)) -
        (1 / 2 : ℝ) * vecDot Pcen (F a) ∂P =
      (∫ a, (D a + J a) - (1 / 2 : ℝ) * vecDot Qcen (G a) ∂P) -
        ∫ a, (1 / 2 : ℝ) * vecDot Pcen (F a) ∂P :=
    integral_sub ((hD.add hJ).sub (hQG.const_mul (1 / 2 : ℝ)))
      (hPF.const_mul (1 / 2 : ℝ))
  have hConstIntegral : ∫ _a : CoeffSpace d,
      (1 / 2 : ℝ) * vecDot Pcen Qcen ∂P =
      (1 / 2 : ℝ) * vecDot Pcen Qcen := by
    rw [integral_const]
    simp [measureReal_def]
  have hTotal : (∫ a,
      (((D a + J a) - (1 / 2 : ℝ) * vecDot Qcen (G a)) -
        (1 / 2 : ℝ) * vecDot Pcen (F a)) +
          (1 / 2 : ℝ) * vecDot Pcen Qcen ∂P) =
      (∫ a, ((D a + J a) - (1 / 2 : ℝ) * vecDot Qcen (G a)) -
        (1 / 2 : ℝ) * vecDot Pcen (F a) ∂P) +
          ∫ _a : CoeffSpace d, (1 / 2 : ℝ) * vecDot Pcen Qcen ∂P := by
    exact integral_add
      (((hD.add hJ).sub (hQG.const_mul (1 / 2 : ℝ))).sub
        (hPF.const_mul (1 / 2 : ℝ))) hconst
  have hIntegral : (∫ a,
      D a + J a - (1 / 2 : ℝ) * vecDot Qcen (G a) -
        (1 / 2 : ℝ) * vecDot Pcen (F a) +
          (1 / 2 : ℝ) * vecDot Pcen Qcen ∂P) =
      (∫ a, D a ∂P) + (∫ a, J a ∂P) -
        (1 / 2 : ℝ) * (∫ a, vecDot Qcen (G a) ∂P) -
          (1 / 2 : ℝ) * (∫ a, vecDot Pcen (F a) ∂P) +
            (1 / 2 : ℝ) * vecDot Pcen Qcen := by
    rw [hTotal, hDJQPF, hDJQ, hDJ, integral_const_mul, integral_const_mul,
      hConstIntegral]
  rw [hCeq, hIntegral, integral_vecDot_const Qcen hG,
    integral_vecDot_const Pcen hF]
  have hGvec : (fun i ↦ ∫ a, G a i ∂P) = Pcen + Mgrad := by
    funext i
    exact hGmean i
  have hFvec : (fun i ↦ ∫ a, F a i ∂P) = Qcen + Mflux := by
    funext i
    exact hFmean i
  rw [hGvec, hFvec, vecDot_add_right, vecDot_add_right,
    vecDot_comm Qcen Pcen]
  ring

private theorem ofReal_abs_le_three_of_eq
    {J C D S : ℝ} (h : J = C - D + (1 / 2 : ℝ) * S) :
    ENNReal.ofReal |J| ≤ ENNReal.ofReal |C| + ENNReal.ofReal |D| +
      ENNReal.ofReal ((1 / 2 : ℝ) * |S|) := by
  have hreal : |J| ≤ |C| + |D| + (1 / 2 : ℝ) * |S| := by
    rw [h]
    calc
      |C - D + (1 / 2 : ℝ) * S| ≤ |C - D| + |(1 / 2 : ℝ) * S| :=
        abs_add_le _ _
      _ ≤ (|C| + |D|) + |(1 / 2 : ℝ) * S| :=
        add_le_add (by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le C (-D)) le_rfl
      _ = |C| + |D| + (1 / 2 : ℝ) * |S| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    ENNReal.ofReal |J| ≤ ENNReal.ofReal (|C| + |D| + (1 / 2 : ℝ) * |S|) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal |C| + ENNReal.ofReal |D| +
        ENNReal.ofReal ((1 / 2 : ℝ) * |S|) := by
      rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg C) (abs_nonneg D))
        (mul_nonneg (by norm_num) (abs_nonneg S)),
        ENNReal.ofReal_add (abs_nonneg C) (abs_nonneg D)]

private theorem integrable_responseJ_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r) P := by
  let X : BlockVec d := (-p, r)
  have hquad := (integrable_coarseBlock_quadratic hint X).const_mul (1 / 2 : ℝ)
  have hsub := hquad.sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock (adaptedDomain hq t) a p r).symm

private theorem integrable_adjointResponseJ_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      (a.transpose.coeffOn (adaptedDomain hq t)) p r) P := by
  let X : BlockVec d := (-p, r)
  let D := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hquad : Integrable (fun a ↦ blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCell q t) a.transpose) X)) P := by
    have hbase := integrable_coarseBlock_quadratic hint D
    refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change blockVecDot D (blockMatVecMul (coarseBlock (adaptedCell q t) a) D) =
      blockVecDot X (blockMatVecMul (coarseBlock (adaptedCell q t) a.transpose) X)
    rw [show coarseBlock (adaptedCell q t) a.transpose =
        blockMatMul (blockDiag 1 (-1))
          (blockMatMul (coarseBlock (adaptedCell q t) a) (blockDiag 1 (-1))) by
      simpa only [adaptedDomain_carrier] using
        (coarseBlock_transpose a (adaptedDomain hq t)),
      blockQuadratic_adjointSign_congr]
  have hsub := (hquad.const_mul (1 / 2 : ℝ)).sub
    (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X, adaptedDomain_carrier, Pi.sub_apply] using
    (responseJ_eq_coarseBlock (adaptedDomain hq t) a.transpose p r).symm

/-- A finite adapted mean makes the constant-skew primal terminal response
integrable. -/
theorem integrable_responseJ_subSkew_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P := by
  refine (integrable_responseJ_of_finiteAdaptedMean hq t hint p
    (r - matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (responseJ_subSkew (adaptedDomain hq t) a g hg p r).symm

/-- A finite adapted mean makes the independently transposed constant-skew
terminal response integrable. -/
theorem integrable_responseJ_adjointSubSkew_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) P := by
  refine (integrable_adjointResponseJ_of_finiteAdaptedMean hq t hint p
    (r + matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  change responseJ (adaptedDomain hq t) (a.transpose.coeffOn
      (adaptedDomain hq t)) p (r + matVecMul g p) =
    responseJ (adaptedDomain hq t) ((a.subSkew g hg).transpose.coeffOn
      (adaptedDomain hq t)) p r
  rw [CoeffSpace.transpose_subSkew]
  have h := responseJ_subSkew (adaptedDomain hq t) a.transpose
    (-g) (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    rw [neg_matVecMul, sub_neg_eq_add]
  rw [hload] at h
  exact h.symm

private theorem integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t a p r)) alpha) P := by
  let X : BlockVec d := (-p, r)
  cases alpha with
  | inl i =>
      have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inr i)
      have hadd := hmul.add (integrable_const (X.1 i))
      refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q t) a) X)
        (Sum.inr i) + X.1 i = toFullBlockVec (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) (Sum.inl i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
        toFullBlockVec, X]
  | inr i =>
      have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inl i)
      have hadd := hmul.add (integrable_const (X.2 i))
      refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q t) a) X)
        (Sum.inl i) + X.2 i = toFullBlockVec (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) (Sum.inr i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
        toFullBlockVec, X]

private theorem integrable_toFullBlockVec_blockCellAverage_adjointState
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t a.transpose p r)) alpha) P := by
  let X : BlockVec d := (-p, r)
  cases alpha with
  | inl i =>
      have h := (integrable_adjoint_coarseBlock_mulVec_apply
        (adaptedDomain hq t) hint X (Sum.inr i)).add (integrable_const (X.1 i))
      refine h.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q t)
        a.transpose) X) (Sum.inr i) + X.1 i = toFullBlockVec
          (blockCellAverage (adaptedCell q t)
            (diagonalWeakState hq t a.transpose p r)) (Sum.inl i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
        toFullBlockVec, X]
  | inr i =>
      have h := (integrable_adjoint_coarseBlock_mulVec_apply
        (adaptedDomain hq t) hint X (Sum.inl i)).add (integrable_const (X.2 i))
      refine h.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q t)
        a.transpose) X) (Sum.inl i) + X.2 i = toFullBlockVec
          (blockCellAverage (adaptedCell q t)
            (diagonalWeakState hq t a.transpose p r)) (Sum.inr i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
        toFullBlockVec, X]

private theorem integrable_matVecMul_of_integrable
    {P : Measure (CoeffSpace d)} (g : Mat d) {F : CoeffSpace d → Vec d}
    (hF : Integrable F P) : Integrable (fun a ↦ matVecMul g (F a)) P := by
  apply Integrable.of_eval
  intro i
  simpa only [matVecMul] using integrable_finsetSum Finset.univ
    (fun j _ ↦ (hF.eval j).const_mul (g i j))

private theorem integrable_toFullBlockVec_blockCellAverage_subSkew
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (a.subSkew g hg) p r)) alpha) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q t)
    (diagonalWeakState hq t a p (r - matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
        (P := P) hq t hint p (r - matVecMul g p) (Sum.inl i))
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
        (P := P) hq t hint p (r - matVecMul g p) (Sum.inr i))
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.sub (integrable_matVecMul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (a.subSkew g hg) p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦
      (blockCellAverage_diagonalWeakState_subSkew hq t a g hg p r).symm)
  cases alpha with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

private theorem integrable_toFullBlockVec_blockCellAverage_adjointSubSkew
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (a.subSkew g hg).transpose p r)) alpha) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q t)
    (diagonalWeakState hq t a.transpose p (r + matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_adjointState
        (P := P) hq t hint p (r + matVecMul g p) (Sum.inl i))
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_adjointState
        (P := P) hq t hint p (r + matVecMul g p) (Sum.inr i))
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.add (integrable_matVecMul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (a.subSkew g hg).transpose p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦ by
      change ((Y a).1, (Y a).2 + matVecMul g (Y a).1) = blockCellAverage
        (adaptedCell q t)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r)
      symm
      dsimp only [Y]
      rw [blockCellAverage_diagonalWeakState, blockCellAverage_diagonalWeakState]
      apply Prod.ext
      · exact averageGradient_centeredAdjointOptimizer_subSkew
          (adaptedDomain hq t) a g hg p r
      · exact averageFlux_centeredAdjointOptimizer_subSkew
          (adaptedDomain hq t) a g hg p r)
  cases alpha with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

private theorem integrableOn_cut_mul_state_readout [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) (alpha : BlockCoord d) :
    IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      toFullBlockVec (diagonalWeakState hq t a p r x) alpha)
      (adaptedCell q t) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
  obtain ⟨hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hcoord : MemScalarL2 (adaptedCell q t)
      (fun x ↦ toFullBlockVec (diagonalWeakState hq t a p r x) alpha) := by
    cases alpha with
    | inl i => simpa only [toFullBlockVec] using hgrad.eval i
    | inr i => simpa only [toFullBlockVec] using hflux.eval i
  exact (Selection.memScalarL2_bounded_mul
    (Selection.measurable_adaptedPreYoungCutoff hq t)
    (Selection.abs_adaptedPreYoungCutoff_le_two hq t) hcoord).integrable (by norm_num)

private theorem integrableOn_raw_state_readout
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) (alpha : BlockCoord d) :
    IntegrableOn (fun x ↦
      toFullBlockVec (diagonalWeakState hq t a p r x) alpha)
      (adaptedCell q t) volume := by
  obtain ⟨hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  cases alpha with
  | inl i => simpa only [toFullBlockVec, adaptedDomain_carrier] using
      integrableOn_component (U := adaptedDomain hq t) hgrad i
  | inr i => simpa only [toFullBlockVec, adaptedDomain_carrier] using
      integrableOn_component (U := adaptedDomain hq t) hflux i

private theorem integrableOn_cut_sub_one_mul_state_readout [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) (alpha : BlockCoord d) :
    IntegrableOn (fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
      toFullBlockVec (diagonalWeakState hq t a p r x) alpha)
      (adaptedCell q t) volume := by
  have hcut := integrableOn_cut_mul_state_readout hq t a p r alpha
  have hraw := integrableOn_raw_state_readout hq t a p r alpha
  refine hcut.sub hraw |>.congr (_root_.Filter.Eventually.of_forall fun x ↦ ?_)
  change adaptedPreYoungCutoff q hq t x *
      toFullBlockVec (diagonalWeakState hq t a p r x) alpha -
    toFullBlockVec (diagonalWeakState hq t a p r x) alpha =
      (adaptedPreYoungCutoff q hq t x - 1) *
        toFullBlockVec (diagonalWeakState hq t a p r x) alpha
  ring

private theorem integrableOn_cut_halfEnergy [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      ((1 / 2 : ℝ) * vecDot
        (diagonalWeakState hq t a p r x).1
        (diagonalWeakState hq t a p r x).2))
      (adaptedCell q t) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
  obtain ⟨hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hterm : ∀ i, IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      (diagonalWeakState hq t a p r x).1 i *
      (diagonalWeakState hq t a p r x).2 i) (adaptedCell q t) volume := by
    intro i
    have hweighted := Selection.memScalarL2_bounded_mul
      (Selection.measurable_adaptedPreYoungCutoff hq t)
      (Selection.abs_adaptedPreYoungCutoff_le_two hq t) (hgrad.eval i)
    have hmul := MemLp.integrable_mul hweighted (hflux.eval i)
    simpa only [IntegrableOn, volumeMeasureOn] using! hmul
  have hsum := integrable_finsetSum Finset.univ fun i _ ↦ hterm i
  refine hsum.const_mul (1 / 2 : ℝ) |>.congr
    (_root_.Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [vecDot]
  calc
    (1 / 2 : ℝ) * ∑ i,
        adaptedPreYoungCutoff q hq t x *
          (diagonalWeakState hq t a p r x).1 i *
          (diagonalWeakState hq t a p r x).2 i =
        ∑ i, (1 / 2 : ℝ) *
          (adaptedPreYoungCutoff q hq t x *
            (diagonalWeakState hq t a p r x).1 i *
            (diagonalWeakState hq t a p r x).2 i) :=
      Finset.mul_sum _ _ _
    _ = ∑ i, ((1 / 2 : ℝ) * adaptedPreYoungCutoff q hq t x) *
          ((diagonalWeakState hq t a p r x).1 i *
            (diagonalWeakState hq t a p r x).2 i) :=
      Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ((1 / 2 : ℝ) * adaptedPreYoungCutoff q hq t x) *
        ∑ i, (diagonalWeakState hq t a p r x).1 i *
          (diagonalWeakState hq t a p r x).2 i :=
      (Finset.mul_sum _ _ _).symm
    _ = adaptedPreYoungCutoff q hq t x *
        ((1 / 2 : ℝ) * ∑ i, (diagonalWeakState hq t a p r x).1 i *
          (diagonalWeakState hq t a p r x).2 i) := by ring

private theorem integrableOn_adaptedPreYoungCutoff [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    IntegrableOn (adaptedPreYoungCutoff q hq t) (adaptedCell q t) volume :=
  ((adaptedPreYoungCutoff_smooth hq t).continuous.integrable_of_hasCompactSupport
    (adaptedPreYoungCutoff_hasCompactSupport hq t)).integrableOn

/-- The primal centered response splits into the centered cutoff product, the
terminal cutoff-energy defect, and the two cutoff-defect means. -/
theorem ofReal_abs_profilePrimalCenteredResponse_le_cutoff_decomposition_of_integrable
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hcutoff : Integrable (fun a ↦
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P)
    (hlocalized : ∀ alpha, Integrable (fun a ↦
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          toFullBlockVec
            (diagonalWeakState hq t (a.subSkew g hg) p r x) alpha)) P) :
    let X := profilePrimalCenter P hq t
      (fun a ↦ a.subSkew g hg) p r
    let cut := adaptedPreYoungCutoff q hq t
    let M := profilePrimalCutoffMean P hq t
      (fun a ↦ a.subSkew g hg) cut p r
    let J := fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r
    let W := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x)
        (matVecMul (((a.subSkew g hg).coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x))))
    let C := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x - X.1)
        (matVecMul (((a.subSkew g hg).coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x) - X.2)))
    ENNReal.ofReal |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot X.1 X.2| ≤
      ENNReal.ofReal |∫ a, C a ∂P| +
        ENNReal.ofReal |∫ a, W a - J a ∂P| +
          ENNReal.ofReal ((1 / 2 : ℝ) *
            |vecDot X.2 M.1 + vecDot X.1 M.2|) := by
  dsimp only
  let sample := fun a : CoeffSpace d ↦ a.subSkew g hg
  let state := fun a : CoeffSpace d ↦ diagonalWeakState hq t (sample a) p r
  let cut := adaptedPreYoungCutoff q hq t
  let X := profilePrimalCenter P hq t sample p r
  let M := profilePrimalCutoffMean P hq t sample cut p r
  let J := fun a : CoeffSpace d ↦ responseJ (adaptedDomain hq t)
    ((sample a).coeffOn (adaptedDomain hq t)) p r
  let W := fun a : CoeffSpace d ↦ volumeAverage (adaptedCell q t) (fun x ↦
    cut x * ((1 / 2 : ℝ) * vecDot (state a x).1 (state a x).2))
  let D := fun a ↦ W a - J a
  let C := fun a : CoeffSpace d ↦ volumeAverage (adaptedCell q t) (fun x ↦
    cut x * ((1 / 2 : ℝ) * vecDot ((state a x).1 - X.1) ((state a x).2 - X.2)))
  let Graw := fun a : CoeffSpace d ↦ (blockCellAverage (adaptedCell q t) (state a)).1
  let Fraw := fun a : CoeffSpace d ↦ (blockCellAverage (adaptedCell q t) (state a)).2
  let Glocal := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ (cut x - 1) * (state a x).1 i)
  let Flocal := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ (cut x - 1) * (state a x).2 i)
  let Gcut := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ cut x * (state a x).1 i)
  let Fcut := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ cut x * (state a x).2 i)
  have hJ : Integrable J P := by
    simpa only [J, sample] using
      integrable_responseJ_subSkew_of_finiteAdaptedMean hq t hint g hg p r
  have hD : Integrable D P := by
    simpa only [D, W, J, state, sample, cut, Book.Ch02.average,
      adaptedDomain_carrier, diagonalWeakState, diagonalWeakOptimizer,
      centeredResponseOptimizer] using! hcutoff
  have hGraw : ∀ i, Integrable (fun a ↦ Graw a i) P := by
    intro i
    simpa only [Graw, state, sample, toFullBlockVec] using
      integrable_toFullBlockVec_blockCellAverage_subSkew
        (P := P) hq t hint g hg p r (Sum.inl i)
  have hFraw : ∀ i, Integrable (fun a ↦ Fraw a i) P := by
    intro i
    simpa only [Fraw, state, sample, toFullBlockVec] using
      integrable_toFullBlockVec_blockCellAverage_subSkew
        (P := P) hq t hint g hg p r (Sum.inr i)
  have hGlocal : ∀ i, Integrable (fun a ↦ Glocal a i) P := by
    intro i
    simpa only [Glocal, state, sample, cut, toFullBlockVec] using
      hlocalized (Sum.inl i)
  have hFlocal : ∀ i, Integrable (fun a ↦ Flocal a i) P := by
    intro i
    simpa only [Flocal, state, sample, cut, toFullBlockVec] using
      hlocalized (Sum.inr i)
  have hGsplit : ∀ a i, Gcut a i = Graw a i + Glocal a i := by
    intro a i
    have hrawSpace : IntegrableOn (fun x ↦
        (diagonalWeakState hq t (sample a) p r x).1 i) (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_raw_state_readout hq t (sample a) p r (Sum.inl i)
    have hlocalSpace : IntegrableOn (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).1 i) (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_cut_sub_one_mul_state_readout
          hq t (sample a) p r (Sum.inl i)
    dsimp only [Gcut, Graw, Glocal, state, cut, toFullBlockVec]
    change volumeAverage (adaptedCell q t) (fun x ↦
      adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a) p r x).1 i) =
      volumeAverage (adaptedCell q t) (fun x ↦
        (diagonalWeakState hq t (sample a) p r x).1 i) +
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).1 i)
    rw [show (fun x ↦ adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a) p r x).1 i) =
      (fun x ↦ (diagonalWeakState hq t (sample a) p r x).1 i) +
        fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).1 i by
        funext x
        change adaptedPreYoungCutoff q hq t x *
            (diagonalWeakState hq t (sample a) p r x).1 i =
          (diagonalWeakState hq t (sample a) p r x).1 i +
            (adaptedPreYoungCutoff q hq t x - 1) *
              (diagonalWeakState hq t (sample a) p r x).1 i
        ring,
      volumeAverage_add hrawSpace hlocalSpace]
  have hFsplit : ∀ a i, Fcut a i = Fraw a i + Flocal a i := by
    intro a i
    have hrawSpace : IntegrableOn (fun x ↦
        (diagonalWeakState hq t (sample a) p r x).2 i) (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_raw_state_readout hq t (sample a) p r (Sum.inr i)
    have hlocalSpace : IntegrableOn (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).2 i) (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_cut_sub_one_mul_state_readout
          hq t (sample a) p r (Sum.inr i)
    dsimp only [Fcut, Fraw, Flocal, state, cut, toFullBlockVec]
    change volumeAverage (adaptedCell q t) (fun x ↦
      adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a) p r x).2 i) =
      volumeAverage (adaptedCell q t) (fun x ↦
        (diagonalWeakState hq t (sample a) p r x).2 i) +
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).2 i)
    rw [show (fun x ↦ adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a) p r x).2 i) =
      (fun x ↦ (diagonalWeakState hq t (sample a) p r x).2 i) +
        fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a) p r x).2 i by
        funext x
        change adaptedPreYoungCutoff q hq t x *
            (diagonalWeakState hq t (sample a) p r x).2 i =
          (diagonalWeakState hq t (sample a) p r x).2 i +
            (adaptedPreYoungCutoff q hq t x - 1) *
              (diagonalWeakState hq t (sample a) p r x).2 i
        ring,
      volumeAverage_add hrawSpace hlocalSpace]
  have hGcut : ∀ i, Integrable (fun a ↦ Gcut a i) P := by
    intro i
    exact (hGraw i).add (hGlocal i) |>.congr
      (_root_.Filter.Eventually.of_forall fun a ↦ (hGsplit a i).symm)
  have hFcut : ∀ i, Integrable (fun a ↦ Fcut a i) P := by
    intro i
    exact (hFraw i).add (hFlocal i) |>.congr
      (_root_.Filter.Eventually.of_forall fun a ↦ (hFsplit a i).symm)
  have hGmean : ∀ i, ∫ a, Gcut a i ∂P = X.1 i + M.1 i := by
    intro i
    rw [integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ hGsplit a i),
      integral_add (hGraw i) (hGlocal i)]
    rfl
  have hFmean : ∀ i, ∫ a, Fcut a i ∂P = X.2 i + M.2 i := by
    intro i
    rw [integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ hFsplit a i),
      integral_add (hFraw i) (hFlocal i)]
    rfl
  have hpoint : ∀ a, C a = D a + J a -
      (1 / 2 : ℝ) * vecDot X.2 (Gcut a) -
      (1 / 2 : ℝ) * vecDot X.1 (Fcut a) +
      (1 / 2 : ℝ) * vecDot X.1 X.2 := by
    intro a
    have hs := volumeAverage_weighted_centered_vecDot
      (integrableOn_cut_halfEnergy hq t (sample a) p r)
      (fun i ↦ integrableOn_cut_mul_state_readout hq t (sample a) p r (Sum.inl i))
      (fun i ↦ integrableOn_cut_mul_state_readout hq t (sample a) p r (Sum.inr i))
      (integrableOn_adaptedPreYoungCutoff hq t)
      (Pcen := X.1) (Qcen := X.2)
    change C a = W a - (1 / 2 : ℝ) * vecDot X.2 (Gcut a) -
      (1 / 2 : ℝ) * vecDot X.1 (Fcut a) +
        (1 / 2 : ℝ) * vecDot X.1 X.2 * volumeAverage
          (adaptedCell q t) cut at hs
    rw [volumeAverage_adaptedPreYoungCutoff_eq_one hq t, mul_one] at hs
    rw [hs]
    dsimp only [D]
    ring
  have hid := centered_integral_identity hD hJ hGcut hFcut hGmean hFmean hpoint
  have hmain := ofReal_abs_le_three_of_eq hid
  simpa only [C, D, W, J, X, M, state, sample, cut, Book.Ch02.average,
    adaptedDomain_carrier, diagonalWeakState, diagonalWeakOptimizer,
    centeredResponseOptimizer] using! hmain

/-- The adjoint centered response splits into the centered cutoff product, the
terminal cutoff-energy defect, and the two cutoff-defect means. -/
theorem ofReal_abs_profileAdjointCenteredResponse_le_cutoff_decomposition_of_integrable
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hcutoff : Integrable (fun a ↦
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) P)
    (hlocalized : ∀ alpha, Integrable (fun a ↦
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          toFullBlockVec
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x) alpha)) P) :
    let X := profileAdjointCenter P hq t
      (fun a ↦ a.subSkew g hg) p r
    let cut := adaptedPreYoungCutoff q hq t
    let M := profileAdjointCutoffMean P hq t
      (fun a ↦ a.subSkew g hg) cut p r
    let J := fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r
    let W := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredAdjointOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x)
        (matVecMul (((a.subSkew g hg).transpose.coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x))))
    let C := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredAdjointOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x - X.1)
        (matVecMul (((a.subSkew g hg).transpose.coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x) - X.2)))
    ENNReal.ofReal |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot X.1 X.2| ≤
      ENNReal.ofReal |∫ a, C a ∂P| +
        ENNReal.ofReal |∫ a, W a - J a ∂P| +
          ENNReal.ofReal ((1 / 2 : ℝ) *
            |vecDot X.2 M.1 + vecDot X.1 M.2|) := by
  dsimp only
  let sample := fun a : CoeffSpace d ↦ a.subSkew g hg
  let state := fun a : CoeffSpace d ↦
    diagonalWeakAdjointState hq t (sample a) p r
  let cut := adaptedPreYoungCutoff q hq t
  let X := profileAdjointCenter P hq t sample p r
  let M := profileAdjointCutoffMean P hq t sample cut p r
  let J := fun a : CoeffSpace d ↦ responseJ (adaptedDomain hq t)
    ((sample a).transpose.coeffOn (adaptedDomain hq t)) p r
  let W := fun a : CoeffSpace d ↦ volumeAverage (adaptedCell q t) (fun x ↦
    cut x * ((1 / 2 : ℝ) * vecDot (state a x).1 (state a x).2))
  let D := fun a ↦ W a - J a
  let C := fun a : CoeffSpace d ↦ volumeAverage (adaptedCell q t) (fun x ↦
    cut x * ((1 / 2 : ℝ) * vecDot ((state a x).1 - X.1) ((state a x).2 - X.2)))
  let Graw := fun a : CoeffSpace d ↦ (blockCellAverage (adaptedCell q t) (state a)).1
  let Fraw := fun a : CoeffSpace d ↦ (blockCellAverage (adaptedCell q t) (state a)).2
  let Glocal := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ (cut x - 1) * (state a x).1 i)
  let Flocal := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ (cut x - 1) * (state a x).2 i)
  let Gcut := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ cut x * (state a x).1 i)
  let Fcut := fun a : CoeffSpace d ↦ fun i ↦ volumeAverage (adaptedCell q t)
    (fun x ↦ cut x * (state a x).2 i)
  have hJ : Integrable J P := by
    simpa only [J, sample] using
      integrable_responseJ_adjointSubSkew_of_finiteAdaptedMean hq t hint g hg p r
  have hD : Integrable D P := by
    simpa only [D, W, J, state, sample, cut, Book.Ch02.average,
      adaptedDomain_carrier, diagonalWeakAdjointState,
      diagonalWeakState, diagonalWeakOptimizer, centeredAdjointOptimizer,
      centeredResponseOptimizer] using! hcutoff
  have hGraw : ∀ i, Integrable (fun a ↦ Graw a i) P := by
    intro i
    simpa only [Graw, state, sample, diagonalWeakAdjointState_eq,
      toFullBlockVec] using
      integrable_toFullBlockVec_blockCellAverage_adjointSubSkew
        (P := P) hq t hint g hg p r (Sum.inl i)
  have hFraw : ∀ i, Integrable (fun a ↦ Fraw a i) P := by
    intro i
    simpa only [Fraw, state, sample, diagonalWeakAdjointState_eq,
      toFullBlockVec] using
      integrable_toFullBlockVec_blockCellAverage_adjointSubSkew
        (P := P) hq t hint g hg p r (Sum.inr i)
  have hGlocal : ∀ i, Integrable (fun a ↦ Glocal a i) P := by
    intro i
    simpa only [Glocal, state, sample, cut, diagonalWeakAdjointState_eq,
      toFullBlockVec] using hlocalized (Sum.inl i)
  have hFlocal : ∀ i, Integrable (fun a ↦ Flocal a i) P := by
    intro i
    simpa only [Flocal, state, sample, cut, diagonalWeakAdjointState_eq,
      toFullBlockVec] using hlocalized (Sum.inr i)
  have hGsplit : ∀ a i, Gcut a i = Graw a i + Glocal a i := by
    intro a i
    have hrawSpace : IntegrableOn (fun x ↦
        (diagonalWeakState hq t (sample a).transpose p r x).1 i)
        (adaptedCell q t) := by
      simpa only [toFullBlockVec] using integrableOn_raw_state_readout
        hq t (sample a).transpose p r (Sum.inl i)
    have hlocalSpace : IntegrableOn (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).1 i)
        (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_cut_sub_one_mul_state_readout
          hq t (sample a).transpose p r (Sum.inl i)
    dsimp only [Gcut, Graw, Glocal, state, cut,
      diagonalWeakAdjointState_eq, toFullBlockVec]
    change volumeAverage (adaptedCell q t) (fun x ↦
      adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a).transpose p r x).1 i) =
      volumeAverage (adaptedCell q t) (fun x ↦
        (diagonalWeakState hq t (sample a).transpose p r x).1 i) +
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).1 i)
    rw [show (fun x ↦ adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a).transpose p r x).1 i) =
      (fun x ↦ (diagonalWeakState hq t (sample a).transpose p r x).1 i) +
        fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).1 i by
        funext x
        change adaptedPreYoungCutoff q hq t x *
            (diagonalWeakState hq t (sample a).transpose p r x).1 i =
          (diagonalWeakState hq t (sample a).transpose p r x).1 i +
            (adaptedPreYoungCutoff q hq t x - 1) *
              (diagonalWeakState hq t (sample a).transpose p r x).1 i
        ring,
      volumeAverage_add hrawSpace hlocalSpace]
  have hFsplit : ∀ a i, Fcut a i = Fraw a i + Flocal a i := by
    intro a i
    have hrawSpace : IntegrableOn (fun x ↦
        (diagonalWeakState hq t (sample a).transpose p r x).2 i)
        (adaptedCell q t) := by
      simpa only [toFullBlockVec] using integrableOn_raw_state_readout
        hq t (sample a).transpose p r (Sum.inr i)
    have hlocalSpace : IntegrableOn (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).2 i)
        (adaptedCell q t) := by
      simpa only [toFullBlockVec] using
        integrableOn_cut_sub_one_mul_state_readout
          hq t (sample a).transpose p r (Sum.inr i)
    dsimp only [Fcut, Fraw, Flocal, state, cut,
      diagonalWeakAdjointState_eq, toFullBlockVec]
    change volumeAverage (adaptedCell q t) (fun x ↦
      adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a).transpose p r x).2 i) =
      volumeAverage (adaptedCell q t) (fun x ↦
        (diagonalWeakState hq t (sample a).transpose p r x).2 i) +
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).2 i)
    rw [show (fun x ↦ adaptedPreYoungCutoff q hq t x *
        (diagonalWeakState hq t (sample a).transpose p r x).2 i) =
      (fun x ↦ (diagonalWeakState hq t (sample a).transpose p r x).2 i) +
        fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
          (diagonalWeakState hq t (sample a).transpose p r x).2 i by
        funext x
        change adaptedPreYoungCutoff q hq t x *
            (diagonalWeakState hq t (sample a).transpose p r x).2 i =
          (diagonalWeakState hq t (sample a).transpose p r x).2 i +
            (adaptedPreYoungCutoff q hq t x - 1) *
              (diagonalWeakState hq t (sample a).transpose p r x).2 i
        ring,
      volumeAverage_add hrawSpace hlocalSpace]
  have hGcut : ∀ i, Integrable (fun a ↦ Gcut a i) P := by
    intro i
    exact (hGraw i).add (hGlocal i) |>.congr
      (_root_.Filter.Eventually.of_forall fun a ↦ (hGsplit a i).symm)
  have hFcut : ∀ i, Integrable (fun a ↦ Fcut a i) P := by
    intro i
    exact (hFraw i).add (hFlocal i) |>.congr
      (_root_.Filter.Eventually.of_forall fun a ↦ (hFsplit a i).symm)
  have hGmean : ∀ i, ∫ a, Gcut a i ∂P = X.1 i + M.1 i := by
    intro i
    rw [integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ hGsplit a i),
      integral_add (hGraw i) (hGlocal i)]
    rfl
  have hFmean : ∀ i, ∫ a, Fcut a i ∂P = X.2 i + M.2 i := by
    intro i
    rw [integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ hFsplit a i),
      integral_add (hFraw i) (hFlocal i)]
    rfl
  have hpoint : ∀ a, C a = D a + J a -
      (1 / 2 : ℝ) * vecDot X.2 (Gcut a) -
      (1 / 2 : ℝ) * vecDot X.1 (Fcut a) +
      (1 / 2 : ℝ) * vecDot X.1 X.2 := by
    intro a
    have hs := volumeAverage_weighted_centered_vecDot
      (integrableOn_cut_halfEnergy hq t (sample a).transpose p r)
      (fun i ↦ integrableOn_cut_mul_state_readout
        hq t (sample a).transpose p r (Sum.inl i))
      (fun i ↦ integrableOn_cut_mul_state_readout
        hq t (sample a).transpose p r (Sum.inr i))
      (integrableOn_adaptedPreYoungCutoff hq t)
      (Pcen := X.1) (Qcen := X.2)
    change C a = W a - (1 / 2 : ℝ) * vecDot X.2 (Gcut a) -
      (1 / 2 : ℝ) * vecDot X.1 (Fcut a) +
        (1 / 2 : ℝ) * vecDot X.1 X.2 * volumeAverage
          (adaptedCell q t) cut at hs
    rw [volumeAverage_adaptedPreYoungCutoff_eq_one hq t, mul_one] at hs
    rw [hs]
    dsimp only [D]
    ring
  have hid := centered_integral_identity hD hJ hGcut hFcut hGmean hFmean hpoint
  have hmain := ofReal_abs_le_three_of_eq hid
  simpa only [C, D, W, J, X, M, state, sample, cut, Book.Ch02.average,
    adaptedDomain_carrier, diagonalWeakAdjointState, diagonalWeakState,
    diagonalWeakOptimizer, centeredAdjointOptimizer,
    centeredResponseOptimizer] using! hmain

/-- Under finite primal weak quantity, response domination supplies every
integrability premise in the centered cutoff decomposition. -/
theorem ofReal_abs_profilePrimalCenteredResponse_le_cutoff_decomposition_of_domination
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (hdom : ∀ a : CoeffSpace d,
      0 ≤ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) ∧
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) ≤
        2 * responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) :
    let X := profilePrimalCenter P hq t
      (fun a ↦ a.subSkew g hg) p r
    let cut := adaptedPreYoungCutoff q hq t
    let M := profilePrimalCutoffMean P hq t
      (fun a ↦ a.subSkew g hg) cut p r
    let J := fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r
    let W := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x)
        (matVecMul (((a.subSkew g hg).coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x))))
    let C := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x - X.1)
        (matVecMul (((a.subSkew g hg).coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x) - X.2)))
    ENNReal.ofReal |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot X.1 X.2| ≤
      ENNReal.ofReal |∫ a, C a ∂P| +
        ENNReal.ofReal |∫ a, W a - J a ∂P| +
          ENNReal.ofReal ((1 / 2 : ℝ) *
            |vecDot X.2 M.1 + vecDot X.1 M.2|) := by
  have hcutoff :=
    integrable_affineSubSkewCutoffEnergyDefect_of_responseJ_domination
      hq t hint g hg p r hdom
  have hsplit := integrable_primal_adaptedFiveTermSplit_readouts
    hq hm0 (s := t) (t := t) (le_refl t) g hg p r hweak
  have hzero : (0 : Fin d → ℤ) ∈ alignedIndex q t t := by
    rw [alignedIndex_self hq t]
    simp
  have hlocalized : ∀ alpha, Integrable (fun a ↦
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          toFullBlockVec
            (diagonalWeakState hq t (a.subSkew g hg) p r x) alpha)) P := by
    intro alpha
    simpa only [adaptedCellAt_zero,
      volumeAverage_adaptedPreYoungCutoff_eq_one] using
      hsplit.2 0 hzero alpha
  exact ofReal_abs_profilePrimalCenteredResponse_le_cutoff_decomposition_of_integrable
    hq t hint g hg p r hcutoff hlocalized

/-- Under finite adjoint weak quantity, response domination supplies every
integrability premise in the centered cutoff decomposition. -/
theorem ofReal_abs_profileAdjointCenteredResponse_le_cutoff_decomposition_of_domination
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (hdom : ∀ a : CoeffSpace d,
      0 ≤ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) ∧
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) ≤
        2 * responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) :
    let X := profileAdjointCenter P hq t
      (fun a ↦ a.subSkew g hg) p r
    let cut := adaptedPreYoungCutoff q hq t
    let M := profileAdjointCutoffMean P hq t
      (fun a ↦ a.subSkew g hg) cut p r
    let J := fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r
    let W := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredAdjointOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x)
        (matVecMul (((a.subSkew g hg).transpose.coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x))))
    let C := fun a ↦ Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      cut x * ((1 / 2 : ℝ) * vecDot
        ((centeredAdjointOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r).toH1.grad x - X.1)
        (matVecMul (((a.subSkew g hg).transpose.coeffOn
          (adaptedDomain hq t)).toCoeffField x)
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x) - X.2)))
    ENNReal.ofReal |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot X.1 X.2| ≤
      ENNReal.ofReal |∫ a, C a ∂P| +
        ENNReal.ofReal |∫ a, W a - J a ∂P| +
          ENNReal.ofReal ((1 / 2 : ℝ) *
            |vecDot X.2 M.1 + vecDot X.1 M.2|) := by
  have hcutoff :=
    integrable_affineAdjointSubSkewCutoffEnergyDefect_of_responseJ_domination
      hq t hint g hg p r hdom
  have hsplit := integrable_adjoint_adaptedFiveTermSplit_readouts
    hq hm0 (s := t) (t := t) (le_refl t) g hg p r hweak
  have hzero : (0 : Fin d → ℤ) ∈ alignedIndex q t t := by
    rw [alignedIndex_self hq t]
    simp
  have hlocalized : ∀ alpha, Integrable (fun a ↦
      volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) *
          toFullBlockVec
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x) alpha)) P := by
    intro alpha
    simpa only [adaptedCellAt_zero,
      volumeAverage_adaptedPreYoungCutoff_eq_one] using
      hsplit.2 0 hzero alpha
  exact ofReal_abs_profileAdjointCenteredResponse_le_cutoff_decomposition_of_integrable
    hq t hint g hg p r hcutoff hlocalized

end

end HCPolySupport.HighContrast.Response
