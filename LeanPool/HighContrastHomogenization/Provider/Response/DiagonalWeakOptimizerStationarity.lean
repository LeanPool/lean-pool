/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedVanishing
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewBlock
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormPartition
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentState
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileSkewMeasurability

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakOptimizerStationarity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-! # Stationarity of aligned optimizer averages

Aligned and centered optimizer averages differ only by sample translation.
Stationarity and the mean-one cutoff therefore cancel their weighted means. -/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Constant-skew recentering preserves aligned translation covariance. -/
theorem exists_blockCellAverage_diagonalWeakChildState_subSkew_eq_translateCoeff
    {l s : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) :
    ∃ z : Fin d → ℤ, adaptedCellCenter q s w = (fun i ↦ (z i : ℝ)) ∧
      ∀ a : CoeffSpace d, blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState (Recurrence.posDef_of_isRoundedGrid hgrid)
            s w (a.subSkew g hg) p r) = blockCellAverage (adaptedCell q s)
          (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid)
            s ((translateCoeff z a).subSkew g hg) p r) := by
  let hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  obtain ⟨z, hz, hresponse⟩ :=
    Recurrence.exists_adaptedResponse_eq_coarseBlock_translateCoeff hgrid hls w
  refine ⟨z, hz, fun a ↦ ?_⟩
  have hparent := coarseBlock_subSkew
    (adaptedDomain hq s) (translateCoeff z a) g hg
  have hshift : adaptedResponse q s w (a.subSkew g hg) = coarseBlock
      (adaptedCell q s) ((translateCoeff z a).subSkew g hg) := by
    rw [adaptedResponse_subSkew hq s w a g hg, hresponse]
    exact (by simpa only [adaptedDomain_carrier] using hparent.symm)
  rw [blockCellAverage_diagonalWeakChildState_eq_response,
    blockCellAverage_diagonalWeakState_eq_response, hshift]

/-- The recentered adjoint optimizer has its own aligned covariance. -/
theorem exists_blockCellAverage_diagonalWeakChildState_adjointSubSkew_eq_translateCoeff
    {l s : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) :
    ∃ z : Fin d → ℤ, adaptedCellCenter q s w = (fun i ↦ (z i : ℝ)) ∧
      ∀ a : CoeffSpace d, blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState (Recurrence.posDef_of_isRoundedGrid hgrid) s w
            (a.subSkew g hg).transpose p r) = blockCellAverage (adaptedCell q s)
          (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) s
            ((translateCoeff z a).subSkew g hg).transpose p r) := by
  let hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  obtain ⟨z, hz, hresponse⟩ :=
    Recurrence.exists_adaptedResponse_eq_coarseBlock_translateCoeff hgrid hls w
  refine ⟨z, hz, fun a ↦ ?_⟩
  have hparent := coarseBlock_subSkew
    (adaptedDomain hq s) (translateCoeff z a) g hg
  have hparentAdjoint := coarseBlock_transpose
    ((translateCoeff z a).subSkew g hg) (adaptedDomain hq s)
  have hshift : adaptedResponse q s w (a.subSkew g hg).transpose = coarseBlock
      (adaptedCell q s) ((translateCoeff z a).subSkew g hg).transpose := by
    rw [adaptedResponse_transpose hq s w (a.subSkew g hg),
      show coarseBlock (adaptedCell q s) ((translateCoeff z a).subSkew g hg).transpose =
        blockMatMul (blockDiag 1 (-1)) (blockMatMul (coarseBlock
          (adaptedCell q s) ((translateCoeff z a).subSkew g hg)) (blockDiag 1 (-1))) by
        simpa only [adaptedDomain_carrier] using hparentAdjoint,
      adaptedResponse_subSkew hq s w a g hg, hresponse,
      show coarseBlock (adaptedCell q s) ((translateCoeff z a).subSkew g hg) =
        skewBlockCongr g (coarseBlock (adaptedCell q s) (translateCoeff z a)) by
        simpa only [adaptedDomain_carrier] using hparent]
  rw [blockCellAverage_diagonalWeakChildState_eq_response,
    blockCellAverage_diagonalWeakState_eq_response, hshift]

private theorem integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ)
    (hint : HasFiniteAdaptedMean P q s) (p r : Vec d) (α : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s a p r)) α) P := by
  let X : BlockVec d := (-p, r)
  cases α with
  | inl i =>
      have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inr i)
      have hadd := hmul.add (integrable_const (X.1 i))
      refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s) a) X)
        (Sum.inr i) + X.1 i = toFullBlockVec (blockCellAverage (adaptedCell q s)
          (diagonalWeakState hq s a p r)) (Sum.inl i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply, toFullBlockVec, X]
  | inr i =>
      have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inl i)
      have hadd := hmul.add (integrable_const (X.2 i))
      refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s) a) X)
        (Sum.inl i) + X.2 i = toFullBlockVec (blockCellAverage (adaptedCell q s)
          (diagonalWeakState hq s a p r)) (Sum.inr i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply, toFullBlockVec, X]

private theorem integrable_toFullBlockVec_blockCellAverage_adjointState
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ) (hint : HasFiniteAdaptedMean P q s)
    (p r : Vec d) (α : BlockCoord d) : Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCell q s)
        (diagonalWeakState hq s a.transpose p r)) α) P := by
  let X : BlockVec d := (-p, r)
  cases α with
  | inl i =>
      have h := (integrable_adjoint_coarseBlock_mulVec_apply
        (adaptedDomain hq s) hint X (Sum.inr i)).add (integrable_const (X.1 i))
      refine h.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s)
        a.transpose) X) (Sum.inr i) + X.1 i = toFullBlockVec (blockCellAverage (adaptedCell q s)
          (diagonalWeakState hq s a.transpose p r)) (Sum.inl i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply, toFullBlockVec, X]
  | inr i =>
      have h := (integrable_adjoint_coarseBlock_mulVec_apply
        (adaptedDomain hq s) hint X (Sum.inl i)).add (integrable_const (X.2 i))
      refine h.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s)
        a.transpose) X) (Sum.inl i) + X.2 i = toFullBlockVec (blockCellAverage (adaptedCell q s)
          (diagonalWeakState hq s a.transpose p r)) (Sum.inr i)
      rw [blockCellAverage_diagonalWeakState_eq_response]
      simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply, toFullBlockVec, X]

private theorem integrable_matVecMul_of_integrable
    {P : Measure (CoeffSpace d)} (g : Mat d) {F : CoeffSpace d → Vec d}
    (hF : Integrable F P) : Integrable (fun a ↦ matVecMul g (F a)) P := by
  apply Integrable.of_eval
  intro i
  simpa only [matVecMul] using integrable_finsetSum Finset.univ
    (fun j _ ↦ (hF.eval j).const_mul (g i j))

private theorem integrable_toFullBlockVec_blockCellAverage_subSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ) (hint : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (α : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) α) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q s)
    (diagonalWeakState hq s a p (r - matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
        (P := P) hq s hint p (r - matVecMul g p) (Sum.inl i))
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_diagonalWeakState
        (P := P) hq s hint p (r - matVecMul g p) (Sum.inr i))
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.sub (integrable_matVecMul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦
      (blockCellAverage_diagonalWeakState_subSkew hq s a g hg p r).symm)
  cases α with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

private theorem integrable_toFullBlockVec_blockCellAverage_adjointSubSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ) (hint : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (α : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) α) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q s)
    (diagonalWeakState hq s a.transpose p (r + matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_adjointState
        (P := P) hq s hint p (r + matVecMul g p) (Sum.inl i))
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    simpa only [Y, toFullBlockVec] using
      (integrable_toFullBlockVec_blockCellAverage_adjointState
        (P := P) hq s hint p (r + matVecMul g p) (Sum.inr i))
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.add (integrable_matVecMul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦ by
      change ((Y a).1, (Y a).2 + matVecMul g (Y a).1) = blockCellAverage
        (adaptedCell q s) (diagonalWeakState hq s (a.subSkew g hg).transpose p r)
      symm
      dsimp only [Y]
      rw [blockCellAverage_diagonalWeakState, blockCellAverage_diagonalWeakState]
      apply Prod.ext
      · exact averageGradient_centeredAdjointOptimizer_subSkew (adaptedDomain hq s) a g hg p r
      · exact averageFlux_centeredAdjointOptimizer_subSkew (adaptedDomain hq s) a g hg p r)
  cases α with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

private theorem integrableOn_adaptedPreYoungCutoff
    [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    IntegrableOn (adaptedPreYoungCutoff q hq t) (adaptedCell q t) volume :=
  ((adaptedPreYoungCutoff_smooth hq t).continuous.integrable_of_hasCompactSupport
    (adaptedPreYoungCutoff_hasCompactSupport hq t)).integrableOn

private theorem avsum_cutoffWeight_mul_integral_eq_zero_of_covariance
    [NeZero d] {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {q : Mat d} (hq : q.PosDef)
    {s t : ℤ} (hst : s ≤ t) (F : (Fin d → ℤ) → CoeffSpace d → ℝ)
    (G : CoeffSpace d → ℝ) (hG : Integrable G P)
    (hcov : ∀ w ∈ alignedIndex q s t, ∃ z : Fin d → ℤ,
      ∀ a, F w a = G (translateCoeff z a)) :
    avsum (alignedIndex q s t) (fun w ↦
      (1 - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * ∫ a, F w a ∂P) = 0 := by
  let Z := alignedIndex q s t
  let c := ∫ a, G a ∂P
  have hchild : ∀ w ∈ Z, (∫ a, F w a ∂P) = c := by
    intro w hw; obtain ⟨z, hz⟩ := hcov w hw
    exact integral_eq_of_translateCoeff_covariance hstat hz hG
  have hpartition := avsum_volumeAverage_adaptedCellAt_eq hq hst
    (integrableOn_adaptedPreYoungCutoff hq t)
  have hZ : Z.Nonempty := alignedIndex_nonempty hq hst
  have hweights : avsum Z (fun w ↦
      1 - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) = 0 := by
    rw [show avsum Z (fun w ↦ 1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) = avsum Z (fun _ ↦ (1 : ℝ)) +
        avsum Z (fun w ↦ (-1 : ℝ) * volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) by
      rw [← avsum_add]
      apply congrArg (avsum Z); funext w; ring]
    rw [avsum_const hZ, avsum_const_mul, hpartition,
      volumeAverage_adaptedPreYoungCutoff_eq_one]
    ring
  calc
    avsum Z (fun w ↦ (1 - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * ∫ a, F w a ∂P) = avsum Z (fun w ↦
      (1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) * c) := by
      rw [avsum_eq, avsum_eq]
      congr 1
      exact Finset.sum_congr rfl fun w hw ↦ by rw [hchild w hw]
    _ = c * avsum Z (fun w ↦ 1 - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) := by
      rw [← avsum_const_mul]
      apply congrArg (avsum Z); funext w; ring
    _ = 0 := by rw [hweights, mul_zero]

/-- The same cancellation holds for the literal constant-skew primal state. -/
theorem avsum_one_sub_cutoffAverage_mul_integral_childState_subSkew_eq_zero
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) (α : BlockCoord d) :
    avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage
      (adaptedCellAt q s w) (adaptedPreYoungCutoff q
        (Recurrence.posDef_of_isRoundedGrid hgrid) t)) * ∫ a, toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w) (diagonalWeakChildState
        (Recurrence.posDef_of_isRoundedGrid hgrid) s w (a.subSkew g hg) p r)) α ∂P) = 0 := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply avsum_cutoffWeight_mul_integral_eq_zero_of_covariance hstat hq hst
    (fun w a ↦ toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg) p r)) α)
    (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) α)
    (integrable_toFullBlockVec_blockCellAverage_subSkew
      hq s hint g hg p r α)
  intro w _
  obtain ⟨z, _, hz⟩ :=
    exists_blockCellAverage_diagonalWeakChildState_subSkew_eq_translateCoeff
      hgrid hls w g hg p r
  exact ⟨z, fun a ↦ congrArg (fun X : BlockVec d ↦ toFullBlockVec X α) (hz a)⟩

/-- The literal constant-skew adjoint state has the independent cancellation. -/
theorem avsum_one_sub_cutoffAverage_mul_integral_childState_adjointSubSkew_eq_zero
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) (α : BlockCoord d) :
    avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage
      (adaptedCellAt q s w) (adaptedPreYoungCutoff q
        (Recurrence.posDef_of_isRoundedGrid hgrid) t)) * ∫ a, toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w) (diagonalWeakChildState
        (Recurrence.posDef_of_isRoundedGrid hgrid) s w
          (a.subSkew g hg).transpose p r)) α ∂P) = 0 := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply avsum_cutoffWeight_mul_integral_eq_zero_of_covariance hstat hq hst
    (fun w a ↦ toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r)) α)
    (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) α)
    (integrable_toFullBlockVec_blockCellAverage_adjointSubSkew
      hq s hint g hg p r α)
  intro w _
  obtain ⟨z, _, hz⟩ :=
    exists_blockCellAverage_diagonalWeakChildState_adjointSubSkew_eq_translateCoeff
      hgrid hls w g hg p r
  exact ⟨z, fun a ↦ congrArg (fun X : BlockVec d ↦ toFullBlockVec X α) (hz a)⟩

end

end HCPolySupport.HighContrast.Response
