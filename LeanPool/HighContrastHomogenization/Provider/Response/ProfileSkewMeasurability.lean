/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewProfiles
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCentered
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakFullLp

/-!
# High-contrast homogenization: Provider.Response.ProfileSkewMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability after constant-skew recentering

The response energy has the same load covariance as the response functional.
The resulting identities transport the profile measurability inputs to a
constant-skew recentered coefficient sample without any invariance assumption
on its law.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem aemeasurable_prod_mk
    {P : Measure (CoeffSpace d)} {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : CoeffSpace d → X} {g : CoeffSpace d → Y}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    AEMeasurable (fun a ↦ (f a, g a)) P := by
  refine ⟨fun a ↦ (hf.mk f a, hg.mk g a),
    hf.measurable_mk.prodMk hg.measurable_mk, ?_⟩
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
  rw [hfa, hga]

private theorem aemeasurable_responseAverage_of_entries
    {P : Measure (CoeffSpace d)} {A : CoeffSpace d → BlockMat d}
    (hA : ∀ α β : BlockCoord d, AEMeasurable
      (fun a ↦ toFullBlockMat (A a) α β) P)
    (X : BlockVec d) :
    AEMeasurable (fun a ↦
      blockMatVecMul (blockR d) (blockMatVecMul (A a) X) + X) P := by
  have hfst : AEMeasurable (fun a ↦
      (blockMatVecMul (blockR d) (blockMatVecMul (A a) X) + X).1) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hleft : AEMeasurable (fun a ↦
        ∑ j, toFullBlockMat (A a) (Sum.inr i) (Sum.inl j) * X.1 j) P :=
      Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
        (hA (Sum.inr i) (Sum.inl j)).mul_const _
    have hright : AEMeasurable (fun a ↦
        ∑ j, toFullBlockMat (A a) (Sum.inr i) (Sum.inr j) * X.2 j) P :=
      Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
        (hA (Sum.inr i) (Sum.inr j)).mul_const _
    have hsum := (hleft.add hright).add_const (X.1 i)
    simpa only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
      blockMatVecMul_fst, blockMatVecMul_snd, matVecMul,
      toFullBlockMat, Matrix.of_apply] using! hsum
  have hsnd : AEMeasurable (fun a ↦
      (blockMatVecMul (blockR d) (blockMatVecMul (A a) X) + X).2) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hleft : AEMeasurable (fun a ↦
        ∑ j, toFullBlockMat (A a) (Sum.inl i) (Sum.inl j) * X.1 j) P :=
      Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
        (hA (Sum.inl i) (Sum.inl j)).mul_const _
    have hright : AEMeasurable (fun a ↦
        ∑ j, toFullBlockMat (A a) (Sum.inl i) (Sum.inr j) * X.2 j) P :=
      Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
        (hA (Sum.inl i) (Sum.inr j)).mul_const _
    have hsum := (hleft.add hright).add_const (X.2 i)
    simpa only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
      blockMatVecMul_fst, blockMatVecMul_snd, matVecMul,
      toFullBlockMat, Matrix.of_apply] using! hsum
  exact aemeasurable_prod_mk hfst hsnd

/-- The terminal spatial average of the primal optimizer state is almost
everywhere measurable. -/
theorem aemeasurable_blockCellAverage_diagonalWeakState [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (p r : Vec d) :
    AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t a p r)) P := by
  have hentries := Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t
  have hreading := aemeasurable_responseAverage_of_entries
    (fun α β ↦ (hentries α β).aemeasurable) ((-p, r) : BlockVec d)
  refine hreading.congr ?_
  filter_upwards [] with a
  exact (blockCellAverage_diagonalWeakState_eq_response hq t a p r).symm

/-- The terminal spatial average of the adjoint optimizer state is almost
everywhere measurable. -/
theorem aemeasurable_blockCellAverage_diagonalWeakAdjointState [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (p r : Vec d) :
    AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t a p r)) P := by
  let D : BlockMat d := blockDiag 1 (-1)
  have hbase := Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t
  have hentries : ∀ α β : BlockCoord d, AEMeasurable (fun a ↦
      toFullBlockMat
        (blockMatMul D (blockMatMul (coarseBlock (adaptedCell q t) a) D))
          α β) P := by
    intro α β
    simp only [toFullBlockMat_blockMatMul, Matrix.mul_apply]
    exact Finset.aemeasurable_fun_sum Finset.univ fun γ _ ↦
      (Finset.aemeasurable_fun_sum Finset.univ fun δ _ ↦
        ((hbase γ δ).aemeasurable.mul_const
          (toFullBlockMat D δ β))).const_mul (toFullBlockMat D α γ)
  have hreading := aemeasurable_responseAverage_of_entries hentries
    ((-p, r) : BlockVec d)
  refine hreading.congr ?_
  filter_upwards [] with a
  rw [diagonalWeakAdjointState_eq,
    blockCellAverage_diagonalWeakState_eq_response hq t a.transpose p r]
  rw [show blockMatMul D
      (blockMatMul (coarseBlock (adaptedCell q t) a) D) =
      coarseBlock (adaptedCell q t) a.transpose by
    simpa only [D, adaptedDomain_carrier] using
      (coarseBlock_transpose a (adaptedDomain hq t)).symm]

/-- Constant-skew recentering shears the averaged primal state after the load
correction. -/
theorem blockCellAverage_diagonalWeakState_subSkew [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    blockCellAverage (adaptedCell q t)
        (diagonalWeakState hq t (a.subSkew g hg) p r) =
      let Y := blockCellAverage (adaptedCell q t)
        (diagonalWeakState hq t a p (r - matVecMul g p))
      (Y.1, Y.2 - matVecMul g Y.1) := by
  rw [blockCellAverage_diagonalWeakState,
    blockCellAverage_diagonalWeakState]
  apply Prod.ext
  · exact averageGradient_centeredResponseOptimizer_subSkew
      (adaptedDomain hq t) a g hg p r
  · exact averageFlux_centeredResponseOptimizer_subSkew
      (adaptedDomain hq t) a g hg p r

/-- The terminal spatial average remains almost everywhere measurable after
constant-skew recentering. -/
theorem aemeasurable_blockCellAverage_diagonalWeakState_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (a.subSkew g hg) p r)) P := by
  let Y : CoeffSpace d → BlockVec d := fun a ↦
    blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t a p (r - matVecMul g p))
  have hY : AEMeasurable Y P :=
    aemeasurable_blockCellAverage_diagonalWeakState hq t p
      (r - matVecMul g p)
  have hYfst : AEMeasurable (fun a ↦ (Y a).1) P :=
    measurable_fst.comp_aemeasurable hY
  have hYsnd : AEMeasurable (fun a ↦ (Y a).2) P :=
    measurable_snd.comp_aemeasurable hY
  have hgY : AEMeasurable (fun a ↦ matVecMul g (Y a).1) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
      ((hYfst.eval j).const_mul (g i j))
  have htarget : AEMeasurable (fun a ↦
      ((Y a).1, (Y a).2 - matVecMul g (Y a).1)) P :=
    aemeasurable_prod_mk hYfst (hYsnd.sub hgY)
  refine htarget.congr ?_
  filter_upwards [] with a
  exact (blockCellAverage_diagonalWeakState_subSkew hq t a g hg p r).symm

/-- The terminal adjoint average remains almost everywhere measurable after
constant-skew recentering. -/
theorem aemeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew
    [NeZero d] {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)) P := by
  let Y : CoeffSpace d → BlockVec d := fun a ↦
    blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t a p (r + matVecMul g p))
  have hY : AEMeasurable Y P :=
    aemeasurable_blockCellAverage_diagonalWeakAdjointState hq t p
      (r + matVecMul g p)
  have hYfst := measurable_fst.comp_aemeasurable hY
  have hYsnd := measurable_snd.comp_aemeasurable hY
  have hgY : AEMeasurable (fun a ↦ matVecMul g (Y a).1) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦
      ((hYfst.eval j).const_mul (g i j))
  have htarget : AEMeasurable (fun a ↦
      ((Y a).1, (Y a).2 + matVecMul g (Y a).1)) P :=
    aemeasurable_prod_mk hYfst (hYsnd.add hgY)
  refine htarget.congr ?_
  filter_upwards [] with a
  symm
  rw [diagonalWeakAdjointState_eq, CoeffSpace.transpose_subSkew]
  have hcov := blockCellAverage_diagonalWeakState_subSkew hq t
    a.transpose (-g) (isSkewMat_neg hg) p r
  have hneg : ∀ x : Vec d, matVecMul (-g) x = -matVecMul g x := by
    intro x
    funext i
    simp only [matVecMul, Matrix.neg_apply, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [Y, hneg, sub_neg_eq_add] using! hcov

/-- The primal terminal energy transforms by subtracting the skew action from
the second load. -/
theorem diagonalWeakEnergy_subSkew [NeZero d] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (g : Mat d)
    (hg : IsSkewMat g) (p r : Vec d) :
    diagonalWeakEnergy hq t (a.subSkew g hg) p r =
      diagonalWeakEnergy hq t a p (r - matVecMul g p) := by
  have hJ := responseJ_subSkew (adaptedDomain hq t) a g hg p r
  rw [responseJ_eq_sq_diagonalWeakEnergy,
    responseJ_eq_sq_diagonalWeakEnergy] at hJ
  have hsq : diagonalWeakEnergy hq t (a.subSkew g hg) p r ^ 2 =
      diagonalWeakEnergy hq t a p (r - matVecMul g p) ^ 2 := by
    linarith only [hJ]
  exact (sq_eq_sq₀
    (diagonalWeakEnergy_nonneg hq t (a.subSkew g hg) p r)
    (diagonalWeakEnergy_nonneg hq t a p (r - matVecMul g p))).mp hsq

/-- The adjoint terminal energy transforms with the opposite load shift. -/
theorem diagonalWeakAdjointEnergy_subSkew [NeZero d] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (g : Mat d)
    (hg : IsSkewMat g) (p r : Vec d) :
    diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r =
      diagonalWeakAdjointEnergy hq t a p (r + matVecMul g p) := by
  rw [diagonalWeakAdjointEnergy_eq, CoeffSpace.transpose_subSkew,
    diagonalWeakAdjointEnergy_eq]
  have h := diagonalWeakEnergy_subSkew hq t a.transpose (-g)
    (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    funext i
    simp only [matVecMul, Matrix.neg_apply, Pi.sub_apply, Pi.add_apply]
    have hsum : ∑ x, -g i x * p x = -∑ x, g i x * p x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    ring
  rwa [hload] at h

/-- The recentered recent cell sum is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakCellSum_subSkew
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) (s : ℝ) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (g : Mat d) (hg : IsSkewMat g) :
    AEMeasurable (fun a ↦ diagonalWeakCellSum q t H s
      (skewBlockCongr g E) (a.subSkew g hg)) P := by
  refine (aemeasurable_diagonalWeakCellSum hq t H s hE hEpd).congr ?_
  filter_upwards [] with a
  exact (diagonalWeakCellSum_subSkew hq t H s E a g hg).symm

/-- The recentered all-scale maximum is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakMaximum_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} {rho : ℝ} {q : Mat d}
    (hq : q.PosDef) {t : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (g : Mat d) (hg : IsSkewMat g) :
    AEMeasurable (fun a ↦ diagonalWeakMaximum rho q t
      (skewBlockCongr g E) (a.subSkew g hg)) P := by
  refine (aemeasurable_diagonalWeakMaximum (rho := rho) (t := t)
    hq hE hEpd).congr ?_
  filter_upwards [] with a
  exact (diagonalWeakMaximum_subSkew hq rho t E a g hg).symm

/-- The recentered primal terminal energy is almost everywhere measurable at
the correctly shifted load. -/
theorem aemeasurable_diagonalWeakEnergy_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    AEMeasurable (fun a ↦
      diagonalWeakEnergy hq t (a.subSkew g hg) p r) P := by
  refine (aemeasurable_diagonalWeakEnergy hq t p
    (r - matVecMul g p)).congr ?_
  filter_upwards [] with a
  exact (diagonalWeakEnergy_subSkew hq t a g hg p r).symm

/-- The recentered adjoint terminal energy is almost everywhere measurable at
the correctly shifted load. -/
theorem aemeasurable_diagonalWeakAdjointEnergy_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    AEMeasurable (fun a ↦
      diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r) P := by
  refine (aemeasurable_diagonalWeakAdjointEnergy hq t p
    (r + matVecMul g p)).congr ?_
  filter_upwards [] with a
  exact (diagonalWeakAdjointEnergy_subSkew hq t a g hg p r).symm

end

end HCPolySupport.HighContrast.Response
