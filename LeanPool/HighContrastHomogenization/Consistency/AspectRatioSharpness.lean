/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Attainment
public import LeanPool.HighContrastHomogenization.Annealed.Witness
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone

/-!
# High-contrast homogenization: Consistency.AspectRatioSharpness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sharpness of the lower bound on the reference aspect ratio

This module checks the definition `aspectRatio`, the Lean encoding of the
reference aspect ratio `Π = Λ_0 / λ_0` of `e.reference.aspect.ratio`, with
`bigLambdaRef` as `Λ_0` and `lambdaRef` as `λ_0`.

Were the check to fail — if the encoding were not the paper's `Π`, or if
`1 ≤ Π` held for a reason unrelated to the ordering of the Schur blocks — then
the ordering hypothesis `σ_* ≤ σ` of the conditional lower bound would be
vacuous, and the estimates written with `2 + Π * K` would bound a quantity other
than the one the paper prints.  This module is a consistency check of that
definition and is not a result of the paper.

The ratio is bounded below by one once the two symmetric Schur blocks of
`e.annealed.schur` are ordered, `σ_* ≤ σ`; that implication is proved in
`HCPoly.Geometry.AspectRatioOrder`.  This module shows the ordering is needed:
without it the bound fails, and it fails at exactly the hypotheses the coarse
ellipticity assumption `e.coarse.ellipticity` places on its reference block.

The witness is the doubled dilation `c · I`, whose Schur skew vanishes and whose
Schur `σ` is `c · I`, so that `Λ_0 = c`, `λ_0 = c⁻¹` and `Π = c²`.  At `c = 1/2`
in dimension two this is a symmetric positive definite doubled block of aspect
ratio one quarter.  The same block carries a complete instance of the coarse
ellipticity assumption, so the assumption structure alone does not force the
bound; the theorems that consume it quantify a probability measure separately,
which the instance below does not provide.

The module closes with the transfer step in the direction the coarse ellipticity
assumption supplies: the aspect ratio is monotone in the doubled Loewner order,
proved in `HCPoly.Geometry.AspectRatioMonotone`, so a block dominated by the
reference block passes its own lower bound upward.

A last remark on dimension: in dimension zero every Loewner comparison is
vacuous and the aspect ratio collapses to zero, so the positive-dimension
hypothesis carried by the bound is not decorative.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Quadratic-form helpers -/

private theorem matVecMul_one_ar (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem zero_matVecMul_ar (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

private theorem quad_one_ar (x : Vec d) :
    vecDot x (matVecMul (1 : Mat d) x) = vecNormSq x := by
  rw [matVecMul_one_ar]
  rfl

private theorem quad_smul_one_ar (t : ℝ) (x : Vec d) :
    vecDot x (matVecMul (t • (1 : Mat d)) x) = t * vecNormSq x := by
  rw [smul_matVecMul, matVecMul_one_ar, vecDot_smul_right]
  rfl

/-- The quadratic form of a congruence `Dᵗ M D`. -/
private theorem quad_conj_ar (D M : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose D * M * D) x) =
      vecDot (matVecMul D x) (matVecMul M (matVecMul D x)) := by
  rw [mul_assoc, ← matVecMul_mul, vecDot_matVecMul_transpose, matVecMul_mul]

private theorem vecNormSq_single_ar (j : Fin d) :
    vecNormSq (Pi.single j (1 : ℝ)) = 1 := by
  change vecDot (Pi.single j (1 : ℝ)) (Pi.single j (1 : ℝ)) = 1
  simp [vecDot, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/-- In a nonempty dimension there is a unit vector.  (For `d = 0` every
`MatLoewnerLE` holds, `specBound` collapses to `0`, and `aspectRatio = 0`.) -/
private theorem exists_vecNormSq_eq_one (hd : 0 < d) : ∃ e : Vec d, vecNormSq e = 1 :=
  ⟨Pi.single ⟨0, hd⟩ (1 : ℝ), vecNormSq_single_ar _⟩

private theorem vecNormSq_pos_of_ne_zero {x : Vec d} (hx : x ≠ 0) : 0 < vecNormSq x := by
  rcases lt_or_eq_of_le (vecNormSq_nonneg x) with h | h
  · exact h
  · exfalso
    refine hx (funext fun i => ?_)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x i * x i :=
      fun i _ => mul_self_nonneg (x i)
    have hz : ∑ i, x i * x i = 0 := h.symm
    exact mul_self_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_univ i))

/-- `specBound (c • 1) = c` in a nonempty dimension. -/
private theorem specBound_smul_one_ar {c : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    specBound (c • (1 : Mat d)) = c := by
  refine le_antisymm (specBound_le hc (MatLoewnerLE.refl _)) ?_
  obtain ⟨e, he⟩ := exists_vecNormSq_eq_one (d := d) hd
  have hq := matLoewnerLE_specBound_smul_one (c • (1 : Mat d)) e
  rw [quad_smul_one_ar, quad_smul_one_ar, he] at hq
  linarith only [hq]

/-- The threshold form of `bigLambdaRef`, in terms of `skewCorrectedForm`. -/
private theorem bigLambdaRef_eq_sInf_ar (E : BlockMat d) :
    bigLambdaRef E = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (t • (1 : Mat d))} := rfl

/-! ## Part 1: the counterexample

`diagBlock d c` is the doubled block matrix `c • I` on both diagonal slots.  It is
symmetric and, for `c > 0`, positive definite, so it satisfies exactly the two
hypotheses `refBlock_isSymm` and `refBlock_posDef` of
`HCPoly.Frozen.CoarseEllipticityDagger`.  Its Schur data are `k = 0`, `σ = c • I`,
`σ_*^{-1} = c • I` (so `σ_* = c⁻¹ • I`), hence `Λ_0 = c`, `λ_0 = c⁻¹`, and
`Π = c²`, which is `< 1` for `c < 1`. -/

/-- The doubled block matrix with `c • I` in both diagonal slots. -/
@[expose]
def diagBlock (d : ℕ) (c : ℝ) : BlockMat d :=
  { upperLeft := c • (1 : Mat d)
    upperRight := 0
    lowerLeft := 0
    lowerRight := c • (1 : Mat d) }

theorem isSymmetricBlockMat_diagBlock (c : ℝ) :
    IsSymmetricBlockMat (diagBlock d c) := by
  have hsm : ∀ i j : Fin d, (c • (1 : Mat d)) i j = (c • (1 : Mat d)) j i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.one_apply_ne (Ne.symm hij)]
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j => exact hsm i j
      | inr j => rfl
  | inr i =>
      cases β with
      | inl j => rfl
      | inr j => exact hsm i j

theorem blockPosDef_diagBlock {c : ℝ} (hc : 0 < c) :
    Book.Ch02.BlockPosDef (diagBlock d c) := by
  rintro ⟨p, q⟩ hX
  have hquad : blockVecDot (p, q) (blockMatVecMul (diagBlock d c) (p, q)) =
      c * vecNormSq p + c * vecNormSq q := by
    change vecDot p (matVecMul (c • (1 : Mat d)) p + matVecMul (0 : Mat d) q) +
        vecDot q (matVecMul (0 : Mat d) p + matVecMul (c • (1 : Mat d)) q) = _
    rw [zero_matVecMul_ar, zero_matVecMul_ar, add_zero, zero_add,
      quad_smul_one_ar, quad_smul_one_ar]
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX (by rw [hcon.1, hcon.2]; rfl)
  rw [hquad]
  rcases hpq with h | h
  · have h1 : 0 < c * vecNormSq p := mul_pos hc (vecNormSq_pos_of_ne_zero h)
    have h2 : 0 ≤ c * vecNormSq q := mul_nonneg hc.le (vecNormSq_nonneg q)
    linarith only [h1, h2]
  · have h1 : 0 ≤ c * vecNormSq p := mul_nonneg hc.le (vecNormSq_nonneg p)
    have h2 : 0 < c * vecNormSq q := mul_pos hc (vecNormSq_pos_of_ne_zero h)
    linarith only [h1, h2]

theorem schurSkew_diagBlock (c : ℝ) : schurSkew (diagBlock d c) = 0 := by
  simp [schurSkew, diagBlock]

theorem schurSigma_diagBlock (c : ℝ) :
    schurSigma (diagBlock d c) = c • (1 : Mat d) := by
  rw [schurSigma, schurSkew_diagBlock, Matrix.mul_zero, sub_zero]
  rfl

theorem skewCorrectedForm_diagBlock (c : ℝ) (h : Mat d) :
    skewCorrectedForm (diagBlock d c) h =
      c • (1 : Mat d) + matTranspose (-h) * (c • (1 : Mat d)) * (-h) := by
  rw [skewCorrectedForm, schurSigma_diagBlock, schurSkew_diagBlock, zero_sub]
  rfl

theorem bigLambdaRef_diagBlock {c : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    bigLambdaRef (diagBlock d c) = c := by
  rw [bigLambdaRef_eq_sInf_ar]
  have hmem : c ∈ {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm (diagBlock d c) h) (t • (1 : Mat d))} := by
    refine ⟨hc, 0, isSkewMat_zero, ?_⟩
    rw [skewCorrectedForm_diagBlock, neg_zero, Matrix.mul_zero, add_zero]
    exact MatLoewnerLE.refl _
  refine le_antisymm (csInf_le ⟨0, fun t ht => ht.1⟩ hmem) (le_csInf ⟨c, hmem⟩ ?_)
  rintro t ⟨-, h, -, hle⟩
  rw [skewCorrectedForm_diagBlock] at hle
  obtain ⟨e, he⟩ := exists_vecNormSq_eq_one (d := d) hd
  have hq := hle e
  rw [add_matVecMul, vecDot_add_right, quad_conj_ar, quad_smul_one_ar,
    quad_smul_one_ar, quad_smul_one_ar, he] at hq
  have hnn : 0 ≤ c * vecNormSq (matVecMul (-h) e) :=
    mul_nonneg hc (vecNormSq_nonneg _)
  linarith only [hq, hnn]

theorem lambdaRef_diagBlock {c : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    lambdaRef (diagBlock d c) = c⁻¹ := by
  rw [lambdaRef]
  change (specBound (c • (1 : Mat d)))⁻¹ = c⁻¹
  rw [specBound_smul_one_ar hc hd]

/-- **The aspect ratio of the diagonal block is `c²`.** -/
theorem aspectRatio_diagBlock {c : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    aspectRatio (diagBlock d c) = c ^ 2 := by
  rw [aspectRatio, bigLambdaRef_diagBlock hc hd, lambdaRef_diagBlock hc hd,
    div_eq_mul_inv, inv_inv]
  ring

/-- **The witness.**  `E = (1/2) • I` on both diagonal slots, in dimension `d = 2`. -/
@[expose]
def counterexampleBlock : BlockMat 2 := diagBlock 2 (1 / 2 : ℝ)

theorem counterexampleBlock_isSymm : IsSymmetricBlockMat counterexampleBlock :=
  isSymmetricBlockMat_diagBlock _

theorem counterexampleBlock_posDef : Book.Ch02.BlockPosDef counterexampleBlock :=
  blockPosDef_diagBlock (by norm_num)

theorem counterexampleBlock_aspectRatio : aspectRatio counterexampleBlock = 1 / 4 := by
  rw [counterexampleBlock, aspectRatio_diagBlock (by norm_num) (by norm_num)]
  norm_num

/-- **`1 ≤ aspectRatio E` is FALSE from the frozen hypothesis block.**
There is a symmetric, positive definite doubled block matrix — the two hypotheses
`refBlock_isSymm` and `refBlock_posDef` of `CoarseEllipticityDagger` — whose
aspect ratio is `1/4`. -/
theorem not_forall_one_le_aspectRatio :
    ∃ E : BlockMat 2, IsSymmetricBlockMat E ∧ Book.Ch02.BlockPosDef E ∧
      aspectRatio E < 1 :=
  ⟨counterexampleBlock, counterexampleBlock_isSymm, counterexampleBlock_posDef, by
    rw [counterexampleBlock_aspectRatio]; norm_num⟩

/-! ## Part 1b: the frozen assumption structure itself

`HCPoly.Frozen.CoarseEllipticityDagger` carries no `IsProbabilityMeasure` field
(the consuming frozen theorems supply that hypothesis separately), so under the
zero law its `coarse_bound` — the only field that constrains `E` beyond symmetry
and positive definiteness — is vacuous, and the structure holds at a reference
block with `Π = 1/4`. -/

open MeasureTheory in
theorem coarseEllipticityDagger_counterexampleBlock :
    HCPoly.Frozen.CoarseEllipticityDagger (0 : Measure (CoeffSpace 2)) 0
      counterexampleBlock Real.exp 2 (fun _ => 0) where
  g_mem := Set.mem_Ico.2 ⟨le_rfl, one_pos⟩
  refBlock_isSymm := counterexampleBlock_isSymm
  refBlock_posDef := counterexampleBlock_posDef
  gauge_admissible := admissiblePsi_exp
  one_lt_growthWitness := by norm_num
  gauge_growth := hasPsiGrowth_exp
  source_measurable := measurable_const
  source_nonneg := fun _ => le_rfl
  source_tail := by
    intro t ht
    rw [upperTailEvent_zero ht, measureReal_empty]
    positivity
  coarse_bound := by
    rw [_root_.Filter.Eventually, MeasureTheory.ae_zero]
    exact _root_.Filter.mem_bot

/-- **The frozen assumption structure does not force `1 ≤ Π`.** -/
theorem exists_coarseEllipticityDagger_aspectRatio_lt_one :
    ∃ (P : MeasureTheory.Measure (CoeffSpace 2)) (g : ℝ) (E : BlockMat 2)
      (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace 2 → ℝ),
      HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S ∧ aspectRatio E < 1 :=
  ⟨0, 0, counterexampleBlock, Real.exp, 2, fun _ => 0,
    coarseEllipticityDagger_counterexampleBlock, by
      rw [counterexampleBlock_aspectRatio]; norm_num⟩

/-- The nonempty-dimension hypothesis of the conditional theorem is not
decorative: in dimension `0` every Loewner comparison is vacuous, `specBound`
collapses to `0`, and `Π = 0 / 0 = 0 < 1`. -/
theorem aspectRatio_eq_zero_dim_zero (E : BlockMat 0) : aspectRatio E = 0 := by
  have htriv : ∀ A B : Mat 0, MatLoewnerLE A B := by
    intro A B x
    simp [vecDot]
  have hs : specBound E.lowerRight = 0 :=
    le_antisymm (specBound_le le_rfl (htriv _ _)) (specBound_nonneg _)
  have hL : bigLambdaRef E = 0 := by
    rw [bigLambdaRef_eq_sInf_ar]
    exact le_antisymm
      (csInf_le ⟨0, fun t ht => ht.1⟩ ⟨le_rfl, 0, isSkewMat_zero, htriv _ _⟩)
      (Real.sInf_nonneg fun _ ht => ht.1)
  rw [aspectRatio, lambdaRef, hs, hL, inv_zero, div_zero]

/-! ## The transfer step -/

/-- A lower bound on the aspect ratio passes upward along the doubled Loewner
order.  Read with the coarse ellipticity assumption at its undiscounted scale,
where the comparison block is the reference block itself, this is the shape in
which a bound on the coarse response would deliver one on the reference block. -/
theorem one_le_aspectRatio_of_blockMatLoewnerLE {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) (hone : 1 ≤ aspectRatio A) : 1 ≤ aspectRatio E :=
  le_trans hone (aspectRatio_mono hAsymm hApos hEsymm hEpos hle)

end

end HighContrast
end HCPolySupport
