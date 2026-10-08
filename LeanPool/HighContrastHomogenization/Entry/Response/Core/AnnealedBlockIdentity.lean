/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.OptimizerMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SkewShearCongruence

/-!
# High-contrast homogenization: Entry.Response.Core.AnnealedBlockIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed block identity

This file proves the annealed block identity for the doubled optimizer state: the annealed means
`Y^∓`, the expectations of the cell average of the doubled optimizer state, agree with the
annealed block of the recentred coefficients `respCoeffMinus`/`respCoeffPlus` under the block
congruence carried by the shear correction, the response-transfer identity `p.response.transfer`.
It records the resulting integrability and symmetry of the coarse block matrix, together with the
closed algebraic identities — for the full block matrix, its transpose, the matrix-valued integral
`matIntegral` and its behaviour under left and right scalar multiplication, and the shear
congruence of the coarse block — that the identification is built from.
-/

section
/-!
## HC bridge I, part 4 of 4: STEPs 4-5c and the annealed block conclusions

The annealed means `Y^∓` are the expectations of the cell average of the doubled optimizer
state, `E[(X_{u_t})_{U_t}] = Y^∓`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock annealedBlock coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem toFullBlockMat_eq_fromBlocks (M : BlockMat d) :
    toFullBlockMat M =
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
  ext (i | i) (j | j) <;> rfl

omit [NeZero d] in
private theorem ofFullBlockMat_fromBlocks (A B C D : Mat d) :
    ofFullBlockMat (Matrix.fromBlocks A B C D) = ⟨A, B, C, D⟩ := rfl

omit [NeZero d] in
private theorem matTranspose_neg_skew {g : Mat d} (hg : matTranspose g = -g) :
    matTranspose (-g) = -(-g) := by
  change (-g : Mat d)ᵀ = -(-g)
  rw [Matrix.transpose_neg]
  exact congrArg Neg.neg hg

/-! ### STEP 4: the block-level shear -/

omit [NeZero d] in
private theorem transpose_toFullBlockMat {A : BlockMat d} (h : IsSymmetricBlockMat A) :
    (toFullBlockMat A)ᵀ = toFullBlockMat A := by
  ext α β
  rw [Matrix.transpose_apply]
  have hb := h β α
  cases α <;> cases β <;> exact hb

omit [NeZero d] in
theorem isCoarseBlockMatrix_sub_skew {U : Set (Vec d)} {a : CoeffField d} {g : Mat d}
    (hg : matTranspose g = -g) (hquad : HasQuadraticMu U a) :
    IsCoarseBlockMatrix U (fun x => a x - g)
      ((blockCongr ⟨1, 0, g, 1⟩ (coarseBlockMatrix U a) : BlockMat d)) := by
  refine ⟨isSymmetricBlockMat_blockCongr _
    (isCoarseBlockMatrix_coarseBlockMatrix
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad)).1, ?_⟩
  intro P
  rw [Mu_sub_skew hg, Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hquad,
    blockVecDot_blockCongr]

omit [NeZero d] in
/-! ### STEP 5a: moving the constant congruence through the annealing integral -/

/-- Integrate a matrix-valued function entrywise with respect to the coefficient measure `P`. -/
@[expose]
public noncomputable def matIntegral {ι : Type*} (P : Measure (CoeffSpace d))
    (f : CoeffSpace d → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ a, f a i j ∂P

omit [NeZero d] in
private theorem integrable_entries_mul_left {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    ∀ i j, Integrable (fun a => (c * f a) i j) P := by
  classical
  intro i j
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun k _ => (hf k j).const_mul _

omit [NeZero d] in
private theorem matIntegral_mul_right {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    matIntegral P (fun a => f a * c) = matIntegral P f * c := by
  classical
  ext i j
  simp only [matIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf i k).mul_const (c k j)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_mul_const _ _

omit [NeZero d] in
private theorem matIntegral_mul_left {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    matIntegral P (fun a => c * f a) = c * matIntegral P f := by
  classical
  ext i j
  simp only [matIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf k j).const_mul (c i k)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_const_mul _ _

omit [NeZero d] in
private theorem blockMatEntry_eq_toFullBlockMat (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry A α β = toFullBlockMat A α β := by
  cases α <;> cases β <;> rfl

omit [NeZero d] in
/-- The annealed block of a constant congruence of the pathwise block is the congruence of the
annealed block: the congruence has constant coefficients, so it passes through the integral. -/
theorem annealedBlockOf_eq_blockCongr {P : Measure (CoeffSpace d)} {V : Set (Vec d)}
    (G : BlockMat d) (b : CoeffSpace d → CoeffField d)
    (hint : HasIntegrableCoarseBlock P V)
    (hb : ∀ a : CoeffSpace d, coarseBlockMatrix V (b a) = blockCongr G (coarseBlock V a)) :
    annealedBlockOf P V b = blockCongr G (annealedBlock P V) := by
  have hint' : ∀ α β, Integrable (fun a => toFullBlockMat (coarseBlock V a) α β) P := by
    intro α β
    have h := hint α β
    simpa only [blockMatEntry_eq_toFullBlockMat] using h
  have hfull : (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))
      = fun a => (toFullBlockMat G)ᵀ * toFullBlockMat (coarseBlock V a) * toFullBlockMat G := by
    funext a
    rw [hb a]
    simp only [blockCongr, toFullBlockMat_ofFullBlockMat]
  have hL : annealedBlockOf P V b
      = ofFullBlockMat (matIntegral P (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  have hR : annealedBlock P V
      = ofFullBlockMat (matIntegral P (fun a => toFullBlockMat (coarseBlock V a))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  rw [hL, hR, hfull,
    matIntegral_mul_right _ (integrable_entries_mul_left _ hint'),
    matIntegral_mul_left _ hint']
  simp only [blockCongr, toFullBlockMat_ofFullBlockMat]

/-! ### STEP 5b -/

omit [NeZero d] in
/-- The recentred annealed block is the congruence of the annealed block
(`p.response.transfer`, `Ehat_t^- = G^t E_t G` with `a_- = a - g`):
`E[A(U_t; a - g)] = G^t E[A(U_t; a)] G`.
The hypotheses `hquad` and `hint` are needed because `coarseBlockMatrix` is recovered from `Mu`
only by polarization and `annealedBlockOf` integrates entries. -/
theorem annealedBlockOf_respCoeffMinus_eq (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hquad : ∀ a : CoeffSpace d, HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    annealedBlockOf P (respCell jStar F t) (respCoeffMinus F) = respEhatMinus P jStar F t := by
  have hgskew : matTranspose (respg F) = -(respg F) := respg_isSkew F
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (respCell jStar F t) a) := fun a =>
    coarseBlockMatrix_sub_skew_eq_blockCongr hgskew (hquad a)
  rw [annealedBlockOf_eq_blockCongr (respG F) (respCoeffMinus F) hint hb]
  rfl

/-! ### STEP 5c -/

omit [NeZero d] in
/-- Congruences compose: `G₂ᵀ (G₁ᵀ A G₁) G₂ = (G₁ G₂)ᵀ A (G₁ G₂)`. -/
theorem blockCongr_blockCongr (G₁ G₂ A : BlockMat d) :
    blockCongr G₂ (blockCongr G₁ A)
      = blockCongr (ofFullBlockMat (toFullBlockMat G₁ * toFullBlockMat G₂)) A := by
  simp only [blockCongr, toFullBlockMat_ofFullBlockMat, Matrix.transpose_mul, Matrix.mul_assoc]

omit [NeZero d] in
/-- Congruence by `D = diag(Id, -Id)` is the flux sign flip of the adjoint symmetry. -/
theorem blockCongr_blockD (A : BlockMat d) :
    blockCongr (blockD d) A = blockMatFlipFlux A := by
  have hD : toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
    rw [toFullBlockMat_eq_fromBlocks]
    rfl
  rw [blockCongr, hD, toFullBlockMat_eq_fromBlocks A, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, neg_mul, mul_neg, neg_neg]
  rw [ofFullBlockMat_fromBlocks]
  rfl

omit [NeZero d] in
/-- `D · G_{-g} = G_g · D` in the full `2d × 2d` carrier: both are `[[Id, 0], [g, -Id]]`. -/
theorem blockD_mul_shear_neg (g : Mat d) :
    toFullBlockMat (blockD d) * toFullBlockMat (⟨1, 0, -g, 1⟩ : BlockMat d)
      = toFullBlockMat (⟨1, 0, g, 1⟩ : BlockMat d) * toFullBlockMat (blockD d) := by
  have hD : toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
    rw [toFullBlockMat_eq_fromBlocks]
    rfl
  have hG : ∀ c : Mat d, toFullBlockMat (⟨1, 0, c, 1⟩ : BlockMat d)
      = Matrix.fromBlocks (1 : Mat d) 0 c 1 := fun c => toFullBlockMat_eq_fromBlocks _
  rw [hD, hG, hG, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

omit [NeZero d] in
/-- The adjoint twin (`p.response.transfer`, `Ehat_t^+ = D Ehat_t^- D`).
The hypotheses `hquad` and `hint` are needed because `coarseBlockMatrix` is recovered from `Mu`
only by polarization and `annealedBlockOf` integrates entries. -/
theorem annealedBlockOf_respCoeffPlus_eq (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hquad : ∀ a : CoeffSpace d, HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    annealedBlockOf P (respCell jStar F t) (respCoeffPlus F) = respEhatPlus P jStar F t := by
  have hgskew : matTranspose (respg F) = -(respg F) := respg_isSkew F
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := matTranspose_neg_skew hgskew
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)
        = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
            toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d)))
            (coarseBlock (respCell jStar F t) a) := by
    intro a
    have h1 : respCoeffPlus F a
        = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
      funext x
      simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
    have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := respCell jStar F t)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
      (hasQuadraticMu_adjointCoeffField (hquad a))
    have h3 : coarseBlockMatrix (respCell jStar F t) (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock (respCell jStar F t) a) := by
      rw [coarseBlockMatrix_adjointCoeffField_of_exists
        (exists_coarseBlockMatrix_of_hasQuadraticMu (hquad a)), ← blockCongr_blockD]
      rfl
    rw [h1, h2, h3, blockCongr_blockCongr]
  rw [annealedBlockOf_eq_blockCongr _ (respCoeffPlus F) hint hb]
  have htar : respEhatPlus P jStar F t
      = blockCongr (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
          (annealedBlock P (respCell jStar F t)) := by
    rw [respEhatPlus, blockAdjoint, respEhatMinus, blockCongr_blockCongr]
    rfl
  rw [htar]
  congr 1
  exact congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F))

omit [NeZero d] in
/-- AUX (helper, NEW).  If the pathwise block of a recentred field family is a CONSTANT
congruence `Gᵀ 𝐀(V; a) G` of the pathwise coarse block, then each of its entries is a fixed real
linear combination of the entries of `𝐀(V; ·)`, hence `P`-integrable by `HasIntegrableCoarseBlock`.
This is the integrability input of `integral_blockResponseMean`. -/
theorem integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr
    {P : Measure (CoeffSpace d)} {V : Set (Vec d)} (G : BlockMat d)
    {b : CoeffSpace d → CoeffField d}
    (hint : HasIntegrableCoarseBlock P V)
    (hb : ∀ a : CoeffSpace d, coarseBlockMatrix V (b a) = blockCongr G (coarseBlock V a)) :
    ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P := by
  intro α β
  have hint' : ∀ κ l : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock V a) κ l) P := by
    intro κ l
    simpa only [blockMatEntry_eq_toFullBlockMat] using hint κ l
  have key : ∀ a : CoeffSpace d, blockMatEntry (coarseBlockMatrix V (b a)) α β
      = ∑ l : BlockCoord d,
          (∑ k : BlockCoord d,
            (toFullBlockMat G)ᵀ α k * toFullBlockMat (coarseBlock V a) k l)
          * toFullBlockMat G l β := by
    intro a
    rw [blockMatEntry_eq_toFullBlockMat, hb a]
    simp only [blockCongr, toFullBlockMat_ofFullBlockMat, Matrix.mul_apply]
  simp only [key]
  refine integrable_finsetSum _ fun l _ => Integrable.mul_const ?_ _
  exact integrable_finsetSum _ fun k _ => (hint' k l).const_mul _

omit [NeZero d] in
/-- AUX (helper, NEW).  The gradient coordinate of `blockResponseMean`:
`(x + R A x).1 i = x.1 i + (A_{lowerLeft} x.1) i + (A_{lowerRight} x.2) i`, visibly affine-linear
in the entries of `A`. -/
private theorem blockResponseMean_fst_apply (A : BlockMat d) (x : BlockVec d) (i : Fin d) :
    (blockResponseMean A x).1 i
      = x.1 i + ((∑ j, A.lowerLeft i j * x.1 j) + (∑ j, A.lowerRight i j * x.2 j)) := by
  simp only [blockResponseMean, Prod.fst_add, Pi.add_apply]
  rw [blockMatVecMul_blockSwap_fst]
  simp only [blockMatVecMul, Pi.add_apply, matVecMul]

omit [NeZero d] in
/-- AUX (helper, NEW).  The flux coordinate of `blockResponseMean`:
`(x + R A x).2 i = x.2 i + (A_{upperLeft} x.1) i + (A_{upperRight} x.2) i`. -/
private theorem blockResponseMean_snd_apply (A : BlockMat d) (x : BlockVec d) (i : Fin d) :
    (blockResponseMean A x).2 i
      = x.2 i + ((∑ j, A.upperLeft i j * x.1 j) + (∑ j, A.upperRight i j * x.2 j)) := by
  simp only [blockResponseMean, Prod.snd_add, Pi.add_apply]
  rw [blockMatVecMul_blockSwap_snd]
  simp only [blockMatVecMul, Pi.add_apply, matVecMul]

omit [NeZero d] in
/-- AUX (helper, NEW).  `blockResponseMean A x` is affine-linear in `A` for fixed `x`, so with
entrywise integrability of `a ↦ 𝐀(V; b a)` the entrywise annealing integral passes through it:
`(∫ (·)₁, ∫ (·)₂) = blockResponseMean (annealedBlockOf P V b) x`.  `P` is a probability measure,
so the constant term `x` survives the integral unchanged. -/
theorem integral_blockResponseMean (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (x : BlockVec d)
    (hA : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P) :
    ((fun i => ∫ a, (blockResponseMean (coarseBlockMatrix V (b a)) x).1 i ∂P),
     (fun i => ∫ a, (blockResponseMean (coarseBlockMatrix V (b a)) x).2 i ∂P))
      = blockResponseMean (annealedBlockOf P V b) x := by
  have hUL : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).upperLeft i j) P :=
    fun i j => hA (Sum.inl i) (Sum.inl j)
  have hUR : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).upperRight i j) P :=
    fun i j => hA (Sum.inl i) (Sum.inr j)
  have hLL : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).lowerLeft i j) P :=
    fun i j => hA (Sum.inr i) (Sum.inl j)
  have hLR : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).lowerRight i j) P :=
    fun i j => hA (Sum.inr i) (Sum.inr j)
  refine Prod.ext ?_ ?_
  · funext i
    simp only [blockResponseMean_fst_apply]
    have h1 : Integrable (fun _ : CoeffSpace d => x.1 i) P := integrable_const _
    have h2 : Integrable
        (fun a => ∑ j, (coarseBlockMatrix V (b a)).lowerLeft i j * x.1 j) P :=
      integrable_finsetSum _ fun j _ => (hLL i j).mul_const _
    have h3 : Integrable
        (fun a => ∑ j, (coarseBlockMatrix V (b a)).lowerRight i j * x.2 j) P :=
      integrable_finsetSum _ fun j _ => (hLR i j).mul_const _
    have h23 : Integrable (fun a => (∑ j, (coarseBlockMatrix V (b a)).lowerLeft i j * x.1 j)
        + ∑ j, (coarseBlockMatrix V (b a)).lowerRight i j * x.2 j) P := h2.add h3
    rw [integral_add h1 h23, integral_add h2 h3,
      integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => (hLL i j).mul_const (x.1 j),
      integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => (hLR i j).mul_const (x.2 j)]
    simp only [integral_const, probReal_univ, one_smul, integral_mul_const]
    rfl
  · funext i
    simp only [blockResponseMean_snd_apply]
    have h1 : Integrable (fun _ : CoeffSpace d => x.2 i) P := integrable_const _
    have h2 : Integrable
        (fun a => ∑ j, (coarseBlockMatrix V (b a)).upperLeft i j * x.1 j) P :=
      integrable_finsetSum _ fun j _ => (hUL i j).mul_const _
    have h3 : Integrable
        (fun a => ∑ j, (coarseBlockMatrix V (b a)).upperRight i j * x.2 j) P :=
      integrable_finsetSum _ fun j _ => (hUR i j).mul_const _
    have h23 : Integrable (fun a => (∑ j, (coarseBlockMatrix V (b a)).upperLeft i j * x.1 j)
        + ∑ j, (coarseBlockMatrix V (b a)).upperRight i j * x.2 j) P := h2.add h3
    rw [integral_add h1 h23, integral_add h2 h3,
      integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => (hUL i j).mul_const (x.1 j),
      integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => (hUR i j).mul_const (x.2 j)]
    simp only [integral_const, probReal_univ, one_smul, integral_mul_const]
    rfl

end

end HCPolySupport.HighContrast.Multiscale
end
