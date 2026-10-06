/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Consistency.WitnessField

/-!
# High-contrast homogenization: Annealed.WitnessBlock

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# The coarse response of the constant identity field is uniformly dominated

The reference block of `e.coarse.ellipticity` has to dominate the coarse
response `𝐀(z + □_k; a)` of every standard aligned cube, at every scale.  For the
constant identity field the domination is scale and location uniform, and it is
obtained from a single admissible competitor: the constant state.  Its averaged
energy is the doubled square norm of the prescribed boundary data, independently
of the cube; combined with the nonnegativity of the variational quantity this
bounds every entry of the coarse response by an absolute constant, hence its
quadratic form by a multiple of the doubled identity.

Consequently no discount factor is needed: the domination holds at the exponent
`g = 0` of `Set.Ico 0 1`, at which `3^{g(m-k)}` is one.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The doubled square norm and the doubled identity -/

/-- The square norm of a doubled vector. -/
@[expose]
def blockNormSq (X : BlockVec d) : ℝ := vecNormSq X.1 + vecNormSq X.2

theorem blockNormSq_nonneg (X : BlockVec d) : 0 ≤ blockNormSq X :=
  add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)

theorem vecNormSq_pos {x : Vec d} (hx : x ≠ 0) : 0 < vecNormSq x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.1 hx
  have hterm : (0 : ℝ) < x i * x i := mul_self_pos.2 hi
  have hle : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hEq : vecNormSq x = ∑ j, x j * x j := rfl
  rw [hEq]
  linarith only [hterm, hle]

theorem blockNormSq_pos {X : BlockVec d} (hX : X ≠ 0) : 0 < blockNormSq X := by
  by_cases h1 : X.1 = 0
  · have h2 : X.2 ≠ 0 := fun h => hX (Prod.ext h1 h)
    have hpos := vecNormSq_pos h2
    have h0 := vecNormSq_nonneg X.1
    simp only [blockNormSq]
    linarith only [hpos, h0]
  · have hpos := vecNormSq_pos h1
    have h0 := vecNormSq_nonneg X.2
    simp only [blockNormSq]
    linarith only [hpos, h0]

theorem vecNormSq_single' (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem vecNormSq_zero' : vecNormSq (0 : Vec d) = 0 := by
  simp [vecNormSq, vecDot]

theorem blockNormSq_blockBasis (γ : BlockCoord d) : blockNormSq (blockBasis γ) = 1 := by
  cases γ with
  | inl i =>
      simp only [blockNormSq, blockBasis]
      rw [vecNormSq_single', vecNormSq_zero', add_zero]
  | inr i =>
      simp only [blockNormSq, blockBasis]
      rw [vecNormSq_single', vecNormSq_zero', zero_add]

theorem vecNormSq_add_le (x y : Vec d) :
    vecNormSq (x + y) ≤ 2 * (vecNormSq x + vecNormSq y) := by
  have h : ∀ i : Fin d, (x + y) i * (x + y) i ≤ 2 * (x i * x i + y i * y i) := by
    intro i
    have h1 : (0 : ℝ) ≤ (x i - y i) ^ 2 := sq_nonneg _
    have h2 : (x i - y i) ^ 2 =
        2 * (x i * x i + y i * y i) - (x i + y i) * (x i + y i) := by ring
    simp only [Pi.add_apply]
    linarith only [h1, h2]
  calc vecNormSq (x + y) = ∑ i, (x + y) i * (x + y) i := rfl
    _ ≤ ∑ i, 2 * (x i * x i + y i * y i) := Finset.sum_le_sum fun i _ => h i
    _ = 2 * (vecNormSq x + vecNormSq y) := by
        rw [← Finset.mul_sum, vecNormSq, vecNormSq, vecDot, vecDot,
          ← Finset.sum_add_distrib]

theorem blockNormSq_add_le (X Y : BlockVec d) :
    blockNormSq (X + Y) ≤ 2 * (blockNormSq X + blockNormSq Y) := by
  have h1 := vecNormSq_add_le X.1 Y.1
  have h2 := vecNormSq_add_le X.2 Y.2
  simp only [blockNormSq, Prod.fst_add, Prod.snd_add]
  linarith only [h1, h2]

theorem sum_sq_toFullBlockVec (X : BlockVec d) :
    ∑ α : BlockCoord d, (toFullBlockVec X α) ^ 2 = blockNormSq X := by
  rw [Fintype.sum_sum_type]
  simp only [toFullBlockVec, blockNormSq, vecNormSq, vecDot]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem card_blockCoord : Fintype.card (BlockCoord d) = 2 * d := by
  simp [Fintype.card_sum, two_mul]

/-- A scalar multiple of the doubled identity. -/
@[expose]
def scaledBlockIdentity (d : ℕ) (c : ℝ) : BlockMat d where
  upperLeft := c • (1 : Mat d)
  upperRight := 0
  lowerLeft := 0
  lowerRight := c • (1 : Mat d)

theorem matVecMul_smul_identity (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = fun i => c * x i := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

theorem matVecMul_zero_left (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

theorem blockVecDot_scaledBlockIdentity (c : ℝ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (scaledBlockIdentity d c) X) = c * blockNormSq X := by
  simp only [blockVecDot, blockMatVecMul, scaledBlockIdentity, matVecMul_smul_identity,
    matVecMul_zero_left, add_zero, zero_add, blockNormSq, vecNormSq, vecDot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem isSymmetricBlockMat_scaledBlockIdentity (c : ℝ) :
    IsSymmetricBlockMat (scaledBlockIdentity d c) := by
  have hone : ∀ i j : Fin d, (1 : Mat d) i j = (1 : Mat d) j i := by
    intro i j
    by_cases h : i = j
    · rw [h]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          show (c • (1 : Mat d)) i j = (c • (1 : Mat d)) j i
          simp only [Matrix.smul_apply, smul_eq_mul, hone i j]
      | inr j => rfl
  | inr i =>
      cases β with
      | inl j => rfl
      | inr j =>
          show (c • (1 : Mat d)) i j = (c • (1 : Mat d)) j i
          simp only [Matrix.smul_apply, smul_eq_mul, hone i j]

theorem blockPosDef_scaledBlockIdentity {c : ℝ} (hc : 0 < c) :
    Book.Ch02.BlockPosDef (scaledBlockIdentity d c) := by
  intro X hX
  rw [blockVecDot_scaledBlockIdentity]
  exact mul_pos hc (blockNormSq_pos hX)

theorem blockMatrixOfCoeff_identity :
    blockMatrixOfCoeff (1 : Mat d) = scaledBlockIdentity d 1 := by
  have hs : symmPart (1 : Mat d) = 1 := by
    funext i j
    by_cases h : i = j <;> simp [symmPart, Matrix.one_apply, h, eq_comm]
  have hk : skewPart (1 : Mat d) = 0 := by
    funext i j
    by_cases h : i = j <;> simp [skewPart, Matrix.one_apply, h, eq_comm]
  simp [blockMatrixOfCoeff, scaledBlockIdentity, hs, hk, matTranspose]

/-! ## The constant competitor -/

/-- The constant admissible state with prescribed doubled boundary data. -/
@[expose]
def constBlockState (P : BlockVec d) : BlockState d where
  potential := fun _ => P.1
  flux := fun _ => P.2

theorem isBlockMuAdmissible_constBlockState (U : Set (Vec d)) (P : BlockVec d) :
    IsBlockMuAdmissible U P (constBlockState P) := by
  have hzero1 : (fun x => (constBlockState P).potential x - P.1) = (0 : Vec d → Vec d) := by
    funext x
    simp [constBlockState]
  have hzero2 : (fun x => (constBlockState P).flux x - P.2) = (0 : Vec d → Vec d) := by
    funext x
    simp [constBlockState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hzero1]
    exact (MeasureTheory.MemLp.zero : MemLp (0 : Vec d → Vec d) 2 (volumeMeasureOn U))
  · rw [hzero1]
    exact isPotentialZeroTraceOn_zero (U := U)
  · rw [hzero2]
    exact (MeasureTheory.MemLp.zero : MemLp (0 : Vec d → Vec d) 2 (volumeMeasureOn U))
  · rw [hzero2]
    exact isSolenoidalZeroNormalTraceOn_zero (U := U)

/-- Every competitor over the coefficient space has nonnegative averaged
energy. -/
theorem zero_le_volumeAverage_blockEnergyDensity (U : Set (Vec d)) (a : CoeffSpace d)
    (X : BlockState d) : 0 ≤ volumeAverage U (blockEnergyDensity (⇑a.1) X) := by
  have hell := a.2.ae_exists_isEllipticMatrix
  have hnn : (0 : ℝ) ≤ ∫ x in U, blockEnergyDensity (⇑a.1) X x ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hell] with x hx
    obtain ⟨lam, Lam, -, -, hx⟩ := hx
    have h := blockMatrixOfCoeff_quadratic_nonneg hx (X.eval x)
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) *
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : Vec d → Mat d) x)) (X.eval x)) := by
      positivity
    simpa [blockEnergyDensity, blockCoeffField] using h2
  have hvol : (0 : ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  simpa [volumeAverage] using mul_nonneg hvol hnn

theorem bddBelow_muValueSet (U : Set (Vec d)) (P : BlockVec d) (a : CoeffSpace d) :
    BddBelow (muValueSet U P (⇑a.1)) := by
  refine ⟨0, ?_⟩
  rintro m ⟨X, -, rfl⟩
  exact zero_le_volumeAverage_blockEnergyDensity U a X

/-- At the constant identity field the constant competitor has averaged energy
equal to half the doubled square norm of the boundary data, at every cube of
finite positive volume. -/
theorem volumeAverage_blockEnergyDensity_constIdentity (U : Set (Vec d)) (P : BlockVec d)
    (hne : volume U ≠ 0) (hfin : volume U ≠ ⊤) :
    volumeAverage U (blockEnergyDensity (⇑(constIdentity d).1) (constBlockState P)) =
      (1 / 2 : ℝ) * blockNormSq P := by
  have hae : (fun x => blockEnergyDensity (⇑(constIdentity d).1) (constBlockState P) x)
      =ᵐ[volume.restrict U] fun _ => (1 / 2 : ℝ) * blockNormSq P := by
    filter_upwards [ae_restrict_of_ae (coeFn_constIdentity (d := d))] with x hx
    have hstate : (constBlockState P).eval x = P := rfl
    simp only [blockEnergyDensity, blockCoeffField, hstate, hx, blockMatrixOfCoeff_identity,
      blockVecDot_scaledBlockIdentity, one_mul]
  have htoReal : (volume U).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hne, hfin⟩
  rw [volumeAverage, integral_congr_ae hae, setIntegral_const, smul_eq_mul, measureReal_def,
    ← mul_assoc, inv_mul_cancel₀ htoReal, one_mul]

/-- **The scale-uniform bound on the variational quantity** of the constant
identity field: the constant competitor is admissible at every cube. -/
theorem Mu_constIdentity_le (U : Set (Vec d)) (P : BlockVec d)
    (hne : volume U ≠ 0) (hfin : volume U ≠ ⊤) :
    Mu U P (⇑(constIdentity d).1) ≤ (1 / 2 : ℝ) * blockNormSq P := by
  have hmem :
      volumeAverage U (blockEnergyDensity (⇑(constIdentity d).1) (constBlockState P)) ∈
        muValueSet U P (⇑(constIdentity d).1) :=
    muValueSet_mem (isBlockMuAdmissible_constBlockState U P)
  have hle : Mu U P (⇑(constIdentity d).1) ≤
      volumeAverage U (blockEnergyDensity (⇑(constIdentity d).1) (constBlockState P)) :=
    csInf_le (bddBelow_muValueSet U P (constIdentity d)) hmem
  rwa [volumeAverage_blockEnergyDensity_constIdentity U P hne hfin] at hle

/-! ## The entries of the coarse response, and its quadratic form -/

/-- Every entry of the coarse response of the constant identity field is bounded
by two, at every cube of finite positive volume. -/
theorem abs_blockMatEntry_coarseBlock_constIdentity_le (U : Set (Vec d))
    (hne : volume U ≠ 0) (hfin : volume U ≠ ⊤) (α β : BlockCoord d) :
    |blockMatEntry (coarseBlock U (constIdentity d)) α β| ≤ 2 := by
  rw [coarseBlock, blockMatEntry_coarseBlockMatrix]
  by_cases h : α = β
  · rw [ite_eq_left h]
    have h0 := zero_le_Mu_coeffSpace U (blockBasis α) (constIdentity d)
    have h1 := Mu_constIdentity_le U (blockBasis α) hne hfin
    rw [blockNormSq_blockBasis] at h1
    rw [abs_le]
    constructor <;> linarith only [h0, h1]
  · rw [ite_eq_right h]
    have h0 := zero_le_Mu_coeffSpace U (blockBasis α + blockBasis β) (constIdentity d)
    have hα0 := zero_le_Mu_coeffSpace U (blockBasis α) (constIdentity d)
    have hβ0 := zero_le_Mu_coeffSpace U (blockBasis β) (constIdentity d)
    have hs := Mu_constIdentity_le U (blockBasis α + blockBasis β) hne hfin
    have hα := Mu_constIdentity_le U (blockBasis α) hne hfin
    have hβ := Mu_constIdentity_le U (blockBasis β) hne hfin
    have hb := blockNormSq_add_le (blockBasis α) (blockBasis β)
    rw [blockNormSq_blockBasis, blockNormSq_blockBasis] at hb
    rw [blockNormSq_blockBasis] at hα hβ
    rw [abs_le]
    constructor <;> linarith only [h0, hα0, hβ0, hs, hα, hβ, hb]

private theorem entry_term_le (x y A : ℝ) (hA : |A| ≤ 2) : x * (A * y) ≤ x ^ 2 + y ^ 2 := by
  have h4 : |x| * (2 * |y|) ≤ x ^ 2 + y ^ 2 := by
    have h5 : (0 : ℝ) ≤ (|x| - |y|) ^ 2 := sq_nonneg _
    have h6 : (|x| - |y|) ^ 2 = x ^ 2 + y ^ 2 - |x| * (2 * |y|) := by
      rw [sub_sq, sq_abs, sq_abs]
      ring
    linarith only [h5, h6]
  calc x * (A * y) ≤ |x * (A * y)| := le_abs_self _
    _ = |x| * (|A| * |y|) := by rw [abs_mul, abs_mul]
    _ ≤ |x| * (2 * |y|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hA (abs_nonneg y)) (abs_nonneg x)
    _ ≤ x ^ 2 + y ^ 2 := h4

/-- A doubled block matrix with entries bounded by two has quadratic form
bounded by `4d` times the doubled square norm. -/
theorem blockVecDot_le_of_abs_blockMatEntry_le (A : BlockMat d)
    (hA : ∀ α β : BlockCoord d, |blockMatEntry A α β| ≤ 2) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) ≤ (4 * d : ℝ) * blockNormSq X := by
  set f : BlockCoord d → ℝ := toFullBlockVec X with hf
  have hrow : ∀ α : BlockCoord d,
      ∑ β : BlockCoord d, f α * (blockMatEntry A α β * f β) ≤
        ∑ β : BlockCoord d, ((f α) ^ 2 + (f β) ^ 2) :=
    fun α => Finset.sum_le_sum fun β _ => entry_term_le (f α) (f β) _ (hA α β)
  have hsum : ∑ α : BlockCoord d, ∑ β : BlockCoord d, ((f α) ^ 2 + (f β) ^ 2) =
      (4 * d : ℝ) * blockNormSq X := by
    have hinner : ∀ α : BlockCoord d,
        ∑ β : BlockCoord d, ((f α) ^ 2 + (f β) ^ 2) =
          (2 * d : ℝ) * (f α) ^ 2 + blockNormSq X := by
      intro α
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_blockCoord, sum_sq_toFullBlockVec]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun α _ => hinner α, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_sq_toFullBlockVec, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, card_blockCoord]
    push_cast
    ring
  calc blockVecDot X (blockMatVecMul A X)
      = ∑ α : BlockCoord d, ∑ β : BlockCoord d, f α * (blockMatEntry A α β * f β) :=
        blockVecDot_blockMatVecMul_eq_sum A X
    _ ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d, ((f α) ^ 2 + (f β) ^ 2) :=
        Finset.sum_le_sum fun α _ => hrow α
    _ = (4 * d : ℝ) * blockNormSq X := hsum

/-! ## The reference block -/

/-- The reference block of the witness law: a positive multiple of the doubled
identity, dimensional and free of every ellipticity constant. -/
@[expose]
def witnessRefBlock (d : ℕ) : BlockMat d :=
  scaledBlockIdentity d (4 * (d : ℝ) + 1)

theorem isSymmetricBlockMat_witnessRefBlock :
    IsSymmetricBlockMat (witnessRefBlock d) :=
  isSymmetricBlockMat_scaledBlockIdentity _

theorem blockPosDef_witnessRefBlock : Book.Ch02.BlockPosDef (witnessRefBlock d) :=
  blockPosDef_scaledBlockIdentity (by positivity)

/-! ## Cube volumes -/

theorem volume_standardCell_ne_zero (k : ℤ) (w : Fin d → ℤ) :
    volume (standardCell d k w) ≠ 0 := by
  intro h
  have hvol := volume_openCubeSet_toReal (translateCube w (originCube d k))
  rw [show openCubeSet (translateCube w (originCube d k)) = standardCell d k w from rfl, h]
    at hvol
  exact (cubeVolume_pos (translateCube w (originCube d k))).ne' (by simpa using hvol.symm)

theorem volume_standardCell_ne_top (k : ℤ) (w : Fin d → ℤ) :
    volume (standardCell d k w) ≠ ⊤ :=
  (volume_openCubeSet_lt_top (translateCube w (originCube d k))).ne

theorem blockScale_scaledBlockIdentity (c r : ℝ) :
    blockScale c (scaledBlockIdentity d r) = scaledBlockIdentity d (c * r) := by
  simp [blockScale, scaledBlockIdentity, smul_smul]

/-- **The uniform domination.**  The coarse response of the constant identity
field at every standard aligned cube, at every scale, is dominated by the
reference block in the Loewner order — with no discount factor. -/
theorem blockMatLoewnerLE_coarseBlock_constIdentity (k : ℤ) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) (constIdentity d))
      (witnessRefBlock d) := by
  intro X
  have hentry := abs_blockMatEntry_coarseBlock_constIdentity_le (standardCell d k w)
    (volume_standardCell_ne_zero k w) (volume_standardCell_ne_top k w)
  have h1 := blockVecDot_le_of_abs_blockMatEntry_le _ hentry X
  have h3 := blockNormSq_nonneg X
  rw [witnessRefBlock, blockVecDot_scaledBlockIdentity]
  linarith only [h1, h3]

/-- The domination survives every dilation of the reference block by a factor at
least one, so it holds with the discount factor `3^{g(m-k)}` of
`e.coarse.ellipticity` at every nonnegative exponent. -/
theorem blockMatLoewnerLE_coarseBlock_constIdentity_blockScale {c : ℝ} (hc : 1 ≤ c)
    (k : ℤ) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) (constIdentity d))
      (blockScale c (witnessRefBlock d)) := by
  intro X
  have hentry := abs_blockMatEntry_coarseBlock_constIdentity_le (standardCell d k w)
    (volume_standardCell_ne_zero k w) (volume_standardCell_ne_top k w)
  have h1 := blockVecDot_le_of_abs_blockMatEntry_le _ hentry X
  have h3 := blockNormSq_nonneg X
  have h4 : (4 * (d : ℝ) + 1) * blockNormSq X ≤ c * ((4 * (d : ℝ) + 1) * blockNormSq X) :=
    le_mul_of_one_le_left (mul_nonneg (by positivity) h3) hc
  rw [witnessRefBlock, blockScale_scaledBlockIdentity, blockVecDot_scaledBlockIdentity]
  linarith only [h1, h3, h4]

end

end HighContrast
end HCPolySupport
