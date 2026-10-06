/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedMainBridge
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.HomogenizationError

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.HomogenizedBlockIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identification of the homogenized coefficient matrix

The two-sided annealed sandwich pins the limiting doubled block between every
finite-volume block and its sharp.  Decay of the annealed contrast makes the
finite-volume block and its sharp asymptotically indistinguishable.  Sharp
order reversal therefore forces the limiting block to be self-dual.  Its
canonical factorization then supplies the positive symmetric part and the skew
part of the homogenized coefficient matrix.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory Topology

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- The geometric envelope in the annealed contrast estimate tends to zero. -/
private theorem tendsto_annealedContrast_geometricEnvelope {alpha : ℝ}
    (halpha : 0 < alpha) :
    Tendsto (fun j : ℕ => (3 : ℝ) ^ (-alpha * (j : ℝ))) atTop (𝓝 0) := by
  have hratioNonneg :
      0 ≤ (3 : ℝ) ^ (-alpha) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hratioLt : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hratioNonneg hratioLt
  convert hpow using 1
  funext j
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- The multiplicative comparison factor forced by contrast decay tends to
one. -/
private theorem tendsto_annealedContrast_comparisonFactor {alpha : ℝ}
    (halpha : 0 < alpha) :
    Tendsto
      (fun j : ℕ => 1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ)))
      atTop (𝓝 1) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsix : Tendsto (fun _ : ℕ => (6 : ℝ)) atTop (𝓝 6) := tendsto_const_nhds
  simpa only [mul_zero, add_zero] using
    hone.add (hsix.mul (tendsto_annealedContrast_geometricEnvelope halpha))

/-- A positive symmetric block pinned between annealed blocks and their sharps
is self-dual when the corresponding contrasts decay geometrically. -/
private theorem blockSharp_eq_of_annealedBlock_sandwich [NeZero d]
    {P : Measure (CoeffSpace d)} {Abar : BlockMat d} {Nann : ℕ} {alpha : ℝ}
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbarPos : Book.Ch02.BlockPosDef Abar)
    (hlower : ∀ m : ℕ,
      BlockMatLoewnerLE Abar
        (annealedBlock P (centeredCube d (m : ℤ))))
    (hupper : ∀ m : ℕ,
      BlockMatLoewnerLE
        (blockSharp (annealedBlock P (centeredCube d (m : ℤ)))) Abar)
    (halpha : 0 < alpha)
    (hcontrast : ∀ j : ℕ,
      annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
        (3 : ℝ) ^ (-alpha * (j : ℝ))) :
    blockSharp Abar = Abar := by
  let F : ℕ → BlockMat d := fun j =>
    annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ))
  let c : ℕ → ℝ := fun j => 1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))
  have hAbarFull : (toFullBlockMat Abar).PosDef :=
    posDef_toFullBlockMat hAbarSymm hAbarPos
  have hFsymm : ∀ j : ℕ, IsSymmetricBlockMat (F j) := by
    intro j
    exact isSymmetricBlockMat_annealedBlock P _
  have hFpos : ∀ j : ℕ, Book.Ch02.BlockPosDef (F j) := by
    intro j
    refine (blockPosDef_iff_posDef (hFsymm j)).mpr ?_
    refine posDef_of_posDef_le hAbarFull ?_
    exact le_of_blockMatLoewnerLE hAbarSymm (hFsymm j) (hlower (Nann + j))
  have hFsharpFull : ∀ j : ℕ, (toFullBlockMat (blockSharp (F j))).PosDef := by
    intro j
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp (posDef_toFullBlockMat (hFsymm j) (hFpos j))
  have hFsharpSymm : ∀ j : ℕ, IsSymmetricBlockMat (blockSharp (F j)) := by
    intro j
    exact isSymmetricBlockMat_of_posSemidef (hFsharpFull j).posSemidef
  have hFsharpPos : ∀ j : ℕ, Book.Ch02.BlockPosDef (blockSharp (F j)) := by
    intro j
    exact (blockPosDef_iff_posDef (hFsharpSymm j)).mpr (hFsharpFull j)
  have hcNonneg : ∀ j : ℕ, 0 ≤ c j := by
    intro j
    have hrpow : 0 < (3 : ℝ) ^ (-alpha * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    dsimp only [c]
    linarith only [hrpow]
  have hfiniteComparison : ∀ j : ℕ,
      BlockMatLoewnerLE (F j) (blockScale (c j) (blockSharp (F j))) := by
    intro j
    have hsharp : BlockMatLoewnerLE (blockSharp (F j)) (F j) :=
      (hupper (Nann + j)).trans (hlower (Nann + j))
    have hkappa :=
      Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one
        (hFsymm j) (hFpos j) hsharp
    have hdecay := hcontrast j
    change refContrast (F j) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ)) at hdecay
    have hkappaBound : kappaRef (F j) ≤ c j := by
      dsimp only [c]
      linarith only [hkappa, hdecay]
    exact
      (Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp
        (hFsymm j) (hFpos j)).trans
        (Quenched.blockMatLoewnerLE_blockScale_of_scalar_le
          hkappaBound (hFsharpPos j))
  have hAbar_le_scaledSharp : ∀ j : ℕ,
      BlockMatLoewnerLE Abar (blockScale (c j) (blockSharp Abar)) := by
    intro j
    have hreverse : BlockMatLoewnerLE (blockSharp (F j)) (blockSharp Abar) :=
      blockMatLoewnerLE_blockSharp_of_le hAbarSymm (hFsymm j)
        hAbarPos (hFpos j) (hlower (Nann + j))
    exact (hlower (Nann + j)).trans
      ((hfiniteComparison j).trans
        (Quenched.blockMatLoewnerLE_blockScale_of_le (hcNonneg j) hreverse))
  have hsharp_le_scaledAbar : ∀ j : ℕ,
      BlockMatLoewnerLE (blockSharp Abar) (blockScale (c j) Abar) := by
    intro j
    have hreverse :
        BlockMatLoewnerLE (blockSharp Abar) (blockSharp (blockSharp (F j))) :=
      blockMatLoewnerLE_blockSharp_of_le (hFsharpSymm j) hAbarSymm
        (hFsharpPos j) hAbarPos (hupper (Nann + j))
    rw [blockSharp_blockSharp (hFsymm j) (hFpos j)] at hreverse
    exact hreverse.trans
      ((hfiniteComparison j).trans
        (Quenched.blockMatLoewnerLE_blockScale_of_le
          (hcNonneg j) (hupper (Nann + j))))
  have hcTendsto : Tendsto c atTop (𝓝 1) := by
    simpa only [c] using tendsto_annealedContrast_comparisonFactor halpha
  have hAbar_le_sharp : BlockMatLoewnerLE Abar (blockSharp Abar) := by
    intro X
    have htend : Tendsto
        (fun j : ℕ => (1 / 2 : ℝ) *
          (c j * blockVecDot X (blockMatVecMul (blockSharp Abar) X)))
        atTop (𝓝 ((1 / 2 : ℝ) *
          blockVecDot X (blockMatVecMul (blockSharp Abar) X))) := by
      have hmul : Tendsto
          (fun j : ℕ => c j *
            blockVecDot X (blockMatVecMul (blockSharp Abar) X))
          atTop (𝓝 (blockVecDot X (blockMatVecMul (blockSharp Abar) X))) := by
        simpa only [one_mul] using
          hcTendsto.mul_const
            (blockVecDot X (blockMatVecMul (blockSharp Abar) X))
      exact tendsto_const_nhds.mul hmul
    refine ge_of_tendsto' htend fun j => ?_
    have h := hAbar_le_scaledSharp j X
    rwa [Quenched.blockVecDot_blockMatVecMul_blockScale] at h
  have hsharp_le_Abar : BlockMatLoewnerLE (blockSharp Abar) Abar := by
    intro X
    have htend : Tendsto
        (fun j : ℕ => (1 / 2 : ℝ) *
          (c j * blockVecDot X (blockMatVecMul Abar X)))
        atTop (𝓝 ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul Abar X))) := by
      have hmul : Tendsto
          (fun j : ℕ => c j * blockVecDot X (blockMatVecMul Abar X))
          atTop (𝓝 (blockVecDot X (blockMatVecMul Abar X))) := by
        simpa only [one_mul] using
          hcTendsto.mul_const (blockVecDot X (blockMatVecMul Abar X))
      exact tendsto_const_nhds.mul hmul
    refine ge_of_tendsto' htend fun j => ?_
    have h := hsharp_le_scaledAbar j X
    rwa [Quenched.blockVecDot_blockMatVecMul_blockScale] at h
  have hAbarSharpFull : (toFullBlockMat (blockSharp Abar)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hAbarFull
  have hAbarSharpSymm : IsSymmetricBlockMat (blockSharp Abar) :=
    isSymmetricBlockMat_of_posSemidef hAbarSharpFull.posSemidef
  apply toFullBlockMat_injective
  exact le_antisymm
    (le_of_blockMatLoewnerLE hAbarSharpSymm hAbarSymm hsharp_le_Abar)
    (le_of_blockMatLoewnerLE hAbarSymm hAbarSharpSymm hAbar_le_sharp)

/-- A self-dual positive doubled block is the constant doubled block of a
coefficient matrix with positive symmetric part. -/
private theorem exists_coeffMatrix_of_blockSharp_eq
    {Abar : BlockMat d}
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbarPos : Book.Ch02.BlockPosDef Abar)
    (hself : blockSharp Abar = Abar) :
    ∃ abar : Mat d,
      (symmPart abar).PosDef ∧
      Book.Ch02.constantBlockMatrix abar = Abar := by
  let E : FullBlockMat d := toFullBlockMat Abar
  have hE : E.PosDef := posDef_toFullBlockMat hAbarSymm hAbarPos
  have hsharpE : fullBlockSharp E = E := by
    dsimp only [E]
    rw [← toFullBlockMat_blockSharp, hself]
  have hcanon : canonBlock E = E := by
    rw [canonBlock, hsharpE, matGeomMean_self hE]
  let m : Mat d := canonMetric E
  let g : Mat d := canonShear E
  have hspec :
      m.PosDef ∧ gᴴ = -g ∧ canonBlock E = schurBlock m m g := by
    simpa only [m, g] using canonFactor_spec hE
  have hm : m.PosDef := hspec.1
  have hgConj : gᴴ = -g := hspec.2.1
  have hEfac : E = schurBlock m m g := hcanon.symm.trans hspec.2.2
  have hmTranspose : matTranspose m = m := by
    change mᵀ = m
    rw [← conjTranspose_eq_transpose']
    exact hm.isHermitian
  have hgTranspose : matTranspose g = -g := by
    change gᵀ = -g
    rw [← conjTranspose_eq_transpose']
    exact hgConj
  have hsymmPart : symmPart (m + g) = m := by
    ext i j
    have hmij := congrFun (congrFun hmTranspose i) j
    have hgij := congrFun (congrFun hgTranspose i) j
    change m j i = m i j at hmij
    change g j i = -g i j at hgij
    simp only [symmPart, Matrix.add_apply]
    rw [hmij, hgij]
    ring
  have hskewPart : skewPart (m + g) = g := by
    ext i j
    have hmij := congrFun (congrFun hmTranspose i) j
    have hgij := congrFun (congrFun hgTranspose i) j
    change m j i = m i j at hmij
    change g j i = -g i j at hgij
    simp only [skewPart, Matrix.add_apply]
    rw [hmij, hgij]
    ring
  refine ⟨m + g, ?_, ?_⟩
  · rw [hsymmPart]
    exact hm
  · apply toFullBlockMat_injective
    change toFullBlockMat (Book.Ch02.constantBlockMatrix (m + g)) = E
    rw [hEfac, toFullBlockMat_eq_fromBlocks, schurBlock_eq]
    simp only [Book.Ch02.constantBlockMatrix, hsymmPart, hskewPart,
      conjTranspose_eq_transpose', matTranspose]

/-- The annealed limit block pinned by the two-sided finite-volume sandwich is
the constant doubled block associated with a homogenized coefficient matrix.
The positive symmetric part and the exact doubled-block identity are produced
simultaneously. -/
theorem exists_homogenizedCoeffMatrix_of_annealedBlock_sandwich [NeZero d]
    {P : Measure (CoeffSpace d)} {Abar : BlockMat d}
    {Nann : ℕ} {alpha : ℝ}
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbarPos : Book.Ch02.BlockPosDef Abar)
    (hlower : ∀ m : ℕ,
      BlockMatLoewnerLE Abar
        (annealedBlock P (centeredCube d (m : ℤ))))
    (hupper : ∀ m : ℕ,
      BlockMatLoewnerLE
        (blockSharp (annealedBlock P (centeredCube d (m : ℤ)))) Abar)
    (halpha : 0 < alpha)
    (hcontrast : ∀ j : ℕ,
      annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
        (3 : ℝ) ^ (-alpha * (j : ℝ))) :
    ∃ abar : Mat d,
      (symmPart abar).PosDef ∧
      Book.Ch02.constantBlockMatrix abar = Abar := by
  exact exists_coeffMatrix_of_blockSharp_eq hAbarSymm hAbarPos
    (blockSharp_eq_of_annealedBlock_sandwich hAbarSymm hAbarPos
      hlower hupper halpha hcontrast)

end

end HighContrast
end HCPolySupport
