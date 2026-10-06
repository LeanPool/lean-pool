/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Geometry.SizeAlignment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One scalar size, two encodings

A doubled block is measured against a positive reference block in two ways in
this development.

The setup layer uses the Loewner recipe stated for the reference imbalance:
`blockSize H F` is the least `t ≥ 0` with `-tF ≤ H ≤ tF`, an infimum
taken in the structural block dialect and involving no matrix square root.  The
canonical block geometry uses the spectral recipe
`relSize P Q = ‖Q^{-1/2} P Q^{-1/2}‖` on the flattened carrier.

On a positive semidefinite numerator and a positive definite denominator the two
recipes name the same real number, and this file proves it.  Two observations
are all that is needed.  First, `relSize P Q` is the least element of the set of
nonnegative scalars `t` with `P ≤ tQ`, by `relSize_le_iff` together with
`le_relSize_smul`, so it is that set's infimum.  Second, the extra lower
constraint `-tF ≤ H` carried by the defining set of `blockSize` is vacuous once
`0 ≤ H`, `0 ≤ F` and `0 ≤ t`, so the two defining sets coincide after the
bridge of `HCPoly.Geometry.BlockBridge` transports the quadratic-form order to
the Loewner order.

The consequence recorded last is the identity a consumer of the reference
imbalance needs: the reference ratio `κ_𝐄` of the setup layer and the imbalance
`𝔡(𝐄)` of `e.response.canonical.imbalance` are literally the same real number.
The companion statement for the excess size reads `blockExcess H F` off the same
relative size, normalized by one.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## The relative size as an infimum -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The relative size is the least nonnegative scalar Loewner bound.**  This
repackages `relSize_le_iff` and `le_relSize_smul` as an `IsLeast` statement. -/
theorem isLeast_relSize {P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef) :
    IsLeast {t : ℝ | 0 ≤ t ∧ P ≤ t • Q} (relSize P Q) :=
  ⟨⟨relSize_nonneg P Q, le_relSize_smul hP hQ⟩, fun _ ht => (relSize_le_iff hP hQ ht.1).mpr ht.2⟩

end Matrices

/-! ## Symmetry bookkeeping in the structural dialect -/

section Blocks

variable {d : ℕ}

/-- A scalar dilation of a symmetric block is symmetric. -/
theorem isSymmetricBlockMat_blockScale (c : ℝ) {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) : IsSymmetricBlockMat (blockScale c A) := by
  intro α β
  rw [blockMatEntry_blockScale, blockMatEntry_blockScale, hA α β]

/-- Symmetry of the flattened matrix is structural symmetry; the converse of
`isSymm_toFullBlockMat`. -/
theorem isSymmetricBlockMat_of_isSymm_toFullBlockMat {A : BlockMat d}
    (hA : (toFullBlockMat A).IsSymm) : IsSymmetricBlockMat A := by
  intro α β
  rw [blockMatEntry_eq_toFullBlockMat, blockMatEntry_eq_toFullBlockMat]
  exact hA.apply β α

/-- A block whose flattening is positive semidefinite is symmetric. -/
theorem isSymmetricBlockMat_of_posSemidef {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) : IsSymmetricBlockMat A :=
  isSymmetricBlockMat_of_isSymm_toFullBlockMat (isSymm_of_isHermitian hA.isHermitian)

/-! ## The two scalar sizes agree -/

/-- **The setup layer's scalar size is the relative size of the canonical block
geometry.**  Positive semidefiniteness of the numerator is what makes the lower
Loewner constraint `-tF ≤ H` of `blockSize` vacuous, so that the defining set of
`blockSize H F` is exactly the set of nonnegative scalar Loewner bounds whose
least element is `relSize`. -/
theorem blockSize_eq_relSize {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    (hHps : (toFullBlockMat H).PosSemidef) :
    blockSize H F = relSize (toFullBlockMat H) (toFullBlockMat F) := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hFps : (toFullBlockMat F).PosSemidef := hFfull.posSemidef
  have hset : {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale t F) ∧
      BlockMatLoewnerLE (blockScale (-t) F) H} =
        {t : ℝ | 0 ≤ t ∧ toFullBlockMat H ≤ t • toFullBlockMat F} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ht, hup, -⟩
      refine ⟨ht, ?_⟩
      have h := (blockMatLoewnerLE_iff_le hH (isSymmetricBlockMat_blockScale t hF)).mp hup
      rwa [toFullBlockMat_blockScale] at h
    · rintro ⟨ht, hle⟩
      refine ⟨ht, blockMatLoewnerLE_of_le ?_, blockMatLoewnerLE_of_le ?_⟩
      · rwa [toFullBlockMat_blockScale]
      · rw [toFullBlockMat_blockScale]
        refine Matrix.le_iff.mpr ?_
        have hrw : toFullBlockMat H - (-t) • toFullBlockMat F =
            toFullBlockMat H + t • toFullBlockMat F := by
          rw [neg_smul, sub_neg_eq_add]
        rw [hrw]
        exact hHps.add (hFps.smul ht)
  simp only [blockSize, hset]
  exact (isLeast_relSize hHps hFfull).csInf_eq

/-- **The reference ratio and the canonical imbalance are the same number.**
The setup layer's reference ratio `κ_𝐄 = |𝐄_*^{-1/2}𝐄𝐄_*^{-1/2}|` and the
imbalance `𝔡(𝐄)` of `e.response.canonical.imbalance` agree on every positive
symmetric block. -/
theorem kappaRef_eq_canonImbalance {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) :
    kappaRef E = canonImbalance (toFullBlockMat E) := by
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hsharp : (toFullBlockMat (blockSharp E)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hEfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_of_posSemidef hsharp.posSemidef
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharp
  rw [kappaRef, blockSize_eq_relSize hE hsharpSymm hsharpPd hEfull.posSemidef,
    toFullBlockMat_blockSharp, canonImbalance_eq hEfull]

/-- **The excess size is the relative size, normalized by one.**  The set
defining `blockExcess H F` is the set of `t ≥ 0` with `relSize ≤ 1 + t`, so it
is a closed half-line and its infimum is the positive part of `relSize - 1`. -/
theorem blockExcess_eq {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    (hHps : (toFullBlockMat H).PosSemidef) :
    blockExcess H F = max (relSize (toFullBlockMat H) (toFullBlockMat F) - 1) 0 := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hset : {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale (1 + t) F)} =
      Set.Ici (max (relSize (toFullBlockMat H) (toFullBlockMat F) - 1) 0) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, max_le_iff]
    constructor
    · rintro ⟨ht, hle⟩
      have h := (blockMatLoewnerLE_iff_le hH (isSymmetricBlockMat_blockScale (1 + t) hF)).mp hle
      rw [toFullBlockMat_blockScale] at h
      have h1 : relSize (toFullBlockMat H) (toFullBlockMat F) ≤ 1 + t :=
        (relSize_le_iff hHps hFfull (by linarith only [ht])).mpr h
      exact ⟨by linarith only [h1], ht⟩
    · rintro ⟨h1, ht⟩
      refine ⟨ht, blockMatLoewnerLE_of_le ?_⟩
      rw [toFullBlockMat_blockScale]
      exact (relSize_le_iff hHps hFfull (by linarith only [ht])).mp (by linarith only [h1])
  simp only [blockExcess, hset]
  exact csInf_Ici

end Blocks

end

end HighContrast
end HCPolySupport
