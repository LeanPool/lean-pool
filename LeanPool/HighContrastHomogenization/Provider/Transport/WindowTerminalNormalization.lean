/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds
public import LeanPool.HighContrastHomogenization.Geometry.AnnealedBlockBridge
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder

/-!
# High-contrast homogenization: Provider.Transport.WindowTerminalNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The terminal mean, its comparison, and the bridged normalization

The terminal clause of `e.source.adapted.bound` compares the annealed block
of the terminal cell with the reference block from both sides,
`b_{\mathbf r}^{-1}𝐄_* ≤ F_0 ≤ b_{\mathbf r}𝐄` with
`b_{\mathbf r} = B_{\mathbf r}\E[Y_P]`
(`e.two.grid.source.normalization`), and reads the resulting
normalization `Λ(F_0;𝐄) ≤ κ_𝐄b_{\mathbf r}` and its bridged form
`Λ(F;𝐄) ≤ κ_𝐄b_{\mathbf r}/(1-η)`.

The upper comparison is the primal cell bound of the window integrated: the
expectation is monotone and the multiplier's mean is the printed factor.  The
lower comparison needs no operator Jensen once the sharp involution is
available.  The sharp reverses the Loewner order and is homogeneous of degree
minus one, so the upper comparison gives `b_{\mathbf r}^{-1}𝐄_* ≤ F_0^♯`; and the
annealed primal-adjoint order gives `F_0^♯ ≤ F_0`.  The
two together are the printed lower bound, and they also give positivity of
`F_0` a second time.

The normalization is then a change of reference block: the reference ratio
`κ_𝐄 = Λ(𝐄_*;𝐄)` is by definition the cost of
measuring `𝐄` against its own dual, and the lower comparison converts that into
the cost of measuring `𝐄` against `F_0`.  One more change of reference, by the
lower bridge, gives the bridged form; the upper bridge is not used.

The agreement of the primal and adjoint normalizations is an identity, not an
estimate: the reflection carries the defining set of one
scalar size onto the defining set of the other.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Strict positivity of the printed constant -/

/-- The witness eccentricity `𝔢_{\mathbf q} = (|m||m^{-1}|)^{1/2}` of a positive
witness is positive in positive dimension: a positive definite matrix is a unit,
hence nonzero, and so is its inverse. -/
theorem zero_lt_witnessEccentricity [NeZero d] {m : Mat d} (hm : m.PosDef) :
    0 < witnessEccentricity m := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have h1 : 0 < ‖m‖ := norm_pos_iff.mpr hm.isUnit.ne_zero
  have h2 : 0 < ‖m⁻¹‖ := norm_pos_iff.mpr hm.inv.isUnit.ne_zero
  rw [witnessEccentricity, Real.sqrt_pos, specBound_eq_norm hm.posSemidef,
    specBound_eq_norm hm.inv.posSemidef]
  exact mul_pos h1 h2

/-- The boundary constant is positive in positive dimension, at a positive
dimensional constant and below the critical growth exponent. -/
theorem zero_lt_boundaryConst [NeZero d] {Cd g : ℝ} (hCd : 0 < Cd) (hg : g < 1)
    {m : Mat d} (hm : m.PosDef) : 0 < boundaryConst Cd g m :=
  mul_pos (mul_pos hCd (zero_lt_witnessEccentricity hm)) (zero_lt_zetaG hg)

/-- A positive dilation of a positive definite block is positive definite. -/
theorem blockPosDef_blockScale {A : BlockMat d} {c : ℝ} (hc : 0 < c)
    (h : Book.Ch02.BlockPosDef A) : Book.Ch02.BlockPosDef (blockScale c A) := by
  intro X hX
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  exact mul_pos hc (h X hX)

/-! ## The adjoint normalization is an identity -/

/-- **The two scalar normalizations agree.**  The reflection commutes
with scalar dilation and preserves the Loewner order in both directions, so the
two scalar sizes are infima of the same set of reals. -/
theorem blockSize_blockReflect (H F : BlockMat d) :
    blockSize (blockReflect H) (blockReflect F) = blockSize H F := by
  have hset : {t : ℝ | 0 ≤ t ∧
      BlockMatLoewnerLE (blockReflect H) (blockScale t (blockReflect F)) ∧
        BlockMatLoewnerLE (blockScale (-t) (blockReflect F)) (blockReflect H)} =
      {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale t F) ∧
        BlockMatLoewnerLE (blockScale (-t) F) H} := by
    ext t
    simp only [Set.mem_ofPred_eq, blockScale_blockReflect,
      blockMatLoewnerLE_blockReflect_iff]
  simp only [blockSize, hset]

/-! ## The terminal comparison -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-! ## The terminal normalization -/

/-! ## The terminal loss -/

end

end Transport
end HighContrast
end HCPolySupport
