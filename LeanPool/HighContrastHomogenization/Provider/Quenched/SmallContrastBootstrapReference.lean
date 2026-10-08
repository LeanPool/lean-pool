/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapIdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapReference

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean reference ratio

The tilt scalarization absorbs a Loewner adapter error `≤ c·𝐄` into a
multiplicative comparison with the reference mean; the absorbed size is
`c · |𝐄 relative to that mean|`.  For the bootstrap the reference mean is the
annealed block of a centered cube, so the size that has to be controlled is
`blockSize 𝐄 (𝐀(□_k))` — and it has to be controlled *uniformly in `k`*, since
the cube used by the bootstrap moves with the generation.

The terminal comparability chain supplies exactly that: the Dagger envelope
bounds the annealed block above by a multiple of `𝐄`, the sharp reverses the
order, the annealed block dominates its own sharp, and `𝐄 ≤ κ_𝐄 𝐄_#`.  On the
Euclidean grid the enlargement is zero — the adapted cell *is* the cube — so
the resulting factor

`κ_𝐄 · C(K) · B_1`

carries no generation-dependent power of three.  It is a law constant, fixed
once, valid at every generation past the source burn.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The Euclidean reference ratio `κ_𝐄 · C(K) · B_1`: the generation-free
comparability constant of the reference block against the annealed block of a
centered cube. -/
@[expose]
def euclideanReferenceRatio (Cd g K : ℝ) (E : BlockMat d) : ℝ :=
  kappaRef E * (sourceMomentOne K * boundaryConst Cd g (1 : Mat d))

/-- **The reference block is dominated by the annealed block of every centered
cube past the source burn**, with a generation-free factor. -/
theorem reference_le_annealedBlock_centeredCube [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k : ℤ} (hk : sK + 1 ≤ k) :
    (1 : ℝ) ≤ euclideanReferenceRatio Cd g K E ∧
      BlockMatLoewnerLE E
        (blockScale (euclideanReferenceRatio Cd g K E)
          (annealedBlock P (centeredCube d k))) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hgrid : roundedGrid ((kZero d : ℤ)) (1 : Mat d) = (1 : Mat d) :=
    roundedGrid_one_of_nonneg (Int.natCast_nonneg _)
  have hDelta : (0 : ℤ) ≤ k + ((0 : ℕ) : ℤ) - 1 - sK := by
    push_cast
    omega
  have hsub : adaptedCell (roundedGrid ((kZero d : ℤ)) (1 : Mat d)) k ⊆
      centeredCube d (k + ((0 : ℕ) : ℤ)) := by
    rw [hgrid, Initialization.adaptedCell_one]
    have hk0 : k + ((0 : ℕ) : ℤ) = k := by push_cast; ring
    rw [hk0]
  have hint : HasFiniteAdaptedMean P
      (roundedGrid ((kZero d : ℤ)) (1 : Mat d)) k := by
    rw [hgrid]
    exact (finite_adaptedMean_of_coarseEllipticityDagger hdag
      Matrix.PosDef.one k).1
  obtain ⟨hone, hquad⟩ := terminal_reference_comparability hd hg hdag
    (l := (kZero d : ℤ)) le_rfl hCd (n := (1 : Mat d)) Matrix.PosDef.one hsK
    k (G := 0) hDelta hsub hint
  have hcast : (((k + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - (k : ℝ)) = 0 := by
    push_cast
    ring
  rw [hcast, mul_zero, Real.rpow_zero, mul_one] at hone hquad
  rw [hgrid, adaptedMean_one] at hquad
  refine ⟨hone, ?_⟩
  intro X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have := hquad X
  rw [euclideanReferenceRatio]
  linarith only [this]

/-- **The absorbed size of the reference against the Euclidean adapted mean**
is bounded by the generation-free reference ratio. -/
theorem blockSize_reference_adaptedMean_one_le [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k : ℤ} (hk : sK + 1 ≤ k) :
    blockSize E (adaptedMean P (1 : Mat d) k) ≤
      euclideanReferenceRatio Cd g K E := by
  obtain ⟨hone, hle⟩ :=
    reference_le_annealedBlock_centeredCube hd hg hdag hCd hsK hk
  rw [adaptedMean_one]
  exact Transport.blockSize_le_of_blockMatLoewnerLE_blockScale
    hdag.refBlock_isSymm
    (posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef).posSemidef
    (isSymmetricBlockMat_annealedBlock P (centeredCube d k))
    (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag k)
    (by linarith only [hone]) hle

end

end HCPolySupport.HighContrast.Quenched
