/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterMajorant

/-!
# High-contrast homogenization: Provider.Entry.AdapterCellBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean filling of an adapted cell

Both halves of the comparison between adapted and Euclidean cubes read an
adapted cell through its filling by the *Euclidean* cells, which
`Entry.adaptedCellAt_one` identifies
with the standard aligned cubes; the printed cross-grid factor is then `|q^{-1}|`,
at most `101/100` by `e.rounded.grid.bounds`, and carries no
eccentricity.

Three readings of that filling are prepared here, all at an arbitrary translate
of the cell so that the aligned cells of the grid are covered as well as the
centred one.

*The pathwise elliptic bound.*  Every row, read through the widened cell bound of
`AdapterMajorant`, gives a multiple of the reference block whose coefficient is
affine in the source scale.  This is what makes the adapted mean defined at every
generation, with no window hypothesis.

*The pathwise rows majorant.*  The rows of a finite range of generations are kept
whole and only the tail below an arbitrary cutoff is paid crudely; this is the
form the averaging of `e.two.grid.whitney.average` consumes.

*The annealed cell bound.*  Averaging the rows against the Euclidean cell bound
`E[𝐀(z+□_i)] ≤ (1+9K_{Ψ_S}^23^{-i})^g𝐄` and summing the geometric series gives
`E[𝐀(z+⋄_r^q)] ≤ C_d(1-g)^{-1}(1+9K_{Ψ_S}^23^{-r})^g𝐄` at every generation and
every aligned centre.  The single factor `(1-g)^{-1}` is the geometric series of
the filling; it is what the composed reading of the reverse comparison spends.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The cells of the filling -/

/-- The cells of the Euclidean filling of a target cell obey the widened cell
bound of `AdapterMajorant`. -/
theorem cell_le {g : ℝ} {E : BlockMat d} {S : CoeffSpace d → ℝ} {q : Mat d}
    {nn M r : ℤ} {y : Vec d} {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ s, ↑(Z s) = Transport.fillingIndex (1 : Mat d) nn (adaptedCellTranslate q nn y) s)
    (hMsub : adaptedCellTranslate q nn y ⊆ centeredCube d M) {a : CoeffSpace d}
    (ha : ∀ (j : ℤ) (v : Fin d → ℤ), standardCell d j v ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (standardCell d j v) a)
        (blockScale ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-j)) ^ g) E))
    (X : BlockVec d) : ∀ w ∈ Z r,
      1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X) ≤
        (1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g *
          (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
  intro w hw
  have hmem : w ∈ Transport.fillingIndex (1 : Mat d) nn (adaptedCellTranslate q nn y) r := by
    rw [← hZ r]
    exact Finset.mem_coe.mpr hw
  have hsub : standardCell d r w ⊆ centeredCube d M := by
    rw [← adaptedCellAt_one]
    exact subset_trans (Transport.adaptedCellAt_subset_of_mem_fillingIndex hmem) hMsub
  have hcell := ha r w hsub X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale, ← adaptedCellAt_one] at hcell
  linarith only [hcell]

/-! ## The pathwise elliptic bound -/

/-- **A translated adapted cell has a pathwise elliptic bound.**  Filling it with
Euclidean cubes and reading every row through the widened cell bound gives a
multiple of the reference block whose coefficient is affine in the source
scale. -/
theorem coarseBlock_adaptedCellTranslate_le_blockScale [NeZero d]
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) {nn M : ℤ} {y : Vec d} (hM : 0 ≤ M)
    (hMsub : adaptedCellTranslate q nn y ⊆ centeredCube d M)
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ s, ↑(Z s) = Transport.fillingIndex (1 : Mat d) nn (adaptedCellTranslate q nn y) s)
    {a : CoeffSpace d}
    (ha : ∀ (j : ℤ) (v : Fin d → ℤ), standardCell d j v ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (standardCell d j v) a)
        (blockScale ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-j)) ^ g) E)) :
    BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate q nn y) a)
      (blockScale ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
        ((3 : ℝ) ^ (-nn)) ^ g * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a)) E) := by
  classical
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr (by linarith only [hg1])
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hnorm : ‖q⁻¹ * (1 : Mat d)‖ = ‖q⁻¹‖ := by rw [Matrix.mul_one]
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hCd0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ := by positivity
  have hM1 : (1 : ℝ) ≤ (3 : ℝ) ^ M := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hM
    rwa [zpow_zero] at this
  have hcancel : (3 : ℝ) ^ (-nn) * (3 : ℝ) ^ nn = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  have hS0 : 0 ≤ S a := hdag.source_nonneg a
  have hbase : (1 : ℝ) ≤ (3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ nn := by positivity
    linarith only [h1, hM1, hS0]
  intro X
  have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
    have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  refine Transport.blockQuadratic_coarseBlock_le_of_forall_filling_rows hq hone hZ a X ?_
  intro J' hJ'n
  have hrowlt : ∀ r ∈ Finset.Ico J' nn,
      ∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X)) ≤
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - nn)) *
          ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g *
            (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
    intro r hr
    refine sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0)
      (cell_le hZ hMsub ha X) ?_
    have hle := Transport.sum_relative_volume_row_le hq hone (Finset.mem_Ico.mp hr).2 (hZ r)
    rw [hnorm] at hle
    exact hle
  have hrowtop : ∑ w ∈ Z nn, (volume (adaptedCellAt (1 : Mat d) nn w)).toReal /
        (volume (adaptedCellTranslate q nn y)).toReal *
      (1 / 2 * blockVecDot X
        (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) nn w) a) X)) ≤
      1 * ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-nn)) ^ g *
        (1 / 2 * blockVecDot X (blockMatVecMul E X))) :=
    sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0)
      (cell_le hZ hMsub ha X) (Transport.sum_relative_volume_row_le_one hq hone (hZ nn))
  have hins : Finset.Icc J' nn = insert nn (Finset.Ico J' nn) :=
    (Finset.Ico_insert_right hJ'n).symm
  have hnotmem : nn ∉ Finset.Ico J' nn := by simp
  rw [hins, Finset.sum_insert hnotmem]
  have htail := sum_crude_below_le hg0 hg1 hM hS0 nn nn J'
  have hlow : ∑ r ∈ Finset.Ico J' nn,
      ∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X)) ≤
      (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a) *
            ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((nn : ℝ) * (1 - g)))) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
    refine le_trans (Finset.sum_le_sum hrowlt) ?_
    have hrw : ∀ r ∈ Finset.Ico J' nn,
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - nn)) *
            ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)))
          = ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
            ((3 : ℝ) ^ (r - nn) * (1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g) :=
      fun r _ => by ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hfac : (0 : ℝ) ≤ (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) := mul_nonneg hCd0 hE0
    refine le_trans (mul_le_mul_of_nonneg_left htail hfac) (le_of_eq ?_)
    ring
  have htop : (1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-nn)) ^ g ≤
      ((3 : ℝ) ^ (-nn)) ^ g * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a) := by
    have hid : 1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-nn)
        = (3 : ℝ) ^ (-nn) * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a) := by
      have h1 : (3 : ℝ) ^ (-nn) * (3 : ℝ) ^ nn = 1 := hcancel
      nlinarith only [h1]
    rw [hid, Real.mul_rpow (by positivity) (by linarith only [hbase])]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) g)
    have := Real.rpow_le_rpow_of_exponent_le hbase hg1.le
    rwa [Real.rpow_one] at this
  have htop' : 1 * ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-nn)) ^ g *
      (1 / 2 * blockVecDot X (blockMatVecMul E X))) ≤
      (((3 : ℝ) ^ (-nn)) ^ g * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a)) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right htop hE0
  have hsum := add_le_add (le_trans hrowtop htop') hlow
  refine le_trans hsum (le_of_eq ?_)
  rw [zpow_neg_mul_rpow]
  ring

/-- The pathwise elliptic bound, read almost everywhere. -/
theorem ae_coarseBlock_adaptedCellTranslate_le_blockScale [NeZero d]
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) {nn M : ℤ} {y : Vec d} (hM : 0 ≤ M)
    (hMsub : adaptedCellTranslate q nn y ⊆ centeredCube d M)
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ s, ↑(Z s) = Transport.fillingIndex (1 : Mat d) nn (adaptedCellTranslate q nn y) s) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate q nn y) a)
      (blockScale ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
        ((3 : ℝ) ^ (-nn)) ^ g * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a)) E) := by
  filter_upwards [ae_coarseBlock_standardCell_le_of_subset hdag M] with a ha
  exact coarseBlock_adaptedCellTranslate_le_blockScale hdag hq hM hMsub hZ ha

/-- **The pathwise elliptic bound at every aligned cell at once.**  The
ellipticity of `e.coarse.ellipticity` is one almost-sure statement quantified
over all cubes, so the bound it yields on the adapted cells holds simultaneously
for all of them. -/
theorem ae_forall_coarseBlock_adaptedCellAt_le_blockScale [NeZero d]
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) {M : ℤ} (hM : 0 ≤ M) :
    ∀ᵐ a ∂P, ∀ (r : ℤ) (w : Fin d → ℤ), adaptedCellAt q r w ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (adaptedCellAt q r w) a)
        (blockScale ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
          ((3 : ℝ) ^ (-r)) ^ g * ((3 : ℝ) ^ r + (3 : ℝ) ^ M + 3 * S a)) E) := by
  classical
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  filter_upwards [ae_coarseBlock_standardCell_le_of_subset hdag M] with a ha
  intro r w hsub
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ :=
    Transport.maximal_filling hq hone r r (adaptedCellCenter q r w)
  exact coarseBlock_adaptedCellTranslate_le_blockScale hdag hq hM hsub hZ ha

/-! ## Definedness of the adapted mean at an arbitrary aligned cell -/

/-- **The adapted mean is defined at every generation and every aligned centre.**
The pathwise elliptic bound dominates the coarse response entrywise by an affine
function of the source scale, which the source moment integrates. -/
theorem hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {q : Mat d} (hq : q.PosDef)
    {nn : ℤ} {y : Vec d}
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellTranslate q nn y)) :
    HasIntegrableCoarseBlock P (adaptedCellTranslate q nn y) := by
  classical
  obtain ⟨M, hM1, hMsub⟩ := exists_containing_centeredCube hq nn y
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ := Transport.maximal_filling hq hone nn nn y
  have hg1 : g < 1 := hdag.g_mem.2
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr (by linarith only [hg1])
  have hc0 : (0 : ℝ) ≤ (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
      ((3 : ℝ) ^ (-nn)) ^ g := by
    have h1 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) := by positivity
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (-nn)) ^ g := Real.rpow_nonneg (by positivity) g
    exact mul_nonneg (by nlinarith only [mul_nonneg h1 hinv0]) h2
  have hbound := ae_coarseBlock_adaptedCellTranslate_le_blockScale hdag hq (by omega) hMsub hZ
  have hSint : Integrable S P := integrable_source hdag
  have haff : Integrable (fun a => (3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a) P :=
    (integrable_const _).add (hSint.const_mul 3)
  have hdom : Integrable (fun a => 2 * ((((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
      (1 - g)⁻¹ + 1) * ((3 : ℝ) ^ (-nn)) ^ g) *
      ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a)) * blockEntrySum E)) P :=
    (((haff.const_mul _).mul_const (blockEntrySum E)).const_mul 2)
  intro α β
  refine hdom.mono' (hmeas α β) ?_
  filter_upwards [hbound] with a hle
  have hS0 : 0 ≤ S a := hdag.source_nonneg a
  have hprod : (0 : ℝ) ≤ ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
      ((3 : ℝ) ^ (-nn)) ^ g) * ((3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a) := by
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ nn + (3 : ℝ) ^ M + 3 * S a := by positivity
    exact mul_nonneg hc0 h2
  have hentry := Transport.abs_blockMatEntry_coarseBlock_le_of_blockMatLoewnerLE hle α β
  rw [abs_of_nonneg hprod] at hentry
  rw [Real.norm_eq_abs]
  exact hentry

end

end Entry
end HighContrast
end HCPolySupport
