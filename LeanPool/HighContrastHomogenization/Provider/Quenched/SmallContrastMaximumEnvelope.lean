/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.ScaledStandardToAdapted
public import LeanPool.HighContrastHomogenization.Provider.Window.CellGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.StoppingRadiusCellExcess
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMaximumEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference-normalized maximal function under the source envelope

The scale-adapted source envelope bounds every aligned adapted cell by
`boundaryConst · 3^{g(m−k)} · E` on the event that the source has burned at
scale `m`.  Measured against the inflated reference `boundaryConst·3^{gG}·E`
covering the generation's geometry, the `ρ`-weighted all-scale maximal
function is therefore at most `1` once the source has burned at the
generation's own scale, and at most `(3·S·3^{-(t+G)})^g` in general — the
printed `𝓜_{n,γ} ≤ (3^{-n}𝒮)^γ`-type envelope, with no window multiplier.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The scale-adapted source envelope** for adapted cells: almost surely,
at every burn scale `m`, every adapted cell of the fixed grid contained in
the cube of scale `m` has coarse block at most
`boundaryConst · 3^{g(m−k)} · E`. -/
theorem coarseBlock_adaptedCell_scaled_le_of_source_burned
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef) :
    ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
      ∀ (k : ℤ) (w : Fin d → ℤ),
        adaptedCellAt (roundedGrid l n) k w ⊆ centeredCube d m →
        BlockMatLoewnerLE
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a)
          (blockScale
            (boundaryConst Cd g n *
              (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E) := by
  filter_upwards [hdag.coarse_bound] with a hbound
  intro m hm k w hsub
  have hd0 : 0 < d := by omega
  rw [adaptedCellAt_eq_adaptedCellTranslate]
  rw [adaptedCellAt_eq_adaptedCellTranslate] at hsub
  refine Window.adapted_scaled_of_standard hd hg hl hCd hn
    hdag.refBlock_posDef
    (Real.rpow_nonneg (by norm_num) _) k
    (adaptedCellCenter (roundedGrid l n) k w) ?_
  intro k' w' hsub'
  have hstdcube : standardCell d k' w' ⊆ centeredCube d m :=
    hsub'.trans hsub
  have hk'm : k' ≤ m :=
    Window.scale_le_of_standardCell_subset_centeredCube hd0 hstdcube
  have hcenter : standardCellCenter k' w' ∈ centeredCube d m :=
    hstdcube (Recurrence.standardCellCenter_mem_standardCell k' w')
  have hbase := hbound m hm k' hk'm w' hcenter
  have hsc : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) *
      (3 : ℝ) ^ (g * ((k : ℝ) - (k' : ℝ))) =
      (3 : ℝ) ^ (g * ((m : ℝ) - (k' : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsc]
  exact hbase

end

end HCPolySupport.HighContrast.Quenched
