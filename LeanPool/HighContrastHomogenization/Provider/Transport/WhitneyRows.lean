/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyFilling
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Transport.WhitneyRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rows and the residual of the maximal filling

The quantitative half of `l.two.grid.whitney`(i), specialized to
the cross-grid setting of part (iv).  A row below the starting scale consists of
cells whose parents escape the target, and the residual left after cutting the
filling off at a scale `J` consists of points in a scale-`J` cell that escapes
the target; both therefore sit in the boundary layer and obey
`e.source.whitney.volumes`, in the cross-grid form
`e.two.grid.whitney.volumes` and the residual volume of the Whitney selection,
with the printed `C_d = 6 d^{3/2}` and
the cross-grid factor `|p^{-1}q|` that `K(q,q')` dominates.

Letting the cutoff go to `-∞` turns the residual bound into the statement that
the selected cells of all scales `a ≤ n` cover the target up to a null set: the
exhaustion is a countable partition up to null, so no triangulation of the
residual is needed.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Volumes of the target and of the cells -/

/-- An aligned adapted cell is the translate of the cell at the origin by its own
center. -/
theorem adaptedCellAt_eq_adaptedCellTranslate (q : Mat d) (a : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt q a w = adaptedCellTranslate q a (adaptedCellCenter q a w) := rfl

/-- **The volume of a centered triadic cube** is `3^{jd}`. -/
theorem volume_centeredCube (j : ℤ) :
    volume (centeredCube d j) = ENNReal.ofReal ((3 : ℝ) ^ (j * (d : ℤ))) := by
  rw [volume_centeredCube_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [← zpow_natCast ((3 : ℝ) ^ j) d, ← zpow_mul]

/-- **The volume of a translated adapted cell** is `|det p| 3^{jd}`.  With the
identification of an aligned cell as a translate this gives every weight
`|V| / |W|` of the filling in closed form. -/
theorem volume_adaptedCellTranslate (p : Mat d) (j : ℤ) (y : Vec d) :
    volume (adaptedCellTranslate p j y)
      = ENNReal.ofReal (|p.det| * (3 : ℝ) ^ (j * (d : ℤ))) := by
  rw [adaptedCellTranslate_eq_image, volume_image_affine, volume_centeredCube,
    ← ENNReal.ofReal_mul (abs_nonneg _)]

/-- A translated adapted cell has finite volume. -/
theorem volume_adaptedCellTranslate_ne_top (p : Mat d) (j : ℤ) (y : Vec d) :
    volume (adaptedCellTranslate p j y) ≠ ⊤ := by
  rw [volume_adaptedCellTranslate]
  exact ENNReal.ofReal_ne_top

/-- A translated adapted cell has positive volume. -/
theorem volume_adaptedCellTranslate_ne_zero {p : Mat d} (hp : p.PosDef) (j : ℤ)
    (y : Vec d) : volume (adaptedCellTranslate p j y) ≠ 0 := by
  rw [volume_adaptedCellTranslate, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have hdet : (0 : ℝ) < |p.det| := abs_pos.mpr hp.det_pos.ne'
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (j * (d : ℤ)) := by positivity
  exact mul_pos hdet h3

/-- A translated adapted cell is bounded. -/
theorem isBoundedDomain_adaptedCellTranslate {p : Mat d} (hp : p.PosDef) (j : ℤ)
    (y : Vec d) : IsBoundedDomain (adaptedCellTranslate p j y) := by
  obtain ⟨R, hR, hRS⟩ := (Recurrence.isOpenBoundedConvexDomain_adaptedCell hp j).isBoundedDomain
  have hy : (0 : ℝ) ≤ ∑ k : Fin d, |y k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R + (∑ k : Fin d, |y k|) + 1, by linarith only [hR, hy], ?_⟩
  rintro x ⟨s, hs, rfl⟩ i
  have h1 : |s i| ≤ R := hRS s hs i
  have h2 : |y i| ≤ ∑ k : Fin d, |y k| :=
    Finset.single_le_sum (f := fun k : Fin d => |y k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h3 : (fun x => y + x) s i = y i + s i := rfl
  rw [h3]
  exact (abs_add_le _ _).trans (by linarith only [h1, h2])

/-! ## The rows of the filling -/

/-- **A row of the maximal filling below the starting scale**, the cross-grid row
`e.two.grid.whitney.volumes`: the selected cells of a scale `a < n` have
total relative volume at most `C_d |p^{-1}q| 3^{a-j}` with `C_d = 6 d^{3/2}`. -/
theorem volume_row_le {p q : Mat d} (hp : p.PosDef) {n j a : ℤ} (han : a < n) {y : Vec d} :
    volume (⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a, adaptedCellAt q a w) ≤
      ENNReal.ofReal (6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (a - j)) *
        volume (adaptedCellTranslate p j y) := by
  have hconst : 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (a + 1 - j)
      = 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (a - j) := by
    rw [show a + 1 - j = a - j + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [← hconst]
  refine volume_le_of_escaping_ancestor hp ?_ ?_
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact adaptedCellAt_subset_of_mem_fillingIndex hw hxw
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨gridParent w, adaptedCellAt_subset_parent q a w hxw,
      hw.2.2.resolve_left (by omega)⟩

/-- **A row of the maximal filling never exceeds the target**, the selected cells
of one scale being disjoint subsets of it.  This is the bound the square-weight
estimate for the bulk cells uses. -/
theorem volume_row_le_target {p q : Mat d} {n j a : ℤ} {y : Vec d} :
    volume (⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a, adaptedCellAt q a w) ≤
      volume (adaptedCellTranslate p j y) := by
  refine measure_mono ?_
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  exact adaptedCellAt_subset_of_mem_fillingIndex hw hxw

private theorem sum_relative_volume_row₀ {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j a : ℤ} {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) {C : ℝ} (hC : 0 ≤ C)
    (hle : volume (⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a,
        adaptedCellAt q a w) ≤
      ENNReal.ofReal C * volume (adaptedCellTranslate p j y)) :
    ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal ≤ C := by
  have hVtop := volume_adaptedCellTranslate_ne_top p j y
  have hVpos : (0 : ℝ) < (volume (adaptedCellTranslate p j y)).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hp j y) hVtop
  have hmemZ : ∀ w ∈ Z, w ∈ fillingIndex q n (adaptedCellTranslate p j y) a := by
    intro w hw
    rw [← hZ]
    exact Finset.mem_coe.mpr hw
  have hcelltop : ∀ w ∈ Z, volume (adaptedCellAt q a w) ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top hVtop
      (measure_mono (adaptedCellAt_subset_of_mem_fillingIndex (hmemZ w hw)))
  have hdisjZ : (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint fun w => adaptedCellAt q a w := by
    intro w hw v hv hwv
    exact disjoint_of_mem_fillingIndex hq (hZ ▸ hw) (hZ ▸ hv) (by simpa using hwv)
  have hmeas : ∀ w ∈ Z, MeasurableSet (adaptedCellAt q a w) := fun w _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq a w).isOpen.measurableSet
  have hsum : ∑ w ∈ Z, volume (adaptedCellAt q a w) =
      volume (⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a, adaptedCellAt q a w) := by
    rw [← measure_biUnion_finset hdisjZ hmeas, ← Finset.set_biUnion_coe, hZ]
  rw [← Finset.sum_div, ← ENNReal.toReal_sum hcelltop, hsum, div_le_iff₀ hVpos]
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h1

/-- **The cross-grid row of the maximal filling**, `e.source.whitney.volumes` and
`e.two.grid.whitney.volumes` in the printed relative-volume form: the
selected cells of a scale `a < n` satisfy `Σ |V| / |W| ≤ C_d |p^{-1}q| 3^{a-j}`
with `C_d = 6 d^{3/2}`. -/
theorem sum_relative_volume_row_le {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j a : ℤ} (han : a < n) {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) :
    ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal ≤
      6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (a - j) :=
  sum_relative_volume_row₀ hp hq hZ (by positivity) (volume_row_le hp han)

/-- **A row of the maximal filling has total relative volume at most one.**  This
is the input the square weight for the bulk cells uses at the starting scale,
where the row bound carries no decay. -/
theorem sum_relative_volume_row_le_one {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j a : ℤ} {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) :
    ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal ≤ 1 := by
  refine sum_relative_volume_row₀ hp hq hZ zero_le_one ?_
  rw [ENNReal.ofReal_one, one_mul]
  exact volume_row_le_target

/-! ## The cross-grid factor against the grid ratio -/

/-- **The grid ratio dominates the cross-grid factor.**  `K(q,q')` is a power at
least one of a quantity exceeding each of `|q^{-1}q'|` and `|(q')^{-1}q|`, so it
dominates both; this is the step that turns the rows of the filling into the
printed cross-grid rows with constant `C_d K_hop`. -/
theorem norm_inv_mul_le_gridRatio (hd : 1 ≤ d) (q q' : Mat d) :
    ‖(q')⁻¹ * q‖ ≤ gridRatio q q' ∧ ‖q⁻¹ * q'‖ ≤ gridRatio q q' := by
  have hA : (0 : ℝ) ≤ ‖q⁻¹ * q'‖ := norm_nonneg _
  have hB : (0 : ℝ) ≤ ‖(q')⁻¹ * q‖ := norm_nonneg _
  have h1 : (1 : ℝ) ≤ 1 + ‖q⁻¹ * q'‖ + ‖(q')⁻¹ * q‖ := by linarith only [hA, hB]
  have hpow : (1 + ‖q⁻¹ * q'‖ + ‖(q')⁻¹ * q‖) ≤ gridRatio q q' := by
    rw [gridRatio]
    have hstep := pow_le_pow_right₀ h1 (show 1 ≤ 2 * d by omega)
    rwa [pow_one] at hstep
  exact ⟨by linarith only [hA, hpow], by linarith only [hB, hpow]⟩

/-- **The cross-grid row of the maximal filling with the printed constant**,
`e.two.grid.whitney.volumes`: `Σ |V| / |W| ≤ C_d K_hop 3^{a-j}` for
`a < n`, whenever the grid ratio of the two grids is at most `K_hop`. -/
theorem sum_relative_volume_row_le_hop {p q : Mat d} (hd : 1 ≤ d) (hp : p.PosDef)
    (hq : q.PosDef) {n j a : ℤ} (han : a < n) {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal ≤
      6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ (a - j) := by
  refine (sum_relative_volume_row_le hp hq han hZ).trans ?_
  have hnorm : ‖p⁻¹ * q‖ ≤ Khop := ((norm_inv_mul_le_gridRatio hd q p).1).trans hK
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (a - j) := by positivity
  have hcd : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm hcd) h3.le

/-! ## The residual of the filling at a finite cutoff -/

/-- **The residual volume of the maximal filling**, the residual volume of the
Whitney selection: after cutting the filling off at the scale `J`, the uncovered
part of the target has relative volume at most
`2 d^{3/2} |p^{-1}q| 3^{J-j}`. -/
theorem volume_residual_le {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef) {n j J : ℤ}
    (hJn : J ≤ n) {y : Vec d} :
    volume (adaptedCellTranslate p j y \
        ⋃ a ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a,
          adaptedCellAt q a w) ≤
      ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (J - j)) *
        volume (adaptedCellTranslate p j y) := by
  have hFnull : volume (matVecMul q '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ J}) = 0 := volume_image_gridFaces q J
  rw [← measure_sdiff_null (μ := volume) (s := adaptedCellTranslate p j y \
      ⋃ a ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a,
        adaptedCellAt q a w) hFnull]
  refine volume_le_of_escaping_ancestor hp (c := J) (fun x hx => hx.1.1) ?_
  rintro x ⟨⟨hxW, hxnot⟩, hxF⟩
  obtain ⟨w, hxw⟩ := exists_mem_adaptedCellAt hq J hxF
  refine ⟨w, hxw, fun hsub => hxnot ?_⟩
  obtain ⟨b, hbn, hbmem, hbsub⟩ := exists_mem_fillingIndex_of_subset hJn hsub
  exact Set.mem_iUnion₂.mpr ⟨J + (b : ℤ), ⟨by omega, hbn⟩,
    Set.mem_iUnion₂.mpr ⟨gridParent^[b] w, hbmem, hbsub hxw⟩⟩

/-! ## The limit exhaustion -/

private theorem eq_zero_of_le_geometric₀ {x K : ℝ} (hx : 0 ≤ x)
    (h : ∀ m : ℕ, x ≤ K * (1 / 3 : ℝ) ^ m) : x = 0 := by
  have hlim : _root_.Filter.Tendsto (fun m : ℕ => K * (1 / 3 : ℝ) ^ m) _root_.Filter.atTop (nhds
    0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 : ℝ) / 3 < 1)
    simpa using hpow.const_mul K
  exact le_antisymm (ge_of_tendsto' hlim h) hx

/-- **The maximal filling exhausts the target up to a null set.**  The residual
volume tends to zero as the cutoff descends, so the selected cells of all scales
`a ≤ n` are a countable disjoint family covering the target almost everywhere:
this is the countable Whitney partition in the form that
`e.fixed.geometry.parent.child` reads. -/
theorem volume_diff_iUnion_fillingIndex {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j : ℤ} {y : Vec d} :
    volume (adaptedCellTranslate p j y \
      ⋃ a ∈ Set.Iic n, ⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a,
        adaptedCellAt q a w) = 0 := by
  set W : Set (Vec d) := adaptedCellTranslate p j y with hW
  set D : Set (Vec d) := W \ ⋃ a ∈ Set.Iic n, ⋃ w ∈ fillingIndex q n W a,
    adaptedCellAt q a w with hD
  have hWtop : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top p j y
  have hDtop : volume D ≠ ⊤ := ne_top_of_le_ne_top hWtop (measure_mono Set.sdiff_subset)
  have hCd : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ := by positivity
  have hkey : ∀ m : ℕ, (volume D).toReal ≤
      (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (n - j) * (volume W).toReal) *
        (1 / 3 : ℝ) ^ m := by
    intro m
    have hmono : D ⊆ W \ ⋃ a ∈ Set.Icc (n - (m : ℤ)) n, ⋃ w ∈ fillingIndex q n W a,
        adaptedCellAt q a w :=
      Set.sdiff_subset_sdiff_right (Set.biUnion_subset_biUnion_left fun a ha => ha.2)
    have hle := (measure_mono hmono).trans
      (volume_residual_le hp hq (n := n) (j := j) (J := n - (m : ℤ)) (by omega) (y := y))
    have hfin : ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
        (3 : ℝ) ^ (n - (m : ℤ) - j)) * volume W ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop
    have hreal := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
    refine hreal.trans_eq ?_
    have hpow : (3 : ℝ) ^ (n - (m : ℤ) - j) = (3 : ℝ) ^ (n - j) * (1 / 3 : ℝ) ^ m := by
      rw [show n - (m : ℤ) - j = n - j + -(m : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, one_div, inv_pow, zpow_natCast]
    rw [hpow]
    ring
  have hzero := eq_zero_of_le_geometric₀ ENNReal.toReal_nonneg hkey
  exact (ENNReal.toReal_eq_zero_iff _ |>.mp hzero).resolve_right hDtop

/-! ## The filling as a family of finite rows -/

/-- **The maximal filling of a target cell by the cells of a second grid**, the
family `𝒱_a(W;q)` of `l.two.grid.whitney`(i) and (iv) presented as
finite rows.  Each row is a finite set of aligned `q`-cells contained in the
target and mutually disjoint across all rows, each cell is a bounded open convex
domain of the printed volume `|det q| 3^{ad}`, a row below the starting scale has
total volume at most `C_d |p^{-1}q| 3^{a-j}` times the target's and no row exceeds
the target, and all the rows together cover the target up to a null set. -/
theorem maximal_filling {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef) (n j : ℤ)
    (y : Vec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ a, ↑(Z a) = fillingIndex q n (adaptedCellTranslate p j y) a) ∧
        (∀ a, ∀ w ∈ Z a, adaptedCellAt q a w ⊆ adaptedCellTranslate p j y) ∧
        (∀ a, ∀ w ∈ Z a, IsOpenBoundedConvexDomain (adaptedCellAt q a w)) ∧
        (∀ a, ∀ w ∈ Z a, volume (adaptedCellAt q a w)
          = ENNReal.ofReal (|q.det| * (3 : ℝ) ^ (a * (d : ℤ)))) ∧
        (∀ a b : ℤ, ∀ w ∈ Z a, ∀ v ∈ Z b, (a, w) ≠ (b, v) →
          Disjoint (adaptedCellAt q a w) (adaptedCellAt q b v)) ∧
        (∀ a : ℤ, a < n → ∑ w ∈ Z a, volume (adaptedCellAt q a w) ≤
          ENNReal.ofReal (6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (a - j)) *
            volume (adaptedCellTranslate p j y)) ∧
        (∀ a : ℤ, ∑ w ∈ Z a, volume (adaptedCellAt q a w) ≤
          volume (adaptedCellTranslate p j y)) ∧
        volume (adaptedCellTranslate p j y \
          ⋃ a ∈ Set.Iic n, ⋃ w ∈ (Z a : Set (Fin d → ℤ)), adaptedCellAt q a w) = 0 := by
  classical
  have hfin : ∀ a : ℤ, (fillingIndex q n (adaptedCellTranslate p j y) a).Finite := fun a =>
    finite_fillingIndex hq (isBoundedDomain_adaptedCellTranslate hp j y) n a
  have hrw : ∀ a : ℤ, (⋃ b ∈ (hfin a).toFinset, adaptedCellAt q a b)
      = ⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) a, adaptedCellAt q a w := by
    intro a
    rw [← Finset.set_biUnion_coe, (hfin a).coe_toFinset]
  refine ⟨fun a => (hfin a).toFinset, fun a => (hfin a).coe_toFinset, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a w hw =>
      adaptedCellAt_subset_of_mem_fillingIndex ((hfin a).mem_toFinset.mp hw)
  · exact fun a w _ => Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq a w
  · intro a w _
    rw [adaptedCellAt_eq_adaptedCellTranslate, volume_adaptedCellTranslate]
  · exact fun a b w hw v hv hne =>
      disjoint_of_mem_fillingIndex hq ((hfin a).mem_toFinset.mp hw)
        ((hfin b).mem_toFinset.mp hv) hne
  · intro a han
    rw [← measure_biUnion_finset ?_ ?_, hrw a]
    · exact volume_row_le hp han
    · rw [(hfin a).coe_toFinset]
      exact fun w hw v hv hwv => disjoint_of_mem_fillingIndex hq hw hv (by simpa using hwv)
    · exact fun w _ => (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq a
      w).isOpen.measurableSet
  · intro a
    rw [← measure_biUnion_finset ?_ ?_, hrw a]
    · exact volume_row_le_target
    · rw [(hfin a).coe_toFinset]
      exact fun w hw v hv hwv => disjoint_of_mem_fillingIndex hq hw hv (by simpa using hwv)
    · exact fun w _ => (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq a
      w).isOpen.measurableSet
  · have hcong : ∀ a : ℤ, ((hfin a).toFinset : Set (Fin d → ℤ))
        = fillingIndex q n (adaptedCellTranslate p j y) a := fun a => (hfin a).coe_toFinset
    simp only [hcong]
    exact volume_diff_iUnion_fillingIndex hp hq

end

end Transport
end HighContrast
end HCPolySupport
