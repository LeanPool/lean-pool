/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexWhitneyGeometry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledTriadicWhitneyCarrier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Disjoint triadic Whitney cells with an enlarged interior margin

The admissible cells are ordinary aligned triadic cells whose concentric
ninefold dilation is contained in the domain.  The selected cells are the
maximal admissible cells.  This is the standard disjoint triadic Whitney
selection.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped ENNReal Matrix Pointwise

noncomputable section

variable {d : ℕ}

/-- The concentric interior buffer of a triadic cell has nine times its side
length. -/
@[expose]
def enlargedMarginWhitneyInteriorBuffer (a : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  Book.Ch03.openCubeAtScale (standardCellCenter a w) (a + 2)

/-- A factor-81 enlargement is sufficient to contain the interior buffer of
the aligned parent. -/
@[expose]
def enlargedMarginWhitneyBoundaryBuffer (a : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  Book.Ch03.openCubeAtScale (standardCellCenter a w) (a + 4)

/-- An aligned triadic cell is admissible when its concentric ninefold
enlargement lies in the domain. -/
@[expose]
def IsEnlargedMarginWhitneyAdmissible (U : Set (Vec d)) (a : ℤ) (w : Fin d → ℤ) : Prop :=
  enlargedMarginWhitneyInteriorBuffer a w ⊆ U

/-- A Whitney cell is an admissible triadic cell with no strictly larger
admissible triadic cell containing it. -/
@[expose]
def IsMaximalEnlargedMarginWhitneyCell (U : Set (Vec d)) (a : ℤ) (w : Fin d → ℤ) : Prop :=
  IsEnlargedMarginWhitneyAdmissible U a w ∧
    ∀ b v, a < b → standardCell d a w ⊆ standardCell d b v →
      ¬ IsEnlargedMarginWhitneyAdmissible U b v

/-- A standard cell is the arbitrary-center cube with its lattice center. -/
theorem standardCell_eq_openCubeAtScale (a : ℤ) (w : Fin d → ℤ) :
    standardCell d a w =
      Book.Ch03.openCubeAtScale (standardCellCenter a w) a := by
  ext x
  rw [Recurrence.mem_standardCell_iff]
  constructor
  · intro hx i
    change |x i - standardCellCenter a w i| <
      Real.rpow (3 : ℝ) (a : ℝ) / 2
    obtain ⟨hlo, hhi⟩ := hx i
    have hi : |x i - standardCellCenter a w i| < (3 : ℝ) ^ a / 2 := by
      rw [abs_sub_lt_iff]
      constructor <;> dsimp [standardCellCenter] <;>
        linarith only [hlo, hhi]
    have hr : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a :=
      Real.rpow_intCast 3 a
    rwa [hr]
  · intro hx
    change (∀ i, |x i - standardCellCenter a w i| <
      Real.rpow (3 : ℝ) (a : ℝ) / 2) at hx
    intro i
    have hxi : |x i - standardCellCenter a w i| < (3 : ℝ) ^ a / 2 := by
      have hr : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a :=
        Real.rpow_intCast 3 a
      rw [hr] at hx
      exact hx i
    obtain ⟨hlo, hhi⟩ := abs_sub_lt_iff.mp hxi
    dsimp [standardCellCenter] at hlo hhi
    constructor <;> linarith only [hlo, hhi]

/-- Every cell lies in its concentric ninefold enlargement. -/
theorem standardCell_subset_enlargedMarginWhitneyInteriorBuffer (a : ℤ)
    (w : Fin d → ℤ) :
    standardCell d a w ⊆ enlargedMarginWhitneyInteriorBuffer a w := by
  rw [standardCell_eq_openCubeAtScale]
  intro x hx
  change (∀ i, |x i - standardCellCenter a w i| <
    Real.rpow (3 : ℝ) (a : ℝ) / 2) at hx
  change ∀ i, |x i - standardCellCenter a w i| <
    Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) / 2
  have hpow : (3 : ℝ) ^ (a + 2) = 9 * (3 : ℝ) ^ a := by
    calc
      (3 : ℝ) ^ (a + 2) = (3 : ℝ) ^ a * (3 : ℝ) ^ (2 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 9 * (3 : ℝ) ^ a := by norm_num; ring
  have hside : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  intro i
  have hxi : |x i - standardCellCenter a w i| < (3 : ℝ) ^ a / 2 := by
    have hr : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a :=
      Real.rpow_intCast 3 a
    rw [hr] at hx
    exact hx i
  have hi : |x i - standardCellCenter a w i| < (3 : ℝ) ^ (a + 2) / 2 := by
    rw [hpow]
    exact hxi.trans (by linarith only [hside])
  have hr : Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) =
      (3 : ℝ) ^ (a + 2) := Real.rpow_intCast 3 (a + 2)
  rwa [hr]

/-- Admissibility implies containment of the physical cell. -/
theorem IsEnlargedMarginWhitneyAdmissible.cell_subset {U : Set (Vec d)} {a : ℤ}
    {w : Fin d → ℤ} (h : IsEnlargedMarginWhitneyAdmissible U a w) :
    standardCell d a w ⊆ U :=
  (standardCell_subset_enlargedMarginWhitneyInteriorBuffer a w).trans h

/-- At each scale the maximal admissible indices form a finite set. -/
theorem finite_isMaximalEnlargedMarginWhitneyCell {U : Set (Vec d)}
    (hU : IsBoundedDomain U) (a : ℤ) :
    {w : Fin d → ℤ | IsMaximalEnlargedMarginWhitneyCell U a w}.Finite := by
  refine Set.Finite.subset
    (Transport.finite_fillingIndex Matrix.PosDef.one hU a a) ?_
  intro w hw
  have hcell : adaptedCellAt (1 : Mat d) a w ⊆ U := by
    rw [adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact hw.1.cell_subset
  exact ⟨le_rfl, hcell, Or.inl rfl⟩

private theorem admissible_side_le_domain_bound (hd : 1 ≤ d)
    {U : Set (Vec d)} {R : ℝ}
    (hbound : ∀ x ∈ U, ∀ i, |x i| ≤ R)
    {a : ℤ} {w : Fin d → ℤ} (hw : IsEnlargedMarginWhitneyAdmissible U a w) :
    (3 : ℝ) ^ a ≤ R := by
  let i0 : Fin d := ⟨0, by omega⟩
  let ell : ℝ := (3 : ℝ) ^ a
  let xp : Vec d := fun i => standardCellCenter a w i + ell
  let xm : Vec d := fun i => standardCellCenter a w i - ell
  have hell : 0 < ell := by
    dsimp only [ell]
    positivity
  have hpow : (3 : ℝ) ^ (a + 2) = 9 * ell := by
    calc
      (3 : ℝ) ^ (a + 2) = (3 : ℝ) ^ a * (3 : ℝ) ^ (2 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 9 * ell := by norm_num [ell]; ring
  have hxpBuffer : xp ∈ enlargedMarginWhitneyInteriorBuffer a w := by
    intro i
    change |xp i - standardCellCenter a w i| <
      Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) / 2
    have hr : Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) =
        (3 : ℝ) ^ (a + 2) := Real.rpow_intCast 3 (a + 2)
    rw [hr, hpow]
    change |standardCellCenter a w i + ell - standardCellCenter a w i| <
      9 * ell / 2
    rw [add_sub_cancel_left, abs_of_pos hell]
    linarith only [hell]
  have hxmBuffer : xm ∈ enlargedMarginWhitneyInteriorBuffer a w := by
    intro i
    change |xm i - standardCellCenter a w i| <
      Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) / 2
    have hr : Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) =
        (3 : ℝ) ^ (a + 2) := Real.rpow_intCast 3 (a + 2)
    rw [hr, hpow]
    change |standardCellCenter a w i - ell - standardCellCenter a w i| <
      9 * ell / 2
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hell]
    linarith only [hell]
  have hxp := hbound xp (hw hxpBuffer) i0
  have hxm := hbound xm (hw hxmBuffer) i0
  have hxplo : -R ≤ xp i0 := (abs_le.mp hxp).1
  have hxphi : xp i0 ≤ R := (abs_le.mp hxp).2
  have hxmlo : -R ≤ xm i0 := (abs_le.mp hxm).1
  have hxmhi : xm i0 ≤ R := (abs_le.mp hxm).2
  change ell ≤ R
  dsimp only [xp, xm] at hxplo hxphi hxmlo hxmhi
  linarith only [hxplo, hxphi, hxmlo, hxmhi]

private theorem standardCell_subset_ancestor (a : ℤ) (w : Fin d → ℤ)
    (k : ℕ) :
    standardCell d a w ⊆
      standardCell d (a + (k : ℤ)) (Transport.gridParent^[k] w) := by
  have h := Transport.adaptedCellAt_subset_ancestor (1 : Mat d) a w k
  rwa [adaptedCellAt_one_eq_openCubeSet_translateCube,
    adaptedCellAt_one_eq_openCubeSet_translateCube] at h

/-- Every admissible cell has a maximal admissible aligned ancestor. -/
theorem exists_maximalEnlargedMarginWhitneyCell_of_admissible (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsBoundedDomain U)
    {J : ℤ} {w : Fin d → ℤ} (hw : IsEnlargedMarginWhitneyAdmissible U J w) :
    ∃ b : ℕ,
      IsMaximalEnlargedMarginWhitneyCell U (J + (b : ℤ)) (Transport.gridParent^[b] w) ∧
      standardCell d J w ⊆
        standardCell d (J + (b : ℤ)) (Transport.gridParent^[b] w) := by
  classical
  obtain ⟨R, hR, hbound⟩ := hU
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_mem_Ico_zpow hR (by norm_num : (1 : ℝ) < 3)
  have hJside := admissible_side_le_domain_bound hd hbound hw
  have hJn : J ≤ n := by
    by_contra hnot
    have hnJ : n + 1 ≤ J := by omega
    have hp : (3 : ℝ) ^ (n + 1) ≤ (3 : ℝ) ^ J :=
      zpow_le_zpow_right₀ (by norm_num) hnJ
    exact (not_lt_of_ge (hp.trans hJside)) hnup
  set S : Finset ℕ := (Finset.range ((n - J).toNat + 1)).filter
    fun k => IsEnlargedMarginWhitneyAdmissible U (J + (k : ℤ)) (Transport.gridParent^[k] w) with hS
  have hzero : 0 ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa using hw⟩
  have hSne : S.Nonempty := ⟨0, hzero⟩
  let b : ℕ := S.max' hSne
  have hbS : b ∈ S := S.max'_mem hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hbS
  refine ⟨b, ⟨hbS.2, ?_⟩, standardCell_subset_ancestor J w b⟩
  intro c v hbc hsub hcv
  have hcside := admissible_side_le_domain_bound hd hbound hcv
  have hcn : c ≤ n := by
    by_contra hnot
    have hnc : n + 1 ≤ c := by omega
    have hp : (3 : ℝ) ^ (n + 1) ≤ (3 : ℝ) ^ c :=
      zpow_le_zpow_right₀ (by norm_num) hnc
    exact (not_lt_of_ge (hp.trans hcside)) hnup
  have hJc : J ≤ c := by omega
  let k : ℕ := (c - J).toNat
  have hkScale : J + (k : ℤ) = c := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hkCast : (k : ℤ) = c - J := by omega
  have hnCast : ((n - J).toNat : ℤ) = n - J := by
    rw [Int.toNat_of_nonneg (by omega)]
  have hbkt : b < k := by
    exact_mod_cast (show (b : ℤ) < (k : ℤ) by omega)
  have hkRange : k < (n - J).toNat + 1 := by
    exact_mod_cast (show (k : ℤ) < ((n - J).toNat : ℤ) + 1 by omega)
  have hJcell : standardCell d J w ⊆
      standardCell d (J + (b : ℤ)) (Transport.gridParent^[b] w) :=
    standardCell_subset_ancestor J w b
  have hcenter : standardCellCenter J w ∈ standardCell d J w :=
    Recurrence.standardCellCenter_mem_standardCell J w
  have hxv : standardCellCenter J w ∈ standardCell d c v :=
    hsub (hJcell hcenter)
  have hxancestor : standardCellCenter J w ∈
      standardCell d (J + (k : ℤ)) (Transport.gridParent^[k] w) :=
    standardCell_subset_ancestor J w k hcenter
  have hindex : Transport.gridParent^[k] w = v := by
    by_contra hne
    have hdisj : Disjoint
        (adaptedCellAt (1 : Mat d) c (Transport.gridParent^[k] w))
        (adaptedCellAt (1 : Mat d) c v) :=
      Recurrence.disjoint_adaptedCellAt Matrix.PosDef.one c hne
    rw [adaptedCellAt_one_eq_openCubeSet_translateCube,
      adaptedCellAt_one_eq_openCubeSet_translateCube] at hdisj
    exact Set.disjoint_left.mp hdisj
      (by rwa [hkScale] at hxancestor) hxv
  have hkS : k ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    refine ⟨hkRange, ?_⟩
    rw [hkScale, hindex]
    exact hcv
  exact (not_lt_of_ge (S.le_max' k hkS)) hbkt

private theorem enlargedMarginWhitneyInteriorBuffer_subset_metricBall_of_mem
    {a : ℤ} {w : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ standardCell d a w) :
    enlargedMarginWhitneyInteriorBuffer a w ⊆ Metric.ball x (5 * (3 : ℝ) ^ a) := by
  intro y hy
  have hell : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
  rw [Recurrence.mem_standardCell_iff] at hx
  intro i
  change |y i - x i| < 5 * (3 : ℝ) ^ a
  have hyi : |y i - standardCellCenter a w i| <
      9 * (3 : ℝ) ^ a / 2 := by
    have hr : Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) =
        (3 : ℝ) ^ (a + 2) := Real.rpow_intCast 3 (a + 2)
    have hpow : (3 : ℝ) ^ (a + 2) = 9 * (3 : ℝ) ^ a := by
      calc
        (3 : ℝ) ^ (a + 2) = (3 : ℝ) ^ a * (3 : ℝ) ^ (2 : ℤ) := by
          rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        _ = 9 * (3 : ℝ) ^ a := by norm_num; ring
    have hyraw := hy i
    change |y i - standardCellCenter a w i| <
      Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) / 2 at hyraw
    rwa [hr, hpow] at hyraw
  have hxi : |x i - standardCellCenter a w i| < (3 : ℝ) ^ a / 2 := by
    obtain ⟨hlo, hhi⟩ := hx i
    rw [abs_sub_lt_iff]
    dsimp only [standardCellCenter]
    constructor <;> linarith only [hlo, hhi]
  calc
    |y i - x i| = |(y i - standardCellCenter a w i) -
        (x i - standardCellCenter a w i)| := by ring_nf
    _ ≤ |y i - standardCellCenter a w i| +
        |x i - standardCellCenter a w i| := abs_sub _ _
    _ < 5 * (3 : ℝ) ^ a := by linarith only [hyi, hxi]

/-- The interior buffer of the aligned parent lies in the factor-81 boundary
buffer of the child. -/
theorem parentEnlargedMarginBuffer_subset_boundaryBuffer (a : ℤ)
    (w : Fin d → ℤ) :
    enlargedMarginWhitneyInteriorBuffer (a + 1) (Transport.gridParent w) ⊆
      enlargedMarginWhitneyBoundaryBuffer a w := by
  intro y hy i
  let ell : ℝ := (3 : ℝ) ^ a
  have hell : 0 < ell := by
    dsimp only [ell]
    positivity
  have hpOne : (3 : ℝ) ^ (a + 1) = 3 * ell := by
    dsimp only [ell]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, mul_comm]
  have hpThree : (3 : ℝ) ^ (a + 3) = 27 * ell := by
    calc
      (3 : ℝ) ^ (a + 3) = (3 : ℝ) ^ a * (3 : ℝ) ^ (3 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 27 * ell := by norm_num [ell]; ring
  have hpFour : (3 : ℝ) ^ (a + 4) = 81 * ell := by
    calc
      (3 : ℝ) ^ (a + 4) = (3 : ℝ) ^ a * (3 : ℝ) ^ (4 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 81 * ell := by norm_num [ell]; ring
  have hparent : |y i - standardCellCenter (a + 1) (Transport.gridParent w) i| <
      27 * ell / 2 := by
    have hyi := hy i
    change |y i - standardCellCenter (a + 1) (Transport.gridParent w) i| <
      Real.rpow (3 : ℝ) (((a + 1) + 2 : ℤ) : ℝ) / 2 at hyi
    rw [show a + 1 + 2 = a + 3 by ring] at hyi
    have hr : Real.rpow (3 : ℝ) ((a + 3 : ℤ) : ℝ) =
        (3 : ℝ) ^ (a + 3) := Real.rpow_intCast 3 (a + 3)
    rwa [hr, hpThree] at hyi
  have hdeltaZlo : -1 ≤ 3 * Transport.gridParent w i - w i := by
    dsimp only [Transport.gridParent]
    omega
  have hdeltaZhi : 3 * Transport.gridParent w i - w i ≤ 1 := by
    dsimp only [Transport.gridParent]
    omega
  have hdeltaLo : (-1 : ℝ) ≤
      3 * (Transport.gridParent w i : ℝ) - (w i : ℝ) := by
    exact_mod_cast hdeltaZlo
  have hdeltaHi : 3 * (Transport.gridParent w i : ℝ) - (w i : ℝ) ≤ 1 := by
    exact_mod_cast hdeltaZhi
  have hcenters :
      |standardCellCenter (a + 1) (Transport.gridParent w) i -
        standardCellCenter a w i| ≤ ell := by
    dsimp only [standardCellCenter]
    rw [hpOne]
    have habs : |3 * (Transport.gridParent w i : ℝ) - (w i : ℝ)| ≤ 1 :=
      abs_le.mpr ⟨hdeltaLo, hdeltaHi⟩
    have hfactor :
        3 * ell * (Transport.gridParent w i : ℝ) - ell * (w i : ℝ) =
          ell * (3 * (Transport.gridParent w i : ℝ) - (w i : ℝ)) := by ring
    calc
      |3 * ell * (Transport.gridParent w i : ℝ) - ell * (w i : ℝ)| =
          ell * |3 * (Transport.gridParent w i : ℝ) - (w i : ℝ)| := by
        rw [hfactor, abs_mul, abs_of_pos hell]
      _ ≤ ell * 1 := mul_le_mul_of_nonneg_left habs hell.le
      _ = ell := mul_one ell
  change |y i - standardCellCenter a w i| <
    Real.rpow (3 : ℝ) ((a + 4 : ℤ) : ℝ) / 2
  have hr : Real.rpow (3 : ℝ) ((a + 4 : ℤ) : ℝ) =
      (3 : ℝ) ^ (a + 4) := Real.rpow_intCast 3 (a + 4)
  rw [hr, hpFour]
  calc
    |y i - standardCellCenter a w i| =
        |(y i - standardCellCenter (a + 1) (Transport.gridParent w) i) +
          (standardCellCenter (a + 1) (Transport.gridParent w) i -
            standardCellCenter a w i)| := by ring_nf
    _ ≤ |y i - standardCellCenter (a + 1) (Transport.gridParent w) i| +
        |standardCellCenter (a + 1) (Transport.gridParent w) i -
          standardCellCenter a w i| := abs_add_le _ _
    _ < 81 * ell / 2 := by linarith only [hparent, hcenters, hell]

private theorem convex_openCubeAtScale (c : Vec d) (a : ℤ) :
    Convex ℝ (Book.Ch03.openCubeAtScale c a) := by
  rw [Book.Ch03.openCubeAtScale_eq_pi_Ioo]
  exact convex_pi fun _ _ => convex_Ioo _ _

private theorem exists_mem_frontier_segment {U : Set (Vec d)}
    {x y : Vec d} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ z, z ∈ segment ℝ x y ∧ z ∈ frontier U := by
  by_contra hnone
  push Not at hnone
  have hsegment : segment ℝ x y ⊆ interior U ∪ interior Uᶜ := by
    intro z hz
    rw [← compl_frontier_eq_union_interior]
    exact hnone z hz
  have hdisj : Disjoint (interior U) (interior Uᶜ) := by
    exact Set.disjoint_left.mpr fun z hzU hzUc =>
      (interior_subset hzUc) (interior_subset hzU)
  have hor := IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
    hdisj hsegment (convex_segment x y).isPreconnected
  rcases hor with hinside | houtside
  · exact hy (interior_subset (hinside (right_mem_segment ℝ x y)))
  · exact (interior_subset (houtside (left_mem_segment ℝ x y))) hx

private theorem vecNormSq_le_dim_mul_supNorm_sq (z : Vec d) :
    vecNormSq z ≤ (d : ℝ) * ‖z‖ ^ 2 := by
  have hcoordinate : ∀ i : Fin d, z i ^ 2 ≤ ‖z‖ ^ 2 := by
    intro i
    have hi := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at hi
    have habs : (0 : ℝ) ≤ |z i| := abs_nonneg _
    calc
      z i ^ 2 = |z i| * |z i| := by rw [← sq_abs, pow_two]
      _ ≤ ‖z‖ * ‖z‖ := mul_self_le_mul_self habs hi
      _ = ‖z‖ ^ 2 := (pow_two _).symm
  unfold vecNormSq vecDot
  calc
    ∑ i, z i * z i ≤ ∑ _i : Fin d, ‖z‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        simpa only [pow_two] using hcoordinate i
    _ = (d : ℝ) * ‖z‖ ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem euclideanNorm_le_sqrt_dim_mul_supNorm (z : Vec d) :
    euclideanNorm z ≤ Real.sqrt d * ‖z‖ := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [euclideanNorm]
  calc
    Real.sqrt (vecNormSq z) ≤ Real.sqrt ((d : ℝ) * ‖z‖ ^ 2) :=
      Real.sqrt_le_sqrt (vecNormSq_le_dim_mul_supNorm_sq z)
    _ = Real.sqrt d * Real.sqrt (‖z‖ ^ 2) := by
      rw [Real.sqrt_mul hd]
    _ = Real.sqrt d * ‖z‖ := by
      rw [Real.sqrt_sq (norm_nonneg z)]

private theorem abs_coordinate_le_euclideanNorm
    (z : Vec d) (i : Fin d) : |z i| ≤ euclideanNorm z := by
  have hsquare := sq_apply_le_vecNormSq z i
  have hsqrt := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  exact hsqrt

private theorem enlarged_margin_gap_lower {center x y : Vec d} {a : ℤ}
    (hx : x ∈ Book.Ch03.openCubeAtScale center a)
    (hy : y ∉ Book.Ch03.openCubeAtScale center (a + 2)) :
    4 * (3 : ℝ) ^ a < euclideanDist x y := by
  change ¬ ∀ i : Fin d,
      |y i - center i| < Real.rpow 3 (((a + 2 : ℤ) : ℝ)) / 2 at hy
  push Not at hy
  rcases hy with ⟨i, hi⟩
  have hrTwo : Real.rpow (3 : ℝ) ((a + 2 : ℤ) : ℝ) =
      (3 : ℝ) ^ (a + 2) := Real.rpow_intCast 3 (a + 2)
  have hpTwo : (3 : ℝ) ^ (a + 2) = 9 * (3 : ℝ) ^ a := by
    calc
      (3 : ℝ) ^ (a + 2) = (3 : ℝ) ^ a * (3 : ℝ) ^ (2 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 9 * (3 : ℝ) ^ a := by norm_num; ring
  rw [hrTwo, hpTwo] at hi
  have hxi := hx i
  have hr : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a :=
    Real.rpow_intCast 3 a
  rw [hr] at hxi
  have htriangle :
      |y i - center i| ≤ |y i - x i| + |x i - center i| := by
    calc
      |y i - center i| = |(y i - x i) + (x i - center i)| := by ring_nf
      _ ≤ |y i - x i| + |x i - center i| := abs_add_le _ _
  have hcoordinate : 4 * (3 : ℝ) ^ a < |(x - y) i| := by
    rw [Pi.sub_apply, abs_sub_comm]
    linarith only [hi, hxi, htriangle]
  calc
    4 * (3 : ℝ) ^ a < |(x - y) i| := hcoordinate
    _ ≤ euclideanNorm (x - y) := abs_coordinate_le_euclideanNorm (x - y) i
    _ = euclideanDist x y := rfl

private theorem enlarged_boundary_gap_upper [NeZero d]
    {center x y : Vec d} {a : ℤ}
    (hx : x ∈ Book.Ch03.openCubeAtScale center a)
    (hy : y ∈ Book.Ch03.openCubeAtScale center (a + 4)) :
    euclideanDist x y < 41 * Real.sqrt d * (3 : ℝ) ^ a := by
  have hell : 0 < (3 : ℝ) ^ a := by positivity
  have hpFour : (3 : ℝ) ^ (a + 4) = 81 * (3 : ℝ) ^ a := by
    calc
      (3 : ℝ) ^ (a + 4) = (3 : ℝ) ^ a * (3 : ℝ) ^ (4 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 81 * (3 : ℝ) ^ a := by norm_num; ring
  have hcoordinate : ∀ i : Fin d, |(x - y) i| < 41 * (3 : ℝ) ^ a := by
    intro i
    have hxi := hx i
    have hyi := hy i
    have hr : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a :=
      Real.rpow_intCast 3 a
    have hrFour : Real.rpow (3 : ℝ) ((a + 4 : ℤ) : ℝ) =
        (3 : ℝ) ^ (a + 4) := Real.rpow_intCast 3 (a + 4)
    rw [hr] at hxi
    rw [hrFour, hpFour] at hyi
    have htriangle :
        |x i - y i| ≤ |x i - center i| + |y i - center i| := by
      calc
        |x i - y i| = |(x i - center i) - (y i - center i)| := by ring_nf
        _ = |(x i - center i) + -(y i - center i)| := by rw [sub_eq_add_neg]
        _ ≤ |x i - center i| + |-(y i - center i)| := abs_add_le _ _
        _ = |x i - center i| + |y i - center i| := by rw [abs_neg]
    rw [Pi.sub_apply]
    linarith only [hxi, hyi, htriangle]
  have hsup : ‖x - y‖ < 41 * (3 : ℝ) ^ a := by
    apply (pi_norm_lt_iff (by positivity)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using hcoordinate i
  have hsqrt : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (NeZero.pos d))
  calc
    euclideanDist x y = euclideanNorm (x - y) := rfl
    _ ≤ Real.sqrt d * ‖x - y‖ := euclideanNorm_le_sqrt_dim_mul_supNorm _
    _ < Real.sqrt d * (41 * (3 : ℝ) ^ a) :=
      mul_lt_mul_of_pos_left hsup hsqrt
    _ = 41 * Real.sqrt d * (3 : ℝ) ^ a := by ring

/-- The ruled carrier stores only the row function and its maximal-admissible
characterization, together with the ball sandwich already carried by its
consumers. -/
structure EnlargedMarginRuledTriadicWhitneySystem (U : Set (Vec d)) (rho Rad : ℝ) where
  center : Vec d
  inner_ball : euclideanBallAt center rho ⊆ U
  outer_ball : U ⊆ euclideanBallAt center Rad
  rows : ℤ → Finset (Fin d → ℤ)
  rows_eq : ∀ a w, w ∈ rows a ↔ IsMaximalEnlargedMarginWhitneyCell U a w

/-- The ruled carrier exists for every bounded domain with the supplied ball
sandwich. -/
theorem exists_enlargedMarginRuledTriadicWhitneySystem
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad : ℝ} (hsand : HasBallSandwich U rho Rad) :
    Nonempty (EnlargedMarginRuledTriadicWhitneySystem U rho Rad) := by
  classical
  obtain ⟨_, _, c, hinner, houter⟩ := hsand
  let rows : ℤ → Finset (Fin d → ℤ) := fun a =>
    (finite_isMaximalEnlargedMarginWhitneyCell hU.isBoundedDomain a).toFinset
  exact ⟨{
    center := c
    inner_ball := hinner
    outer_ball := houter
    rows := rows
    rows_eq := by
      intro a w
      exact (finite_isMaximalEnlargedMarginWhitneyCell hU.isBoundedDomain a).mem_toFinset }⟩

namespace EnlargedMarginRuledTriadicWhitneySystem

variable {U : Set (Vec d)} {rho Rad : ℝ}

/-- The countable index of all selected Whitney cells. -/
abbrev CellIndex (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) :=
  Σ a : ℤ, ↑(system.rows a)

/-- The scale of a selected Whitney cell. -/
@[expose]
def scale (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : ℤ :=
  i.1

/-- The lattice index of a selected Whitney cell. -/
@[expose]
def index (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Fin d → ℤ :=
  i.2.1

/-- The selected physical cell. -/
@[expose]
def cell (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Set (Vec d) :=
  standardCell d (system.scale i) (system.index i)

/-- The observation buffer contained in the domain. -/
@[expose]
def interiorBuffer (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Set (Vec d) :=
  enlargedMarginWhitneyInteriorBuffer (system.scale i) (system.index i)

/-- The fixed enlargement used to meet the boundary. -/
@[expose]
def boundaryBuffer (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Set (Vec d) :=
  enlargedMarginWhitneyBoundaryBuffer (system.scale i) (system.index i)

/-- Every selected cell has its observation buffer inside the domain. -/
theorem interiorBuffer_subset (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : system.interiorBuffer i ⊆ U := by
  exact (system.rows_eq i.1 i.2.1).mp i.2.2 |>.1

/-- Every selected physical cell is contained in the domain. -/
theorem cell_subset (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : system.cell i ⊆ U :=
  (standardCell_subset_enlargedMarginWhitneyInteriorBuffer _ _).trans
    (system.interiorBuffer_subset i)

private theorem standardCell_subset_of_mem_of_mem {a b : ℤ}
    (hab : a ≤ b) {w v : Fin d → ℤ} {x : Vec d}
    (hxw : x ∈ standardCell d a w) (hxv : x ∈ standardCell d b v) :
    standardCell d a w ⊆ standardCell d b v := by
  have hxw' : x ∈ adaptedCellAt (1 : Mat d) a w := by
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube]
  have hxv' : x ∈ adaptedCellAt (1 : Mat d) b v := by
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube]
  have hsub := Transport.adaptedCellAt_subset_of_mem_of_mem Matrix.PosDef.one hab hxw' hxv'
  rwa [adaptedCellAt_one_eq_openCubeSet_translateCube,
    adaptedCellAt_one_eq_openCubeSet_translateCube] at hsub

/-- Distinct selected cells have disjoint interiors, even when their scales
differ. -/
theorem pairwise_disjoint (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i j : system.CellIndex) (hij : i ≠ j) :
    Disjoint (system.cell i) (system.cell j) := by
  rcases i with ⟨a, ⟨w, hw⟩⟩
  rcases j with ⟨b, ⟨v, hv⟩⟩
  change Disjoint (standardCell d a w) (standardCell d b v)
  have hi := (system.rows_eq a w).mp hw
  have hj := (system.rows_eq b v).mp hv
  rcases lt_trichotomy a b with hlt | heq | hgt
  · by_contra hnot
    obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp hnot
    exact (hi.2 b v hlt
      (standardCell_subset_of_mem_of_mem hlt.le hxi hxj)) hj.1
  · subst b
    have hindex : w ≠ v := by
      intro h
      subst v
      exact hij rfl
    have hdisj : Disjoint (adaptedCellAt (1 : Mat d) a w)
        (adaptedCellAt (1 : Mat d) a v) :=
      Recurrence.disjoint_adaptedCellAt Matrix.PosDef.one a hindex
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube,
      adaptedCellAt_one_eq_openCubeSet_translateCube] at hdisj
  · by_contra hnot
    obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp hnot
    exact (hj.2 a w hgt
      (standardCell_subset_of_mem_of_mem hgt.le hxj hxi)) hi.1

/-- The aligned parent of a selected cell is not admissible. -/
theorem parent_not_admissible (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    ¬ IsEnlargedMarginWhitneyAdmissible U (system.scale i + 1)
      (Transport.gridParent (system.index i)) := by
  change ¬ IsEnlargedMarginWhitneyAdmissible U (i.1 + 1) (Transport.gridParent i.2.1)
  have hi := (system.rows_eq i.1 i.2.1).mp i.2.2
  exact hi.2 _ _ (by omega) (Transport.standardCell_subset_parent _ _)

/-- Maximality makes the fixed factor-81 enlargement meet the boundary. -/
theorem boundaryBuffer_meets_frontier
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    Set.Nonempty (system.boundaryBuffer i ∩ frontier U) := by
  rcases i with ⟨a, ⟨w, hw⟩⟩
  change Set.Nonempty (enlargedMarginWhitneyBoundaryBuffer a w ∩ frontier U)
  have hparent : ¬ enlargedMarginWhitneyInteriorBuffer (a + 1) (Transport.gridParent w) ⊆ U := by
    exact system.parent_not_admissible ⟨a, ⟨w, hw⟩⟩
  obtain ⟨y, hyParent, hyU⟩ := Set.not_subset.mp hparent
  have hyBoundary : y ∈ enlargedMarginWhitneyBoundaryBuffer a w :=
    parentEnlargedMarginBuffer_subset_boundaryBuffer a w hyParent
  let x := standardCellCenter a w
  have hxCell : x ∈ standardCell d a w :=
    Recurrence.standardCellCenter_mem_standardCell a w
  have hxU : x ∈ U := by
    exact system.cell_subset ⟨a, ⟨w, hw⟩⟩ hxCell
  have hxParentCell : x ∈ standardCell d (a + 1) (Transport.gridParent w) :=
    Transport.standardCell_subset_parent a w hxCell
  have hxParentBuffer : x ∈
      enlargedMarginWhitneyInteriorBuffer (a + 1) (Transport.gridParent w) :=
    standardCell_subset_enlargedMarginWhitneyInteriorBuffer (a + 1)
      (Transport.gridParent w) hxParentCell
  have hxBoundary : x ∈ enlargedMarginWhitneyBoundaryBuffer a w :=
    parentEnlargedMarginBuffer_subset_boundaryBuffer a w hxParentBuffer
  obtain ⟨z, hzSegment, hzFrontier⟩ :=
    exists_mem_frontier_segment hxU hyU
  refine ⟨z, ?_, hzFrontier⟩
  exact (convex_openCubeAtScale (standardCellCenter a w) (a + 4)).segment_subset
    hxBoundary hyBoundary hzSegment

/-- The ruled buffers compare the cell scale with point-to-boundary distance.
The constants are the exact gap of the factor-9 inner buffer and the safe
factor-81 outer enlargement. -/
theorem boundaryDistance_compare [NeZero d]
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpen U) (i : system.CellIndex) {x : Vec d}
    (hx : x ∈ system.cell i) :
    (∀ y ∈ frontier U,
      4 * (3 : ℝ) ^ system.scale i < euclideanDist x y) ∧
      ∃ y ∈ frontier U,
        euclideanDist x y <
          41 * Real.sqrt d * (3 : ℝ) ^ system.scale i := by
  rcases i with ⟨a, ⟨w, hw⟩⟩
  change x ∈ standardCell d a w at hx
  have hxCube : x ∈
      Book.Ch03.openCubeAtScale (standardCellCenter a w) a := by
    rwa [← standardCell_eq_openCubeAtScale]
  constructor
  · intro y hyFrontier
    have hyU : y ∉ U := by
      intro hy
      have : y ∈ U ∩ frontier U := ⟨hy, hyFrontier⟩
      rw [hU.inter_frontier_eq] at this
      exact this
    have hyBuffer : y ∉ enlargedMarginWhitneyInteriorBuffer a w := by
      intro hy
      exact hyU (system.interiorBuffer_subset ⟨a, ⟨w, hw⟩⟩ hy)
    exact enlarged_margin_gap_lower hxCube hyBuffer
  · obtain ⟨y, hyBoundary, hyFrontier⟩ :=
      system.boundaryBuffer_meets_frontier ⟨a, ⟨w, hw⟩⟩
    exact ⟨y, hyFrontier, enlarged_boundary_gap_upper hxCube hyBoundary⟩

/-- The maximal admissible cells exhaust the open domain away from the
countable union of triadic grid faces. -/
theorem ae_exhaustion (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hd : 1 ≤ d) (hU : IsOpenBoundedConvexDomain U) :
    volume (U \ ⋃ a : ℤ, ⋃ w ∈ (system.rows a : Set (Fin d → ℤ)),
      standardCell d a w) = 0 := by
  have hfaces :
      volume (⋃ a : ℤ, matVecMul (1 : Mat d) '' ⋃ (i : Fin d) (k : ℤ),
        {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a}) = 0 :=
    measure_iUnion_null fun a => Transport.volume_image_gridFaces (1 : Mat d) a
  refine measure_mono_null ?_ hfaces
  rintro x ⟨hxU, hxnot⟩
  by_contra hxfaces
  obtain ⟨eps, heps, hballU⟩ :=
    Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hxU)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 3 : ℝ) ^ m < eps / 5 :=
    exists_pow_lt_of_lt_one (div_pos heps (by norm_num)) (by norm_num)
  let J : ℤ := -(m : ℤ)
  have hscale : 5 * (3 : ℝ) ^ J < eps := by
    have hpow : (3 : ℝ) ^ J = (1 / 3 : ℝ) ^ m := by
      dsimp only [J]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [hpow]
    linarith only [hm]
  have hxfaceJ : x ∉ matVecMul (1 : Mat d) '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ J} := by
    intro hx
    exact hxfaces (Set.mem_iUnion.mpr ⟨J, hx⟩)
  obtain ⟨w, hxwAdapted⟩ :=
    Transport.exists_mem_adaptedCellAt Matrix.PosDef.one J hxfaceJ
  have hxw : x ∈ standardCell d J w := by
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube] at hxwAdapted
  have hadmissible : IsEnlargedMarginWhitneyAdmissible U J w :=
    (enlargedMarginWhitneyInteriorBuffer_subset_metricBall_of_mem hxw).trans
      ((Metric.ball_subset_ball hscale.le).trans hballU)
  obtain ⟨b, hbmax, hbsub⟩ :=
    exists_maximalEnlargedMarginWhitneyCell_of_admissible hd hU.isBoundedDomain hadmissible
  have hbrow : Transport.gridParent^[b] w ∈ system.rows (J + (b : ℤ)) :=
    (system.rows_eq _ _).mpr hbmax
  apply hxnot
  refine Set.mem_iUnion.mpr ⟨J + (b : ℤ), ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨Transport.gridParent^[b] w, hbrow, ?_⟩
  exact hbsub hxw

end EnlargedMarginRuledTriadicWhitneySystem

end

end HighContrast
end HCPolySupport
