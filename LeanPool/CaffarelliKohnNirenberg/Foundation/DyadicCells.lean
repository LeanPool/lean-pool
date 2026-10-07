/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Union

/-!
# Dyadic cells for the short-time layer

The cells partition each slab `ℝ³ × (2⁻ᵏ/2, 2⁻ᵏ)` up to null grid times.
The spatial cubes are half-open and the time intervals are open, as in
`lem:bu-small-time` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set
open scoped ENNReal Function
open CKN.Foundation.Parabolic

namespace CKN.Foundation

noncomputable section



/-- The time scale of the `k`th dyadic layer. -/
@[expose]
def buSmallTimeDyadicScale (k : ℤ) : ℝ := (2 : ℝ) ^ (-k)

/-- The spatial side length of each cell in the `k`th layer. -/
@[expose]
def buSmallTimeDyadicSide (k : ℤ) : ℝ := Real.sqrt (buSmallTimeDyadicScale k) / 128

/-- The time length of each cell in the `k`th layer. -/
@[expose]
def buSmallTimeDyadicTimeLength (k : ℤ) : ℝ := buSmallTimeDyadicScale k / 4096

/-- A time-grid point in the `k`th layer. -/
@[expose]
def buSmallTimeDyadicTimeBoundary (k : ℤ) (n : ℕ) : ℝ :=
  buSmallTimeDyadicScale k / 2 + (n : ℝ) * buSmallTimeDyadicTimeLength k

/-- The spatial cube indexed by the integer lattice point `m`. -/
@[expose]
def buSmallTimeDyadicSpatialCell (k : ℤ) (m : Fin 3 → ℤ) : Set Vec3 :=
  Set.pi Set.univ fun i =>
    Set.Ico ((m i : ℝ) * buSmallTimeDyadicSide k)
      (((m i : ℝ) + 1) * buSmallTimeDyadicSide k)

/-- The open time interval indexed by `ell`. -/
@[expose]
def buSmallTimeDyadicTimeCell (k : ℤ) (ell : Fin 2048) : Set ℝ :=
  Set.Ioo (buSmallTimeDyadicTimeBoundary k ell.val)
    (buSmallTimeDyadicTimeBoundary k (ell.val + 1))

/-- A dyadic space-time cell in the `k`th short-time layer. -/
@[expose]
def buSmallTimeDyadicCell (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    Set ParabolicPoint :=
  buSmallTimeDyadicSpatialCell k m ×ˢ buSmallTimeDyadicTimeCell k ell

/-- The spatial and temporal midpoint of a dyadic cell. -/
@[expose]
def buSmallTimeDyadicCellCenter (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    ParabolicPoint :=
  (fun i => ((m i : ℝ) + 1 / 2) * buSmallTimeDyadicSide k,
    buSmallTimeDyadicScale k / 2 + ((ell.val : ℝ) + 1 / 2) *
      buSmallTimeDyadicTimeLength k)

/-- The dyadic time scale is positive. -/
theorem buSmallTimeDyadicScale_pos (k : ℤ) : 0 < buSmallTimeDyadicScale k := by
  exact zpow_pos (by norm_num : (0 : ℝ) < 2) _

/-- The spatial side length of each cell is positive. -/
theorem buSmallTimeDyadicSide_pos (k : ℤ) : 0 < buSmallTimeDyadicSide k := by
  exact div_pos (Real.sqrt_pos.2 (buSmallTimeDyadicScale_pos k)) (by norm_num)

/-- The time length of each cell is positive. -/
theorem buSmallTimeDyadicTimeLength_pos (k : ℤ) :
    0 < buSmallTimeDyadicTimeLength k := by
  exact div_pos (buSmallTimeDyadicScale_pos k) (by norm_num)

private theorem buSmallTimeDyadicLastTime (k : ℤ) :
    buSmallTimeDyadicScale k / 2 + (2048 : ℝ) * buSmallTimeDyadicTimeLength k =
      buSmallTimeDyadicScale k := by
  simp only [buSmallTimeDyadicTimeLength]
  ring

private theorem buSmallTimeDyadicTimeBoundary_zero (k : ℤ) :
    buSmallTimeDyadicTimeBoundary k 0 = buSmallTimeDyadicScale k / 2 := by
  simp [buSmallTimeDyadicTimeBoundary]

private theorem buSmallTimeDyadicTimeBoundary_last (k : ℤ) :
    buSmallTimeDyadicTimeBoundary k 2048 = buSmallTimeDyadicScale k := by
  simp only [buSmallTimeDyadicTimeBoundary]
  exact buSmallTimeDyadicLastTime k

private theorem buSmallTimeDyadicTimeCell_halfOpen_union (k : ℤ) :
    Set.iUnion (fun ell : Fin 2048 =>
      Set.Ico (buSmallTimeDyadicTimeBoundary k ell.val)
        (buSmallTimeDyadicTimeBoundary k (ell.val + 1))) =
      Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) := by
  let a : ℕ → ℝ := buSmallTimeDyadicTimeBoundary k
  have hτ := buSmallTimeDyadicTimeLength_pos k
  have hlast : a 2048 = buSmallTimeDyadicScale k := buSmallTimeDyadicTimeBoundary_last k
  ext t
  constructor
  · intro ht
    rcases Set.mem_iUnion.mp ht with ⟨ell, ht⟩
    have hstart : a 0 ≤ a ell.val := by
      simp only [a, buSmallTimeDyadicTimeBoundary, Nat.cast_zero, zero_mul]
      have hn : (0 : ℝ) ≤ (ell.val : ℝ) := Nat.cast_nonneg _
      simpa using add_le_add_right
        (mul_nonneg hn (le_of_lt hτ)) (buSmallTimeDyadicScale k / 2)
    have hend : a (ell.val + 1) ≤ a 2048 := by
      simp only [a, buSmallTimeDyadicTimeBoundary, Nat.cast_add, Nat.cast_one]
      have hn : (ell.val : ℝ) + 1 ≤ 2048 := by
        exact_mod_cast Nat.succ_le_of_lt ell.isLt
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hn (le_of_lt hτ)) (buSmallTimeDyadicScale k / 2)
    constructor
    · have hstart' : buSmallTimeDyadicScale k / 2 ≤ a ell.val := by
        simpa [a, buSmallTimeDyadicTimeBoundary_zero] using hstart
      exact hstart'.trans ht.1
    · have hendFinal : a (ell.val + 1) ≤ buSmallTimeDyadicScale k := by
        exact hend.trans_eq hlast
      exact ht.2.trans_le hendFinal
  · intro ht
    have ht' : t ∈ Set.Ico (a 0) (a 2048) := by
      simpa [a, buSmallTimeDyadicTimeBoundary_zero, buSmallTimeDyadicTimeBoundary_last] using ht
    have hcover := Ico_subset_biUnion_Ico 2048 a ht'
    rcases Set.mem_iUnion.mp hcover with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hn with ⟨hhn, htn⟩
    have hn : n < 2048 := Finset.mem_range.mp hhn
    refine Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩
    simpa [a] using htn

private theorem buSmallTimeDyadicTimeCell_open_union_ae (k : ℤ) :
    Set.iUnion (fun ell : Fin 2048 => buSmallTimeDyadicTimeCell k ell) =ᵐ[volume]
      Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) := by
  let halfOpen : Fin 2048 → Set ℝ := fun ell =>
    Set.Ico (buSmallTimeDyadicTimeBoundary k ell.val)
      (buSmallTimeDyadicTimeBoundary k (ell.val + 1))
  let openCells : Fin 2048 → Set ℝ := buSmallTimeDyadicTimeCell k
  have hsubset :
      Set.iUnion openCells ⊆ Set.iUnion halfOpen := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨ell, hEll⟩
    rcases hEll with ⟨hl, hu⟩
    exact Set.mem_iUnion.mpr ⟨ell, ⟨hl.le, hu⟩⟩
  have hHalfUnion : Set.iUnion halfOpen =
      Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) := by
    change (Set.iUnion fun ell : Fin 2048 =>
      Set.Ico (buSmallTimeDyadicTimeBoundary k ell.val)
        (buSmallTimeDyadicTimeBoundary k (ell.val + 1))) = _
    exact buSmallTimeDyadicTimeCell_halfOpen_union k
  have hOpenSubsetIco : Set.iUnion openCells ⊆
      Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) := by
    intro t ht
    rw [← hHalfUnion]
    exact hsubset ht
  have hIcoDiff :
      (Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) \
        Set.iUnion openCells) ⊆
        Set.iUnion (fun ell : Fin 2048 =>
          ({buSmallTimeDyadicTimeBoundary k ell.val} : Set ℝ)) := by
    intro t ht
    rw [← hHalfUnion] at ht
    rcases ht with ⟨htHalfOpen, htNotOpen⟩
    rcases Set.mem_iUnion.mp htHalfOpen with ⟨ell, hEll⟩
    rcases hEll with ⟨hle, hlt⟩
    have hnot : ¬ buSmallTimeDyadicTimeBoundary k ell.val < t := by
      intro hleft
      apply htNotOpen
      exact Set.mem_iUnion.mpr ⟨ell, ⟨hleft, hlt⟩⟩
    have heq : t = buSmallTimeDyadicTimeBoundary k ell.val :=
      le_antisymm (le_of_not_gt hnot) hle
    exact Set.mem_iUnion.mpr ⟨ell, by simp [heq]⟩
  have hEndpointsNull : volume (Set.iUnion (fun ell : Fin 2048 =>
      ({buSmallTimeDyadicTimeBoundary k ell.val} : Set ℝ))) = 0 :=
    measure_iUnion_null fun ell => measure_singleton _
  have hFirstNull : volume
      (Set.iUnion openCells \
        Set.Ico (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k)) = 0 := by
    apply measure_mono_null (t := ∅)
    · intro t ht
      exact (ht.2 (hOpenSubsetIco ht.1)).elim
    · simp
  apply MeasureTheory.ae_eq_set.mpr
  constructor
  · exact hFirstNull
  · exact measure_mono_null hIcoDiff hEndpointsNull

private theorem buSmallTimeDyadicTimeCell_union_ae (k : ℤ) :
    Set.iUnion (fun ell : Fin 2048 => buSmallTimeDyadicTimeCell k ell) =ᵐ[volume]
      Set.Ioo (buSmallTimeDyadicScale k / 2) (buSmallTimeDyadicScale k) := by
  exact (buSmallTimeDyadicTimeCell_open_union_ae k).trans
    (MeasureTheory.Ioo_ae_eq_Ico' (by simp)).symm

private theorem buSmallTimeDyadicSpatialCell_union (k : ℤ) :
    Set.iUnion (fun m : Fin 3 → ℤ => buSmallTimeDyadicSpatialCell k m) = Set.univ := by
  classical
  ext x
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    have hside := buSmallTimeDyadicSide_pos k
    have hcoordinate (i : Fin 3) : ∃ n : ℤ,
        x i ∈ Set.Ico (n • buSmallTimeDyadicSide k)
          ((n + 1) • buSmallTimeDyadicSide k) := by
      have hx : x i ∈ ⋃ n : ℤ,
          Set.Ico (n • buSmallTimeDyadicSide k)
            ((n + 1) • buSmallTimeDyadicSide k) := by
        rw [iUnion_Ico_zsmul hside]
        exact Set.mem_univ _
      exact Set.mem_iUnion.mp hx
    let m : Fin 3 → ℤ := fun i => Classical.choose (hcoordinate i)
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    apply Set.mem_pi.mpr
    intro i _
    have hi := Classical.choose_spec (hcoordinate i)
    simpa [buSmallTimeDyadicSpatialCell, m, smul_eq_mul] using hi

private theorem buSmallTimeDyadicCell_union_eq_prod (k : ℤ) :
    Set.iUnion (fun ij : (Fin 3 → ℤ) × Fin 2048 =>
      buSmallTimeDyadicCell k ij.1 ij.2) =
      (Set.iUnion (fun m : Fin 3 → ℤ => buSmallTimeDyadicSpatialCell k m)) ×ˢ
        (Set.iUnion (fun ell : Fin 2048 => buSmallTimeDyadicTimeCell k ell)) := by
  exact Set.iUnion_prod (fun m : Fin 3 → ℤ => buSmallTimeDyadicSpatialCell k m)
    (fun ell : Fin 2048 => buSmallTimeDyadicTimeCell k ell)

private theorem buSmallTimeDyadicCell_union_ae (k : ℤ) :
    Set.iUnion (fun ij : (Fin 3 → ℤ) × Fin 2048 =>
      buSmallTimeDyadicCell k ij.1 ij.2) =ᵐ[volume]
      (Set.univ ×ˢ Set.Ioo (buSmallTimeDyadicScale k / 2)
        (buSmallTimeDyadicScale k) : Set ParabolicPoint) := by
  rw [buSmallTimeDyadicCell_union_eq_prod, buSmallTimeDyadicSpatialCell_union]
  change (Set.univ ×ˢ Set.iUnion
      (fun ell : Fin 2048 => buSmallTimeDyadicTimeCell k ell) :
        Set (Vec3 × ℝ)) =ᵐ[volume]
      (Set.univ ×ˢ Set.Ioo (buSmallTimeDyadicScale k / 2)
        (buSmallTimeDyadicScale k) : Set (Vec3 × ℝ))
  rw [Measure.volume_eq_prod Vec3 ℝ]
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (buSmallTimeDyadicTimeCell_union_ae k)

private theorem buSmallTimeDyadicGridIntervals_disjoint {h : ℝ} (hh : 0 < h)
    {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (Set.Ico ((m : ℝ) * h) (((m : ℝ) + 1) * h))
      (Set.Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h)) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hstep : (m : ℝ) + 1 ≤ n := by
      exact_mod_cast Int.add_one_le_iff.mpr hlt
    have hend : ((m : ℝ) + 1) * h ≤ (n : ℝ) * h :=
      mul_le_mul_of_nonneg_right hstep (le_of_lt hh)
    exact (not_lt_of_ge hend) (lt_of_le_of_lt hx₂.1 hx₁.2)
  · have hstep : (n : ℝ) + 1 ≤ m := by
      exact_mod_cast Int.add_one_le_iff.mpr hgt
    have hend : ((n : ℝ) + 1) * h ≤ (m : ℝ) * h :=
      mul_le_mul_of_nonneg_right hstep (le_of_lt hh)
    exact (not_lt_of_ge hend) (lt_of_le_of_lt hx₁.1 hx₂.2)

private theorem buSmallTimeDyadicSpatialCells_disjoint (k : ℤ)
    {m n : Fin 3 → ℤ} (hmn : m ≠ n) :
    Disjoint (buSmallTimeDyadicSpatialCell k m) (buSmallTimeDyadicSpatialCell k n) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ n i := by
    by_contra h
    apply hmn
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  have hx₁i : x i ∈ Set.Ico ((m i : ℝ) * buSmallTimeDyadicSide k)
      (((m i : ℝ) + 1) * buSmallTimeDyadicSide k) :=
    (Set.mem_pi.mp hx₁) i (Set.mem_univ i)
  have hx₂i : x i ∈ Set.Ico ((n i : ℝ) * buSmallTimeDyadicSide k)
      (((n i : ℝ) + 1) * buSmallTimeDyadicSide k) :=
    (Set.mem_pi.mp hx₂) i (Set.mem_univ i)
  exact (Set.disjoint_left.mp
    (buSmallTimeDyadicGridIntervals_disjoint (buSmallTimeDyadicSide_pos k) hi))
    hx₁i hx₂i

private theorem buSmallTimeDyadicTimeCells_disjoint (k : ℤ)
    {ell₁ ell₂ : Fin 2048} (hell : ell₁ ≠ ell₂) :
    Disjoint (buSmallTimeDyadicTimeCell k ell₁) (buSmallTimeDyadicTimeCell k ell₂) := by
  have hval : ell₁.val ≠ ell₂.val := by
    intro h
    exact hell (Fin.ext h)
  have hτ := buSmallTimeDyadicTimeLength_pos k
  apply Set.disjoint_left.mpr
  intro t ht₁ ht₂
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hn : (ell₁.val : ℝ) + 1 ≤ ell₂.val := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hend : buSmallTimeDyadicTimeBoundary k (ell₁.val + 1) ≤
        buSmallTimeDyadicTimeBoundary k ell₂.val := by
      dsimp only [buSmallTimeDyadicTimeBoundary]
      simp only [Nat.cast_add, Nat.cast_one]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hn (le_of_lt hτ))
        (buSmallTimeDyadicScale k / 2)
    exact (not_lt_of_ge hend) (lt_trans ht₂.1 ht₁.2)
  · have hn : (ell₂.val : ℝ) + 1 ≤ ell₁.val := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    have hend : buSmallTimeDyadicTimeBoundary k (ell₂.val + 1) ≤
        buSmallTimeDyadicTimeBoundary k ell₁.val := by
      dsimp only [buSmallTimeDyadicTimeBoundary]
      simp only [Nat.cast_add, Nat.cast_one]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hn (le_of_lt hτ))
        (buSmallTimeDyadicScale k / 2)
    exact (not_lt_of_ge hend) (lt_trans ht₁.1 ht₂.2)

private theorem buSmallTimeDyadicCells_pairwise_disjoint (k : ℤ) :
    Pairwise (Disjoint on fun ij : (Fin 3 → ℤ) × Fin 2048 =>
      buSmallTimeDyadicCell k ij.1 ij.2) := by
  classical
  intro ij₁ ij₂ hne
  have hindices : ij₁.1 ≠ ij₂.1 ∨ ij₁.2 ≠ ij₂.2 := by
    by_cases hm : ij₁.1 = ij₂.1
    · right
      intro hell
      exact hne (Prod.ext hm hell)
    · exact Or.inl hm
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  rcases hz₁ with ⟨hx₁, ht₁⟩
  rcases hz₂ with ⟨hx₂, ht₂⟩
  rcases hindices with hm | hell
  · exact (Set.disjoint_left.mp
      (buSmallTimeDyadicSpatialCells_disjoint k hm)) hx₁ hx₂
  · exact (Set.disjoint_left.mp
      (buSmallTimeDyadicTimeCells_disjoint k hell)) ht₁ ht₂

private theorem buSmallTimeDyadicCell_measurable (k : ℤ)
    (ij : (Fin 3 → ℤ) × Fin 2048) :
    MeasurableSet (buSmallTimeDyadicCell k ij.1 ij.2) := by
  apply (MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)).prod
  exact measurableSet_Ioo

/-- Every cell is contained in the dyadic time slab it partitions. -/
theorem buSmallTimeDyadicCell_subset_layer (k : ℤ) (m : Fin 3 → ℤ)
    (ell : Fin 2048) :
    buSmallTimeDyadicCell k m ell ⊆
      (Set.univ ×ˢ Set.Ioo (buSmallTimeDyadicScale k / 2)
        (buSmallTimeDyadicScale k) : Set ParabolicPoint) := by
  intro z hz
  rcases hz with ⟨_, ht⟩
  have hτ := buSmallTimeDyadicTimeLength_pos k
  have hstart : buSmallTimeDyadicScale k / 2 ≤
      buSmallTimeDyadicTimeBoundary k ell.val := by
    change buSmallTimeDyadicScale k / 2 ≤ buSmallTimeDyadicScale k / 2 +
      (ell.val : ℝ) * buSmallTimeDyadicTimeLength k
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hτ))
  have hend : buSmallTimeDyadicTimeBoundary k (ell.val + 1) ≤
      buSmallTimeDyadicScale k := by
    have hn : (ell.val : ℝ) + 1 ≤ 2048 := by
      exact_mod_cast Nat.succ_le_of_lt ell.isLt
    have hmul := mul_le_mul_of_nonneg_right hn (le_of_lt hτ)
    dsimp only [buSmallTimeDyadicTimeBoundary]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ buSmallTimeDyadicScale k / 2 + (2048 : ℝ) *
          buSmallTimeDyadicTimeLength k :=
        add_le_add_right hmul (buSmallTimeDyadicScale k / 2)
      _ = buSmallTimeDyadicScale k := buSmallTimeDyadicLastTime k
  exact ⟨Set.mem_univ _, hstart.trans_lt ht.1, ht.2.trans_le hend⟩

/-- The spatial displacement of a point in a cell from its center is bounded
by `√3` times the spatial side length. -/
theorem buSmallTimeDyadicCell_spatial_distance_le (k : ℤ)
    (m : Fin 3 → ℤ) (ell : Fin 2048) (z : ParabolicPoint)
    (hz : z ∈ buSmallTimeDyadicCell k m ell) :
    vec3EuclideanNorm (z.1 - (buSmallTimeDyadicCellCenter k m ell).1) ≤
      Real.sqrt 3 * buSmallTimeDyadicSide k := by
  rcases hz with ⟨hx, _⟩
  have hside := buSmallTimeDyadicSide_pos k
  have hcoordinate (i : Fin 3) :
      |z.1 i - (buSmallTimeDyadicCellCenter k m ell).1 i| ≤
        buSmallTimeDyadicSide k / 2 := by
    have hmem := (Set.mem_pi.mp hx) i (Set.mem_univ i)
    rcases hmem with ⟨hlo, hhi⟩
    have hhi' : z.1 i < (m i : ℝ) * buSmallTimeDyadicSide k +
        buSmallTimeDyadicSide k := by
      convert hhi using 1
      ring
    have hmid : ((m i : ℝ) + 1 / 2) * buSmallTimeDyadicSide k =
        (m i : ℝ) * buSmallTimeDyadicSide k + buSmallTimeDyadicSide k / 2 := by
      ring
    change |z.1 i - ((m i : ℝ) + 1 / 2) * buSmallTimeDyadicSide k| ≤
      buSmallTimeDyadicSide k / 2
    rw [hmid, abs_le]
    constructor
    · linarith only [hlo]
    · linarith only [hhi']
  have hsum :
      (∑ i : Fin 3, (z.1 i - (buSmallTimeDyadicCellCenter k m ell).1 i) ^ 2) ≤
        3 * (buSmallTimeDyadicSide k / 2) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 3, (buSmallTimeDyadicSide k / 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hcoordinate i)
      _ = 3 * (buSmallTimeDyadicSide k / 2) ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring
  have hhalf : buSmallTimeDyadicSide k / 2 ≤ buSmallTimeDyadicSide k := by
    linarith only [hside]
  have hsum' :
      (∑ i : Fin 3, (z.1 i - (buSmallTimeDyadicCellCenter k m ell).1 i) ^ 2) ≤
        (Real.sqrt 3 * buSmallTimeDyadicSide k) ^ 2 := by
    calc
      _ ≤ 3 * (buSmallTimeDyadicSide k / 2) ^ 2 := hsum
      _ ≤ 3 * buSmallTimeDyadicSide k ^ 2 := by
        have hsq : (buSmallTimeDyadicSide k / 2) ^ 2 ≤
            buSmallTimeDyadicSide k ^ 2 :=
          (sq_le_sq₀ (by positivity) (le_of_lt hside)).2 hhalf
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (Real.sqrt 3 * buSmallTimeDyadicSide k) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold vec3EuclideanNorm
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · exact hsum'

/-- The dyadic cells partition the layer for integration of nonnegative data. -/
theorem buSmallTimeDyadicCell_lintegral_eq_tsum (k : ℤ)
    (f : ParabolicPoint → ℝ≥0∞) :
    ∫⁻ z in (Set.univ ×ˢ Set.Ioo (buSmallTimeDyadicScale k / 2)
        (buSmallTimeDyadicScale k) : Set ParabolicPoint), f z ∂volume =
      ∑' ij : (Fin 3 → ℤ) × Fin 2048,
        ∫⁻ z in buSmallTimeDyadicCell k ij.1 ij.2, f z ∂volume := by
  calc
    _ = ∫⁻ z in Set.iUnion (fun ij : (Fin 3 → ℤ) × Fin 2048 =>
        buSmallTimeDyadicCell k ij.1 ij.2), f z ∂volume :=
      MeasureTheory.setLIntegral_congr (buSmallTimeDyadicCell_union_ae k).symm
    _ = ∑' ij : (Fin 3 → ℤ) × Fin 2048,
        ∫⁻ z in buSmallTimeDyadicCell k ij.1 ij.2, f z ∂volume :=
      MeasureTheory.lintegral_iUnion
        (buSmallTimeDyadicCell_measurable k)
        (buSmallTimeDyadicCells_pairwise_disjoint k) f

end
end CKN.Foundation
