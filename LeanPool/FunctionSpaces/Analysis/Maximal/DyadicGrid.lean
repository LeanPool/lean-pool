/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The dyadic grid of a finite-dimensional inner product space

In the coordinates `x_i = ⟪b_i, x⟫` of the orthonormal basis `b = stdOrthonormalBasis ℝ V`
(`Rd.gridBasis`), the **dyadic cube** of level `k ∈ ℤ` and index `m ∈ ℤ^n` is
`Q_{k,m} = {x : ⌊2^k x_i⌋ = m_i for all i}` (`Rd.zcell`, `Rd.zcellIndex`). The cubes of one level
partition `V` (`Rd.zcell_disjoint`, `Rd.iUnion_zcell`). The centre `c_{k,m}` has the coordinates
`(m_i + 1/2) 2^(-k)` (`Rd.zcellCenter`), and `‖x - c_{k,m}‖ ≤ n 2^(-k)` on `Q_{k,m}`
(`Rd.norm_sub_zcellCenter_le`), so the cube lies between the balls of radii `2^(-k)/2` and
`n 2^(-k)` around its centre (`Rd.ball_subset_zcell`, `Rd.zcell_subset_closedBall`).

The **dyadic cells** `P_{j,m}` of level `j ∈ ℕ` are the cubes of natural level (`Rd.cell`,
`Rd.cellIndex`, `Rd.cellCenter`, `Rd.zcell_natCast`), and their lemmas are the cases `k = j` of
those for cubes. **Counting**: at most `(2ρ + 2)^n` centres of level `j` lie in a ball of radius
`ρ 2^(-j)` (`Rd.card_le_of_norm_cellCenter_sub_le`), since each coordinate of such a centre lies
in an interval of length `2ρ 2^(-j)`. The cells of one level split integrals and `L_p` norms into
sums (`Rd.lintegral_eq_tsum_cell`, `Rd.eLpNorm_rpow_eq_tsum_cell`).

**Bounded overlap**: if at every point at most `N` of the functions `g_m` are nonzero and
`F = ∑_m g_m`, then `‖F‖_p^p ≤ N^(p-1) ∑_m ‖g_m‖_p^p` (`Rd.eLpNorm_rpow_le_of_overlap`).
-/

@[expose] public section

open MeasureTheory Module Metric
open scoped ENNReal

namespace Rd

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The orthonormal basis of the dyadic grid. -/
noncomputable abbrev gridBasis : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V :=
  stdOrthonormalBasis ℝ V

variable {V}

/-! ### Dyadic cubes of every level -/

/-- The index `(⌊2^k x_i⌋)_i` of the dyadic cube of level `k ∈ ℤ` containing `x`. -/
noncomputable def zcellIndex (k : ℤ) (x : V) : Fin (finrank ℝ V) → ℤ :=
  fun i => ⌊(2 : ℝ) ^ k * (gridBasis V).repr x i⌋

/-- The **dyadic cube** `Q_{k,m}` of level `k ∈ ℤ` and index `m ∈ ℤ^n`: the points whose scaled
coordinates `2^k x_i` have the integer parts `m_i`. -/
def zcell (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) : Set V := {x | zcellIndex k x = m}

/-- The **centre** of the dyadic cube `Q_{k,m}`, with the coordinates `(m_i + 1/2) 2^(-k)`. -/
noncomputable def zcellCenter (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) : V :=
  (gridBasis V).repr.symm (WithLp.toLp 2 fun i => ((m i : ℝ) + 1 / 2) / 2 ^ k)

/-- Every point lies in the cube of its index. -/
theorem mem_zcell_zcellIndex (k : ℤ) (x : V) : x ∈ zcell k (zcellIndex k x) := rfl

/-- The coordinates of a centre. -/
theorem repr_zcellCenter (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) (i : Fin (finrank ℝ V)) :
    (gridBasis V).repr (zcellCenter k m) i = ((m i : ℝ) + 1 / 2) / 2 ^ k := by
  simp [zcellCenter]

/-- A coordinate is at most the norm. -/
theorem abs_repr_le_norm (y : V) (i : Fin (finrank ℝ V)) : |(gridBasis V).repr y i| ≤ ‖y‖ := by
  rw [← Real.norm_eq_abs, ← (gridBasis V).repr.norm_map y]
  exact PiLp.norm_apply_le _ i

/-- The `i`-th coordinate of `x - c_{k,m}` is `(2^k x_i - m_i - 1/2) / 2^k`. -/
theorem repr_sub_zcellCenter (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) (x : V) (i : Fin (finrank ℝ V)) :
    (gridBasis V).repr (x - zcellCenter k m) i =
      (2 ^ k * (gridBasis V).repr x i - m i - 1 / 2) / 2 ^ k := by
  rw [map_sub, PiLp.sub_apply, repr_zcellCenter]
  field_simp
  ring

/-- On a cube of level `k`, every coordinate differs from that of the centre by at most
`2^(-k)/2`. -/
theorem abs_repr_sub_zcellCenter_le {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} {x : V}
    (hx : x ∈ zcell k m) (i : Fin (finrank ℝ V)) :
    |(gridBasis V).repr (x - zcellCenter k m) i| ≤ 1 / 2 / 2 ^ k := by
  have hm : ⌊(2 : ℝ) ^ k * (gridBasis V).repr x i⌋ = m i := congrFun hx i
  have h1 := Int.floor_le ((2 : ℝ) ^ k * (gridBasis V).repr x i)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * (gridBasis V).repr x i)
  rw [hm] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [repr_sub_zcellCenter, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos, abs_le]
  constructor <;> linarith

/-- **Cubes are small**: `‖x - c_{k,m}‖ ≤ n 2^(-k)` on `Q_{k,m}`. -/
theorem norm_sub_zcellCenter_le {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} {x : V}
    (hx : x ∈ zcell k m) : ‖x - zcellCenter k m‖ ≤ finrank ℝ V / 2 ^ k := by
  have hy : x - zcellCenter k m = ∑ i, (gridBasis V).repr (x - zcellCenter k m) i •
      (gridBasis V) i := ((gridBasis V).sum_repr _).symm
  calc ‖x - zcellCenter k m‖
      = ‖∑ i, (gridBasis V).repr (x - zcellCenter k m) i • (gridBasis V) i‖ := by rw [← hy]
    _ ≤ ∑ i, ‖(gridBasis V).repr (x - zcellCenter k m) i • (gridBasis V) i‖ := norm_sum_le _ _
    _ = ∑ i, |(gridBasis V).repr (x - zcellCenter k m) i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, (gridBasis V).orthonormal.1 i, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin (finrank ℝ V), 1 / 2 ^ k :=
        Finset.sum_le_sum fun i _ => (abs_repr_sub_zcellCenter_le hx i).trans
          (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    _ = finrank ℝ V / 2 ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

/-- **Outer ball**: the cube `Q_{k,m}` lies in the closed ball of radius `n 2^(-k)` around its
centre. -/
theorem zcell_subset_closedBall (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    zcell k m ⊆ closedBall (zcellCenter k m) (finrank ℝ V / 2 ^ k) := fun _ hx =>
  mem_closedBall_iff_norm.2 (norm_sub_zcellCenter_le hx)

/-- **Inner ball**: the cube `Q_{k,m}` contains the open ball of radius `2^(-k)/2` around its
centre. -/
theorem ball_subset_zcell (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    ball (zcellCenter k m) (1 / 2 / 2 ^ k) ⊆ zcell k m := by
  intro y hy
  funext i
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h := (abs_repr_le_norm (y - zcellCenter k m) i).trans_lt (mem_ball_iff_norm.1 hy)
  rw [repr_sub_zcellCenter, abs_div, abs_of_pos hpos, div_lt_div_iff_of_pos_right hpos, abs_lt] at h
  exact Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩

/-- The cube index is measurable. -/
theorem measurable_zcellIndex [MeasurableSpace V] [BorelSpace V] (k : ℤ) :
    Measurable (zcellIndex (V := V) k) := by
  refine Measurable.of_eval fun i => ?_
  simp only [zcellIndex, OrthonormalBasis.repr_apply_apply]
  exact Int.measurable_floor.comp
    (measurable_const.mul (continuous_const.inner continuous_id).measurable)

/-- Cubes are measurable. -/
theorem measurableSet_zcell [MeasurableSpace V] [BorelSpace V] (k : ℤ)
    (m : Fin (finrank ℝ V) → ℤ) : MeasurableSet (zcell (V := V) k m) :=
  measurable_zcellIndex k (measurableSet_singleton m)

/-- Cubes of the same level with different indices are disjoint: they are the fibres of the
cube index (Mathlib's `pairwise_disjoint_fiber`). -/
theorem zcell_disjoint (k : ℤ) : Pairwise (Function.onFun Disjoint (zcell (V := V) k)) :=
  pairwise_disjoint_fiber (zcellIndex k)

/-- The cubes of one level cover the space. -/
theorem iUnion_zcell (k : ℤ) : ⋃ m, zcell (V := V) k m = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨_, mem_zcell_zcellIndex k x⟩

/-! ### Dyadic cells of nonnegative level -/

/-- The index `(⌊2^j x_i⌋)_i` of the dyadic cell of level `j ∈ ℕ` containing `x`: the cube index
`Rd.zcellIndex` of level `j`. -/
noncomputable def cellIndex (j : ℕ) (x : V) : Fin (finrank ℝ V) → ℤ := zcellIndex j x

/-- The **dyadic cell** `P_{j,m}` of level `j ∈ ℕ` and index `m`: the dyadic cube `Q_{j,m}`. -/
def cell (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : Set V := zcell j m

/-- The **centre** of the dyadic cell `P_{j,m}`, with the coordinates `(m_i + 1/2) 2^(-j)`. -/
noncomputable def cellCenter (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : V := zcellCenter j m

/-- For natural levels the cube indices are the cell indices of `Rd.cellIndex`. -/
theorem zcellIndex_natCast (j : ℕ) : zcellIndex (V := V) (j : ℤ) = cellIndex j := rfl

/-- For natural levels the cubes are the cells of `Rd.cell`. -/
theorem zcell_natCast (j : ℕ) : zcell (V := V) (j : ℤ) = cell j := rfl

/-- For natural levels the centres are those of `Rd.cellCenter`. -/
theorem zcellCenter_natCast (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) :
    zcellCenter (V := V) (j : ℤ) m = cellCenter j m := rfl

/-- Every point lies in the cell of its index. -/
theorem mem_cell_cellIndex (j : ℕ) (x : V) : x ∈ cell j (cellIndex j x) := rfl

/-- The coordinates of a centre. -/
theorem repr_cellCenter (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) (i : Fin (finrank ℝ V)) :
    (gridBasis V).repr (cellCenter j m) i = ((m i : ℝ) + 1 / 2) / 2 ^ j := by
  rw [← zcellCenter_natCast, repr_zcellCenter, zpow_natCast]

/-- On a cell, every coordinate differs from that of the centre by at most `2^(-j)/2`. -/
theorem abs_repr_sub_cellCenter_le {j : ℕ} {m : Fin (finrank ℝ V) → ℤ} {x : V}
    (hx : x ∈ cell j m) (i : Fin (finrank ℝ V)) :
    |(gridBasis V).repr (x - cellCenter j m) i| ≤ 1 / 2 / 2 ^ j := by
  rw [← zcellCenter_natCast, ← zpow_natCast]
  exact abs_repr_sub_zcellCenter_le hx i

/-- **Cells are small**: `‖x - c_{j,m}‖ ≤ n 2^(-j)` on `P_{j,m}`. -/
theorem norm_sub_cellCenter_le {j : ℕ} {m : Fin (finrank ℝ V) → ℤ} {x : V} (hx : x ∈ cell j m) :
    ‖x - cellCenter j m‖ ≤ finrank ℝ V / 2 ^ j := by
  rw [← zcellCenter_natCast, ← zpow_natCast]
  exact norm_sub_zcellCenter_le hx

/-- The cell index is measurable. -/
theorem measurable_cellIndex [MeasurableSpace V] [BorelSpace V] (j : ℕ) :
    Measurable (cellIndex (V := V) j) :=
  measurable_zcellIndex j

/-- Cells are measurable. -/
theorem measurableSet_cell [MeasurableSpace V] [BorelSpace V] (j : ℕ)
    (m : Fin (finrank ℝ V) → ℤ) : MeasurableSet (cell (V := V) j m) :=
  measurableSet_zcell j m

/-- **Counting centres**: at most `(2ρ + 2)^n` centres of level `j` lie in the ball of radius
`ρ 2^(-j)` around `x`. -/
theorem card_le_of_norm_cellCenter_sub_le (j : ℕ) (x : V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (S : Finset (Fin (finrank ℝ V) → ℤ)) (hS : ∀ m ∈ S, ‖cellCenter j m - x‖ ≤ ρ / 2 ^ j) :
    (S.card : ℝ) ≤ (2 * ρ + 2) ^ finrank ℝ V := by
  set a : Fin (finrank ℝ V) → ℝ := fun i => (2 : ℝ) ^ j * (gridBasis V).repr x i
  set T := Fintype.piFinset fun i => Finset.Icc ⌈a i - ρ - 1 / 2⌉ ⌊a i + ρ - 1 / 2⌋
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hST : S ⊆ T := fun m hm => by
    rw [Fintype.mem_piFinset]
    intro i
    have h := (abs_repr_le_norm (cellCenter j m - x) i).trans (hS m hm)
    rw [map_sub, PiLp.sub_apply, repr_cellCenter] at h
    have key : ((m i : ℝ) + 1 / 2) / 2 ^ j - (gridBasis V).repr x i =
        ((m i : ℝ) + 1 / 2 - a i) / 2 ^ j := by
      simp only [a]
      field_simp
    rw [key, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos, abs_le] at h
    have h1 := h.1
    have h2 := h.2
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  calc (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hST
    _ = ∏ i, ((Finset.Icc ⌈a i - ρ - 1 / 2⌉ ⌊a i + ρ - 1 / 2⌋).card : ℝ) := by
        rw [Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ ∏ _i : Fin (finrank ℝ V), (2 * ρ + 2) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        rw [Int.card_Icc]
        have hc := Int.le_ceil (a i - ρ - 1 / 2)
        have hf := Int.floor_le (a i + ρ - 1 / 2)
        rcases le_or_gt 0 (⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉) with h | h
        · have hcast : (((⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉).toNat : ℕ) : ℝ) =
              ((⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
          rw [hcast]
          push_cast
          linarith
        · rw [Int.toNat_of_nonpos h.le]
          push_cast
          linarith
    _ = (2 * ρ + 2) ^ finrank ℝ V := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The cells partition the space -/

section Partition

variable [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- Cells of the same level with different indices are disjoint: they are the fibres of
`Rd.cellIndex j` (Mathlib's `pairwise_disjoint_fiber`). -/
theorem cell_disjoint (j : ℕ) : Pairwise (Function.onFun Disjoint (cell (V := V) j)) :=
  zcell_disjoint j

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cells of one level cover the space. -/
theorem iUnion_cell (j : ℕ) : ⋃ m, cell (V := V) j m = Set.univ :=
  iUnion_zcell j

/-- `∫ F = ∑_m ∫_{P_{j,m}} F`. -/
theorem lintegral_eq_tsum_cell (j : ℕ) (F : V → ℝ≥0∞) :
    ∫⁻ x, F x = ∑' m, ∫⁻ x in cell j m, F x := by
  rw [← lintegral_iUnion (measurableSet_cell j) (cell_disjoint j), iUnion_cell,
    Measure.restrict_univ]

/-- `‖g‖_p^p = ∑_m ‖1_{P_{j,m}} g‖_p^p`. -/
theorem eLpNorm_rpow_eq_tsum_cell {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) (j : ℕ) :
    eLpNorm g p volume ^ p.toReal =
      ∑' m, eLpNorm ((cell j m).indicator g) p volume ^ p.toReal := by
  rw [eLpNorm_rpow_eq hg hp0 hp, lintegral_eq_tsum_cell j]
  congr 1
  funext m
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_cell j m).nullMeasurableSet,
    eLpNorm_rpow_eq hg.restrict hp0 hp]

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Bounded overlap of the centres**: at most `⌈(2ρ + 2)^n⌉` centres of level `j` lie in a
ball of radius `ρ 2^(-j)`. -/
theorem card_le_of_norm_sub_cellCenter_le (j : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : V)
    (S : Finset (Fin (finrank ℝ V) → ℤ)) (hS : ∀ m ∈ S, ‖x - cellCenter j m‖ ≤ ρ / 2 ^ j) :
    S.card ≤ ⌈(2 * ρ + 2) ^ finrank ℝ V⌉₊ := by
  have h := card_le_of_norm_cellCenter_sub_le j x hρ S fun m hm => by
    rw [norm_sub_rev]
    exact hS m hm
  exact_mod_cast h.trans (Nat.le_ceil _)

end Partition

/-! ### Bounded overlap -/

/-- If every finite set of indices with property `P` has at most `N` elements, the indices with
property `P` form a finite set with at most `N` elements. -/
theorem exists_finset_of_card_le {ι : Type*} {P : ι → Prop} {N : ℕ}
    (h : ∀ S : Finset ι, (∀ m ∈ S, P m) → S.card ≤ N) :
    ∃ T : Finset ι, (∀ m, P m → m ∈ T) ∧ T.card ≤ N := by
  have hfin : {m | P m}.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := h S fun m hm => hS hm
    omega
  exact ⟨hfin.toFinset, fun m hm => hfin.mem_toFinset.2 hm,
    h _ fun m hm => hfin.mem_toFinset.1 hm⟩

/-- **Bounded overlap, pointwise**: if at most `N` of the `g m` are nonzero, then
`‖∑' m, g m‖^p ≤ N^(p-1) ∑' m, ‖g m‖^p` for `p ≥ 1`. -/
theorem enorm_tsum_rpow_le_of_overlap {ι : Type*} (g : ι → ℂ) {N : ℕ}
    (hN : ∀ S : Finset ι, (∀ m ∈ S, g m ≠ 0) → S.card ≤ N) {p : ℝ} (hp : 1 ≤ p) :
    ‖∑' m, g m‖ₑ ^ p ≤ (N : ℝ≥0∞) ^ (p - 1) * ∑' m, ‖g m‖ₑ ^ p := by
  obtain ⟨T, hT, hTN⟩ := exists_finset_of_card_le hN
  have hzero : ∀ m ∉ T, g m = 0 := fun m hm => by_contra fun h => hm (hT m h)
  rw [tsum_eq_sum hzero]
  calc ‖∑ m ∈ T, g m‖ₑ ^ p ≤ (∑ m ∈ T, ‖g m‖ₑ) ^ p :=
        ENNReal.rpow_le_rpow (eNorm_sum_le _ _) (by linarith)
    _ ≤ (T.card : ℝ≥0∞) ^ (p - 1) * ∑ m ∈ T, ‖g m‖ₑ ^ p :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hp
    _ ≤ (N : ℝ≥0∞) ^ (p - 1) * ∑' m, ‖g m‖ₑ ^ p :=
        mul_le_mul' (ENNReal.rpow_le_rpow (by exact_mod_cast hTN) (by linarith))
          (sum_le_tsum _)

/-- **Bounded overlap in `L_p`**: if at every point at most `N` of the `g m` are nonzero and
`F = ∑' m, g m` almost everywhere, then `‖F‖_p^p ≤ N^(p-1) ∑' m, ‖g m‖_p^p`. -/
theorem eLpNorm_rpow_le_of_overlap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Countable ι] {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : ι → α → ℂ}
    (hg : ∀ m, AEStronglyMeasurable (g m) μ) {N : ℕ}
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, g m x ≠ 0) → S.card ≤ N) {F : α → ℂ}
    (hF : AEStronglyMeasurable F μ) (hFg : ∀ᵐ x ∂μ, F x = ∑' m, g m x) :
    eLpNorm F p μ ^ p.toReal ≤
      (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, eLpNorm (g m) p μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  rw [eLpNorm_rpow_eq hF hp0 hp]
  calc ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, ‖g m x‖ₑ ^ p.toReal ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hFg] with x hx
        rw [hx]
        exact enorm_tsum_rpow_le_of_overlap (fun m => g m x) (hN x) hpr
    _ = (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, ∫⁻ x, ‖g m x‖ₑ ^ p.toReal ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ENNReal.natCast_ne_top N)), lintegral_tsum fun m => ((hg m).eNorm.pow_const _)]
    _ = (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, eLpNorm (g m) p μ ^ p.toReal := by
        congr 2
        funext m
        rw [eLpNorm_rpow_eq (hg m) hp0 hp]

end Rd
