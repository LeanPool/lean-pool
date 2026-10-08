/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AlignedSubdivision
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport

/-!
# High-contrast homogenization: Provider.PortableHistory.MajorizationIndex

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Splitting an aligned index along the subdivision of the coarse block

The proof of `p.fixed.geometry.one.grid.propagation` partitions the terminal cell
`⋄_T^q` into its `3^{d(T-b)}` aligned scale-`b` cells and reads the part of the
centered maximum `e.scale.selection.fluctuation.history` carried by scales at most `b`
on each of them separately.

For that reading, an aligned scale-`j` center inside `⋄_T^q` has to be exhibited
as an aligned scale-`j` center inside one of the scale-`b` children.  In the
index coordinates of the adapted cubes this is division with a *centered*
remainder: writing `m = 3^{b-j}`, every integer `w` is `w' + m y` with
`2|w'| < m`, and the admissibility bound `2|w| < 3^{T-j} = m 3^{T-b}` then forces
`2|y| < 3^{T-b}`, both bounds being strict because the powers of three are odd.
No center falls on a face of the subdivision: the centered remainder is exact.

The center of the child is an integral vector, so the response over the
scale-`j` cell at `w` is the response over the scale-`j` cell at `w'` evaluated
at the translated sample, which is the form the stationarity transport consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

open MeasureTheory

noncomputable section

/-! ## Division with a centered remainder -/

/-- **Centered division by an odd modulus.**  Every integer splits as
`w = w' + m y` with `|w'|` below half of `m`, and an admissibility bound
`2|w| < m M` with `M` odd forces the strict bound `2|y| < M`. -/
theorem exists_centered_split {m M c e : ℤ} (hm : 0 < m) (hc : m = 2 * c + 1)
    (he : M = 2 * e + 1) {w : ℤ} (hw : 2 * |w| < m * M) :
    ∃ y w' : ℤ, w = w' + m * y ∧ 2 * |w'| < m ∧ 2 * |y| < M := by
  obtain ⟨y, r, hsplit, hr0, hrm⟩ : ∃ y r : ℤ, w + c = m * y + r ∧ 0 ≤ r ∧ r < m :=
    ⟨(w + c) / m, (w + c) % m, (Int.mul_ediv_add_emod (w + c) m).symm,
      Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
  have hrc : |r - c| ≤ c := abs_le.mpr ⟨by omega, by omega⟩
  have hwabs : -|w| ≤ w ∧ w ≤ |w| := ⟨neg_abs_le w, le_abs_self w⟩
  have hrcabs : -c ≤ r - c ∧ r - c ≤ c := abs_le.mp hrc
  refine ⟨y, r - c, by linarith only [hsplit], ?_, ?_⟩
  · have h2 : |2 * (r - c)| = 2 * |r - c| := by rw [abs_mul]; norm_num
    rw [← h2]
    rcases abs_cases (2 * (r - c)) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  · have hmy : m * y = w - (r - c) := by linarith only [hsplit]
    have hup : m * (2 * y) < m * (M + 1) := by
      have h1 : m * (2 * y) = 2 * (m * y) := by ring
      have h2 : m * (M + 1) = m * M + m := by ring
      rw [h1, h2, hmy]
      linarith only [hw, hwabs.2, hrcabs.1, hc]
    have hlo : m * (-(2 * y)) < m * (M + 1) := by
      have h1 : m * (-(2 * y)) = -(2 * (m * y)) := by ring
      have h2 : m * (M + 1) = m * M + m := by ring
      rw [h1, h2, hmy]
      linarith only [hw, hwabs.1, hrcabs.2, hc]
    have hup' : 2 * y < M + 1 := lt_of_mul_lt_mul_left hup hm.le
    have hlo' : -(2 * y) < M + 1 := lt_of_mul_lt_mul_left hlo hm.le
    have h2 : |2 * y| = 2 * |y| := by rw [abs_mul]; norm_num
    rw [← h2]
    rcases abs_cases (2 * y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega

section Cells

variable {d : ℕ}

/-- The three-power exponents of the two stages of the subdivision add up. -/
theorem three_pow_toNat_split {j b T : ℤ} (hjb : j ≤ b) (hbT : b ≤ T) :
    (3 : ℤ) ^ (T - j).toNat = (3 : ℤ) ^ (b - j).toNat * (3 : ℤ) ^ (T - b).toNat := by
  rw [← pow_add]
  congr 1
  omega

/-- **Every aligned scale-`j` center of the terminal cell sits in a scale-`b`
child.**  The index splits as `w = w' + 3^{b-j} y`, with the child index `y`
admissible for the terminal cell and the residual index `w'` admissible for the
centered scale-`b` cell. -/
theorem exists_index_split {q : Mat d} (hq : q.PosDef) {j b T : ℤ} (hjb : j ≤ b)
    (hbT : b ≤ T) {w : Fin d → ℤ} (hw : adaptedCellCenter q j w ∈ adaptedCell q T) :
    ∃ y w' : Fin d → ℤ, adaptedCellCenter q b y ∈ adaptedCell q T ∧
      adaptedCellCenter q j w' ∈ adaptedCell q b ∧
      ∀ i, w i = w' i + (3 : ℤ) ^ (b - j).toNat * y i := by
  obtain ⟨c, hc⟩ := Recurrence.odd_three_pow (b - j).toNat
  obtain ⟨e, he⟩ := Recurrence.odd_three_pow (T - b).toNat
  have hm : (0 : ℤ) < (3 : ℤ) ^ (b - j).toNat := by positivity
  have hwbound := (Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq (le_trans hjb hbT) w).mp hw
  have hstep : ∀ i, 2 * |w i| < (3 : ℤ) ^ (b - j).toNat * (3 : ℤ) ^ (T - b).toNat := by
    intro i
    rw [← three_pow_toNat_split hjb hbT]
    exact hwbound i
  choose y w' hsum hw' hy using fun i => exists_centered_split hm hc he (hstep i)
  refine ⟨y, w', (Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq hbT y).mpr hy,
    (Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq hjb w').mpr hw', hsum⟩

/-- **The centers add along the split.**  The scale-`j` center at `w` is the
scale-`b` center at `y` translated by the scale-`j` center at `w'`. -/
theorem adaptedCellCenter_split (q : Mat d) {j b : ℤ} (hjb : j ≤ b) {y w' w : Fin d → ℤ}
    (hw : ∀ i, w i = w' i + (3 : ℤ) ^ (b - j).toNat * y i) :
    adaptedCellCenter q j w = adaptedCellCenter q b y + adaptedCellCenter q j w' := by
  have hpow : (3 : ℝ) ^ j * (3 : ℝ) ^ ((b - j).toNat : ℕ) = (3 : ℝ) ^ b := by
    rw [← zpow_natCast (3 : ℝ) ((b - j).toNat), ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hcast : (fun i => ((w i : ℝ))) =
      (3 : ℝ) ^ ((b - j).toNat : ℕ) • (fun i => ((y i : ℝ))) + fun i => ((w' i : ℝ)) := by
    funext i
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    push_cast
    ring
  rw [adaptedCellCenter, adaptedCellCenter, adaptedCellCenter, hcast, matVecMul_add,
    matVecMul_smul, smul_add, smul_smul, hpow]

/-- **The response at a split index is the response at the residual index of the
translated sample.**  This is the translation invariance of the variational
coarse block read along the subdivision. -/
theorem adaptedResponse_split (q : Mat d) {j b : ℤ} {y w' w v : Fin d → ℤ}
    (hw : adaptedCellCenter q j w = adaptedCellCenter q b y + adaptedCellCenter q j w')
    (hv : adaptedCellCenter q b y = fun i => (v i : ℝ)) (a : CoeffSpace d) :
    adaptedResponse q j w a = adaptedResponse q j w' (translateCoeff v a) := by
  have hadd : ∀ (x z : Vec d) (U : Set (Vec d)),
      translateSet (x + z) U = translateSet x (translateSet z U) := by
    intro x z U
    ext u
    simp only [mem_translateSet_iff_sub_mem]
    constructor
    · intro hu; simpa [sub_sub, add_comm] using hu
    · intro hu; simpa [sub_sub, add_comm] using hu
  have hcell : adaptedCellAt q j w =
      translateSet (Source.AKL.intTranslation v) (adaptedCellAt q j w') := by
    rw [Recurrence.adaptedCellAt_eq_translateSet, Recurrence.adaptedCellAt_eq_translateSet, hw,
      hadd, hv]
    rfl
  rw [adaptedResponse, adaptedResponse, hcell, Recurrence.coarseBlock_translateSet]

end Cells

end

end PortableHistory
end HighContrast
end HCPolySupport
