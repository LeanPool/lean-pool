/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.LocalizationCover
public import LeanPool.ArnoldKAM.Arnold1963.Main.LocalThreshold

/-!
Finite localization and a perturbation-independent common threshold. Patches may have
different numerical bounds. The loss budget accounts for the number of patches rather than
adding overlapping patch volumes as though they were disjoint.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- A finite collection of Hamiltonian patches with a common threshold and global measure budget. -/
structure FiniteLocalization (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) (ρ : ℝ≥0) (κ : ℝ) where
  dimension_pos : 0 < n
  /-- The finite set of local Hamiltonian patches used for the global construction. -/
  patches : Finset (HamiltonianPatch n H₀ ambient)
  /-- The common positive angle width available in every patch. -/
  width : ℝ≥0
  width_pos : 0 < width
  width_le_one : width ≤ 1
  width_le : width ≤ ρ
  /-- The per-patch relative measure-loss tolerance. -/
  fraction : ℝ
  fraction_pos : 0 < fraction
  fraction_lt_one : fraction < 1
  fraction_le : fraction ≤ κ
  /-- The relative volume allowed to escape the finite patch cover. -/
  coverError : ℝ
  coverError_pos : 0 < coverError
  coverError_lt_one : coverError < 1
  cover : volume (realSlice ambient \ ⋃ c ∈ patches, realSlice c.domain) <
    ENNReal.ofReal coverError * volume (realSlice ambient)
  budget : coverError + (patches.card : ℝ) * fraction ≤ κ
  /-- The positive perturbation threshold valid uniformly across the patch collection. -/
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_le : ∀ c ∈ patches, threshold ≤ c.threshold width fraction

theorem GlobalHamiltonianData.exists_finiteLocalization {n : ℕ}
    {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ ambient) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) : Nonempty (FiniteLocalization n H₀ ambient ρ κ) := by
  let τ := min κ 1
  have hτ : 0 < τ := lt_min hκ zero_lt_one
  have hτκ : τ ≤ κ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  obtain ⟨s, hs⟩ := h.exists_cover (τ / 4) (by positivity)
  let η := τ / (4 * ((s.card : ℝ) + 1))
  have hm : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hd : 0 < 4 * ((s.card : ℝ) + 1) := by positivity
  have hη : 0 < η := div_pos hτ hd
  have heq : η * (4 * ((s.card : ℝ) + 1)) = τ := div_mul_cancel₀ _ hd.ne'
  have hη1 : η < 1 := by nlinarith
  have hητ : η ≤ τ := by nlinarith
  have hb : τ / 4 + (s.card : ℝ) * η ≤ κ := by nlinarith
  have hw : (0 : ℝ≥0) < min ρ 1 := lt_min hρ zero_lt_one
  obtain ⟨M, hM, hMs⟩ := HamiltonianPatch.exists_common_threshold s h.dimension_pos hw hη
  exact ⟨{
    dimension_pos := h.dimension_pos
    patches := s
    width := min ρ 1
    width_pos := hw
    width_le_one := min_le_right _ _
    width_le := min_le_left _ _
    fraction := η
    fraction_pos := hη
    fraction_lt_one := hη1
    fraction_le := hητ.trans hτκ
    coverError := τ / 4
    coverError_pos := by positivity
    coverError_lt_one := by linarith
    cover := hs
    budget := hb
    threshold := M
    threshold_pos := hM
    threshold_le := hMs }⟩

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)

theorem parameters (c : L.patches) :
    Iteration.InitialParameters n (c.val.seed L.width L.fraction)
      c.val.lower c.val.upper L.width L.fraction c.val.typeConstant :=
  c.val.parameters L.dimension_pos L.width_pos L.width_le_one L.fraction_pos L.fraction_lt_one

/-- The initial iteration data for a perturbation restricted to a selected patch. -/
def data (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) :=
  c.val.initialData L.dimension_pos L.width_pos L.fraction_pos f L.width_le
    (hf.trans (L.threshold_le c c.property))

theorem local_result (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) : LocalKAMResult (L.parameters c) (L.data f hf c) := localKAM _ _

theorem hamiltonian_zero (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) (z : ComplexPhaseSpace n) :
    (L.data f hf c).hamiltonian (L.parameters c) 0 z = H₀ z.1 + f.toFun z := rfl

theorem patches_nonempty : L.patches.Nonempty := by
  classical
  by_contra he
  have hempty : L.patches = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hh := L.cover
  simp only [hempty, Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty] at hh
  have hle : ENNReal.ofReal L.coverError * volume (realSlice ambient) ≤
      volume (realSlice ambient) := by
    calc
      _ ≤ 1 * volume (realSlice ambient) :=
        mul_le_mul' (ENNReal.ofReal_le_one.mpr L.coverError_lt_one.le) le_rfl
      _ = _ := one_mul _
  exact (not_lt_of_ge hle) hh

end FiniteLocalization
end KamProject.Arnold1963
