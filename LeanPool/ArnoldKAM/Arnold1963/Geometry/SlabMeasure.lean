/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.TypeD
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.PolydiscBoundary

/-!
Fubini slab estimates using a coordinate with nonzero covector coefficient. The argument
retains the maximum norm and introduces no Euclidean norm comparison.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal NNReal
namespace KamProject.Arnold1963

private theorem volume_affine_strip {A B a : ℝ} (hA : A ≠ 0) :
    volume {y : ℝ | |A * y + B| < a} = ENNReal.ofReal (2 * a / |A|) := by
  have he : {y : ℝ | |A * y + B| < a} = Metric.ball (-B / A) (a / |A|) := by
    ext y
    rw [Metric.mem_ball, Real.dist_eq]
    change |A * y + B| < a ↔ |y - -B / A| < a / |A|
    have heq : A * y + B = A * (y - -B / A) := by field_simp; ring
    rw [heq, abs_mul, lt_div_iff₀ (abs_pos.mpr hA), mul_comm]
  rw [he, Real.volume_ball]
  congr 1
  ring

theorem realLebesgue_le_box_of_fiber {n : ℕ} (c r : RealSpace n)
    (hr : ∀ i, 0 < r i) (j : Fin n) {s : Set (RealSpace n)} (hs : MeasurableSet s)
    (hsub : s ⊆ realSlice (realCenteredPolydisc c r)) {L : ℝ} (hL : 0 ≤ L)
    (hfib : ∀ x : RealSpace n,
      volume {y : ℝ | update x j y ∈ s} ≤ ENNReal.ofReal L) :
    realLebesgue n s ≤ ENNReal.ofReal (L / (2 * r j)) *
      realVolume (realCenteredPolydisc c r) := by
  classical
  let B := realSlice (realCenteredPolydisc c r)
  let C := ENNReal.ofReal (L / (2 * r j))
  have hB : MeasurableSet B :=
    (isClosed_realSlice (isClosed_realCenteredPolydisc c r)).measurableSet
  have hC : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hupdate (x : RealSpace n) : Measurable (fun y : ℝ => update x j y) :=
    (continuous_const.update j continuous_id).measurable
  have hm : (∫⁻ x, s.indicator 1 x ∂realLebesgue n) ≤
      ∫⁻ x, C * B.indicator 1 x ∂realLebesgue n := by
    apply lintegral_le_of_lmarginal_le {j} (measurable_one.indicator hs)
      (measurable_const.mul (measurable_one.indicator hB))
    rw [lmarginal_singleton, lmarginal_singleton]
    intro x
    change (∫⁻ y : ℝ, s.indicator (1 : RealSpace n → ℝ≥0∞) (update x j y)) ≤
      ∫⁻ y : ℝ, C * B.indicator (1 : RealSpace n → ℝ≥0∞) (update x j y)
    by_cases hx : ∀ i, i ≠ j → x i ∈ Icc (c i - r i) (c i + r i)
    · have hb : (fun y : ℝ => B.indicator (1 : RealSpace n → ℝ≥0∞) (update x j y)) =
          (Icc (c j - r j) (c j + r j)).indicator (1 : ℝ → ℝ≥0∞) := by
        funext y
        have he : update x j y ∈ B ↔ y ∈ Icc (c j - r j) (c j + r j) := by
          dsimp [B]
          rw [realSlice_realCenteredPolydisc, mem_univ_pi]
          constructor
          · intro h
            simpa using h j
          · intro hy i
            by_cases hi : i = j
            · subst i; simpa using hy
            · simpa [update_of_ne hi] using hx i hi
        simp only [indicator, he, Pi.one_apply]
      rw [lintegral_const_mul' _ _ hC, hb, lintegral_indicator_one measurableSet_Icc,
        Real.volume_Icc]
      have he : C * ENNReal.ofReal (c j + r j - (c j - r j)) = ENNReal.ofReal L := by
        dsimp [C]
        rw [← ENNReal.ofReal_mul (div_nonneg hL (mul_nonneg (by norm_num) (hr j).le))]
        congr 1
        field_simp [ne_of_gt (hr j)]
        ring
      rw [he]
      calc
        _ = volume {y : ℝ | update x j y ∈ s} := by
          change (∫⁻ y, ((fun y : ℝ => update x j y) ⁻¹' s).indicator 1 y) =
            volume ((fun y : ℝ => update x j y) ⁻¹' s)
          exact lintegral_indicator_one (hs.preimage (hupdate x))
        _ ≤ _ := hfib x
    · have hnot (y : ℝ) : update x j y ∉ B := by
        intro hy
        apply hx
        intro i hi
        dsimp [B] at hy
        rw [realSlice_realCenteredPolydisc] at hy
        simpa [update_of_ne hi] using (mem_univ_pi.mp hy) i
      have hsnot (y : ℝ) : update x j y ∉ s := fun hy => hnot y (hsub hy)
      simp only [indicator_of_notMem (hsnot _), lintegral_zero]
      exact zero_le
  rw [lintegral_indicator_one hs, lintegral_const_mul' _ _ hC,
    lintegral_indicator_one hB] at hm
  exact hm

theorem polydisc_slab_coordinate_le {n : ℕ} (c r ℓ : RealSpace n)
    (hr : ∀ i, 0 < r i) (j : Fin n) (hj : ℓ j ≠ 0) (b a : ℝ) (ha : 0 ≤ a) :
    realVolume (realCenteredPolydisc c r ∩ complexSlab ℓ b a) ≤
      ENNReal.ofReal (a / (|ℓ j| * r j)) * realVolume (realCenteredPolydisc c r) := by
  classical
  have hcont : Continuous (fun x : RealSpace n => ∑ i, ℓ i * x i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have he : realSlice (realCenteredPolydisc c r ∩ complexSlab ℓ b a) =
      realSlice (realCenteredPolydisc c r) ∩ {x | |(∑ i, ℓ i * x i) - b| < a} := by
    ext x
    simp [realSlice, complexSlab, realCovectorPairing, complexify,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub]
  have hm : MeasurableSet (realSlice (realCenteredPolydisc c r) ∩
      {x : RealSpace n | |(∑ i, ℓ i * x i) - b| < a}) :=
    (isClosed_realSlice (isClosed_realCenteredPolydisc c r)).measurableSet.inter
      (isOpen_lt ((hcont.sub continuous_const).abs) continuous_const).measurableSet
  have hfib (x : RealSpace n) : volume {y : ℝ | update x j y ∈
      realSlice (realCenteredPolydisc c r) ∩ {x | |(∑ i, ℓ i * x i) - b| < a}} ≤
      ENNReal.ofReal (2 * a / |ℓ j|) := by
    have heq (y : ℝ) : (∑ i, ℓ i * update x j y i) - b =
        ℓ j * y + ((∑ i ∈ Finset.univ.erase j, ℓ i * x i) - b) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      simp only [update_self]
      rw [show (∑ i ∈ Finset.univ.erase j, ℓ i * update x j y i) =
          ∑ i ∈ Finset.univ.erase j, ℓ i * x i from
        Finset.sum_congr rfl (fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)])]
      ring
    calc
      _ ≤ volume {y : ℝ | |ℓ j * y + ((∑ i ∈ Finset.univ.erase j, ℓ i * x i) - b)| < a} :=
        measure_mono fun y hy => by
          change |ℓ j * y + ((∑ i ∈ Finset.univ.erase j, ℓ i * x i) - b)| < a
          rw [← heq y]
          exact hy.2
      _ = _ := volume_affine_strip hj
  have hh := realLebesgue_le_box_of_fiber c r hr j hm inter_subset_left
    (div_nonneg (by positivity) (abs_nonneg _)) hfib
  rw [realVolume, he]
  have hc : (2 * a / |ℓ j|) / (2 * r j) = a / (|ℓ j| * r j) := by ring
  simpa only [hc] using hh

theorem realCenteredPolydisc_typeD {n : ℕ} (hn : 0 < n) (c r : RealSpace n)
    (hr : ∀ j, 0 < r j) : TypeD (realCenteredPolydisc c r) (polydiscTypeConstant r) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let j₀ : Fin n := ⟨0, hn⟩
  have hD : 0 < polydiscTypeConstant r :=
    (inv_pos.mpr (hr j₀)).trans_le (Finset.single_le_sum
      (fun i _ => inv_nonneg.mpr (hr i).le) (Finset.mem_univ j₀))
  refine ⟨hD, isCompact_realCenteredPolydisc c r, ?_, polydisc_boundary_le c r hr, ?_⟩
  · rw [realVolume_realCenteredPolydisc]
    exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ =>
      (ENNReal.ofReal_pos.mpr (by linarith [hr j])).ne')
  · intro ℓ b a hℓ ha
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |ℓ i|)
      ⟨j₀, Finset.mem_univ _⟩
    have hmax : covectorLength ℓ ≤ n * |ℓ j| := by
      calc
        _ ≤ ∑ _i : Fin n, |ℓ j| := Finset.sum_le_sum fun i hi => hj i hi
        _ = _ := by simp
    have hjpos : 0 < |ℓ j| := by nlinarith
    have hjne : ℓ j ≠ 0 := abs_pos.mp hjpos
    have hrecip : 1 / |ℓ j| ≤ (n : ℝ) / covectorLength ℓ :=
      (div_le_div_iff₀ hjpos hℓ).mpr (by simpa only [one_mul] using hmax)
    have hjD : (r j)⁻¹ ≤ polydiscTypeConstant r :=
      Finset.single_le_sum (fun i _ => inv_nonneg.mpr (hr i).le) (Finset.mem_univ j)
    apply (polydisc_slab_coordinate_le c r ℓ hr j hjne b a ha).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
    calc
      a / (|ℓ j| * r j) = (a * (1 / |ℓ j|)) * (r j)⁻¹ := by ring
      _ ≤ (a * ((n : ℝ) / covectorLength ℓ)) * polydiscTypeConstant r :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrecip ha) hjD
          (inv_nonneg.mpr (hr j).le) (by positivity)
      _ ≤ polydiscTypeConstant r * n * (2 * a / covectorLength ℓ) := by
        have hh : 0 ≤ (a * ((n : ℝ) / covectorLength ℓ)) * polydiscTypeConstant r :=
          mul_nonneg (by positivity) hD.le
        have he : polydiscTypeConstant r * n * (2 * a / covectorLength ℓ) =
            2 * ((a * ((n : ℝ) / covectorLength ℓ)) * polydiscTypeConstant r) := by ring
        rw [he]
        linarith

end KamProject.Arnold1963
