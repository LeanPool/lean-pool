/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Leray Limit Slices

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Weak convergence against compactly supported tests extends to all global
`L²` tests when the sequence and limit have a common global norm bound. -/
theorem lerayLimit_globalWeakLp_of_compactSupport
    {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [R1Space α] [WeaklyLocallyCompactSpace α] {μ : Measure α} [μ.Regular]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ℕ → α → E) (G : α → E)
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : MemLp G 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ n, ‖(hF n).toLp (F n)‖ ≤ C)
    (hGbound : ‖hG.toLp G‖ ≤ C)
    (hlocal : ∀ (v : α → E), HasCompactSupport v → Continuous v →
      (hv : MemLp v 2 μ) →
      Tendsto (fun n => inner ℝ ((hF n).toLp (F n)) (hv.toLp v)) atTop
        (𝓝 (inner ℝ (hG.toLp G) (hv.toLp v)))) :
    ∀ (w : α → E), (hw : MemLp w 2 μ) →
      Tendsto (fun n => inner ℝ ((hF n).toLp (F n)) (hw.toLp w)) atTop
        (𝓝 (inner ℝ (hG.toLp G) (hw.toLp w))) := by
  intro w hw
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hCpos : 0 < C + 1 := by linarith only [hC]
  let δ : ℝ := ε / (8 * (C + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε (mul_pos (by norm_num) hCpos)
  have hδENN : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨v, hvSupport, hvClose, hvContinuous, hvMem⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hδENN.ne'
  let wLp : Lp E 2 μ := hw.toLp w
  let vLp : Lp E 2 μ := hvMem.toLp v
  have hLpClose : ‖wLp - vLp‖ ≤ δ := by
    rw [Lp.norm_def]
    have heq : eLpNorm (⇑(wLp - vLp)) 2 μ = eLpNorm (w - v) 2 μ := by
      rw [eLpNorm_congr_ae (Lp.coeFn_sub wLp vLp)]
      apply eLpNorm_congr_ae
      filter_upwards [hw.coeFn_toLp, hvMem.coeFn_toLp] with x hx hy
      simp [wLp, vLp, hx, hy]
    rw [heq]
    calc
      (eLpNorm (w - v) 2 μ).toReal ≤ (ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hvClose
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hlocalConv := hlocal v hvSupport hvContinuous hvMem
  have hlocalSmall : ∀ᶠ n : ℕ in atTop,
      dist (inner ℝ ((hF n).toLp (F n)) vLp)
        (inner ℝ (hG.toLp G) vLp) < ε / 2 := by
    exact (Metric.tendsto_nhds.mp hlocalConv) (ε / 2) (by linarith only [hε])
  have herrorBound (n : ℕ) :
      |inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (wLp - vLp)| ≤
        2 * C * δ := by
    calc
      |inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (wLp - vLp)| ≤
          ‖((hF n).toLp (F n)) - hG.toLp G‖ * ‖wLp - vLp‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2 * C) * δ := by
        apply mul_le_mul
        · calc
            ‖((hF n).toLp (F n)) - hG.toLp G‖ ≤
                ‖(hF n).toLp (F n)‖ + ‖hG.toLp G‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add (hFbound n) hGbound
            _ = 2 * C := by ring
        · exact hLpClose
        · exact norm_nonneg _
        · positivity
  have herrorSmall : 2 * C * δ < ε / 2 := by
    calc
      2 * C * δ ≤ 2 * (C + 1) * δ := by
        gcongr
        linarith only [hC]
      _ = ε / 4 := by
        dsimp [δ]
        field_simp
        ring
      _ < ε / 2 := by linarith only [hε]
  filter_upwards [hlocalSmall] with n hn
  have hsplit :
      inner ℝ ((hF n).toLp (F n)) (hw.toLp w) -
          inner ℝ (hG.toLp G) (hw.toLp w) =
        inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (vLp) +
          inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (wLp - vLp) := by
    calc
      _ = inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (hw.toLp w) := by
        rw [inner_sub_left]
      _ = inner ℝ (((hF n).toLp (F n)) - hG.toLp G)
            (vLp + (wLp - vLp)) := by
        congr 1
        dsimp [wLp, vLp]
        abel
      _ = inner ℝ (((hF n).toLp (F n)) - hG.toLp G) vLp +
            inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (wLp - vLp) := by
        rw [inner_add_right]
  have hdist : dist (inner ℝ ((hF n).toLp (F n)) (hw.toLp w))
      (inner ℝ (hG.toLp G) (hw.toLp w)) < ε := by
    rw [Real.dist_eq]
    calc
      |inner ℝ ((hF n).toLp (F n)) (hw.toLp w) -
          inner ℝ (hG.toLp G) (hw.toLp w)|
          ≤ |inner ℝ (((hF n).toLp (F n)) - hG.toLp G) vLp| +
            |inner ℝ (((hF n).toLp (F n)) - hG.toLp G) (wLp - vLp)| := by
        rw [hsplit]
        exact abs_add_le _ _
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_lt_of_le
        · simpa [inner_sub_left, Real.dist_eq, abs_sub_comm] using hn
        · exact le_of_lt ((herrorBound n).trans_lt herrorSmall)
      _ = ε := by ring
  exact hdist

end CKN.Leray

end
