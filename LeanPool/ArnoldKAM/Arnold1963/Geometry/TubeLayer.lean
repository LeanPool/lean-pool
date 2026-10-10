/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.CovectorTube

/-!
Two-sided tube boundary layers. Right limits extend open-slab bounds to closed slabs.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace KamProject.Arnold1963

theorem TypeD.realVolume_ne_top {n} {Ω : Set (ComplexSpace n)} {D : ℝ}
    (h : TypeD Ω D) : realVolume Ω ≠ ∞ := by
  change volume (realSlice Ω) ≠ ∞
  exact (isCompact_realSlice h.compact).measure_lt_top.ne

theorem TypeD.closed_slab {n} {Ω : Set (ComplexSpace n)} {D : ℝ} (h : TypeD Ω D)
    (ℓ : RealSpace n) (c a : ℝ) (hℓ : 0 < covectorLength ℓ) (ha : 0 ≤ a) :
    realVolume (Ω ∩ {z | ‖realCovectorPairing ℓ z - (c : ℂ)‖ ≤ a}) ≤
      ENNReal.ofReal (D * n * (2 * a / covectorLength ℓ)) * realVolume Ω := by
  have ht : Tendsto (fun t : ℝ => ENNReal.ofReal (D * n * (2 * t / covectorLength ℓ)) *
      realVolume Ω) (𝓝[>] a)
      (𝓝 (ENNReal.ofReal (D * n * (2 * a / covectorLength ℓ)) * realVolume Ω)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr h.realVolume_ne_top)
    exact (ENNReal.continuous_ofReal.comp (by fun_prop)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realVolume_mono (inter_subset_inter_right Ω (fun z hx =>
    (show ‖realCovectorPairing ℓ z - (c : ℂ)‖ ≤ a from hx).trans_lt ht))).trans
    (h.slab ℓ c t hℓ (ha.trans ht.le))

theorem realCovectorPairing_complexify {n} (ℓ x : RealSpace n) :
    realCovectorPairing ℓ (complexify x) = ((∑ j, ℓ j * x j : ℝ) : ℂ) := by
  simp [realCovectorPairing, complexify]

theorem TypeD.tube_layer {n} {Ω : Set (ComplexSpace n)} {D : ℝ} (h : TypeD Ω D)
    (ℓ : RealSpace n) (c a₁ a₂ : ℝ) (hℓ : 0 < covectorLength ℓ)
    (_ha₁ : 0 ≤ a₁) (haa : a₁ ≤ a₂) :
    realVolume (Ω ∩ {z | a₁ ≤ ‖realCovectorPairing ℓ z - (c : ℂ)‖ ∧
      ‖realCovectorPairing ℓ z - (c : ℂ)‖ < a₂}) ≤
      ENNReal.ofReal (2 * D * n * ((a₂ - a₁) / covectorLength ℓ)) * realVolume Ω := by
  let Spos := Ω ∩ {z | ‖realCovectorPairing ℓ z - ((c + (a₁ + a₂) / 2 : ℝ) : ℂ)‖ ≤ (a₂ - a₁) / 2}
  let Sneg := Ω ∩ {z | ‖realCovectorPairing ℓ z - ((c - (a₁ + a₂) / 2 : ℝ) : ℂ)‖ ≤ (a₂ - a₁) / 2}
  have hsub : realSlice (Ω ∩ {z | a₁ ≤ ‖realCovectorPairing ℓ z - (c : ℂ)‖ ∧
      ‖realCovectorPairing ℓ z - (c : ℂ)‖ < a₂}) ⊆ realSlice Spos ∪ realSlice Sneg := by
    intro x ⟨hxΩ, hlo, hhi⟩
    simp only [realCovectorPairing_complexify, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hlo hhi
    by_cases hx : 0 ≤ (∑ j, ℓ j * x j) - c
    · left
      refine ⟨hxΩ, ?_⟩
      change ‖realCovectorPairing ℓ (complexify x) - _‖ ≤ _
      simp only [realCovectorPairing_complexify, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      rw [abs_of_nonneg hx] at hlo hhi
      constructor <;> linarith
    · right
      refine ⟨hxΩ, ?_⟩
      change ‖realCovectorPairing ℓ (complexify x) - _‖ ≤ _
      simp only [realCovectorPairing_complexify, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      rw [abs_of_neg (lt_of_not_ge hx)] at hlo hhi
      constructor <;> linarith
  have hw : 0 ≤ (a₂ - a₁) / 2 := by linarith
  let C := D * n * (2 * ((a₂ - a₁) / 2) / covectorLength ℓ)
  have hC : 0 ≤ C := by dsimp [C]; positivity [h.constant_pos]
  calc
    _ ≤ realVolume Spos + realVolume Sneg :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal C * realVolume Ω + ENNReal.ofReal C * realVolume Ω :=
      add_le_add (h.closed_slab ℓ _ _ hℓ hw) (h.closed_slab ℓ _ _ hℓ hw)
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add hC hC]
      have he : C + C = 2 * D * n * ((a₂ - a₁) / covectorLength ℓ) := by dsimp [C]; ring
      rw [he]

end KamProject.Arnold1963
