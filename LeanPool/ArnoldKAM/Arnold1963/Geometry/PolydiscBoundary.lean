/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.Polydisc

/-!
Boundary-layer estimates for polydiscs, with the sum of inverse radii as the type constant.
The estimate also covers erosion beyond an individual coordinate radius.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

private theorem prod_sub_prod_le_sum_sub {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hba : ∀ i ∈ s, b i ≤ a i) (ha : ∀ i ∈ s, a i ≤ 1) :
    (∏ i ∈ s, a i) - (∏ i ∈ s, b i) ≤ ∑ i ∈ s, (a i - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hb' : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hba' : ∀ i ∈ s, b i ≤ a i := fun i hi => hba i (Finset.mem_insert_of_mem hi)
    have ha' : ∀ i ∈ s, a i ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hpa := Finset.prod_le_one₀ (fun i hi => (hb' i hi).trans (hba' i hi)) ha'
    have hdiff : 0 ≤ (∏ i ∈ s, a i) - (∏ i ∈ s, b i) :=
      sub_nonneg.mpr (Finset.prod_le_prod₀ hb' hba')
    have hjb := hb j (Finset.mem_insert_self j s)
    have hjba := hba j (Finset.mem_insert_self j s)
    have hja := ha j (Finset.mem_insert_self j s)
    have h1 := mul_le_mul_of_nonneg_left hpa (sub_nonneg.mpr hjba)
    have h2 := mul_le_mul_of_nonneg_right (hjba.trans hja) hdiff
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    nlinarith [ih hb' hba' ha']

/-- The reciprocal-radius coefficient controlling boundary and slab losses in a polydisc. -/
def polydiscTypeConstant {n : ℕ} (r : RealSpace n) : ℝ := ∑ j, (r j)⁻¹

private def relativeRadius (r t : ℝ) : ℝ := max (r - t) 0 / r

private theorem relativeRadius_bounds {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ relativeRadius r t ∧ relativeRadius r t ≤ 1 := by
  constructor
  · exact div_nonneg (le_max_right _ _) hr.le
  · apply (div_le_one hr).mpr
    exact max_le (by linarith) hr.le

private theorem relativeRadius_sub_le {r t₁ t₂ : ℝ} (hr : 0 < r) (ht : t₁ ≤ t₂) :
    relativeRadius r t₂ ≤ relativeRadius r t₁ ∧
      relativeRadius r t₁ - relativeRadius r t₂ ≤ (t₂ - t₁) / r := by
  constructor
  · exact div_le_div_of_nonneg_right (max_le_max (by linarith) le_rfl) hr.le
  · unfold relativeRadius
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    rcases le_total t₂ r with h₂ | h₂
    · rw [max_eq_left (by linarith : 0 ≤ r - t₂), max_eq_left (by linarith : 0 ≤ r - t₁)]
      linarith
    · rw [max_eq_right (by linarith : r - t₂ ≤ 0)]
      simp only [sub_zero]
      exact max_le (by linarith) (by linarith)

private theorem polydisc_volume_relative {n : ℕ} (c r : RealSpace n)
    (hr : ∀ j, 0 < r j) (t : ℝ≥0) :
    realVolume (erosion (realCenteredPolydisc c r) t) =
      ENNReal.ofReal ((∏ j, 2 * r j) * ∏ j, relativeRadius (r j) t) := by
  rw [realVolume_erosion_polydisc]
  have he (j : Fin n) : ENNReal.ofReal (2 * (r j - t)) =
      ENNReal.ofReal (2 * r j * relativeRadius (r j) t) := by
    have he' : 2 * r j * relativeRadius (r j) t = 2 * max (r j - t) 0 := by
      unfold relativeRadius
      field_simp [ne_of_gt (hr j)]
    rw [he', ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  simp_rw [he]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (by norm_num) (hr j).le)
      (relativeRadius_bounds (hr j) t.coe_nonneg).1),
    Finset.prod_mul_distrib]

theorem polydisc_boundary_le {n : ℕ} (c r : RealSpace n) (hr : ∀ j, 0 < r j)
    (d₁ d₂ : ℝ≥0) (hd : d₁ ≤ d₂) :
    realVolume (erosion (realCenteredPolydisc c r) d₁ \
      erosion (realCenteredPolydisc c r) d₂) ≤
      ENNReal.ofReal (polydiscTypeConstant r * ((d₂ : ℝ) - d₁)) *
        realVolume (realCenteredPolydisc c r) := by
  let V : ℝ := ∏ j, 2 * r j
  have hV : 0 ≤ V := Finset.prod_nonneg fun j _ => mul_nonneg (by norm_num) (hr j).le
  have hb (t : ℝ≥0) (j : Fin n) := relativeRadius_bounds (hr j) t.coe_nonneg
  have hdiff (j : Fin n) := relativeRadius_sub_le (hr j) (show (d₁ : ℝ) ≤ d₂ from hd)
  have hprod : (∏ j, relativeRadius (r j) d₁) - (∏ j, relativeRadius (r j) d₂) ≤
      polydiscTypeConstant r * ((d₂ : ℝ) - d₁) := by
    calc
      _ ≤ ∑ j, (relativeRadius (r j) d₁ - relativeRadius (r j) d₂) :=
        prod_sub_prod_le_sum_sub _ _ _ (fun j _ => (hb d₂ j).1)
          (fun j _ => (hdiff j).1) (fun j _ => (hb d₁ j).2)
      _ ≤ ∑ j, ((d₂ : ℝ) - d₁) / r j := Finset.sum_le_sum fun j _ => (hdiff j).2
      _ = _ := by
        simp only [polydiscTypeConstant, div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsub : realSlice (erosion (realCenteredPolydisc c r) d₂) ⊆
      realSlice (erosion (realCenteredPolydisc c r) d₁) :=
    preimage_mono (erosion_antitone_radius _ hd)
  have hm := (isClosed_realSlice
    (isClosed_erosion (isClosed_realCenteredPolydisc c r) d₂)).measurableSet
  have hfin : realVolume (erosion (realCenteredPolydisc c r) d₂) ≠ ∞ := by
    rw [polydisc_volume_relative c r hr]
    exact ENNReal.ofReal_ne_top
  have he : realVolume (erosion (realCenteredPolydisc c r) d₁ \
      erosion (realCenteredPolydisc c r) d₂) =
      realVolume (erosion (realCenteredPolydisc c r) d₁) -
        realVolume (erosion (realCenteredPolydisc c r) d₂) :=
    measure_sdiff hsub hm.nullMeasurableSet hfin
  rw [he, polydisc_volume_relative c r hr, polydisc_volume_relative c r hr,
    ← ENNReal.ofReal_sub _ (mul_nonneg hV (Finset.prod_nonneg fun j _ => (hb d₂ j).1))]
  have hVeq : realVolume (realCenteredPolydisc c r) = ENNReal.ofReal V := by
    rw [realVolume_realCenteredPolydisc,
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => mul_nonneg (by norm_num) (hr j).le)]
  rw [hVeq, ← ENNReal.ofReal_mul (by
    apply mul_nonneg
    · exact Finset.sum_nonneg fun j _ => inv_nonneg.mpr (hr j).le
    · exact sub_nonneg.mpr (show (d₁ : ℝ) ≤ d₂ from hd))]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left hprod hV
  dsimp [V] at *
  nlinarith

end KamProject.Arnold1963
