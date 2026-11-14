/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SignSquareProduct
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.EMetricSpace.Lipschitz

-- [TABLET NODE: P4953T1QuadrilateralSections]

/-!
# P4953T1QuadrilateralSections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace QuadrilateralSectionsConstruction

private noncomputable abbrev fA (h : ℝ) (A : ℂ) : ℂ := by
  classical
  exact ⟨h, A.im⟩

private noncomputable abbrev fB (h : ℝ) (B : ℂ) : ℂ := by
  classical
  exact ⟨h, B.im⟩

private noncomputable abbrev d (A : ℂ) (B : ℂ) (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) /
    (B.im - A.im)

private noncomputable abbrev Q (h : ℝ) (A : ℂ) (B : ℂ) := convexHull ℝ ({A, B, (fA h A), (fB h
    B)} : Set ℂ)

private abbrev hσsq := SignSquareProduct.product

private noncomputable abbrev T (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) : Set ℂ := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  exact {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}

private theorem hconv (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hAB : A.im < B.im) : Convex ℝ (T h σ A B)
    := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  change (Convex ℝ T)
  intro z hz w hw a b ha hb hab
  change A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re) at hz
  change A.im ≤ w.im ∧ w.im ≤ B.im ∧
    0 ≤ σ * (w.re - h) ∧ 0 ≤ σ * (d w.im - w.re) at hw
  change A.im ≤ (a • z + b • w).im ∧ (a • z + b • w).im ≤ B.im ∧
    0 ≤ σ * ((a • z + b • w).re - h) ∧
    0 ≤ σ * (d (a • z + b • w).im - (a • z + b • w).re)
  simp only [Complex.add_im, Complex.smul_im, Complex.add_re, Complex.smul_re]
  simp only [smul_eq_mul]
  have hd : d (a * z.im + b * w.im) = a * d z.im + b * d w.im := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    dsimp [d]
    field_simp [ne_of_gt hAB]
    ring
  have hre : σ * (a * z.re + b * w.re - h) =
      a * (σ * (z.re - h)) + b * (σ * (w.re - h)) := by
    rw [show a * z.re + b * w.re - h =
      a * (z.re - h) + b * (w.re - h) by linear_combination h * hab]
    ring
  have hrd : σ * (a * d z.im + b * d w.im - (a * z.re + b * w.re)) =
      a * (σ * (d z.im - z.re)) + b * (σ * (d w.im - w.re)) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      A.im = a * A.im + b * A.im := by rw [← add_mul, hab, one_mul]
      _ ≤ a * z.im + b * w.im := add_le_add
        (mul_le_mul_of_nonneg_left hz.1 ha) (mul_le_mul_of_nonneg_left hw.1 hb)
  · calc
      a * z.im + b * w.im ≤ a * B.im + b * B.im := add_le_add
        (mul_le_mul_of_nonneg_left hz.2.1 ha) (mul_le_mul_of_nonneg_left hw.2.1 hb)
      _ = B.im := by rw [← add_mul, hab, one_mul]
  · have hz' := hz.2.2.1
    have hw' := hw.2.2.1
    rw [hre]
    exact add_nonneg (mul_nonneg ha hz') (mul_nonneg hb hw')
  · have hz' := hz.2.2.2
    have hw' := hw.2.2.2
    rw [hd]
    rw [hrd]
    exact add_nonneg (mul_nonneg ha hz') (mul_nonneg hb hw')

private theorem hda (A : ℂ) (B : ℂ) (hAB : A.im < B.im) : (d A B) A.im = A.re := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  change (d A.im = A.re)
  dsimp [d]
  field_simp [ne_of_gt hAB];
  ring

private theorem hdb (A : ℂ) (B : ℂ) (hAB : A.im < B.im) : (d A B) B.im = B.re := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  change (d B.im = B.re)
  have hv : B.im - A.im ≠ 0 := sub_ne_zero.mpr (ne_of_gt hAB)
  dsimp [d]
  simp [hv]

private theorem hQsub (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hA : 0 < σ * (A.re - h)) (hB : 0 < σ *
    (B.re - h)) (hAB : A.im < B.im) : (Q h A B) ⊆ (T h σ A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hconv : Convex ℝ T := hconv h σ A B hAB
  have hda : d A.im = A.re := hda A B hAB
  have hdb : d B.im = B.re := hdb A B hAB
  change (Q ⊆ T)
  apply convexHull_min
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨le_rfl, hAB.le, le_of_lt (by simpa [fA] using hA), by
        rw [hda]
        simp
      ⟩
    · exact ⟨hAB.le, le_rfl, le_of_lt (by simpa [fB] using hB), by
        rw [hdb]
        simp
      ⟩
    · exact ⟨le_rfl, hAB.le, by simp [fA], by
        rw [hda]
        simpa [fA] using hA.le
      ⟩
    · exact ⟨hAB.le, le_rfl, by simp [fB], by
        rw [hdb]
        simpa [fB] using hB.le
      ⟩
  · exact hconv

private theorem hTsub (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (T h σ A B) ⊆ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  have hσsq : σ * σ = 1 := hσsq σ hσ
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  change (T ⊆ Q)
  intro z hz
  change A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re) at hz
  have hv : 0 < B.im - A.im := sub_pos.mpr hAB
  let t := (z.im - A.im) / (B.im - A.im)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hz.1) hv.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one₀ hv).2
    linarith [hz.2.1]
  have ht : (1 - t) + t = 1 := by ring
  have hlinD : d z.im = (1 - t) * A.re + t * B.re := by
    dsimp [d, t]
    field_simp [ne_of_gt hv]
    ring
  have hDform : σ * (d z.im - h) =
      (1 - t) * (σ * (A.re - h)) + t * (σ * (B.re - h)) := by
    rw [hlinD]
    rw [show (1 - t) * A.re + t * B.re - h =
      (1 - t) * (A.re - h) + t * (B.re - h) by linear_combination h * ht]
    ring
  have hD : 0 < σ * (d z.im - h) := by
    rw [hDform]
    by_cases htEq : t = 1
    · rw [htEq]
      simpa using hB
    · have hleft : 0 < 1 - t := by
        have htlt : t < 1 := by
          by_contra hn
          have hge : 1 ≤ t := le_of_not_gt hn
          exact htEq (le_antisymm ht1 hge)
        linarith
      exact add_pos_of_pos_of_nonneg (mul_pos hleft hA)
        (mul_nonneg ht0 hB.le)
  let r := σ * (z.re - h) / (σ * (d z.im - h))
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg hz.2.2.1 hD.le
  have hnumle : σ * (z.re - h) ≤ σ * (d z.im - h) := by
    have := hz.2.2.2
    nlinarith
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one₀ hD).2 hnumle
  have hreal : z.re = h + r * (d z.im - h) := by
    have hcancel : r * (σ * (d z.im - h)) = σ * (z.re - h) := by
      dsimp [r]
      exact div_mul_cancel₀ _ (ne_of_gt hD)
    have hσsq : σ * σ = 1 := by nlinarith [hσ]
    have hratio : r * (d z.im - h) = z.re - h := by
      calc
        r * (d z.im - h) = σ * (r * (σ * (d z.im - h))) := by
          calc
            r * (d z.im - h) = r * (d z.im - h) * (σ * σ) := by rw [hσsq]; ring
            _ = σ * (r * (σ * (d z.im - h))) := by ring
        _ = σ * (σ * (z.re - h)) := by rw [hcancel]
        _ = z.re - h := by calc
          σ * (σ * (z.re - h)) = (σ * σ) * (z.re - h) := by ring
          _ = z.re - h := by rw [hσsq]; ring
    rw [hratio]
    ring
  let foot : ℂ := ⟨h, z.im⟩
  let top : ℂ := ⟨d z.im, z.im⟩
  have hfootSeg : foot ∈ segment ℝ fA fB := by
    rw [segment_eq_image]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, foot, fA, fB]
      simp only [smul_eq_mul]
      ring
    · simp only [Complex.add_im, Complex.smul_im]
      simp only [smul_eq_mul]
      rw [show (1 - t) * A.im + t * B.im = z.im by
        dsimp [t]
        field_simp [ne_of_gt hv]
        ring]
  have htopSeg : top ∈ segment ℝ A B := by
    rw [segment_eq_image]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re]
      simp only [smul_eq_mul]
      change (1 - t) * A.re + t * B.re = d z.im
      exact hlinD.symm
    · simp only [Complex.add_im, Complex.smul_im]
      simp only [smul_eq_mul]
      rw [show (1 - t) * A.im + t * B.im = z.im by
        dsimp [t]
        field_simp [ne_of_gt hv]
        ring]
  have hfootQ : foot ∈ Q := by
    dsimp [Q]
    have hfA : fA ∈ ({A, B, fA, fB} : Set ℂ) := by simp [fA]
    have hfB : fB ∈ ({A, B, fA, fB} : Set ℂ) := by simp [fB]
    exact segment_subset_convexHull hfA hfB hfootSeg
  have htopQ : top ∈ Q := by
    dsimp [Q]
    have hA' : A ∈ ({A, B, fA, fB} : Set ℂ) := by simp
    have hB' : B ∈ ({A, B, fA, fB} : Set ℂ) := by simp
    exact segment_subset_convexHull hA' hB' htopSeg
  have hzSeg : z ∈ segment ℝ foot top := by
    rw [segment_eq_image]
    refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, foot, top]
      simp only [smul_eq_mul]
      rw [hreal]
      ring
    · simp only [Complex.add_im, Complex.smul_im, foot, top]
      simp only [smul_eq_mul]
      ring
  simpa [Q] using (convex_convexHull ℝ _).segment_subset hfootQ htopQ hzSeg

private theorem hQeq (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (Q h A B) = (T h σ A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hQsub : Q ⊆ T := hQsub h σ A B hA hB hAB
  have hTsub : T ⊆ Q := hTsub h σ A B hσ hA hB hAB
  change (Q = T)
  exact Set.Subset.antisymm hQsub hTsub

private noncomputable abbrev S (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) : Set ℂ := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  exact {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}

private theorem hcReLip : LipschitzWith 1 (fun z : ℂ => z.re) := by
  classical
  intro z w
  rw [edist_dist, edist_dist, Real.dist_eq, Complex.dist_eq]
  have he : |z.re - w.re| ≤ ‖z - w‖ := by
    calc
      |z.re - w.re| = |(z - w).re| := by simp
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  calc
    ENNReal.ofReal |z.re - w.re| ≤ ENNReal.ofReal ‖z - w‖ := ENNReal.ofReal_le_ofReal he
    _ = ((1 : NNReal) : ENNReal) * ENNReal.ofReal ‖z - w‖ := by norm_num

private theorem hcImLip : LipschitzWith 1 (fun z : ℂ => z.im) := by
  classical
  intro z w
  rw [edist_dist, edist_dist, Real.dist_eq, Complex.dist_eq]
  have he : |z.im - w.im| ≤ ‖z - w‖ := by
    calc
      |z.im - w.im| = |(z - w).im| := by simp
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  calc
    ENNReal.ofReal |z.im - w.im| ≤ ENNReal.ofReal ‖z - w‖ := ENNReal.ofReal_le_ofReal he
    _ = ((1 : NNReal) : ENNReal) * ENNReal.ofReal ‖z - w‖ := by norm_num

private theorem hcIm : Continuous fun z : ℂ => z.im := by
  classical
  have hcImLip : LipschitzWith 1 (fun z : ℂ => z.im) := hcImLip
  exact hcImLip.continuous

private theorem hcRe : Continuous fun z : ℂ => z.re := by
  classical
  have hcReLip : LipschitzWith 1 (fun z : ℂ => z.re) := hcReLip
  exact hcReLip.continuous

private theorem hcD (A : ℂ) (B : ℂ) : Continuous fun z : ℂ => (d A B) z.im := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have hcIm : Continuous fun z : ℂ => z.im := hcIm
  change (Continuous fun z : ℂ => d z.im)
  dsimp [d]
  exact continuous_const.add
    ((continuous_const.mul (hcIm.sub continuous_const)).div_const (B.im - A.im))

private theorem hcSide (h : ℝ) (σ : ℝ) : Continuous fun z : ℂ => σ * (z.re - h) := by
  classical
  have hcRe : Continuous fun z : ℂ => z.re := hcRe
  exact continuous_const.mul (hcRe.sub continuous_const)

private theorem hcTop (σ : ℝ) (A : ℂ) (B : ℂ) : Continuous fun z : ℂ => σ * ((d A B) z.im - z.re)
    := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have hcRe : Continuous fun z : ℂ => z.re := hcRe
  have hcD : Continuous fun z : ℂ => d z.im := hcD A B
  change (Continuous fun z : ℂ => σ * (d z.im - z.re))
  exact continuous_const.mul (hcD.sub hcRe)

private theorem hSopen (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) : IsOpen (S h σ A B) := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hcIm : Continuous fun z : ℂ => z.im := hcIm
  have hcSide : Continuous fun z : ℂ => σ * (z.re - h) := hcSide h σ
  have hcTop : Continuous fun z : ℂ => σ * (d z.im - z.re) := hcTop σ A B
  change (IsOpen S)
  dsimp [S]
  exact (isOpen_lt continuous_const hcIm).inter
    (isOpen_lt hcIm continuous_const) |>.inter
    (isOpen_lt continuous_const hcSide) |>.inter
    (isOpen_lt continuous_const hcTop)

private theorem hSsub (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (S h σ A B) ⊆ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hTsub : T ⊆ Q := hTsub h σ A B hσ hA hB hAB
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  change (S ⊆ Q)
  intro z hz
  apply hTsub
  rcases hz with ⟨⟨⟨hz₁, hz₂⟩, hz₃⟩, hz₄⟩
  exact ⟨hz₁.le, hz₂.le, hz₃.le, hz₄.le⟩

private theorem hSinter (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re -
    h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (S h σ A B) ⊆ interior (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hSopen : IsOpen S := hSopen h σ A B
  have hSsub : S ⊆ Q := hSsub h σ A B hσ hA hB hAB
  change (S ⊆ interior Q)
  exact hSopen.subset_interior_iff.mpr hSsub

private theorem hInteriorRev (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re
    - h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) (x : ℂ) (hx : x ∈ interior (Q h A B)) : x
    ∈ (S h σ A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  have hσsq : σ * σ = 1 := hσsq σ hσ
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hQsub : Q ⊆ T := hQsub h σ A B hA hB hAB
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  change (x ∈ S)
  have hxQ := hQsub (interior_subset hx)
  change A.im ≤ x.im ∧ x.im ≤ B.im ∧
    0 ≤ σ * (x.re - h) ∧ 0 ≤ σ * (d x.im - x.re) at hxQ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hx)
  have stepV (r : ℝ) (hr : |r| < ε) :
      x + (r : ℂ) * Complex.I ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left,
      Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    simpa using hr
  have stepR (r : ℝ) (hr : |r| < ε) :
      x + (r : ℂ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs]
    simpa using hr
  have hVlo := hQsub (hball (stepV (-ε / 2) (by
    rw [abs_of_neg (by linarith [hε])]
    linarith)))
  have hVhi := hQsub (hball (stepV (ε / 2) (by
    rw [abs_of_pos (by linarith [hε])]
    linarith)))
  change A.im ≤ (x + ((-ε / 2 : ℝ) : ℂ) * Complex.I).im ∧ _ at hVlo
  change A.im ≤ (x + ((ε / 2 : ℝ) : ℂ) * Complex.I).im ∧ _ at hVhi
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hVlo hVhi
  have hsigmaAbs : |σ| = 1 := by
    have habs : |σ| * |σ| = 1 := by
      calc
        |σ| * |σ| = |σ * σ| := by rw [abs_mul]
        _ = |1| := by rw [← pow_two, hσ]
        _ = 1 := abs_one
    nlinarith [habs, abs_nonneg σ]
  have hrAbs : |σ * ε / 2| = ε / 2 := by
    rw [abs_div, abs_mul, hsigmaAbs, abs_of_pos hε]
    norm_num
  have hRlo := hQsub (hball (stepR (-σ * ε / 2) (by
    rw [show -σ * ε / 2 = -(σ * ε / 2) by ring, abs_neg, hrAbs]
    linarith)))
  have hRhi := hQsub (hball (stepR (σ * ε / 2) (by
    rw [hrAbs]
    linarith)))
  change _ ∧ _ ∧ 0 ≤ σ * ((x + ((-σ * ε / 2 : ℝ) : ℂ)).re - h) ∧ _ at hRlo
  change _ ∧ _ ∧ _ ∧ 0 ≤ σ * (d (x + ((σ * ε / 2 : ℝ) : ℂ)).im -
    (x + ((σ * ε / 2 : ℝ) : ℂ)).re) at hRhi
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
    add_zero] at hRlo hRhi
  have hstrictYlo : A.im < x.im := by linarith [hVlo.1]
  have hstrictYhi : x.im < B.im := by linarith [hVhi.2.1]
  have hstrictX : 0 < σ * (x.re - h) := by
    have := hRlo.2.2.1
    nlinarith [hσsq]
  have hstrictD : 0 < σ * (d x.im - x.re) := by
    have := hRhi.2.2.2
    nlinarith [hσsq]
  change x ∈ S
  exact ⟨⟨⟨hstrictYlo, hstrictYhi⟩, hstrictX⟩, hstrictD⟩

private theorem hInteriorEq (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re
    - h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : interior (Q h A B) = (S h σ A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hSinter : S ⊆ interior Q := hSinter h σ A B hσ hA hB hAB
  have hInteriorRev (x : ℂ) (hx : x ∈ interior Q) : x ∈ S := hInteriorRev h σ A B hσ hA hB hAB x hx
  change (interior Q = S)
  ext z
  constructor
  · exact hInteriorRev z
  · exact fun hz => hSinter hz

private theorem hTclosed (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) : IsClosed (T h σ A B) := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hcIm : Continuous fun z : ℂ => z.im := hcIm
  have hcSide : Continuous fun z : ℂ => σ * (z.re - h) := hcSide h σ
  have hcTop : Continuous fun z : ℂ => σ * (d z.im - z.re) := hcTop σ A B
  change (IsClosed T)
  have hset : T = ({z : ℂ | A.im ≤ z.im} ∩ {z | z.im ≤ B.im} ∩
      {z | 0 ≤ σ * (z.re - h)} ∩ {z | 0 ≤ σ * (d z.im - z.re)}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    simp [T]; tauto
  rw [hset]
  exact (isClosed_le continuous_const hcIm).inter
    (isClosed_le hcIm continuous_const) |>.inter
    (isClosed_le continuous_const hcSide) |>.inter
    (isClosed_le continuous_const hcTop)

private theorem hfrontier (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re -
    h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : frontier (Q h A B) = (Q h A B) \ interior
    (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hQeq : Q = T := hQeq h σ A B hσ hA hB hAB
  have hTclosed : IsClosed T := hTclosed h σ A B
  change (frontier Q = Q \ interior Q)
  simpa [Q, hQeq] using hTclosed.frontier_eq

private theorem segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := by
  classical
  rw [segment_eq_image]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨t, ht, hz⟩
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at him
    exact ⟨t, ht.1, ht.2, hre.symm, him.symm⟩
  · rintro ⟨t, ht0, ht1, hre, him⟩
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hre.symm
    · simpa only [Complex.add_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul] using him.symm

private theorem hDinterp (A : ℂ) (B : ℂ) (hAB : A.im < B.im) (t : ℝ) : (d A B) ((1 - t) * A.im +
    t * B.im) =
      (1 - t) * A.re + t * B.re := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  change (d ((1 - t) * A.im + t * B.im) =
      (1 - t) * A.re + t * B.re)
  dsimp [d]
  field_simp [ne_of_gt (sub_pos.mpr hAB)]
  ring

private theorem heightParam (y u v : ℝ) (huv : u < v) (hyu : u ≤ y) (hyv : y ≤ v) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = (1 - t) * u + t * v := by
  classical
  let t := (y - u) / (v - u)
  have hv : 0 < v - u := sub_pos.mpr huv
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hyu) hv.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one₀ hv).2
    linarith
  refine ⟨t, ht0, ht1, ?_⟩
  dsimp [t]
  field_simp [ne_of_gt hv]
  ring

private theorem sideParam (h : ℝ) (σ : ℝ) (hσ : σ ^ 2 = 1) (x c : ℝ) (hc : 0 < σ * (c - h))
      (hlo : 0 ≤ σ * (x - h)) (hhi : 0 ≤ σ * (c - x)) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) * c + t * h := by
  classical
  have hσsq : σ * σ = 1 := hσsq σ hσ
  let s := σ * (x - h) / (σ * (c - h))
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact div_nonneg hlo hc.le
  have hnumle : σ * (x - h) ≤ σ * (c - h) := by nlinarith
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (div_le_one₀ hc).2 hnumle
  have hcancel : s * (σ * (c - h)) = σ * (x - h) := by
    dsimp [s]
    exact div_mul_cancel₀ _ (ne_of_gt hc)
  have hratio : s * (c - h) = x - h := by
    calc
      s * (c - h) = σ * (s * (σ * (c - h))) := by
        calc
          s * (c - h) = s * (c - h) * (σ * σ) := by rw [hσsq]; ring
          _ = σ * (s * (σ * (c - h))) := by ring
      _ = σ * (σ * (x - h)) := by rw [hcancel]
      _ = x - h := by
        calc
          σ * (σ * (x - h)) = (σ * σ) * (x - h) := by ring
          _ = x - h := by rw [hσsq]; ring
  refine ⟨1 - s, by linarith, by linarith, ?_⟩
  rw [show x = h + s * (c - h) by linarith [hratio]]
  ring

private theorem hSegFoot (h : ℝ) (A : ℂ) (B : ℂ) (hAB : A.im < B.im) (z : ℂ) (hzY₁ : A.im ≤ z.im)
    (hzY₂ : z.im ≤ B.im)
      (hzx : z.re = h) : z ∈ segment ℝ (fA h A) (fB h B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  have segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := segCoords P R z
  have heightParam (y u v : ℝ) (huv : u < v) (hyu : u ≤ y) (hyv : y ≤ v) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = (1 - t) * u + t * v := heightParam y u v huv hyu hyv
  change (z ∈ segment ℝ fA fB)
  obtain ⟨t, ht0, ht1, him⟩ := heightParam z.im A.im B.im hAB hzY₁ hzY₂
  apply (segCoords fA fB z).2
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · rw [hzx]
    simp only [fA, fB]
    ring
  · simpa [fA, fB] using him

private theorem hSegDiag (A : ℂ) (B : ℂ) (hAB : A.im < B.im) (z : ℂ) (hzY₁ : A.im ≤ z.im) (hzY₂ :
    z.im ≤ B.im)
      (hzd : z.re = (d A B) z.im) : z ∈ segment ℝ A B := by
  classical
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := segCoords P R z
  have hDinterp (t : ℝ) : d ((1 - t) * A.im + t * B.im) =
      (1 - t) * A.re + t * B.re := hDinterp A B hAB t
  have heightParam (y u v : ℝ) (huv : u < v) (hyu : u ≤ y) (hyv : y ≤ v) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = (1 - t) * u + t * v := heightParam y u v huv hyu hyv
  obtain ⟨t, ht0, ht1, him⟩ := heightParam z.im A.im B.im hAB hzY₁ hzY₂
  apply (segCoords A B z).2
  refine ⟨t, ht0, ht1, ?_, him⟩
  calc
    z.re = d z.im := hzd
    _ = (1 - t) * A.re + t * B.re := by rw [him]; exact hDinterp t

private theorem hSegA (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hAB : A.im < B.im) (z : ℂ) (hz : z ∈ (T h σ A B)) (hzy : z.im = A.im) :
      z ∈ segment ℝ A (fA h A) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have hda : d A.im = A.re := hda A B hAB
  have segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := segCoords P R z
  have sideParam (x c : ℝ) (hc : 0 < σ * (c - h))
      (hlo : 0 ≤ σ * (x - h)) (hhi : 0 ≤ σ * (c - x)) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) * c + t * h := sideParam h σ hσ x c hc hlo hhi
  change (z ∈ segment ℝ A fA)
  change A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re) at hz
  have hhi : 0 ≤ σ * (A.re - z.re) := by simpa [hzy, hda] using hz.2.2.2
  obtain ⟨t, ht0, ht1, hre⟩ := sideParam z.re A.re hA hz.2.2.1 hhi
  apply (segCoords A fA z).2
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · simpa [fA] using hre
  · rw [hzy]
    simp only [fA]
    ring

private theorem hSegB (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hB : 0 < σ * (B.re - h))
    (hAB : A.im < B.im) (z : ℂ) (hz : z ∈ (T h σ A B)) (hzy : z.im = B.im) :
      z ∈ segment ℝ B (fB h B) := by
  classical
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have hdb : d B.im = B.re := hdb A B hAB
  have segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := segCoords P R z
  have sideParam (x c : ℝ) (hc : 0 < σ * (c - h))
      (hlo : 0 ≤ σ * (x - h)) (hhi : 0 ≤ σ * (c - x)) :
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) * c + t * h := sideParam h σ hσ x c hc hlo hhi
  change (z ∈ segment ℝ B fB)
  change A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re) at hz
  have hlow : 0 ≤ σ * (z.re - h) := hz.2.2.1
  have hhi : 0 ≤ σ * (B.re - z.re) := by simpa [hzy, hdb] using hz.2.2.2
  obtain ⟨t, ht0, ht1, hre⟩ := sideParam z.re B.re hB hlow hhi
  apply (segCoords B fB z).2
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · simpa [fB] using hre
  · rw [hzy]
    simp only [fB]
    ring

private noncomputable abbrev E (h : ℝ) (A : ℂ) (B : ℂ) := segment ℝ A B ∪ segment ℝ A (fA h A) ∪
    segment ℝ B (fB h B) ∪
    segment ℝ (fA h A) (fB h B)

private theorem hAin (h : ℝ) (A : ℂ) (B : ℂ) : A ∈ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  change (A ∈ Q)
  dsimp [Q]; exact subset_convexHull ℝ _ (by simp)

private theorem hBin (h : ℝ) (A : ℂ) (B : ℂ) : B ∈ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  change (B ∈ Q)
  dsimp [Q]; exact subset_convexHull ℝ _ (by simp)

private theorem hfAin (h : ℝ) (A : ℂ) (B : ℂ) : (fA h A) ∈ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  change (fA ∈ Q)
  dsimp [Q]; exact subset_convexHull ℝ _ (by simp [fA])

private theorem hfBin (h : ℝ) (A : ℂ) (B : ℂ) : (fB h B) ∈ (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  change (fB ∈ Q)
  dsimp [Q]; exact subset_convexHull ℝ _ (by simp [fB])

private theorem hEsub (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (E h A B) ⊆ (Q h A B) \ interior (Q h A B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hInteriorEq : interior Q = S := hInteriorEq h σ A B hσ hA hB hAB
  have segCoords (P R z : ℂ) : z ∈ segment ℝ P R ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        z.re = (1 - t) * P.re + t * R.re ∧
        z.im = (1 - t) * P.im + t * R.im := segCoords P R z
  have hDinterp (t : ℝ) : d ((1 - t) * A.im + t * B.im) =
      (1 - t) * A.re + t * B.re := hDinterp A B hAB t
  let E := segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
    segment ℝ fA fB
  have hAin : A ∈ Q := hAin h A B
  have hBin : B ∈ Q := hBin h A B
  have hfAin : fA ∈ Q := hfAin h A B
  have hfBin : fB ∈ Q := hfBin h A B
  change (E ⊆ Q \ interior Q)
  intro z hz
  constructor
  · change z ∈ E at hz
    dsimp [E] at hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · rcases hz with hz | hz
        · exact (convex_convexHull ℝ _).segment_subset hAin hBin hz
        · exact (convex_convexHull ℝ _).segment_subset hAin hfAin hz
      · exact (convex_convexHull ℝ _).segment_subset hBin hfBin hz
    · exact (convex_convexHull ℝ _).segment_subset hfAin hfBin hz
  · rw [hInteriorEq]
    dsimp [E] at hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · rcases hz with hz | hz
        · intro hs
          obtain ⟨t, ht0, ht1, hre, him⟩ := (segCoords A B z).mp hz
          rcases hs with ⟨⟨⟨_, _⟩, _⟩, hsupper⟩
          have hdeq : d z.im = z.re := by
            rw [him, hDinterp t]
            exact hre.symm
          change 0 < σ * (d z.im - z.re) at hsupper
          rw [hdeq] at hsupper
          simp at hsupper
        · intro hs
          obtain ⟨t, ht0, ht1, hre, him⟩ := (segCoords A fA z).mp hz
          rcases hs with ⟨⟨⟨hlo, _⟩, _⟩, _⟩
          change A.im < z.im at hlo
          have hconst : (1 - t) * A.im + t * A.im = A.im := by ring
          simp only [fA] at him
          rw [hconst] at him
          linarith
      · intro hs
        obtain ⟨t, ht0, ht1, hre, him⟩ := (segCoords B fB z).mp hz
        rcases hs with ⟨⟨⟨_, hhi⟩, _⟩, _⟩
        change z.im < B.im at hhi
        have hconst : (1 - t) * B.im + t * B.im = B.im := by ring
        simp only [fB] at him
        rw [hconst] at him
        linarith
    · intro hs
      obtain ⟨t, ht0, ht1, hre, him⟩ := (segCoords fA fB z).mp hz
      rcases hs with ⟨⟨⟨_, _⟩, hsx⟩, _⟩
      change 0 < σ * (z.re - h) at hsx
      have hconst : (1 - t) * h + t * h = h := by ring
      simp only [fA, fB] at hre
      rw [hconst] at hre
      rw [hre] at hsx
      simp at hsx

private theorem hBoundarySub (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re
    - h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (Q h A B) \ interior (Q h A B) ⊆ (E h A
    B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  have hσsq : σ * σ = 1 := hσsq σ hσ
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hQsub : Q ⊆ T := hQsub h σ A B hA hB hAB
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hInteriorEq : interior Q = S := hInteriorEq h σ A B hσ hA hB hAB
  have hSegFoot (z : ℂ) (hzY₁ : A.im ≤ z.im) (hzY₂ : z.im ≤ B.im)
      (hzx : z.re = h) : z ∈ segment ℝ fA fB := hSegFoot h A B hAB z hzY₁ hzY₂ hzx
  have hSegDiag (z : ℂ) (hzY₁ : A.im ≤ z.im) (hzY₂ : z.im ≤ B.im)
      (hzd : z.re = d z.im) : z ∈ segment ℝ A B := hSegDiag A B hAB z hzY₁ hzY₂ hzd
  have hSegA (z : ℂ) (hz : z ∈ T) (hzy : z.im = A.im) :
      z ∈ segment ℝ A fA := hSegA h σ A B hσ hA hAB z hz hzy
  have hSegB (z : ℂ) (hz : z ∈ T) (hzy : z.im = B.im) :
      z ∈ segment ℝ B fB := hSegB h σ A B hσ hB hAB z hz hzy
  let E := segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
    segment ℝ fA fB
  change (Q \ interior Q ⊆ E)
  intro z hz
  rcases hz with ⟨hzQ, hnint⟩
  have hzT := hQsub hzQ
  rw [hInteriorEq] at hnint
  change A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re) at hzT
  change z ∉ S at hnint
  rcases lt_or_eq_of_le hzT.1 with hylo | hylo
  · rcases lt_or_eq_of_le hzT.2.1 with hyhi | hyhi
    · rcases lt_or_eq_of_le hzT.2.2.1 with hxlo | hxlo
      · rcases lt_or_eq_of_le hzT.2.2.2 with hxhi | hxhi
        · exfalso
          apply hnint
          exact ⟨⟨⟨hylo, hyhi⟩, hxlo⟩, hxhi⟩
        · have hdiag : z.re = d z.im := by
            have hmul := congrArg (fun y : ℝ => σ * y) hxhi
            have hzero : d z.im - z.re = 0 := by
              calc
                d z.im - z.re = (σ * σ) * (d z.im - z.re) := by rw [hσsq]; ring
                _ = σ * (σ * (d z.im - z.re)) := by ring
                _ = σ * 0 := hmul.symm
                _ = 0 := by ring
            linarith
          change z ∈ segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
            segment ℝ fA fB
          exact Or.inl (Or.inl (Or.inl (hSegDiag z hzT.1 hzT.2.1 hdiag)))
      · have hleft : z.re = h := by
          have hmul := congrArg (fun y : ℝ => σ * y) hxlo
          have hzero : z.re - h = 0 := by
            calc
              z.re - h = (σ * σ) * (z.re - h) := by rw [hσsq]; ring
              _ = σ * (σ * (z.re - h)) := by ring
              _ = σ * 0 := hmul.symm
              _ = 0 := by ring
          linarith
        change z ∈ segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
          segment ℝ fA fB
        exact Or.inr (hSegFoot z hzT.1 hzT.2.1 hleft)
    · have hzy : z.im = B.im := hyhi
      change z ∈ segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
        segment ℝ fA fB
      exact Or.inl (Or.inr (hSegB z hzT hzy))
  · have hzy : z.im = A.im := hylo.symm
    change z ∈ segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
      segment ℝ fA fB
    exact Or.inl (Or.inl (Or.inr (hSegA z hzT hzy)))

private theorem hBoundary (h : ℝ) (σ : ℝ) (A : ℂ) (B : ℂ) (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re -
    h)) (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) : (Q h A B) \ interior (Q h A B) = (E h A
    B) := by
  classical
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let E := segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
    segment ℝ fA fB
  have hEsub : E ⊆ Q \ interior Q := hEsub h σ A B hσ hA hB hAB
  have hBoundarySub : Q \ interior Q ⊆ E := hBoundarySub h σ A B hσ hA hB hAB
  change (Q \ interior Q = E)
  exact Set.Subset.antisymm hBoundarySub hEsub

end QuadrilateralSectionsConstruction

theorem P4953T1QuadrilateralSections (h σ : ℝ) (A B : ℂ)
    (hσ : σ ^ 2 = 1) (hA : 0 < σ * (A.re - h))
    (hB : 0 < σ * (B.re - h)) (hAB : A.im < B.im) :
    let fA : ℂ := ⟨h, A.im⟩
    let fB : ℂ := ⟨h, B.im⟩
    let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
    let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
    (∀ z, z ∈ Q ↔ A.im ≤ z.im ∧ z.im ≤ B.im ∧
      0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)) ∧
    (∀ z, z ∈ interior Q ↔ A.im < z.im ∧ z.im < B.im ∧
      0 < σ * (z.re - h) ∧ 0 < σ * (d z.im - z.re)) ∧
    frontier Q = segment ℝ A B ∪ segment ℝ A fA ∪
      segment ℝ B fB ∪ segment ℝ fA fB := by
-- BODY
  classical
  dsimp only
  let fA : ℂ := ⟨h, A.im⟩
  let fB : ℂ := ⟨h, B.im⟩
  let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let Q := convexHull ℝ ({A, B, fA, fB} : Set ℂ)
  let T : Set ℂ := {z | A.im ≤ z.im ∧ z.im ≤ B.im ∧
    0 ≤ σ * (z.re - h) ∧ 0 ≤ σ * (d z.im - z.re)}
  have hQeq : Q = T := QuadrilateralSectionsConstruction.hQeq h σ A B hσ hA hB hAB
  let S : Set ℂ := {z | A.im < z.im} ∩ {z | z.im < B.im} ∩
    {z | 0 < σ * (z.re - h)} ∩ {z | 0 < σ * (d z.im - z.re)}
  have hInteriorEq : interior Q = S := QuadrilateralSectionsConstruction.hInteriorEq h σ A B hσ
      hA hB hAB
  have hfrontier : frontier Q = Q \ interior Q := QuadrilateralSectionsConstruction.hfrontier h σ
      A B hσ hA hB hAB
  let E := segment ℝ A B ∪ segment ℝ A fA ∪ segment ℝ B fB ∪
    segment ℝ fA fB
  have hBoundary : Q \ interior Q = E := QuadrilateralSectionsConstruction.hBoundary h σ A B hσ
      hA hB hAB
  refine ⟨?_, ?_, ?_⟩
  · intro z
    change z ∈ Q ↔ z ∈ T
    rw [hQeq]
  · intro z
    rw [hInteriorEq]
    simp [S, d]; tauto
  · calc
      frontier Q = Q \ interior Q := hfrontier
      _ = E := hBoundary

end ApollonianSuperharmonic

end
