/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGlue

/-!
# Spatial weak derivatives across the gluing time

A spatial weak-derivative identity on a slab extends, without any boundary
term, to test fields that do not vanish at the ends of the slab, by a time
cutoff and dominated convergence. Consequently spatial weak derivatives of two
adjacent slabs glue (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Cutting off near the right end of a slab and letting the cutoff width tend to
zero recovers the integral. -/
theorem lps_cutoff_right_integral_tendsto {ν : Measure (Vec3 × ℝ)} {A : Vec3 × ℝ → ℝ} (b : ℝ)
    (hA : Integrable A ν) (hlt : ∀ᵐ q ∂ν, q.2 < b) :
    Tendsto (fun ε : ℝ => ∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * A q ∂ν)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : Vec3 × ℝ, A q ∂ν)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun q => ‖A q‖) ?_ ?_ hA.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    exact ((lpsCutoffRight_contDiff b ε).continuous.comp continuous_snd).aestronglyMeasurable.mul
      hA.aestronglyMeasurable
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_
    rw [norm_mul]
    have h0 := lpsCutoffRight_nonneg b ε q.2
    have h1 := lpsCutoffRight_le_one b ε q.2
    rw [Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · filter_upwards [hlt] with q hq
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lpsCutoffRight b ε q.2 = 1 := by
      have hpos : 0 < b - q.2 := by linarith only [hq]
      have hIoo : Ioo (0 : ℝ) ((b - q.2) / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith only
        [hpos])
      filter_upwards [hIoo] with ε hε
      exact lpsCutoffRight_eq_one hε.1 (by linarith only [hε.2])
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with ε hε
    rw [hε, one_mul]

/-- The left-end version of `lps_cutoff_right_integral_tendsto`. -/
theorem lps_cutoff_left_integral_tendsto {ν : Measure (Vec3 × ℝ)} {A : Vec3 × ℝ → ℝ} (a : ℝ)
    (hA : Integrable A ν) (hgt : ∀ᵐ q ∂ν, a < q.2) :
    Tendsto (fun ε : ℝ => ∫ q : Vec3 × ℝ, lpsCutoffLeft a ε q.2 * A q ∂ν)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : Vec3 × ℝ, A q ∂ν)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun q => ‖A q‖) ?_ ?_ hA.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    exact ((lpsCutoffLeft_contDiff a ε).continuous.comp continuous_snd).aestronglyMeasurable.mul
      hA.aestronglyMeasurable
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_
    rw [norm_mul]
    have h0 := lpsCutoffLeft_nonneg a ε q.2
    have h1 := lpsCutoffLeft_le_one a ε q.2
    rw [Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · filter_upwards [hgt] with q hq
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lpsCutoffLeft a ε q.2 = 1 := by
      have hpos : 0 < q.2 - a := by linarith only [hq]
      have hIoo : Ioo (0 : ℝ) ((q.2 - a) / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith only
        [hpos])
      filter_upwards [hIoo] with ε hε
      exact lpsCutoffLeft_eq_one hε.1 (by linarith only [hε.2])
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with ε hε
    rw [hε, one_mul]

/-- A spatial weak-derivative identity on a slab extends to test fields on a larger
slab, when restricted to the smaller one. -/
theorem lps_spatial_weak_extend_right {a b c : ℝ} {F G : ParabolicPoint → ℝ} {j : Fin 3}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hw : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G z * φ z)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z * spatialPartial φ j z) =
      -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G z * φ z := by
  have hφ0 := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
    with hν
  have hFν := lps_memLp_slab_to_prod hF
  have hGν := lps_memLp_slab_to_prod hG
  obtain ⟨hdc, hdk⟩ := lps_spatialPartial_cont_compact hφs hφc j
  have hA : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
      spatialPartial φ j q) ν := hFν.integrable_mul (q := 2) (hdc.memLp_of_hasCompactSupport hdk)
  have hB : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) * φ q) ν :=
    hGν.integrable_mul (q := 2) (hφs.continuous.memLp_of_hasCompactSupport hφc)
  have hlt : ∀ᵐ q ∂ν, q.2 < b := by
    have : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t < b := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using ht.2
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Vec3))
      (ν := volume.restrict (Ioo a b))).ae this
  have hlimA := lps_cutoff_right_integral_tendsto b hA hlt
  have hlimB := lps_cutoff_right_integral_tendsto b hB hlt
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * (F (parabolicHomeomorph.symm q) *
        spatialPartial φ j q) ∂ν) =
      -∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * (G (parabolicHomeomorph.symm q) * φ q) ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hηs : tsupport (lpsCutoffRight b ε) ⊆ Iic (b - ε) := by
      refine closure_minimal ?_ isClosed_Iic
      intro t ht
      by_contra hnot
      exact ht (lpsCutoffRight_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
    have hmem := lps_cutoff_test_mem_right (β := b - ε) (b := b) hφ0
      (lpsCutoffRight_contDiff b ε) hηs (by linarith only [hε0])
    have hwε := hw _ hmem
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at hwε
    have e1 : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
        spatialPartial (fun y : ParabolicPoint => lpsCutoffRight b ε y.2 * φ y) j
          (parabolicHomeomorph.symm q) ∂ν) =
        ∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * (F (parabolicHomeomorph.symm q) *
          spatialPartial φ j q) ∂ν := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only []
      rw [lps_cutoff_spatialPartial hφs]
      change F (parabolicHomeomorph.symm q) * (lpsCutoffRight b ε q.2 * spatialPartial φ j q) = _
      ring
    have e2 : (∫ q : Vec3 × ℝ, G (parabolicHomeomorph.symm q) *
        (lpsCutoffRight b ε q.2 * φ q) ∂ν) =
        ∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * (G (parabolicHomeomorph.symm q) * φ q) ∂ν := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      ring
    exact (e1.symm.trans hwε).trans (congrArg Neg.neg e2)
  rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod]
  exact tendsto_nhds_unique hlimA (hlimB.neg.congr' (hε.mono fun ε h => h.symm))

/-- The left-end version of `lps_spatial_weak_extend_right`. -/
theorem lps_spatial_weak_extend_left {a b c : ℝ} {F G : ParabolicPoint → ℝ} {j : Fin 3}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hw : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo b c) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G z * φ z)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F z * spatialPartial φ j z) =
      -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G z * φ z := by
  have hφ0 := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo b c))
    with hν
  have hFν := lps_memLp_slab_to_prod hF
  have hGν := lps_memLp_slab_to_prod hG
  obtain ⟨hdc, hdk⟩ := lps_spatialPartial_cont_compact hφs hφc j
  have hA : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
      spatialPartial φ j q) ν := hFν.integrable_mul (q := 2) (hdc.memLp_of_hasCompactSupport hdk)
  have hB : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) * φ q) ν :=
    hGν.integrable_mul (q := 2) (hφs.continuous.memLp_of_hasCompactSupport hφc)
  have hgt : ∀ᵐ q ∂ν, b < q.2 := by
    have : ∀ᵐ t ∂(volume.restrict (Ioo b c)), b < t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using ht.1
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Vec3))
      (ν := volume.restrict (Ioo b c))).ae this
  have hlimA := lps_cutoff_left_integral_tendsto b hA hgt
  have hlimB := lps_cutoff_left_integral_tendsto b hB hgt
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ q : Vec3 × ℝ, lpsCutoffLeft b ε q.2 * (F (parabolicHomeomorph.symm q) *
        spatialPartial φ j q) ∂ν) =
      -∫ q : Vec3 × ℝ, lpsCutoffLeft b ε q.2 * (G (parabolicHomeomorph.symm q) * φ q) ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hηs : tsupport (lpsCutoffLeft b ε) ⊆ Ici (b + ε) := by
      refine closure_minimal ?_ isClosed_Ici
      intro t ht
      by_contra hnot
      exact ht (lpsCutoffLeft_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
    have hmem := lps_cutoff_test_mem_left (α := b + ε) (b := b) hφ0
      (lpsCutoffLeft_contDiff b ε) hηs (by linarith only [hε0])
    have hwε := hw _ hmem
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at hwε
    have e1 : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
        spatialPartial (fun y : ParabolicPoint => lpsCutoffLeft b ε y.2 * φ y) j
          (parabolicHomeomorph.symm q) ∂ν) =
        ∫ q : Vec3 × ℝ, lpsCutoffLeft b ε q.2 * (F (parabolicHomeomorph.symm q) *
          spatialPartial φ j q) ∂ν := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only []
      rw [lps_cutoff_spatialPartial hφs]
      change F (parabolicHomeomorph.symm q) * (lpsCutoffLeft b ε q.2 * spatialPartial φ j q) = _
      ring
    have e2 : (∫ q : Vec3 × ℝ, G (parabolicHomeomorph.symm q) *
        (lpsCutoffLeft b ε q.2 * φ q) ∂ν) =
        ∫ q : Vec3 × ℝ, lpsCutoffLeft b ε q.2 * (G (parabolicHomeomorph.symm q) * φ q) ∂ν := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      ring
    exact (e1.symm.trans hwε).trans (congrArg Neg.neg e2)
  rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod]
  exact tendsto_nhds_unique hlimA (hlimB.neg.congr' (hε.mono fun ε h => h.symm))

/-- Spatial weak derivatives of two adjacent slabs glue. -/
theorem lps_spatial_weak_glue {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {F₁ F₂ F G₁ G₂ G : ParabolicPoint → ℝ} {j : Fin 3}
    (hF₁ : MemLp F₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG₁ : MemLp G₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hF₂ : MemLp F₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hG₂ : MemLp G₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hw₁ : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F₁ z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G₁ z * φ z)
    (hw₂ : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo b c) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F₂ z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G₂ z * φ z)
    (hF : ∀ z : ParabolicPoint, z.2 ≤ b → F z = F₁ z)
    (hF' : ∀ z : ParabolicPoint, b < z.2 → F z = F₂ z)
    (hG : ∀ z : ParabolicPoint, z.2 ≤ b → G z = G₁ z)
    (hG' : ∀ z : ParabolicPoint, b < z.2 → G z = G₂ z)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), F z * spatialPartial φ j z) =
      -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), G z * φ z := by
  have hφ' := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hFm := lps_memLp_slab_glue hF₁ hF₂ hF hF'
  have hGm := lps_memLp_slab_glue hG₁ hG₂ hG hG'
  obtain ⟨hdc, hdk⟩ := lps_spatialPartial_cont_compact hφs hφc j
  have hI1 : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
      spatialPartial φ j (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    (lps_memLp_slab_to_prod hFm).integrable_mul (q := 2) (hdc.memLp_of_hasCompactSupport hdk)
  have hI2 : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) *
      φ (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    (lps_memLp_slab_to_prod hGm).integrable_mul (q := 2)
      (hφs.continuous.memLp_of_hasCompactSupport hφc)
  have hs1 := lps_slab_integral_split hab.le hbc.le
    (f := fun z => F z * spatialPartial φ j z) hI1
  have hs2 := lps_slab_integral_split hab.le hbc.le (f := fun z => G z * φ z) hI2
  have hmeas1 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hmeas2 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hA1 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z * spatialPartial φ j z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F₁ z * spatialPartial φ j z :=
    setIntegral_congr_fun hmeas1 fun z hz => by simp only [hF z hz.2.2.le]
  have hA2 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F z * spatialPartial φ j z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F₂ z * spatialPartial φ j z :=
    setIntegral_congr_fun hmeas2 fun z hz => by simp only [hF' z hz.2.1]
  have hB1 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G z * φ z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G₁ z * φ z :=
    setIntegral_congr_fun hmeas1 fun z hz => by simp only [hG z hz.2.2.le]
  have hB2 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G z * φ z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G₂ z * φ z :=
    setIntegral_congr_fun hmeas2 fun z hz => by simp only [hG' z hz.2.1]
  rw [hs1, hs2, hA1, hA2, hB1, hB2,
    lps_spatial_weak_extend_right hF₁ hG₁ hw₁ hφ',
    lps_spatial_weak_extend_left (a := a) hF₂ hG₂ hw₂ hφ']
  ring

end ESS

end
