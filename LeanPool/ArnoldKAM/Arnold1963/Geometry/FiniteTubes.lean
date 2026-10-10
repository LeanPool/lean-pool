/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.TubeLayer

/-!
Finite-tube domain representations and complete erosion loss bounds, relative to the
original domain type constant.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- An eroded complex domain with finitely many covector-tube exclusions. -/
def finiteTubeDomain {n : ℕ} {ι : Type*} (Ω : Set (ComplexSpace n)) (s : Finset ι)
    (ℓ : ι → RealSpace n) (c a : ι → ℝ) (r : ℝ≥0) : Set (ComplexSpace n) :=
  {z | z ∈ erosion Ω r ∧ ∀ i ∈ s, a i ≤ ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖}

theorem finiteTubeDomain_subset {n : ℕ} {ι : Type*} (Ω : Set (ComplexSpace n)) (s : Finset ι)
    (ℓ : ι → RealSpace n) (c a : ι → ℝ) (r : ℝ≥0) :
    finiteTubeDomain Ω s ℓ c a r ⊆ Ω := fun _ hx => erosion_subset _ _ hx.1

theorem erosion_finiteTubeDomain {n : ℕ} {ι : Type*} (Ω : Set (ComplexSpace n)) (s : Finset ι)
    (ℓ : ι → RealSpace n) (c a : ι → ℝ) (r d : ℝ≥0)
    (hℓ : ∀ i ∈ s, 0 < covectorLength (ℓ i)) (ha : ∀ i ∈ s, 0 < a i) :
    erosion (finiteTubeDomain Ω s ℓ c a r) d =
      finiteTubeDomain Ω s ℓ c (fun i => a i + (d : ℝ) * covectorLength (ℓ i)) (r + d) := by
  ext x
  constructor
  · intro hx
    constructor
    · rw [← erosion_add]
      exact fun z hz => (hx hz).1
    · intro i hi
      have hh : x ∈ erosion {z | a i ≤ ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖} d :=
        fun z hz => (hx hz).2 i hi
      rwa [erosion_tube_complement (ℓ i) (hℓ i hi) (c i) (a i) (ha i hi) d] at hh
  · rintro ⟨hx, hs⟩ z hz
    constructor
    · rw [← erosion_add] at hx
      exact hx hz
    · intro i hi
      have hh := hs i hi
      change x ∈ {z | a i + (d : ℝ) * covectorLength (ℓ i) ≤
        ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖} at hh
      rw [← erosion_tube_complement (ℓ i) (hℓ i hi) (c i) (a i) (ha i hi) d] at hh
      exact hh hz

theorem finiteTube_layer_subset {n : ℕ} {ι : Type*} (Ω : Set (ComplexSpace n)) (s : Finset ι)
    (ℓ : ι → RealSpace n) (c a : ι → ℝ) (r d₁ d₂ : ℝ≥0)
    (hℓ : ∀ i ∈ s, 0 < covectorLength (ℓ i)) (ha : ∀ i ∈ s, 0 < a i) :
    erosion (finiteTubeDomain Ω s ℓ c a r) d₁ \ erosion (finiteTubeDomain Ω s ℓ c a r) d₂ ⊆
      (erosion Ω (r + d₁) \ erosion Ω (r + d₂)) ∪
        ⋃ i ∈ s, Ω ∩ {z | a i + (d₁ : ℝ) * covectorLength (ℓ i) ≤
          ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖ ∧
          ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖ < a i + (d₂ : ℝ) * covectorLength (ℓ i)} := by
  classical
  rw [erosion_finiteTubeDomain Ω s ℓ c a r d₁ hℓ ha,
    erosion_finiteTubeDomain Ω s ℓ c a r d₂ hℓ ha]
  intro z ⟨hz, hn⟩
  by_cases hz₂ : z ∈ erosion Ω (r + d₂)
  · right
    have hh : ¬ ∀ i ∈ s, a i + (d₂ : ℝ) * covectorLength (ℓ i) ≤
        ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖ := fun hh => hn ⟨hz₂, hh⟩
    push Not at hh
    obtain ⟨i, hi, hbad⟩ := hh
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, erosion_subset _ _ hz.1, hz.2 i hi, hbad⟩⟩
  · exact Or.inl ⟨hz.1, hz₂⟩

theorem TypeD.finiteTube_erosion_layer {n : ℕ} {ι : Type*} {Ω : Set (ComplexSpace n)}
    {D : ℝ} (h : TypeD Ω D) (s : Finset ι) (ℓ : ι → RealSpace n) (c a : ι → ℝ)
    (r d₁ d₂ : ℝ≥0) (hd : d₁ ≤ d₂)
    (hℓ : ∀ i ∈ s, 0 < covectorLength (ℓ i)) (ha : ∀ i ∈ s, 0 < a i) :
    realVolume (erosion (finiteTubeDomain Ω s ℓ c a r) d₁ \
      erosion (finiteTubeDomain Ω s ℓ c a r) d₂) ≤
      ENNReal.ofReal (D * (1 + 2 * n * s.card) * ((d₂ : ℝ) - d₁)) * realVolume Ω := by
  let δ : ℝ := (d₂ : ℝ) - d₁
  have hδ : 0 ≤ δ := sub_nonneg.mpr hd
  let L i := Ω ∩ {z | a i + (d₁ : ℝ) * covectorLength (ℓ i) ≤
      ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖ ∧
      ‖realCovectorPairing (ℓ i) z - (c i : ℂ)‖ < a i + (d₂ : ℝ) * covectorLength (ℓ i)}
  have hLi : ∀ i ∈ s, realVolume (L i) ≤ ENNReal.ofReal (2 * D * n * δ) * realVolume Ω := by
    intro i hi
    have hh := h.tube_layer (ℓ i) (c i) (a i + (d₁ : ℝ) * covectorLength (ℓ i))
      (a i + (d₂ : ℝ) * covectorLength (ℓ i)) (hℓ i hi)
      (by positivity [ha i hi, hℓ i hi])
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (show (d₁ : ℝ) ≤ d₂ from hd) (hℓ i hi).le))
    have he : (a i + (d₂ : ℝ) * covectorLength (ℓ i) -
        (a i + (d₁ : ℝ) * covectorLength (ℓ i))) / covectorLength (ℓ i) = δ := by
      dsimp [δ]
      field_simp [(hℓ i hi).ne']
      ring
    simpa only [he] using hh
  have hb := h.boundary (r + d₁) (r + d₂) (add_le_add le_rfl hd)
  have hsub := finiteTube_layer_subset Ω s ℓ c a r d₁ d₂ hℓ ha
  calc
    _ ≤ realVolume ((erosion Ω (r + d₁) \ erosion Ω (r + d₂)) ∪ ⋃ i ∈ s, L i) :=
      realVolume_mono hsub
    _ ≤ realVolume (erosion Ω (r + d₁) \ erosion Ω (r + d₂)) +
        realVolume (⋃ i ∈ s, L i) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (D * δ) * realVolume Ω +
        ∑ i ∈ s, ENNReal.ofReal (2 * D * n * δ) * realVolume Ω := by
      apply add_le_add
      · simpa only [NNReal.coe_add, add_sub_add_left_eq_sub] using hb
      · exact (realVolume_biUnion_finset_le s L).trans (Finset.sum_le_sum hLi)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
        positivity [h.constant_pos]), ← add_mul,
        ← ENNReal.ofReal_add (by positivity [h.constant_pos]) (by positivity [h.constant_pos])]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have he : D * δ + (s.card : ℝ) * (2 * D * n * δ) = D * (1 + 2 * n * s.card) * δ := by ring
      rw [he]

end KamProject.Arnold1963
