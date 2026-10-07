/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientDiagonal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessTimeExhaustion

/-!
# Compactness Gradient Extract

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩

/-- One subsequence converges weakly for the matrix gradients on every
compact rectangle of a countable exhaustion. -/
theorem exists_common_subsequence_gradient_weak_on_exhaustion
    {U : Set Vec3} {I : Set ℝ}
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (hDuMeas : ∀ n, Measurable (Du n))
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in T, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∃ D : ∀ j, Lp CompactnessGradientFiber 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))),
        ∀ j,
          ∃ hmem : ∀ k, MemLp
            (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du (τ k) z)) 2
            ((volume.restrict (K j)).prod (volume.restrict (J j))),
            ∀ w, Tendsto
              (fun k => inner ℝ ((hmem k).toLp
                (fun z => toCompactnessGradientFiber (Du (τ k) z))) w) atTop
              (nhds (inner ℝ (D j) w)) := by
  classical
  choose G hG hGbound using fun j =>
    hgradBound (K j) (hK j).1 (hK j).2 (J j) (hJ j).1 (hJ j).2
  let μ (j : ℕ) : Measure (Vec3 × ℝ) :=
    (volume.restrict (K j)).prod (volume.restrict (J j))
  let E (j : ℕ) := Lp CompactnessGradientFiber 2 (μ j)
  let : ∀ j, IsFiniteMeasure (volume.restrict (K j)) :=
    fun j => isFiniteMeasure_restrict.mpr (hK j).1.measure_lt_top.ne
  let : ∀ j, IsFiniteMeasure (volume.restrict (J j)) :=
    fun j => isFiniteMeasure_restrict.mpr (hJ j).1.measure_lt_top.ne
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => inferInstance
  have hfiber : TopologicalSpace.SeparableSpace CompactnessGradientFiber :=
    inferInstance
  have hmeasure (j : ℕ) : IsSeparable (μ j) := inferInstance
  have hseparable (j : ℕ) : TopologicalSpace.SeparableSpace (E j) := by
    let : IsSeparable (μ j) := hmeasure j
    let : TopologicalSpace.SeparableSpace CompactnessGradientFiber := hfiber
    change TopologicalSpace.SeparableSpace
      (Lp CompactnessGradientFiber 2 (μ j))
    exact TopologicalSpace.SecondCountableTopology.to_separableSpace
  have hmem (n j : ℕ) : MemLp
      (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du n z)) 2 (μ j) :=
    memLp_gradient_fiber_of_integrated_energy (u n) (Du n)
      (hDuMeas n) ((hGbound j n).trans_lt (hG j))
  let F (n : ℕ) (j : ℕ) : E j :=
    (hmem n j).toLp (fun z => toCompactnessGradientFiber (Du n z))
  let C (j : ℕ) : ℝ := (G j ^ (1 / 2 : ℝ)).toReal
  have hC (j : ℕ) : 0 ≤ C j := ENNReal.toReal_nonneg
  have hbound (n j : ℕ) : ‖F n j‖ ≤ C j := by
    have hF : Measurable (fun z : ParabolicPoint =>
        ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) z)) := by
      unfold CKN.spatialGradientSq
      fun_prop
    have hμeq : μ j =
        (volume : Measure ParabolicPoint).restrict (K j ×ˢ J j) := by
      change (volume.restrict (K j)).prod (volume.restrict (J j)) =
        ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (K j ×ˢ J j)
      rw [Measure.prod_restrict]
    have henergy : (∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) z) ∂(μ j)) ≤
        G j := by
      rw [hμeq]
      change (∫⁻ z in K j ×ˢ J j,
        ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) z)
          ∂(volume : Measure ParabolicPoint)) ≤ G j
      rw [lintegral_parabolic_rectangle_eq_iterated _ hF]
      exact hGbound j n
    exact norm_toLp_gradient_fiber_le (u n) (Du n) (hmem n j)
      (G j) (hG j) henergy
  obtain ⟨τ, hτ, D, hweak⟩ :=
    exists_common_subsequence_weak_limit_of_bounded F C hC hbound
  refine ⟨τ, hτ, D, fun j => ?_⟩
  refine ⟨fun k => hmem (τ k) j, ?_⟩
  exact hweak j

end CKN.Leray
