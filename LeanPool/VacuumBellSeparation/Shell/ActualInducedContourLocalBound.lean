/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ActualContourLocalBound
public import LeanPool.VacuumBellSeparation.Shell.RegularShellFamilyNeighborhood

/-!
# Actual contour domination on an open mass-shell neighbourhood

The constants and parameter probability are chosen at a fixed positive base
mass and apply uniformly in a neighborhood of that mass.
Outside the chosen mass interval the fibre is empty. The lower bound
uses the physical shell measure and its true energy cutoff; no local
Jacobian, density, inverse-function or cover assumption remains.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

private theorem contour_ENNReal_mul_pos {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) :
    0 < a * b :=
  pos_iff_ne_zero.mpr (mul_ne_zero ha.ne' hb.ne')

theorem referenceContourMap_zero (m B θ : ℝ) :
    referenceContourMap m B θ 0 = complexShellCoordinates (radialShellContour m B θ 0) := by
  have ha : activeLorentzParameters 0 = 0 := by ext i; fin_cases i <;> rfl
  rw [referenceContourMap, ha, complexLorentzFamilyAction_zero]
  rfl

theorem referenceContourMap_zero_mem_domain {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    referenceContourMap m B θ 0 ∈ complexShellChartDomain m := by
  have hs : radialShellContour m B θ 0 ∈ complexShell m := by
    rw [radialShellContour_eq_boost]
    exact complexShellBoost_mem_shell _ _ _
  rw [referenceContourMap_zero]
  change 0 < (complexShellRadicand m (complexShellCoordinates _)).re
  rw [complexShellRadicand_coordinates hs]
  simpa [radialShellContour, ← Complex.ofReal_pow] using sq_pos_of_pos hB

/-- Positive finite coefficients permit normalization even when the
integrals themselves are infinite. -/
theorem normalize_ENNReal_domination {a b c I J P : ℝ≥0∞}
    (hb : b ≠ 0) (hbt : b ≠ ∞) (hc : c ≠ 0) (hct : c ≠ ∞)
    (hI : I ≤ c * J) (hJ : a * J ≤ b * P) :
    (a / (c * b)) * I ≤ P := by
  have h : a * I ≤ (c * b) * P := calc
    a * I ≤ a * (c * J) := _root_.mul_le_mul_right hI a
    _ = c * (a * J) := by ac_rfl
    _ ≤ c * (b * P) := _root_.mul_le_mul_right hJ c
    _ = (c * b) * P := (mul_assoc _ _ _).symm
  calc
    _ = (c * b)⁻¹ * (a * I) := by rw [div_eq_mul_inv]; ac_rfl
    _ ≤ (c * b)⁻¹ * ((c * b) * P) := _root_.mul_le_mul_right h _
    _ = P := ENNReal.inv_mul_cancel_left (mul_ne_zero hc hb) (ENNReal.mul_ne_top hct hbt)

theorem actualContour_induced_local_bound {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (m : ℝ) {B θ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (hE : radialShellEnergy m B 0 < R)
    (hn : spacetimeEuclideanOperatorNorm Λ < R)
    (hi : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∀ s : Fin 6 → ℝ, ‖s‖ ≤ ρ →
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s) < R ∧
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s).symm < R) ∧
      ∃ V : Set (ℝ × ComplexSpacetime), IsOpen V ∧
        (m, complexifiedSpacetimeMap Λ (radialShellContour m B θ 0)) ∈ V ∧
        ∃ k : ℝ≥0∞, 0 < k ∧ k < ∞ ∧
          ∀ t : ℝ, ∀ F : ComplexSpacetime → ℝ≥0∞, Measurable F →
            k * (∫⁻ z in {z : complexShell t | (t, z.1) ∈ V},
              F z.1 ∂inducedRegularShellVolume t) ≤
              ∫⁻ y, physicalContourCutoffWeight t θ R Λ F y
                ∂(smoothBallProbability (Fin 6 → ℝ) ρ hρ).prod (oneParticleMeasure t) := by
  obtain ⟨ρ, hρ, hnorm, C, δ, d, hC, hδ, hd, hbound⟩ :=
    actualContour_local_bound hΛ m hB hθ hE hn hi
  let w := referenceContourMap m B θ 0
  have hw : shellEuclideanCoordinates.symm w ∈ euclideanShellChartDomain m := by
    simpa [euclideanShellChartDomain] using referenceContourMap_zero_mem_domain hB m θ
  obtain ⟨ε, cJ, CJ, hε, hcJ, hCJ, hJ⟩ := inducedShellChartDensity_joint_local_bounds Λ hw
  let V := regularShellFamilyNeighborhood m Λ w δ ε
  have hR : 0 < R := (radialShellEnergy_pos hB m).trans hE
  let a : ℝ≥0∞ := ((ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))) *
    (physicalParameterHaarScale : ℝ≥0∞) * volume (ball (0 : Fin 3 → ℝ) δ))
  let b : ℝ≥0∞ := (fixedMassContourHaarScale m hB hθ : ℝ≥0∞) * ENNReal.ofReal C
  have ha : 0 < a := by
    dsimp [a]
    exact contour_ENNReal_mul_pos (contour_ENNReal_mul_pos (contour_ENNReal_mul_pos
      (ENNReal.ofReal_pos.mpr hd)
      (ENNReal.ofReal_pos.mpr (by positivity)))
        (ENNReal.coe_pos.mpr physicalParameterHaarScale_pos)) (measure_ball_pos _ _ hδ)
  have hat : a ≠ ∞ := by
    dsimp [a]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top) measure_ball_ne_top
  have hb : 0 < b := contour_ENNReal_mul_pos (ENNReal.coe_pos.mpr
    (fixedMassContourHaarScale_pos m hB hθ))
    (ENNReal.ofReal_pos.mpr hC)
  have hbt : b ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hCJe : 0 < ENNReal.ofReal CJ := ENNReal.ofReal_pos.mpr hCJ
  let k : ℝ≥0∞ := a / (ENNReal.ofReal CJ * b)
  have hk : 0 < k := by
    rw [show k = a * (ENNReal.ofReal CJ * b)⁻¹ from div_eq_mul_inv _ _]
    exact contour_ENNReal_mul_pos ha (ENNReal.inv_pos.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt))
  have hkt : k < ∞ := ENNReal.div_lt_top hat (contour_ENNReal_mul_pos hCJe hb).ne'
  refine ⟨ρ, hρ, hnorm, V, isOpen_regularShellFamilyNeighborhood m Λ w δ ε, ?_,
    k, hk, hkt, ?_⟩
  · have hz : 0 < ((complexifiedSpacetimeMap Λ.symm
        (complexifiedSpacetimeMap Λ (radialShellContour m B θ 0))).2 1).re := by
      rw [complexifiedSpacetimeMap_inverse]
      simpa [radialShellContour] using hB
    have hcoord : lorentzComplexShellCoordinates Λ
        (complexifiedSpacetimeMap Λ (radialShellContour m B θ 0)) = w := by
      change complexShellCoordinates (complexifiedSpacetimeMap Λ.symm
        (complexifiedSpacetimeMap Λ (radialShellContour m B θ 0))) = _
      rw [complexifiedSpacetimeMap_inverse, ← referenceContourMap_zero]
    have hmem : lorentzComplexShellCoordinates Λ
        (complexifiedSpacetimeMap Λ (radialShellContour m B θ 0)) ∈ complexShellChartDomain m := by
      rw [hcoord]
      exact referenceContourMap_zero_mem_domain hB m θ
    have hc := regularShellFamilyNeighborhood_mem_center Λ hδ hε hz hmem
    simpa only [hcoord] using hc
  · intro t F hF
    by_cases ht : |t - m| < min δ ε
    · have hpatch := regularShellFamilyNeighborhood_fiber Λ w ht
      change k * (∫⁻ z in {z : complexShell t |
          (t, z.1) ∈ regularShellFamilyNeighborhood m Λ w δ ε},
          F z.1 ∂inducedRegularShellVolume t) ≤ _
      rw [hpatch]
      have hs := (isOpen_localShellCoordinateSet t w δ ε).measurableSet
      have hflat := inducedRegularShellVolume_coordinatePatch_le_flat Λ hΛ hs
        (fun _ hx => hx.1.1)
        (fun x hx => (hJ t (ht.trans_le (min_le_right _ _)).le x hx.2.le).2.2)
        measurableSet_ball (fun _ hx => hx.1.2) hF
      have hphys := hbound (t - m) (ht.trans_le (min_le_left _ _)) F hF
      have hmass : m + (t - m) = t := by ring
      rw [hmass] at hphys
      exact normalize_ENNReal_domination hb.ne' hbt hCJe.ne' ENNReal.ofReal_ne_top hflat hphys
    · have he := regularShellFamilyNeighborhood_fiber_empty Λ w ht
      change k * (∫⁻ z in {z : complexShell t |
          (t, z.1) ∈ regularShellFamilyNeighborhood m Λ w δ ε},
          F z.1 ∂inducedRegularShellVolume t) ≤ _
      rw [he, setLIntegral_empty, mul_zero]
      exact bot_le

end VacuumBellSeparation
