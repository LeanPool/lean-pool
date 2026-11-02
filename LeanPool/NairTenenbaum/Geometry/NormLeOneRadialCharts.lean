/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Geometry.MixedPolarCoordinates
public import LeanPool.NairTenenbaum.Geometry.NormLeOneBoundaryRadii
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-! # Smooth compact parametrizations of the norm-one region

The parameter indexed by the distinguished infinite place is radial; the other
infinite-place parameters are unit coordinates. Complex places contribute one
angular parameter each. The total parameter count is the field degree.
-/

@[expose] public section


namespace NairTenenbaum

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

/-- The parameter space for radial charts of the number-field norm region. -/
abbrev NormRegionParameter := InfinitePlace K ⊕ {w : InfinitePlace K // IsComplex w}

open Classical in
/-- Unit directions used in the radial parametrization of the norm region. -/
noncomputable def normRegionUnitCoordinates (v : NormRegionParameter K → ℝ) : realSpace K :=
  fun w => if w = w₀ then 0 else v (Sum.inl w)

/-- The radial chart associated with a norm-region parameter. -/
noncomputable def normRegionRadialChart
    (σ : {w : InfinitePlace K // IsReal w} → Bool) (v : NormRegionParameter K → ℝ) : mixedSpace K :=
  mixedPolarCoordinates σ (v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v))
    (fun w => v (Sum.inr w))

open Classical in
theorem card_normRegionParameter : Fintype.card (NormRegionParameter K) = Module.finrank ℚ K := by
  rw [Fintype.card_sum, card_eq_nrRealPlaces_add_nrComplexPlaces]
  change nrRealPlaces K + nrComplexPlaces K + nrComplexPlaces K = Module.finrank ℚ K
  have H := card_add_two_mul_card_eq_rank K
  omega

theorem contDiff_expMapBasis : ContDiff ℝ ⊤ (expMapBasis : realSpace K → realSpace K) := by
  apply contDiff_pi.mpr
  intro w
  change ContDiff ℝ ⊤ (fun v : realSpace K =>
    Real.exp ((w.mult : ℝ)⁻¹ * ((completeBasis K).equivFunL.symm v) w))
  fun_prop

open Classical in
theorem contDiff_normRegionRadialChart (σ : {w : InfinitePlace K // IsReal w} → Bool) :
    ContDiff ℝ ⊤ (normRegionRadialChart K σ) := by
  classical
  have hu : ContDiff ℝ ⊤ (normRegionUnitCoordinates K) := by
    apply contDiff_pi.mpr
    intro w
    by_cases hw : w = w₀
    · simp only [normRegionUnitCoordinates, hw, ↓reduceIte]
      fun_prop
    · simp only [normRegionUnitCoordinates, hw, ↓reduceIte]
      fun_prop
  have hr : ContDiff ℝ ⊤ (fun v : NormRegionParameter K → ℝ =>
      v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v)) := by
    exact (contDiff_apply ℝ ℝ (Sum.inl w₀)).smul
        ((contDiff_expMapBasis K).comp hu)
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro w
    change ContDiff ℝ ⊤ (fun v : NormRegionParameter K → ℝ =>
      if σ w then (v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v)) w
      else -(v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v)) w)
    cases hσ : σ w <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ((contDiff_apply ℝ ℝ w.1).comp hr).neg
    · exact (contDiff_apply ℝ ℝ w.1).comp hr
  · apply contDiff_pi.mpr
    intro w
    change ContDiff ℝ ⊤ (fun v : NormRegionParameter K → ℝ =>
      (((v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v)) w : ℝ) : ℂ) *
        Complex.exp (((2 * v (Sum.inr w) - 1) * Real.pi : ℝ) * Complex.I))
    have hcoord := (contDiff_apply ℝ ℝ w.1).comp hr
    have hangle : ContDiff ℝ ⊤ (fun v : NormRegionParameter K → ℝ =>
        (2 * v (Sum.inr w) - 1) * Real.pi) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp hcoord).mul
      (((Complex.ofRealCLM.contDiff.comp hangle).mul contDiff_const).cexp)

theorem normLeOne_frontier_radialChart {x : mixedSpace K} (hx : x ∈ frontier (normLeOne K)) :
    ∃ σ : {w : InfinitePlace K // IsReal w} → Bool,
      ∃ v : NormRegionParameter K → ℝ,
        v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧ normRegionRadialChart K σ v = x ∧
        ∃ w : InfinitePlace K, v (Sum.inl w) = 0 ∨ v (Sum.inl w) = 1 := by
  classical
  obtain ⟨r, u, hr, hu0, hu, hnorm, hface⟩ := normLeOne_frontier_radial_faces K hx
  obtain ⟨σ, a, ha, hpolar⟩ := exists_mixedPolarCoordinates x
  let v : NormRegionParameter K → ℝ := Sum.elim (fun w => if w = w₀ then r else u w) a
  have hv0 : v (Sum.inl w₀) = r := by simp [v]
  have hvunit : normRegionUnitCoordinates K v = u := by
    ext w
    by_cases hw : w = w₀
    · subst w
      simp [normRegionUnitCoordinates, hu0]
    · simp [normRegionUnitCoordinates, v, hw]
  refine ⟨σ, v, ?_, ?_, ?_⟩
  · constructor <;> intro i <;> cases i with
    | inl w =>
      by_cases hw : w = w₀
      · simp only [v, Sum.elim_inl, hw, ↓reduceIte]
        first | exact hr.1 | exact hr.2
      · simp only [v, Sum.elim_inl, hw, ↓reduceIte]
        first | exact (hu w hw).1 | exact (hu w hw).2
    | inr w =>
      first | exact ha.1 w | exact ha.2 w
  · change mixedPolarCoordinates σ (v (Sum.inl w₀) • expMapBasis (normRegionUnitCoordinates K v))
      (fun w => v (Sum.inr w)) = x
    rw [hv0, hvunit, ← hnorm]
    exact hpolar
  · rcases hface with hzero | hone | ⟨w, hw, h⟩
    · exact ⟨w₀, Or.inl (hv0.trans hzero)⟩
    · exact ⟨w₀, Or.inr (hv0.trans hone)⟩
    · exact ⟨w, by simpa [v, hw] using h⟩

end NairTenenbaum
