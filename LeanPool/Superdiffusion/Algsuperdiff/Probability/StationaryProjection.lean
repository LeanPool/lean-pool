/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.HilbertFinite
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# StationaryProjection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Stationary potential projection

This file constructs the Hilbert-space realization of the stationary operator
`∇ Δ⁻¹ div`.  The potential space is the closure of the full range of strong
horizontal gradients for a real translation action; it is not a selected
cylinder class or an abstract subspace parameter.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Probability.Stationary

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable [AddAction (Vec d) Ω]
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- A fixed stationary translation is measure-preserving.  The construction
only needs measurability in the field variable, not joint measurability of the
translation parameter and the field. -/
theorem measurePreserving_const_vadd (x : Vec d) :
    MeasurePreserving (fun ω : Ω ↦ x +ᵥ ω) μ μ := by
  refine ⟨measurable_const_vadd x, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_const_vadd x) hs]
  exact VAddInvariantMeasure.measure_preimage_vadd x hs

/-- Scalar stationary square-integrable random variables. -/
abbrev ScalarL2 (μ : Measure Ω) := Lp ℝ 2 μ

/-- Euclidean-vector-valued stationary square-integrable random variables. -/
abbrev VectorL2 (d : ℕ) (μ : Measure Ω) := Lp (HilbertVec d) 2 μ

/-- The Koopman isometry induced by a measure-preserving translation. -/
def koopman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Vec d) : Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (x +ᵥ ·) (measurePreserving_const_vadd (μ := μ) x)

/-- The `i`th coordinate of a vector-valued `L²` random variable. -/
def vectorL2Coord (i : Fin d) : VectorL2 d μ →L[ℝ] ScalarL2 μ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin d ↦ ℝ) i).compLpL 2 μ

/-- `F` is the full strong horizontal gradient of `φ`. -/
def HasHorizontalGradient (φ : ScalarL2 μ) (F : VectorL2 d μ) : Prop :=
  ∀ i : Fin d,
    HasDerivAt
      (fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ)
      (vectorL2Coord (μ := μ) i F) 0

theorem hasHorizontalGradient_zero :
    HasHorizontalGradient (μ := μ) (d := d) 0 0 := by
  intro i
  simpa only [map_zero] using
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ScalarL2 μ)))

theorem HasHorizontalGradient.add {φ ψ : ScalarL2 μ} {F G : VectorL2 d μ}
    (hφ : HasHorizontalGradient (μ := μ) φ F)
    (hψ : HasHorizontalGradient (μ := μ) ψ G) :
    HasHorizontalGradient (μ := μ) (φ + ψ) (F + G) := by
  intro i
  have hfun : (fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) (φ + ψ))
      = fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ
          + koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) ψ := by
    funext t
    exact map_add (koopman (μ := μ) (t • (Pi.single i 1 : Vec d))) φ ψ
  have hcoord : vectorL2Coord (μ := μ) i (F + G)
      = vectorL2Coord (μ := μ) i F + vectorL2Coord (μ := μ) i G :=
    ContinuousLinearMap.map_add (vectorL2Coord (μ := μ) i) F G
  rw [hfun, hcoord]
  exact (hφ i).add (hψ i)

theorem HasHorizontalGradient.smul (c : ℝ) {φ : ScalarL2 μ}
    {F : VectorL2 d μ} (hφ : HasHorizontalGradient (μ := μ) φ F) :
    HasHorizontalGradient (μ := μ) (c • φ) (c • F) := by
  intro i
  have hfun : (fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) (c • φ))
      = fun t : ℝ ↦ c • koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ := by
    funext t
    exact map_smul (koopman (μ := μ) (t • (Pi.single i 1 : Vec d))) c φ
  have hcoord : vectorL2Coord (μ := μ) i (c • F)
      = c • vectorL2Coord (μ := μ) i F :=
    ContinuousLinearMap.map_smul (vectorL2Coord (μ := μ) i) c F
  rw [hfun, hcoord]
  exact (hφ i).const_smul c

/-- The linear range of all full strong horizontal gradients. -/
def horizontalGradientRange : Submodule ℝ (VectorL2 d μ) where
  carrier := {F | ∃ φ, HasHorizontalGradient (μ := μ) φ F}
  zero_mem' := ⟨0, hasHorizontalGradient_zero (μ := μ) (d := d)⟩
  add_mem' := by
    rintro F G ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    exact ⟨φ + ψ, hφ.add hψ⟩
  smul_mem' := by
    rintro c F ⟨φ, hφ⟩
    exact ⟨c • φ, hφ.smul c⟩

/-- The closed stationary potential subspace. -/
def stationaryPotentialSubspace : Submodule ℝ (VectorL2 d μ) :=
  (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure

/-- The stationary solenoidal subspace. -/
def stationarySolenoidalSubspace : Submodule ℝ (VectorL2 d μ) :=
  (stationaryPotentialSubspace (μ := μ) (d := d))ᗮ

instance stationaryPotentialSubspace_hasOrthogonalProjection :
    (stationaryPotentialSubspace (μ := μ) (d := d)).HasOrthogonalProjection := by
  let : CompleteSpace (stationaryPotentialSubspace (μ := μ) (d := d)) := by
    change CompleteSpace
      (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure
    infer_instance
  infer_instance

/-- Orthogonal projection onto stationary potential fields. -/
def stationaryPotentialProjection : VectorL2 d μ →L[ℝ] VectorL2 d μ :=
  (stationaryPotentialSubspace (μ := μ) (d := d)).starProjection

theorem stationaryPotentialProjection_mem (F : VectorL2 d μ) :
    stationaryPotentialProjection (μ := μ) F ∈
      stationaryPotentialSubspace (μ := μ) (d := d) :=
  Submodule.starProjection_apply_mem _ _

theorem sub_stationaryPotentialProjection_mem_orthogonal (F : VectorL2 d μ) :
    F - stationaryPotentialProjection (μ := μ) F ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) :=
  Submodule.sub_starProjection_mem_orthogonal
    (K := stationaryPotentialSubspace (μ := μ) (d := d)) F

/-- Potential membership and the weak divergence identity characterize the
stationary potential projection. -/
theorem eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    {F q : VectorL2 d μ}
    (hq : q ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hFq : F - q ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    q = stationaryPotentialProjection (μ := μ) F := by
  exact (Submodule.eq_starProjection_of_mem_orthogonal hq hFq).symm

section ContinuousAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω]
variable [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- Every Koopman orbit is strongly continuous under the standard topological
hypotheses on the probability carrier and its real translation action. -/
theorem continuous_koopman_orbit (f : Lp E 2 μ) :
    Continuous (fun x : Vec d ↦ koopman (μ := μ) x f) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  change Continuous (fun x : Vec d ↦ DomAddAct.mk x +ᵥ f)
  exact DomAddAct.continuous_mk.vadd continuous_const

end ContinuousAction

end

end Algsuperdiff.Probability.Stationary
