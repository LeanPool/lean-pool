/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.MidpointFourthJet
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact fourth-order approximate-geodesic identities. -/

@[expose] public section
noncomputable section
namespace PlanarMidpoint

/-- A bilinear second derivative of a planar cubic coefficient field. -/
abbrev Hessian := E →L[ℝ] E →L[ℝ] Coeff

/-- The polynomial tail after removing the first three force coefficients. -/
def forceTail (c c₁ c₂ c₃ : Coeff) (v₁ v₂ v₃ v₄ : E) (ε : ℝ) : E :=
  let W₃ := v₃ + ε • v₄
  let W₂ := v₂ + ε • W₃
  let U := v₁ + ε • W₂
  2 • K c v₁ v₄ + 2 • K c v₂ W₃ + ε • K c W₃ W₃ + 2 • K c₁ v₁ W₃ + K c₁ W₂ W₂ + 2 • K c₂ v₁ W₂ + ε
      • K c₂ W₂ W₂ + K c₃ U U

/-- Exact trilinear expansion, with no division by the small parameter. -/
theorem force_expansion (c c₁ c₂ c₃ : Coeff) (v₁ v₂ v₃ v₄ : E) (ε : ℝ) :
    K (c + ε • c₁ + ε ^ 2 • c₂ + ε ^ 3 • c₃)
      (ε • v₁ + ε ^ 2 • v₂ + ε ^ 3 • v₃ + ε ^ 4 • v₄)
      (ε • v₁ + ε ^ 2 • v₂ + ε ^ 3 • v₃ + ε ^ 4 • v₄) =
    ε ^ 2 • K c v₁ v₁ + ε ^ 3 • (2 • K c v₁ v₂ + K c₁ v₁ v₁) + ε ^ 4 • (2 • K c v₁ v₃ + K c v₂ v₂
        + 2 • K c₁ v₁ v₂ + K c₂ v₁ v₁) + ε ^ 5 • forceTail c c₁ c₂ c₃ v₁ v₂ v₃ v₄ ε := by
  apply vec_ext <;> simp [K, forceTail] <;> ring

/-- The exact coefficient-field Taylor tail induced by a quartic displacement. -/
def coefficientTail (J : E →L[ℝ] Coeff) (H : Hessian)
    (d₁ d₂ d₃ d₄ : E) (ε : ℝ) : Coeff :=
  let D := d₂ + ε • d₃ + ε ^ 2 • d₄
  J (d₃ + ε • d₄) + (1 / 2 : ℝ) • (H d₁ D + H D d₁) + (ε / 2) • H D D

/-- Exact substitution into the quadratic spatial Taylor polynomial. -/
theorem coefficient_expansion (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (d₁ d₂ d₃ d₄ : E) (ε : ℝ) :
    let δ := ε • d₁ + ε ^ 2 • d₂ + ε ^ 3 • d₃ + ε ^ 4 • d₄
    c + J δ + (1 / 2 : ℝ) • H δ δ =
      c + ε • J d₁ + ε ^ 2 • (J d₂ + (1 / 2 : ℝ) • H d₁ d₁) + ε ^ 3 • coefficientTail J H d₁ d₂ d₃
          d₄ ε := by
  ext i
  simp [coefficientTail, map_add, map_smul]
  ring

/-- The quadratic Dirichlet jet. -/
def secondJet (c : Coeff) (h : E) (t : ℝ) : E :=
  (1 / 8 - (1 / 2) * (t - 1 / 2) ^ 2 : ℝ) • K c h h

/-- The cubic Dirichlet jet. -/
def thirdJet (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) (t : ℝ) : E :=
  ((t - 1 / 2) ^ 3 / 6 - (t - 1 / 2) / 24) • cubicJetVector c J h

/-- The velocity of the quadratic Dirichlet jet. -/
def secondJetVelocity (c : Coeff) (h : E) (t : ℝ) : E :=
  (-(t - 1 / 2)) • K c h h

/-- The velocity of the cubic Dirichlet jet. -/
def thirdJetVelocity (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) (t : ℝ) : E :=
  ((t - 1 / 2) ^ 2 / 2 - 1 / 24) • cubicJetVector c J h

/-- The quartic Dirichlet jet determined by its constant and quadratic acceleration. -/
def fourthJet (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian) (h : E) : ℝ → E :=
  fourthDirichlet (fourthAccelerationZero c J h) (fourthAccelerationTwo c J (H h h) h)

/-- The velocity of the quartic Dirichlet jet. -/
def fourthJetVelocity (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (t : ℝ) : E :=
  (t - 1 / 2) • fourthAccelerationZero c J h + ((t - 1 / 2) ^ 3 / 3) • fourthAccelerationTwo c J
      (H h h) h

/-- Quartic endpoint-matched approximate geodesic, relative to its center. -/
def approxDisplacement (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  ε • ((t - 1 / 2) • h) + ε ^ 2 • secondJet c h t + ε ^ 3 • thirdJet c J h t + ε ^ 4 • fourthJet c
      J H h t

/-- The velocity of the fourth-order endpoint-matched approximate geodesic. -/
def approxVelocity (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  ε • h + ε ^ 2 • secondJetVelocity c h t + ε ^ 3 • thirdJetVelocity c J h t + ε ^ 4 •
      fourthJetVelocity c J H h t

/-- The acceleration of the fourth-order approximate geodesic. -/
def approxAcceleration (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  ε ^ 2 • (-K c h h) + ε ^ 3 • ((t - 1 / 2) • cubicJetVector c J h) + ε ^ 4 •
      (fourthAccelerationZero c J h + (t - 1 / 2) ^ 2 • fourthAccelerationTwo c J (H h h) h)

@[simp] theorem secondJet_zero (c : Coeff) (h : E) : secondJet c h 0 = 0 := by
  norm_num [secondJet]
@[simp] theorem secondJet_one (c : Coeff) (h : E) : secondJet c h 1 = 0 := by
  norm_num [secondJet]
@[simp] theorem thirdJet_zero (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) :
    thirdJet c J h 0 = 0 := by norm_num [thirdJet]
@[simp] theorem thirdJet_one (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) :
    thirdJet c J h 1 = 0 := by norm_num [thirdJet]

@[simp] theorem approxDisplacement_zero (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε : ℝ) :
    approxDisplacement c J H h ε 0 = (-ε / 2) • h := by
  norm_num [approxDisplacement, fourthJet]
  module

@[simp] theorem approxDisplacement_one (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε : ℝ) :
    approxDisplacement c J H h ε 1 = (ε / 2) • h := by
  norm_num [approxDisplacement, fourthJet]
  module

theorem hasDerivAt_secondJet (c : Coeff) (h : E) (t : ℝ) :
    HasDerivAt (secondJet c h) (secondJetVelocity c h t) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  convert (((hs.pow 2).const_mul (1 / 2)).const_sub (1 / 8)).smul_const (K c h h) using 1 <;>
    ext <;> simp [secondJet, secondJetVelocity]

theorem hasDerivAt_secondJetVelocity (c : Coeff) (h : E) (t : ℝ) :
    HasDerivAt (secondJetVelocity c h) (-K c h h) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  change HasDerivAt (fun s ↦ secondJetVelocity c h s) _ t
  simpa [secondJetVelocity] using hs.neg.smul_const (K c h h)

theorem hasDerivAt_thirdJet (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) (t : ℝ) :
    HasDerivAt (thirdJet c J h) (thirdJetVelocity c J h t) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  convert (((hs.pow 3).div_const 6).sub (hs.div_const 24)).smul_const
    (cubicJetVector c J h) using 1 <;>
    ext <;> simp [thirdJet, thirdJetVelocity]; ring_nf; simp

theorem hasDerivAt_thirdJetVelocity (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) (t : ℝ) :
    HasDerivAt (thirdJetVelocity c J h) ((t - 1 / 2) • cubicJetVector c J h) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  convert (((hs.pow 2).div_const 2).sub_const (1 / 24)).smul_const
    (cubicJetVector c J h) using 1 <;>
    ext <;> simp [thirdJetVelocity]

theorem hasDerivAt_approxDisplacement (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε t : ℝ) :
    HasDerivAt (approxDisplacement c J H h ε) (approxVelocity c J H h ε t) t := by
  have h₁ := (((hasDerivAt_id t).sub_const (1 / 2 : ℝ)).smul_const h).const_smul ε
  have h₂ := (hasDerivAt_secondJet c h t).const_smul (ε ^ 2)
  have h₃ := (hasDerivAt_thirdJet c J h t).const_smul (ε ^ 3)
  have h₄ := (hasDerivAt_fourthDirichlet (fourthAccelerationZero c J h)
    (fourthAccelerationTwo c J (H h h) h) t).const_smul (ε ^ 4)
  change HasDerivAt (fun s ↦ approxDisplacement c J H h ε s) _ t
  simpa [approxDisplacement, approxVelocity, fourthJet, fourthJetVelocity] using
    ((h₁.fun_add h₂).fun_add h₃).fun_add h₄

theorem hasDerivAt_approxVelocity (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε t : ℝ) :
    HasDerivAt (approxVelocity c J H h ε) (approxAcceleration c J H h ε t) t := by
  have h₁ := hasDerivAt_const t (ε • h)
  have h₂ := (hasDerivAt_secondJetVelocity c h t).const_smul (ε ^ 2)
  have h₃ := (hasDerivAt_thirdJetVelocity c J h t).const_smul (ε ^ 3)
  have h₄ := (hasDerivAt_fourthDirichlet_velocity (fourthAccelerationZero c J h)
    (fourthAccelerationTwo c J (H h h) h) t).const_smul (ε ^ 4)
  change HasDerivAt (fun s ↦ approxVelocity c J H h ε s) _ t
  simpa [approxVelocity, approxAcceleration, fourthJetVelocity] using
    ((h₁.fun_add h₂).fun_add h₃).fun_add h₄

private theorem cubic_force_coefficient (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) (t : ℝ) :
    2 • K c h (secondJetVelocity c h t) + K (J ((t - 1 / 2) • h)) h h =
      -((t - 1 / 2) • cubicJetVector c J h) := by
  apply vec_ext <;> simp [secondJetVelocity, cubicJetVector, K] <;> ring

private theorem quartic_force_coefficient (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (t : ℝ) :
    2 • K c h (thirdJetVelocity c J h t) + K c (secondJetVelocity c h t) (secondJetVelocity c h t)
        + 2 • K (J ((t - 1 / 2) • h)) h (secondJetVelocity c h t) + K (J (secondJet c h t) + (1 /
        2 : ℝ) • H ((t - 1 / 2) • h) ((t - 1 / 2) • h)) h h =
      -(fourthAccelerationZero c J h + (t - 1 / 2) ^ 2 • fourthAccelerationTwo c J (H h h) h) := by
  apply vec_ext <;> simp [secondJetVelocity, thirdJetVelocity, secondJet,
    fourthAccelerationZero, fourthAccelerationTwo, cubicJetVector, K] <;> ring

/-- The exact fifth-order residual tail for the quadratic spatial model. -/
def approxResidualTail (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  forceTail c (J ((t - 1 / 2) • h))
    (J (secondJet c h t) + (1 / 2 : ℝ) • H ((t - 1 / 2) • h) ((t - 1 / 2) • h))
    (coefficientTail J H ((t - 1 / 2) • h) (secondJet c h t)
      (thirdJet c J h t) (fourthJet c J H h t) ε)
    h (secondJetVelocity c h t) (thirdJetVelocity c J h t) (fourthJetVelocity c J H h t) ε

/-- The approximate geodesic solves the quadratic spatial model through order four.
The remainder is a polynomial expression, including at `ε=0`. -/
theorem approx_residual_exact (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) :
    let δ := approxDisplacement c J H h ε t
    approxAcceleration c J H h ε t + K (c + J δ + (1 / 2 : ℝ) • H δ δ)
        (approxVelocity c J H h ε t) (approxVelocity c J H h ε t) =
      ε ^ 5 • approxResidualTail c J H h ε t := by
  dsimp only
  unfold approxDisplacement approxVelocity
  rw [coefficient_expansion, force_expansion, cubic_force_coefficient, quartic_force_coefficient]
  unfold approxAcceleration approxResidualTail
  module

/-- Removing the explicit small parameter from the approximate displacement. -/
def approxDisplacementScaled (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  (t - 1 / 2) • h + ε • secondJet c h t + ε ^ 2 • thirdJet c J h t + ε ^ 3 • fourthJet c J H h t

/-- Removing the explicit small parameter from the approximate velocity. -/
def approxVelocityScaled (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) : E :=
  h + ε • secondJetVelocity c h t + ε ^ 2 • thirdJetVelocity c J h t + ε ^ 3 • fourthJetVelocity c
      J H h t

theorem approxDisplacement_factor (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) :
    approxDisplacement c J H h ε t = ε • approxDisplacementScaled c J H h ε t := by
  unfold approxDisplacement approxDisplacementScaled
  module

theorem approxVelocity_factor (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian)
    (h : E) (ε t : ℝ) :
    approxVelocity c J H h ε t = ε • approxVelocityScaled c J H h ε t := by
  unfold approxVelocity approxVelocityScaled
  module

@[fun_prop] theorem continuous_approxDisplacementScaled (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) :
    Continuous (fun p : ℝ × ℝ ↦ approxDisplacementScaled c J H h p.1 p.2) := by
  unfold approxDisplacementScaled secondJet thirdJet fourthJet fourthDirichlet
  fun_prop

@[fun_prop] theorem continuous_approxVelocityScaled (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) :
    Continuous (fun p : ℝ × ℝ ↦ approxVelocityScaled c J H h p.1 p.2) := by
  unfold approxVelocityScaled secondJetVelocity thirdJetVelocity fourthJetVelocity
  fun_prop

@[fun_prop] theorem continuous_K_family {X : Type*} [TopologicalSpace X]
    {c : X → Coeff} {u v : X → E} (hc : Continuous c) (hu : Continuous u)
    (hv : Continuous v) : Continuous (fun x ↦ K (c x) (u x) (v x)) := by
  unfold K vec
  fun_prop

@[fun_prop] theorem continuous_approxResidualTail (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) :
    Continuous (fun p : ℝ × ℝ ↦ approxResidualTail c J H h p.1 p.2) := by
  unfold approxResidualTail forceTail coefficientTail secondJet thirdJet fourthJet
    fourthDirichlet secondJetVelocity thirdJetVelocity fourthJetVelocity
  fun_prop

/-- Uniform estimates on the compact parameter rectangle. The displacement and
velocity bounds include their explicit first-order small parameter. -/
theorem approx_uniform_bounds (c : Coeff) (J : E →L[ℝ] Coeff) (H : Hessian) (h : E) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ R : ℝ, 0 ≤ R ∧
      ∀ ε t : ℝ, |ε| ≤ 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        ‖approxDisplacement c J H h ε t‖ ≤ B * |ε| ∧
        ‖approxVelocity c J H h ε t‖ ≤ B * |ε| ∧
        ‖approxResidualTail c J H h ε t‖ ≤ R := by
  let S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn
    (continuous_approxDisplacementScaled c J H h).continuousOn
  obtain ⟨V, hV⟩ := hS.exists_bound_of_continuousOn
    (continuous_approxVelocityScaled c J H h).continuousOn
  obtain ⟨T, hT⟩ := hS.exists_bound_of_continuousOn
    (continuous_approxResidualTail c J H h).continuousOn
  let B := max 1 (max D V)
  have hDB : D ≤ B := (le_max_left D V).trans (le_max_right 1 (max D V))
  have hVB : V ≤ B := (le_max_right D V).trans (le_max_right 1 (max D V))
  refine ⟨B, le_max_left _ _, max 0 T, le_max_left _ _, ?_⟩
  intro ε t hε ht
  have hp : (ε, t) ∈ S := ⟨abs_le.mp hε, ht⟩
  refine ⟨?_, ?_, (hT (ε, t) hp).trans (le_max_right _ _)⟩
  · rw [approxDisplacement_factor, norm_smul, Real.norm_eq_abs]
    calc
      |ε| * ‖approxDisplacementScaled c J H h ε t‖ ≤ |ε| * B :=
        mul_le_mul_of_nonneg_left ((hD (ε, t) hp).trans hDB) (abs_nonneg ε)
      _ = B * |ε| := mul_comm _ _
  · rw [approxVelocity_factor, norm_smul, Real.norm_eq_abs]
    calc
      |ε| * ‖approxVelocityScaled c J H h ε t‖ ≤ |ε| * B :=
        mul_le_mul_of_nonneg_left ((hV (ε, t) hp).trans hVB) (abs_nonneg ε)
      _ = B * |ε| := mul_comm _ _

/-- Midpoint value of the approximate geodesic. -/
theorem approxDisplacement_midpoint (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε : ℝ) :
    approxDisplacement c J H h ε (1 / 2) =
      (ε ^ 2 / 8) • K c h h + ε ^ 4 • fourthMidpointCoefficient c J (H h h) h := by
  simp only [approxDisplacement, secondJet, thirdJet, fourthJet,
    fourthDirichlet_coefficient]
  norm_num
  module

/-- The opposite approximate midpoints retain exactly the quartic obstruction. -/
theorem approxDisplacement_add_opposite_midpoint (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Hessian) (h : E) (ε : ℝ) :
    approxDisplacement c J H h ε (1 / 2) + approxDisplacement (-c) (-J) (-H) h ε (1 / 2) =
      (ε ^ 4 / 192) • obstruction c J h := by
  have hk : K (-c) h h = -K c h h := by
    apply vec_ext <;> simp [K] <;> ring
  rw [approxDisplacement_midpoint, approxDisplacement_midpoint]
  simp only [neg_apply, hk]
  calc
    (ε ^ 2 / 8) • K c h h + ε ^ 4 • fourthMidpointCoefficient c J (H h h) h + ((ε ^ 2 / 8) • -K c
        h h + ε ^ 4 • fourthMidpointCoefficient (-c) (-J) (-(H h h)) h) =
      ε ^ 4 • (fourthMidpointCoefficient c J (H h h) h + fourthMidpointCoefficient (-c) (-J) (-(H
          h h)) h) := by module
    _ = _ := by
      rw [fourthMidpointCoefficient_add_opposite]
      module

end PlanarMidpoint
