/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffOperator

/-!
# Derivatives of a locally constant cutoff

The first spatial, second spatial, and time derivatives of a smooth scalar
factor vanish wherever it is locally constant. This identifies the support
of the phase-cutoff errors in `lem:bu-small-time`.
-/

public section


open Set CKN CKN.Foundation.Parabolic Filter
open scoped Topology

noncomputable section

namespace ESS

private theorem eventuallyEq_spatial_slice
    {S : Set (Vec3 × ℝ)} {κ : Vec3 × ℝ → ℝ} {c : ℝ}
    (hS : IsOpen S) (hκ : EqOn κ (fun _ => c) S)
    {q : Vec3 × ℝ} (hq : q ∈ S) :
    (fun y : Vec3 => κ (y, q.2)) =ᶠ[𝓝 q.1] (fun _ => c) := by
  have hmap : ContinuousAt (fun y : Vec3 => ((y, q.2) : Vec3 × ℝ)) q.1 := by
    fun_prop
  have hmem : ∀ᶠ r : Vec3 × ℝ in 𝓝 q, r ∈ S := hS.mem_nhds hq
  have hevent : ∀ᶠ r : Vec3 × ℝ in 𝓝 q, κ r = c :=
    hmem.mono (fun r hr => hκ hr)
  exact hmap.tendsto.eventually hevent

private theorem eventuallyEq_time_slice
    {S : Set (Vec3 × ℝ)} {κ : Vec3 × ℝ → ℝ} {c : ℝ}
    (hS : IsOpen S) (hκ : EqOn κ (fun _ => c) S)
    {q : Vec3 × ℝ} (hq : q ∈ S) :
    (fun s : ℝ => κ (q.1, s)) =ᶠ[𝓝 q.2] (fun _ => c) := by
  have hmap : ContinuousAt (fun s : ℝ => ((q.1, s) : Vec3 × ℝ)) q.2 := by
    fun_prop
  have hmem : ∀ᶠ r : Vec3 × ℝ in 𝓝 q, r ∈ S := hS.mem_nhds hq
  have hevent : ∀ᶠ r : Vec3 × ℝ in 𝓝 q, κ r = c :=
    hmem.mono (fun r hr => hκ hr)
  exact hmap.tendsto.eventually hevent

/-- All derivatives used by the cutoff heat operator vanish on an open
region where the scalar cutoff is constant. -/
theorem buCutScalar_derivatives_eq_zero_of_eqOn
    {S : Set (Vec3 × ℝ)} {κ : Vec3 × ℝ → ℝ} {c : ℝ}
    (hS : IsOpen S) (hκ : EqOn κ (fun _ => c) S)
    {z : ParabolicPoint} (hz : parabolicHomeomorph z ∈ S) :
    (∀ j : Fin 3, spatialPartial (buCutScalar κ) j z = 0) ∧
      (∀ j k : Fin 3,
        spatialSecondPartial (buCutScalar κ) j k z = 0) ∧
      timePartial (buCutScalar κ) z = 0 := by
  rcases z with ⟨y, s⟩
  have hq : (y, s) ∈ S := hz
  have hsp (q : Vec3 × ℝ) (hq' : q ∈ S) (j : Fin 3) :
      spatialPartial (buCutScalar κ) j
        ((q.1, q.2) : ParabolicPoint) = 0 := by
    have heq := eventuallyEq_spatial_slice hS hκ hq'
    change (fderiv ℝ (fun x : Vec3 => κ (x, q.2)) q.1) (basisVec j) = 0
    rw [heq.fderiv_eq]
    simp
  constructor
  · intro j
    exact hsp (y, s) hq j
  constructor
  · intro j k
    have hinner : (fun x : Vec3 =>
        spatialPartial (buCutScalar κ) j
          ((x, s) : ParabolicPoint)) =ᶠ[𝓝 y] (fun _ => 0) := by
      have hmap : ContinuousAt (fun x : Vec3 => ((x, s) : Vec3 × ℝ)) y := by
        fun_prop
      have hnear : ∀ᶠ r : Vec3 × ℝ in 𝓝 (y, s), r ∈ S :=
        hS.mem_nhds hq
      have hmem : ∀ᶠ x : Vec3 in 𝓝 y, (x, s) ∈ S :=
        hmap.tendsto.eventually hnear
      exact hmem.mono (fun x hx => hsp (x, s) hx j)
    change (fderiv ℝ (fun x : Vec3 =>
      spatialPartial (buCutScalar κ) j ((x, s) : ParabolicPoint)) y)
        (basisVec k) = 0
    rw [hinner.fderiv_eq]
    simp
  · have heq := eventuallyEq_time_slice hS hκ hq
    change (fderiv ℝ (fun t : ℝ => κ (y, t)) s) 1 = 0
    rw [heq.fderiv_eq]
    simp

end ESS
