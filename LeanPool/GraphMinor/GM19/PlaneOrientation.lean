/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneOrientation
public import LeanPool.GraphMinor.GM19.Section4b
public import LeanPool.GraphMinor.GM19.FragmentDirection
public import LeanPool.GraphMinor.GM19.FragmentChord

/-!
# The orientation of the plane

We orient the plane (`planeOrientation : SurfaceOrientation ℂ`) using the positive boundary
parametrization `IsPosParam` and nested-disc lemma `order_of_nested` from
`GraphMinor.Surface.PlaneOrientation`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

export GraphMinor.Surface (wind exp_add_two_pi' isAngle_exp turn_period circle_exp_ne
  exists_plane_extension wind_ne_zero exists_mem_period wind_eq_of_ball turn_eq_of_nested
  image_sphere_of_extension discInt_eq_of_extension wind_eq_turn_rotate wind_eq_of_nested
  IsPosParam isPosParam_or_inv exists_posParam not_isPosParam_inv order_of_nested planePos)

/-- **The orientation of the plane.** -/
noncomputable def planeOrientation : SurfaceOrientation ℂ where
  pos := planePos
  isDirection := fun Δ hΔ => by
    obtain ⟨φ, hφ⟩ := exists_posParam hΔ
    refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2.1,
      fun a b c _ _ _ => ⟨?_, fun h => ⟨φ, a, b, c, hφ, rfl, rfl, rfl, h⟩⟩⟩
    rintro ⟨φ', u, v, w, hφ', ha, hb, hc, hcy⟩
    exact order_of_nested hΔ hΔ subset_rfl hφ' hφ hcy ha hb hc
  agree := fun Δ₁ Δ₂ h₁ h₂ hsub a b c ha hb hc hab hbc hac => by
    obtain ⟨φ₁, hφ₁⟩ := exists_posParam h₁
    obtain ⟨φ₂, hφ₂⟩ := exists_posParam h₂
    have hm₁ : ∀ {x}, x ∈ discBd Δ₁ → ∃ u, φ₁ u = x := fun hx => by
      rw [← hφ₁.2.2.1] at hx; exact hx
    have hm₂ : ∀ {x}, x ∈ discBd Δ₂ → ∃ u, φ₂ u = x := fun hx => by
      rw [← hφ₂.2.2.1] at hx; exact hx
    obtain ⟨u₁, rfl⟩ := hm₁ ha.1
    obtain ⟨v₁, rfl⟩ := hm₁ hb.1
    obtain ⟨w₁, rfl⟩ := hm₁ hc.1
    obtain ⟨u₂, hu₂⟩ := hm₂ ha.2
    obtain ⟨v₂, hv₂⟩ := hm₂ hb.2
    obtain ⟨w₂, hw₂⟩ := hm₂ hc.2
    have key : ∀ {x y z : Circle}, IsPosParam Δ₁ φ₁ →
        planePos Δ₁ (φ₁ x) (φ₁ y) (φ₁ z) → CircleCyclic x y z := by
      rintro x y z - ⟨φ, u, v, w, hφ, h1, h2, h3, hcy⟩
      exact order_of_nested h₁ h₁ subset_rfl hφ hφ₁ hcy h1 h2 h3
    constructor
    · intro h
      exact ⟨φ₂, u₂, v₂, w₂, hφ₂, hu₂, hv₂, hw₂,
        order_of_nested h₁ h₂ hsub hφ₁ hφ₂ (key hφ₁ h) hu₂.symm hv₂.symm hw₂.symm⟩
    · rintro ⟨φ, u, v, w, hφ, h1, h2, h3, hcy⟩
      have hd : u₁ ≠ v₁ := fun he => hab (by rw [he])
      have hd' : u₁ ≠ w₁ := fun he => hac (by rw [he])
      have hd'' : v₁ ≠ w₁ := fun he => hbc (by rw [he])
      refine ⟨φ₁, u₁, v₁, w₁, hφ₁, rfl, rfl, rfl, ?_⟩
      rcases circleCyclic_or hd hd' hd'' with h | h
      · exact h
      · exfalso
        have := order_of_nested h₁ h₂ hsub hφ₁ hφ h h1.symm h3.symm h2.symm
        exact not_circleCyclic_both hcy this

end GraphMinor.GM19
