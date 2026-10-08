/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorPropagate

/-!
# Vorticity vanishing on a regular slab

On a unit-scale slab `B_{ρ+1} × (-2, 2)` where a suitable solution has bounded
velocity, vanishing of the weak vorticity on a small seed cylinder propagates
through the connected ball `B_ρ` at every time of `(-1, 1)`.  This is the
connectedness argument in the proof of `thm:ess-local`, with the relatively
closed step supplied by
`essLocal_vorticityZero_propagate`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- On a unit-scale slab of bounded velocity, the weak vorticity of a suitable
solution vanishes as soon as it vanishes near one point of the slab. -/
theorem essLocal_slabVorticityZero
    {J : Set ℝ} {V : ParabolicPoint → Vec3} {DV : ParabolicPoint → Fin 3 → Vec3}
    {pv : ParabolicPoint → ℝ} (ρ M : ℝ) (hM : 0 ≤ M)
    (hsws : IsSuitableWeakSolution Set.univ J 3 V DV pv (0 : ParabolicPoint → Vec3))
    (hJ : Ioo (-2 : ℝ) 2 ⊆ J)
    (hV : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 (ρ + 1)) (Ioo (-2 : ℝ) 2))),
      vec3EuclideanNorm (V z) ≤ M)
    (y₀ : Vec3) (hy₀ : y₀ ∈ vec3Ball 0 ρ) (ε : ℝ) (hε : 0 < ε)
    (hseed : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball y₀ ε) (Ioo (-1 : ℝ) 1))), weakVorticity DV z = 0) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (-1 : ℝ) 1))),
      weakVorticity DV z = 0 := by
  have htriangle : ∀ a b c : Vec3, vec3EuclideanNorm (a - c) ≤
      vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
    intro a b c
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hself : ∀ (c : Vec3) (s : ℝ), 0 < s → c ∈ vec3Ball c s := by
    intro c s hs
    change vec3EuclideanNorm (c - c) < s
    rw [sub_self, vec3EuclideanNorm_zero]
    exact hs
  have hloc : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ vec3Ball (0 : Vec3) ρ, ∃ r : ℝ, 0 < r ∧
      ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet (vec3Ball x r) (Ioo (t - r ^ 2) (t + r ^ 2)))),
        weakVorticity DV z = 0 := by
    intro t ht
    let Z : Set Vec3 := {y | ∃ r : ℝ, 0 < r ∧
      ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet (vec3Ball y r) (Ioo (t - r ^ 2) (t + r ^ 2)))),
        weakVorticity DV z = 0}
    have hZopen : IsOpen Z := by
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨r, hr, hy⟩
      refine ⟨vec3Ball y (r / 2), ?_, isOpen_vec3Ball y _, hself y _ (by positivity)⟩
      intro y' hy'
      refine ⟨r / 2, by positivity, ae_restrict_of_ae_restrict_of_subset ?_ hy⟩
      rintro z ⟨hz1, hz2, hz3⟩
      have hsq : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
      have hr2 : 0 < r ^ 2 := by positivity
      refine ⟨?_, ?_, ?_⟩
      · have htri := htriangle z.1 y' y
        have hz1' : vec3EuclideanNorm (z.1 - y') < r / 2 := hz1
        have hy'' : vec3EuclideanNorm (y' - y) < r / 2 := hy'
        change vec3EuclideanNorm (z.1 - y) < r
        linarith only [htri, hz1', hy'']
      · linarith only [hz2, hsq, hr2]
      · linarith only [hz3, hsq, hr2]
    have hZne : (vec3Ball (0 : Vec3) ρ ∩ Z).Nonempty := by
      let r₀ : ℝ := min ε (min (t + 1) (1 - t))
      have hr₀pos : 0 < r₀ :=
        lt_min hε (lt_min (by linarith only [ht.1]) (by linarith only [ht.2]))
      have hr₀ε : r₀ ≤ ε := min_le_left _ _
      have hr₀a : r₀ ≤ t + 1 := (min_le_right _ _).trans (min_le_left _ _)
      have hr₀b : r₀ ≤ 1 - t := (min_le_right _ _).trans (min_le_right _ _)
      have hr₀sq : r₀ ^ 2 ≤ r₀ := by nlinarith only [hr₀pos, hr₀a, hr₀b]
      refine ⟨y₀, hy₀, r₀, hr₀pos, ae_restrict_of_ae_restrict_of_subset ?_ hseed⟩
      rintro z ⟨hz1, hz2, hz3⟩
      exact ⟨vec3Ball_mono hr₀ε hz1, by linarith only [hz2, hr₀sq, hr₀a],
        by linarith only [hz3, hr₀sq, hr₀b]⟩
    have hZcl : closure Z ∩ vec3Ball (0 : Vec3) ρ ⊆ Z := by
      rintro x ⟨hxcl, hxρ⟩
      obtain ⟨x', hx'ball, hx'Z⟩ :=
        mem_closure_iff.1 hxcl (vec3Ball x (1 / 8)) (isOpen_vec3Ball x _)
          (hself x _ (by norm_num))
      obtain ⟨r, hr, hr0⟩ := hx'Z
      have hcl : closure (parabolicCylinder x (t + 1 / 8) 1) ⊆
          spaceTimeSet Set.univ J := by
        rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
        rintro z ⟨_, hz2, hz3⟩
        exact ⟨mem_univ _, hJ ⟨by linarith only [hz2, ht.1], by linarith only [hz3, ht.2]⟩⟩
      have hsub : parabolicCylinder x (t + 1 / 8) 1 ⊆
          spaceTimeSet (vec3Ball 0 (ρ + 1)) (Ioo (-2 : ℝ) 2) := by
        rintro z ⟨hz1, hz2, hz3⟩
        refine ⟨?_, by linarith only [hz2, ht.1], by linarith only [hz3, ht.2]⟩
        have htri := htriangle z.1 x 0
        have hz1' : vec3EuclideanNorm (z.1 - x) < 1 := hz1
        have hx' : vec3EuclideanNorm (x - 0) < ρ := hxρ
        change vec3EuclideanNorm (z.1 - 0) < ρ + 1
        linarith only [htri, hz1', hx']
      exact essLocal_vorticityZero_propagate M hM hsws x t hcl
        (ae_restrict_of_ae_restrict_of_subset hsub hV) x' hx'ball r hr hr0
    have hpre : IsPreconnected (vec3Ball (0 : Vec3) ρ) :=
      (essLocal_convex_vec3Ball 0 ρ).isPreconnected
    intro x hx
    exact hpre.subset_of_closure_inter_subset hZopen hZne hZcl hx
  refine essLocal_ae_restrict_of_local
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball 0 ρ) isOpen_Ioo).measurableSet ?_
  rintro z ⟨hz1, hz2⟩
  obtain ⟨r, hr, hae⟩ := hloc z.2 hz2 z.1 hz1
  have hr2 : 0 < r ^ 2 := by positivity
  refine ⟨spaceTimeSet (vec3Ball z.1 r) (Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)),
    isOpen_spaceTimeSet _ _ (isOpen_vec3Ball z.1 r) isOpen_Ioo,
    ⟨hself z.1 r hr, by linarith only [hr2], by linarith only [hr2]⟩, hae⟩

end ESS
