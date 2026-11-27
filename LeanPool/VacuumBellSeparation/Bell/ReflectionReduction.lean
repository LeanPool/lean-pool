/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Reflections
public import LeanPool.VacuumBellSeparation.Bell.StateBound

/-!
# Reduction of the CHSH bound from reflections to self-adjoint contractions

The first step of the proof of Theorem 3.1 of the manuscript: "the CHSH expression is
separately affine in its four observables", so a bound on reflection quartets extends to
the norm-closed convex hull of the reflections in each slot.

`chsh_bound_of_reflections` takes the approximation property
`saContractions M ⊆ closure (convexHull ℝ (reflections M))` as an explicit hypothesis; that
property (the spectral resolution of a self-adjoint contraction inside a von Neumann
algebra) is proved separately.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A state is norm continuous. -/
theorem State.continuous (ω : State H) : Continuous (fun T : H →L[ℂ] H => ω T) :=
  AddMonoidHomClass.continuous_of_bound ω.toLinearMap 2 (fun T => ω.norm_apply_le T)

/-- Real-linear combinations pass through a state. -/
theorem State.map_real_combo (ω : State H) (a b : ℝ) (S T : H →L[ℂ] H) :
    ω (a • S + b • T) = (a : ℂ) * ω S + (b : ℂ) * ω T := by
  have ha : a • S = (a : ℂ) • S := (Complex.coe_smul a S).symm
  have hb : b • T = (b : ℂ) • T := (Complex.coe_smul b T).symm
  rw [ha, hb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- An affine combination distributes over a common summand. -/
theorem affine_aux {V : Type*} [AddCommGroup V] [Module ℝ V] (P Q D : V) {a b : ℝ}
    (hab : a + b = 1) : a • P + b • Q + D = a • (P + D) + b • (Q + D) := by
  have hD : a • D + b • D = D := by rw [← add_smul, hab, one_smul]
  have h : a • (P + D) + b • (Q + D) = a • P + b • Q + (a • D + b • D) := by
    rw [smul_add, smul_add]
    abel
  rw [h, hD]

omit [CompleteSpace H] in
/-- The CHSH operator is affine in its first slot. -/
theorem chshOp_affine_fst (X Y A₁ B₀ B₁ : H →L[ℂ] H) {a b : ℝ} (hab : a + b = 1) :
    chshOp (a • X + b • Y) A₁ B₀ B₁ = a • chshOp X A₁ B₀ B₁ + b • chshOp Y A₁ B₀ B₁ := by
  have h : chshOp (a • X + b • Y) A₁ B₀ B₁
      = a • (X * (B₀ + B₁)) + b • (Y * (B₀ + B₁)) + A₁ * (B₀ - B₁) := by
    unfold chshOp
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hX : chshOp X A₁ B₀ B₁ = X * (B₀ + B₁) + A₁ * (B₀ - B₁) := rfl
  have hY : chshOp Y A₁ B₀ B₁ = Y * (B₀ + B₁) + A₁ * (B₀ - B₁) := rfl
  rw [h, hX, hY]
  exact affine_aux _ _ _ hab

omit [CompleteSpace H] in
/-- The CHSH operator is affine in its second slot. -/
theorem chshOp_affine_snd (A₀ X Y B₀ B₁ : H →L[ℂ] H) {a b : ℝ} (hab : a + b = 1) :
    chshOp A₀ (a • X + b • Y) B₀ B₁ = a • chshOp A₀ X B₀ B₁ + b • chshOp A₀ Y B₀ B₁ := by
  have h : chshOp A₀ (a • X + b • Y) B₀ B₁
      = a • (X * (B₀ - B₁)) + b • (Y * (B₀ - B₁)) + A₀ * (B₀ + B₁) := by
    unfold chshOp
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, add_comm]
  have hX : chshOp A₀ X B₀ B₁ = X * (B₀ - B₁) + A₀ * (B₀ + B₁) := by
    unfold chshOp
    exact add_comm _ _
  have hY : chshOp A₀ Y B₀ B₁ = Y * (B₀ - B₁) + A₀ * (B₀ + B₁) := by
    unfold chshOp
    exact add_comm _ _
  rw [h, hX, hY]
  exact affine_aux _ _ _ hab

omit [CompleteSpace H] in
/-- The CHSH operator is affine in its third slot. -/
theorem chshOp_affine_thd (A₀ A₁ X Y B₁ : H →L[ℂ] H) {a b : ℝ} (hab : a + b = 1) :
    chshOp A₀ A₁ (a • X + b • Y) B₁ = a • chshOp A₀ A₁ X B₁ + b • chshOp A₀ A₁ Y B₁ := by
  have h : chshOp A₀ A₁ (a • X + b • Y) B₁
      = a • (A₀ * X + A₁ * X) + b • (A₀ * Y + A₁ * Y) + (A₀ * B₁ - A₁ * B₁) := by
    unfold chshOp
    simp only [mul_add, mul_sub, mul_smul_comm, smul_add]
    abel
  have hX : chshOp A₀ A₁ X B₁ = (A₀ * X + A₁ * X) + (A₀ * B₁ - A₁ * B₁) := by
    unfold chshOp
    rw [mul_add, mul_sub]
    abel
  have hY : chshOp A₀ A₁ Y B₁ = (A₀ * Y + A₁ * Y) + (A₀ * B₁ - A₁ * B₁) := by
    unfold chshOp
    rw [mul_add, mul_sub]
    abel
  rw [h, hX, hY]
  exact affine_aux _ _ _ hab

omit [CompleteSpace H] in
/-- The CHSH operator is affine in its fourth slot. -/
theorem chshOp_affine_fth (A₀ A₁ B₀ X Y : H →L[ℂ] H) {a b : ℝ} (hab : a + b = 1) :
    chshOp A₀ A₁ B₀ (a • X + b • Y) = a • chshOp A₀ A₁ B₀ X + b • chshOp A₀ A₁ B₀ Y := by
  have h : chshOp A₀ A₁ B₀ (a • X + b • Y)
      = a • (A₀ * X - A₁ * X) + b • (A₀ * Y - A₁ * Y) + (A₀ * B₀ + A₁ * B₀) := by
    unfold chshOp
    simp only [mul_add, mul_sub, mul_smul_comm, smul_sub]
    abel
  have hX : chshOp A₀ A₁ B₀ X = (A₀ * X - A₁ * X) + (A₀ * B₀ + A₁ * B₀) := by
    unfold chshOp
    rw [mul_add, mul_sub]
    abel
  have hY : chshOp A₀ A₁ B₀ Y = (A₀ * Y - A₁ * Y) + (A₀ * B₀ + A₁ * B₀) := by
    unfold chshOp
    rw [mul_add, mul_sub]
    abel
  rw [h, hX, hY]
  exact affine_aux _ _ _ hab

omit [CompleteSpace H] in
/-- A norm bound for a continuous, real-affine, complex-valued function on a set extends to
the closure of the convex hull of that set. -/
theorem norm_le_on_closure_convexHull {g : (H →L[ℂ] H) → ℂ} (hcont : Continuous g)
    (haff : ∀ (X Y : H →L[ℂ] H) (a b : ℝ), a + b = 1 →
      g (a • X + b • Y) = (a : ℂ) * g X + (b : ℂ) * g Y)
    {s : Set (H →L[ℂ] H)} {c : ℝ} (hs : ∀ X ∈ s, ‖g X‖ ≤ c) :
    ∀ X ∈ closure (convexHull ℝ s), ‖g X‖ ≤ c := by
  have hconv : Convex ℝ {X : H →L[ℂ] H | ‖g X‖ ≤ c} := by
    intro X hX Y hY a b ha hb hab
    have hX' : ‖g X‖ ≤ c := hX
    have hY' : ‖g Y‖ ≤ c := hY
    change ‖g (a • X + b • Y)‖ ≤ c
    rw [haff X Y a b hab]
    calc ‖(a : ℂ) * g X + (b : ℂ) * g Y‖
        ≤ ‖(a : ℂ) * g X‖ + ‖(b : ℂ) * g Y‖ := norm_add_le _ _
      _ = a * ‖g X‖ + b * ‖g Y‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * c + b * c :=
          add_le_add (mul_le_mul_of_nonneg_left hX' ha) (mul_le_mul_of_nonneg_left hY' hb)
      _ = c := by rw [← add_mul, hab, one_mul]
  have hclosed : IsClosed {X : H →L[ℂ] H | ‖g X‖ ≤ c} :=
    isClosed_le (continuous_norm.comp hcont) continuous_const
  have hsub : s ⊆ {X : H →L[ℂ] H | ‖g X‖ ≤ c} := fun X hX => hs X hX
  exact fun X hX => closure_minimal (convexHull_min hsub hconv) hclosed hX

/-- If every self-adjoint contraction of `𝔄` and of `𝔅` is a norm limit of convex
combinations of reflections of the same algebra, then a bound on the CHSH expectations of
reflection quartets extends to all quartets of self-adjoint contractions. -/
theorem chsh_bound_of_reflections
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} {c : ℝ}
    (hA : saContractions 𝔄 ⊆ closure (convexHull ℝ (reflections 𝔄)))
    (hB : saContractions 𝔅 ⊆ closure (convexHull ℝ (reflections 𝔅)))
    (h : ∀ A₀ ∈ reflections 𝔄, ∀ A₁ ∈ reflections 𝔄, ∀ B₀ ∈ reflections 𝔅,
      ∀ B₁ ∈ reflections 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ c) :
    ∀ A₀ ∈ saContractions 𝔄, ∀ A₁ ∈ saContractions 𝔄, ∀ B₀ ∈ saContractions 𝔅,
      ∀ B₁ ∈ saContractions 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ c := by
  have h1 : ∀ A₀ ∈ saContractions 𝔄, ∀ A₁ ∈ reflections 𝔄, ∀ B₀ ∈ reflections 𝔅,
      ∀ B₁ ∈ reflections 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ c := by
    intro A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
    have hcont : Continuous (fun X : H →L[ℂ] H => ω (chshOp X A₁ B₀ B₁)) := by
      have hc : Continuous (fun X : H →L[ℂ] H => chshOp X A₁ B₀ B₁) := by
        unfold chshOp
        fun_prop
      exact ω.continuous.comp hc
    exact norm_le_on_closure_convexHull (g := fun X => ω (chshOp X A₁ B₀ B₁)) hcont
      (fun X Y a b hab => by
        show ω (chshOp (a • X + b • Y) A₁ B₀ B₁) = _
        rw [chshOp_affine_fst X Y A₁ B₀ B₁ hab, ω.map_real_combo])
      (fun X hX => h X hX A₁ hA₁ B₀ hB₀ B₁ hB₁) A₀ (hA hA₀)
  have h2 : ∀ A₀ ∈ saContractions 𝔄, ∀ A₁ ∈ saContractions 𝔄, ∀ B₀ ∈ reflections 𝔅,
      ∀ B₁ ∈ reflections 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ c := by
    intro A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
    have hcont : Continuous (fun X : H →L[ℂ] H => ω (chshOp A₀ X B₀ B₁)) := by
      have hc : Continuous (fun X : H →L[ℂ] H => chshOp A₀ X B₀ B₁) := by
        unfold chshOp
        fun_prop
      exact ω.continuous.comp hc
    exact norm_le_on_closure_convexHull (g := fun X => ω (chshOp A₀ X B₀ B₁)) hcont
      (fun X Y a b hab => by
        show ω (chshOp A₀ (a • X + b • Y) B₀ B₁) = _
        rw [chshOp_affine_snd A₀ X Y B₀ B₁ hab, ω.map_real_combo])
      (fun X hX => h1 A₀ hA₀ X hX B₀ hB₀ B₁ hB₁) A₁ (hA hA₁)
  have h3 : ∀ A₀ ∈ saContractions 𝔄, ∀ A₁ ∈ saContractions 𝔄, ∀ B₀ ∈ saContractions 𝔅,
      ∀ B₁ ∈ reflections 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ c := by
    intro A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
    have hcont : Continuous (fun X : H →L[ℂ] H => ω (chshOp A₀ A₁ X B₁)) := by
      have hc : Continuous (fun X : H →L[ℂ] H => chshOp A₀ A₁ X B₁) := by
        unfold chshOp
        fun_prop
      exact ω.continuous.comp hc
    exact norm_le_on_closure_convexHull (g := fun X => ω (chshOp A₀ A₁ X B₁)) hcont
      (fun X Y a b hab => by
        show ω (chshOp A₀ A₁ (a • X + b • Y) B₁) = _
        rw [chshOp_affine_thd A₀ A₁ X Y B₁ hab, ω.map_real_combo])
      (fun X hX => h2 A₀ hA₀ A₁ hA₁ X hX B₁ hB₁) B₀ (hB hB₀)
  intro A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
  have hcont : Continuous (fun X : H →L[ℂ] H => ω (chshOp A₀ A₁ B₀ X)) := by
    have hc : Continuous (fun X : H →L[ℂ] H => chshOp A₀ A₁ B₀ X) := by
      unfold chshOp
      fun_prop
    exact ω.continuous.comp hc
  exact norm_le_on_closure_convexHull (g := fun X => ω (chshOp A₀ A₁ B₀ X)) hcont
    (fun X Y a b hab => by
      show ω (chshOp A₀ A₁ B₀ (a • X + b • Y)) = _
      rw [chshOp_affine_fth A₀ A₁ B₀ X Y hab, ω.map_real_combo])
    (fun X hX => h3 A₀ hA₀ A₁ hA₁ B₀ hB₀ X hX) B₁ (hB hB₁)

end VacuumBellSeparation
