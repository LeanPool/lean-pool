/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.MainTheorems
public import LeanPool.VacuumBellSeparation.FreeField.Corollary
public import LeanPool.VacuumBellSeparation.Bell.StateBound
public import LeanPool.VacuumBellSeparation.Bell.EventConstants

/-!
# Open Quantum Problem 12 for bounded regions: the CHSH inequality at large separation

Open Quantum Problem 12 of the IQOQI Vienna list ("Bell inequalities for long range vacuum
correlations") asks whether some (necessarily small) violation of the CHSH-Bell inequalities by
the vacuum is possible for regions arbitrarily far apart, for a massive scalar free relativistic
Bose field. For two bounded regions moved apart along a fixed spacelike direction or by a spatial
translation, this module states the plain form of the CHSH inequality, `|⟨Ω, (A₀(B₀ + B₁) + A₁(B₀
- B₁)) Ω⟩| ≤ 2` for all self-adjoint contractions
`A₀, A₁` and `B₀, B₁` of the two local algebras, without the supremum and the factor `1/2` of
the Bell correlation `β`.

* `norm_apply_chshOp_le_two_of_bellCorrelation_eq_one`: `β = 1` gives the CHSH inequality for
  every choice of local observables.
* `no_chsh_violation_far_apart`: two bounded regions, the second translated by `t a` along a fixed
  spacelike vector `a`; there is no CHSH violation once `t ≥ T₀` (from `corollary_1_2`).
* `bellCorrelation_eq_one_of_spatial_separation`: two bounded regions, the second translated by a
  spatial vector `𝐱` in any direction; `β = 1` once `|𝐱| ≥ D`, with `D` independent of the
  direction (from `theorem_1_1`, a spatial reflection taking `𝐱` to `|𝐱| 𝐞₁`, and isotony).
* `no_chsh_violation_far_apart_uniform`: the same in the plain CHSH form.
* `bellCorrelation_vacuum_eq_sSup`, `theorem_1_1_explicit`, `corollary_1_2_explicit`: the vacuum
Bell
  correlation written out as a supremum of CHSH values, and Theorem 1.1 and Corollary 1.2 in that
  form
  (the form in which `Challenge.lean` states them).
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

section CHSH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If the Bell correlation of a state for two von Neumann algebras equals its classical value `1`,
then every CHSH expectation `ω(A₀(B₀ + B₁) + A₁(B₀ - B₁))` with self-adjoint contractions
`A₀, A₁ ∈ 𝔄` and `B₀, B₁ ∈ 𝔅` has modulus at most `2`. -/
theorem norm_apply_chshOp_le_two_of_bellCorrelation_eq_one (ω : State H)
    {𝔄 𝔅 : VonNeumannAlgebra H} (h : bellCorrelation ω 𝔄 𝔅 = 1)
    {A₀ A₁ B₀ B₁ : H →L[ℂ] H} (hA₀ : A₀ ∈ saContractions 𝔄) (hA₁ : A₁ ∈ saContractions 𝔄)
    (hB₀ : B₀ ∈ saContractions 𝔅) (hB₁ : B₁ ∈ saContractions 𝔅) :
    ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ 2 := by
  have hmem : (1 / 2 : ℝ) * ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ∈ chshValues ω 𝔄 𝔅 :=
    ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
  have hle := le_csSup (bddAbove_chshValues ω 𝔄 𝔅) hmem
  have hsup : sSup (chshValues ω 𝔄 𝔅) = 1 := h
  rw [hsup] at hle
  linarith

end CHSH

/-- **No CHSH violation for bounded regions far apart along a fixed spacelike direction.**
For every mass `m > 0`, any two bounded regions `O₁, O₂` and any spacelike vector `a`, there is
`T₀` such that for all `t ≥ T₀`, in every vacuum Weyl system of the free field of mass `m`, all
self-adjoint contractions `A₀, A₁ ∈ 𝔄(O₁)` and `B₀, B₁ ∈ 𝔄(O₂ + t a)` satisfy the CHSH inequality
`|⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ - B₁)) Ω⟩| ≤ 2`. -/
theorem no_chsh_violation_far_apart (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂)
    (a : Spacetime) (ha : a.1 ^ 2 < ‖a.2‖ ^ 2) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 := by
  obtain ⟨T₀, hT₀⟩ := corollary_1_2 m hm O₁ O₂ hO₁ hO₂ a ha
  refine ⟨T₀, ?_⟩
  intro t ht H _ _ _ V A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ sA₀ sA₁ sB₀ sB₁ nA₀ nA₁ nB₀ nB₁
  exact norm_apply_chshOp_le_two_of_bellCorrelation_eq_one _ (hT₀ t ht H V)
    ⟨hA₀, sA₀, nA₀⟩ ⟨hA₁, sA₁, nA₁⟩ ⟨hB₀, sB₀, nB₀⟩ ⟨hB₁, sB₁, nB₁⟩

/-- **The Bell correlation of bounded regions at large spatial separation, uniformly over the
direction.** For every mass `m > 0` and any two bounded regions `O₁, O₂` there is `D` such that,
for every spatial vector `𝐱` with `|𝐱| ≥ D` (in any direction), the vacuum Bell correlation of
`𝔄(O₁)` and `𝔄(O₂ + (0, 𝐱))` equals `1`, in every vacuum Weyl system of mass `m`. -/
theorem bellCorrelation_eq_one_of_spatial_separation (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂) :
    ∃ D : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H),
        bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁)
          (localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂)) = 1 := by
  obtain ⟨C, -, hC⟩ := theorem_1_1
  obtain ⟨ρ, hρ, hsub⟩ := exists_subset_doubleCone_of_isBounded (hO₁.union hO₂)
  refine ⟨C * ρ, ?_⟩
  intro x hx H _ _ _ V
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_apply_eq_norm_smul_e₁ x
  obtain ⟨Λ, hΛc, hΛx, hΛ⟩ : ∃ Λ : Spacetime ≃L[ℝ] Spacetime,
      (∀ y : Spacetime, |(Λ y).1| + ‖(Λ y).2‖ = |y.1| + ‖y.2‖) ∧
      Λ ((0 : ℝ), x) = (0, ‖x‖ • e₁) ∧
      ∀ F G : RealTestFunction,
        oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G := by
    refine ⟨spatialRotation R, fun y => ?_, ?_, oneParticleInner_spatialRotation m R⟩
    · simp only [spatialRotation_apply, LinearIsometryEquiv.norm_map]
    · rw [spatialRotation_apply]
      exact Prod.ext rfl hR
  have hcone : ∀ S : Set Spacetime, S ⊆ doubleCone 0 ρ → Λ '' S ⊆ doubleCone 0 ρ := by
    rintro S hS _ ⟨y, hy, rfl⟩
    have h : |y.1 - 0| + ‖y.2 - 0‖ < ρ := hS hy
    change |(Λ y).1 - 0| + ‖(Λ y).2 - 0‖ < ρ
    simp only [sub_zero] at h ⊢
    rw [hΛc y]
    exact h
  have h₁ : Λ '' O₁ ⊆ doubleCone 0 ρ := hcone O₁ fun y hy => hsub (Or.inl hy)
  have h₂' : Λ '' O₂ ⊆ doubleCone 0 ρ := hcone O₂ fun y hy => hsub (Or.inr hy)
  have h₂ : Λ '' ((fun y => y + ((0 : ℝ), x)) '' O₂) ⊆ doubleCone (0, ‖x‖ • e₁) ρ := by
    rw [image_image_add_eq Λ O₂ ((0 : ℝ), x), hΛx]
    exact image_add_subset_doubleCone h₂' _
  have hle : bellCorrelation
      (vectorState (V.lorentz Λ hΛ).vacuum (V.lorentz Λ hΛ).vacuum_norm)
      (localAlgebra (V.lorentz Λ hΛ) (Λ '' O₁))
      (localAlgebra (V.lorentz Λ hΛ) (Λ '' ((fun y => y + ((0 : ℝ), x)) '' O₂))) ≤
      freeFieldBell (V.lorentz Λ hΛ) ρ ‖x‖ :=
    bellCorrelation_mono _ (localAlgebra_mono (V.lorentz Λ hΛ) h₁)
      (localAlgebra_mono (V.lorentz Λ hΛ) h₂)
  rw [V.bellCorrelation_lorentz_image Λ hΛ] at hle
  exact le_antisymm (hle.trans_eq (hC m ρ ‖x‖ hm hρ hx H (V.lorentz Λ hΛ)))
    (one_le_bellCorrelation _ _ _)

/-- **No CHSH violation for bounded regions far apart, uniformly over spatial directions.**
For every mass `m > 0` and any two bounded regions `O₁, O₂` there is `D` such that, for every
spatial vector `𝐱` with `|𝐱| ≥ D` (in any direction), in every vacuum Weyl system of mass `m`,
all self-adjoint contractions `A₀, A₁ ∈ 𝔄(O₁)` and `B₀, B₁ ∈ 𝔄(O₂ + (0, 𝐱))` satisfy the CHSH
inequality `|⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ - B₁)) Ω⟩| ≤ 2`. -/
theorem no_chsh_violation_far_apart_uniform (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂) :
    ∃ D : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        B₁ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 := by
  obtain ⟨D, hD⟩ := bellCorrelation_eq_one_of_spatial_separation m hm O₁ O₂ hO₁ hO₂
  refine ⟨D, ?_⟩
  intro x hx H _ _ _ V A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ sA₀ sA₁ sB₀ sB₁ nA₀ nA₁ nB₀ nB₁
  exact norm_apply_chshOp_le_two_of_bellCorrelation_eq_one _ (hD x hx H V)
    ⟨hA₀, sA₀, nA₀⟩ ⟨hA₁, sA₁, nA₁⟩ ⟨hB₀, sB₀, nB₀⟩ ⟨hB₁, sB₁, nB₁⟩

/-! ### Theorem 1.1 and Corollary 1.2 with the vacuum Bell correlation written out

`Challenge.lean` copies the definitions of `FreeField/Defs.lean` up to `e₁`, so its statements of
Theorem 1.1 and Corollary 1.2 spell out the vacuum Bell correlation as the supremum of the CHSH
values
`½ |⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ - B₁)) Ω⟩|`. The theorems below have exactly those statements. -/

section Explicit

variable {m : ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vacuum Bell correlation of two local algebras, written out: the supremum of
`½ |⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ - B₁)) Ω⟩|` over self-adjoint contractions `A₀, A₁ ∈ 𝔄(O₁)` and
`B₀, B₁ ∈ 𝔄(O₂)`. -/
theorem bellCorrelation_vacuum_eq_sSup (V : FreeFieldVacuum m H) (O₁ O₂ : Set Spacetime) :
    bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁) (localAlgebra V O₂) =
      sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
        A₀ ∈ localAlgebra V O₁ ∧ A₁ ∈ localAlgebra V O₁ ∧
        B₀ ∈ localAlgebra V O₂ ∧ B₁ ∈ localAlgebra V O₂ ∧
        IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
        ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
        v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} := by
  change sSup (chshValues _ _ _) = _
  refine congrArg sSup ?_
  ext v
  constructor
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
    obtain ⟨hA₀, sA₀, nA₀⟩ : A₀ ∈ localAlgebra V O₁ ∧ IsSelfAdjoint A₀ ∧ ‖A₀‖ ≤ 1 := hA₀
    obtain ⟨hA₁, sA₁, nA₁⟩ : A₁ ∈ localAlgebra V O₁ ∧ IsSelfAdjoint A₁ ∧ ‖A₁‖ ≤ 1 := hA₁
    obtain ⟨hB₀, sB₀, nB₀⟩ : B₀ ∈ localAlgebra V O₂ ∧ IsSelfAdjoint B₀ ∧ ‖B₀‖ ≤ 1 := hB₀
    obtain ⟨hB₁, sB₁, nB₁⟩ : B₁ ∈ localAlgebra V O₂ ∧ IsSelfAdjoint B₁ ∧ ‖B₁‖ ≤ 1 := hB₁
    exact ⟨A₀, A₁, B₀, B₁, hA₀, hA₁, hB₀, hB₁, sA₀, sA₁, sB₀, sB₁, nA₀, nA₁, nB₀, nB₁, rfl⟩
  · rintro ⟨A₀, A₁, B₀, B₁, hA₀, hA₁, hB₀, hB₁, sA₀, sA₁, sB₀, sB₁, nA₀, nA₁, nB₀, nB₁, rfl⟩
    exact ⟨A₀, ⟨hA₀, sA₀, nA₀⟩, A₁, ⟨hA₁, sA₁, nA₁⟩, B₀, ⟨hB₀, sB₀, nB₀⟩, B₁, ⟨hB₁, sB₁, nB₁⟩,
      rfl⟩

end Explicit

/-- **Theorem 1.1**, with the vacuum Bell correlation `β_m(R, L)` written out as the supremum of the
CHSH values. -/
theorem theorem_1_1_explicit :
    ∃ Cstar : ℝ, 2 < Cstar ∧
      ∀ m R L : ℝ, 0 < m → 0 < R → Cstar * R ≤ L →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
            A₀ ∈ localAlgebra V (doubleCone 0 R) ∧ A₁ ∈ localAlgebra V (doubleCone 0 R) ∧
            B₀ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            B₁ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
            ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
            v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} = 1 := by
  obtain ⟨C, hC2, hC⟩ := theorem_1_1
  refine ⟨C, hC2, ?_⟩
  intro m R L hm hR hL H _ _ _ V
  exact (bellCorrelation_vacuum_eq_sSup V (doubleCone 0 R) (doubleCone (0, L • e₁) R)).symm.trans
    (hC m R L hm hR hL H V)

/-- **Corollary 1.2**, with the vacuum Bell correlation written out as the supremum of the CHSH
values. -/
theorem corollary_1_2_explicit :
    ∀ m : ℝ, 0 < m → ∀ O₁ O₂ : Set Spacetime, Bornology.IsBounded O₁ → Bornology.IsBounded O₂ →
      ∀ a : Spacetime, a.1 ^ 2 < ‖a.2‖ ^ 2 →
        ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
            (V : FreeFieldVacuum m H),
            sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
              A₀ ∈ localAlgebra V O₁ ∧ A₁ ∈ localAlgebra V O₁ ∧
              B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
              ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
              v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} =
              1 := by
  intro m hm O₁ O₂ hO₁ hO₂ a ha
  obtain ⟨T₀, hT₀⟩ := corollary_1_2 m hm O₁ O₂ hO₁ hO₂ a ha
  refine ⟨T₀, ?_⟩
  intro t ht H _ _ _ V
  exact (bellCorrelation_vacuum_eq_sSup V O₁ ((fun x => x + t • a) '' O₂)).symm.trans
    (hT₀ t ht H V)

end VacuumBellSeparation
