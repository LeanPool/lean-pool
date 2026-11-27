/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz
public import LeanPool.VacuumBellSeparation.FreeField.Isotony
public import LeanPool.VacuumBellSeparation.FreeField.Statements
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Corollary 1.2 as a consequence of Theorem 1.1

The manuscript derives Corollary 1.2 (fixed bounded regions) from Theorem 1.1 by Lorentz
covariance, isotony
and the lower bound `β ≥ 1`.  This module formalizes that derivation as the conditional theorem
`corollary_1_2_of_theorem_1_1 : Theorem_1_1 → Corollary_1_2`.  Theorem 1.1 itself is proved in
`FreeField/MainTheorems.lean`.

* `exists_linearIsometryEquiv_apply_eq_norm_smul_e₁`: a reflection of `ℝ³` maps `𝐯` to `|𝐯| 𝐞₁`.
* `boost_arsinh_apply`: the boost of rapidity `arsinh (-t / ℓ)` along `𝐞₁` maps `(t, s 𝐞₁)` to
  `(0, ℓ 𝐞₁)` when `s ≥ 0`, `ℓ > 0`, `ℓ² = s² - t²`.
* `exists_lorentz_to_e₁_axis`: a spacelike vector `a` is mapped to `(0, ℓ 𝐞₁)`,
  `ℓ = √(|𝐚|² - (a⁰)²) > 0`, by a continuous linear automorphism of spacetime (a spatial
  reflection followed by a boost along `𝐞₁`) that preserves the one-particle inner product for
  every `m ≠ 0`.
* `FreeFieldVacuum.localAlgebra_lorentz_image`, `FreeFieldVacuum.bellCorrelation_lorentz_image`:
  for the transported vacuum system `V' = V.lorentz Λ _` (same vacuum vector), `𝔄'(Λ O) = 𝔄(O)`,
  so the vacuum Bell correlation of `(Λ O₁, Λ O₂)` for `V'` equals that of `(O₁, O₂)` for `V`.
* `image_image_add_eq`, `exists_subset_doubleCone_of_isBounded`, `image_add_subset_doubleCone`:
  `Λ (O + c) = Λ O + Λ c`; a bounded region lies in a double cone `D_ρ` about the origin, and its
  translate by `c` in `D_ρ + c`.
* `corollary_1_2_of_theorem_1_1`: Corollary 1.2, assuming Theorem 1.1.

The spatial map is a reflection (an improper orthogonal map of `ℝ³`, or the identity if `𝐚` already
points along `+𝐞₁`).  The model is covariant
under every linear isometry of `ℝ³` (`oneParticleInner_spatialRotation`), so the transported
system is again a vacuum system of the same mass and Theorem 1.1 applies to it; the formal
statement of Corollary 1.2 does not refer to the transformation.
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

/-! ### A Lorentz transformation taking a spacelike vector to the `𝐞₁` axis -/

/-- For every `𝐯 ∈ ℝ³` there is a linear isometry of `ℝ³` taking `𝐯` to `|𝐯| 𝐞₁`: the reflection
in the plane orthogonal to `𝐯 - |𝐯| 𝐞₁` (`Submodule.reflection_sub`). -/
theorem exists_linearIsometryEquiv_apply_eq_norm_smul_e₁ (v : EuclideanSpace ℝ (Fin 3)) :
    ∃ R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3), R v = ‖v‖ • e₁ := by
  have h : ‖v‖ = ‖‖v‖ • e₁‖ := by
    rw [norm_smul, norm_e₁, mul_one, norm_norm]
  exact ⟨_, Submodule.reflection_sub h⟩

/-- The boost of rapidity `arsinh (-t / ℓ)` along `𝐞₁`, where `s ≥ 0`, `ℓ > 0` and
`ℓ² = s² - t²`, maps the spacelike vector `(t, s 𝐞₁)` to the purely spatial vector `(0, ℓ 𝐞₁)`
(`sinh η = -t / ℓ`, `cosh η = s / ℓ`). -/
theorem boost_arsinh_apply {t s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 < ℓ)
    (hℓ2 : ℓ ^ 2 = s ^ 2 - t ^ 2) :
    boost (Real.arsinh (-t / ℓ)) (t, s • e₁) = (0, ℓ • e₁) := by
  have h1 : 1 + (-t / ℓ) ^ 2 = (s / ℓ) ^ 2 := by
    have h3 : (s / ℓ) ^ 2 - (-t / ℓ) ^ 2 = (s ^ 2 - t ^ 2) / ℓ ^ 2 := by ring
    rw [← hℓ2, div_self (pow_ne_zero 2 hℓ.ne')] at h3
    linarith
  have hsinh : Real.sinh (Real.arsinh (-t / ℓ)) = -t / ℓ := Real.sinh_arsinh _
  have hcosh : Real.cosh (Real.arsinh (-t / ℓ)) = s / ℓ := by
    rw [Real.cosh_arsinh, h1, Real.sqrt_sq (div_nonneg hs hℓ.le)]
  have hin : ⟪e₁, s • e₁⟫_ℝ = s := by
    rw [real_inner_smul_right, inner_e₁_self, mul_one]
  rw [boost_apply, boostCLM_apply]
  refine Prod.ext ?_ ?_
  · change Real.cosh (Real.arsinh (-t / ℓ)) * t +
        Real.sinh (Real.arsinh (-t / ℓ)) * ⟪e₁, s • e₁⟫_ℝ = 0
    rw [hin, hsinh, hcosh]
    ring
  · change s • e₁ + (Real.sinh (Real.arsinh (-t / ℓ)) * t +
        (Real.cosh (Real.arsinh (-t / ℓ)) - 1) * ⟪e₁, s • e₁⟫_ℝ) • e₁ = ℓ • e₁
    rw [hin, hsinh, hcosh, ← add_smul]
    congr 1
    calc s + (-t / ℓ * t + (s / ℓ - 1) * s) = (s ^ 2 - t ^ 2) / ℓ := by ring
      _ = ℓ := by rw [← hℓ2, sq, mul_div_assoc, div_self hℓ.ne', mul_one]

/-- `F ∘ (Λ₂ ∘ Λ₁) = (F ∘ Λ₂) ∘ Λ₁` for real test functions. -/
theorem RealTestFunction.compCLE_trans (Λ₁ Λ₂ : Spacetime ≃L[ℝ] Spacetime)
    (F : RealTestFunction) : F.compCLE (Λ₁.trans Λ₂) = (F.compCLE Λ₂).compCLE Λ₁ :=
  Subtype.ext (funext fun _ => rfl)

/-- If `Λ₁` and `Λ₂` preserve the one-particle inner product `⟨κ_m ·, κ_m ·⟩`, so does their
composition `Λ₂ ∘ Λ₁`. -/
theorem oneParticleInner_compCLE_trans {m : ℝ} {Λ₁ Λ₂ : Spacetime ≃L[ℝ] Spacetime}
    (h₁ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ₁) (G.compCLE Λ₁) = oneParticleInner m F G)
    (h₂ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ₂) (G.compCLE Λ₂) = oneParticleInner m F G)
    (F G : RealTestFunction) :
    oneParticleInner m (F.compCLE (Λ₁.trans Λ₂)) (G.compCLE (Λ₁.trans Λ₂)) =
      oneParticleInner m F G := by
  rw [RealTestFunction.compCLE_trans, RealTestFunction.compCLE_trans, h₁, h₂]

/-- **A Lorentz transformation taking a spacelike vector to the positive `𝐞₁` axis.**  For a
spacelike vector `a` (`(a⁰)² < |𝐚|²`) let `ℓ = √(|𝐚|² - (a⁰)²) > 0`.  The continuous linear
automorphism `Λ` of spacetime given by a spatial reflection `R` with `R 𝐚 = |𝐚| 𝐞₁` followed by
the boost of rapidity `arsinh (-a⁰ / ℓ)` along `𝐞₁` satisfies `Λ a = (0, ℓ 𝐞₁)` and preserves
the one-particle inner product for every `m ≠ 0` (that `Λ` also preserves the Minkowski form
belongs to
the construction; the statement records only what the proof of Corollary 1.2 uses). -/
theorem exists_lorentz_to_e₁_axis (a : Spacetime) (ha : a.1 ^ 2 < ‖a.2‖ ^ 2) :
    ∃ (Λ : Spacetime ≃L[ℝ] Spacetime) (ℓ : ℝ), 0 < ℓ ∧ ℓ = Real.sqrt (‖a.2‖ ^ 2 - a.1 ^ 2) ∧
      Λ a = (0, ℓ • e₁) ∧
      ∀ m : ℝ, m ≠ 0 → ∀ F G : RealTestFunction,
        oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G := by
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_apply_eq_norm_smul_e₁ a.2
  have hpos : 0 < ‖a.2‖ ^ 2 - a.1 ^ 2 := sub_pos.2 ha
  refine ⟨(spatialRotation R).trans
      (boost (Real.arsinh (-a.1 / Real.sqrt (‖a.2‖ ^ 2 - a.1 ^ 2)))),
    Real.sqrt (‖a.2‖ ^ 2 - a.1 ^ 2), Real.sqrt_pos.2 hpos, rfl, ?_, fun m hm F G => ?_⟩
  · rw [ContinuousLinearEquiv.trans_apply, spatialRotation_apply, hR]
    exact boost_arsinh_apply (norm_nonneg _) (Real.sqrt_pos.2 hpos) (Real.sq_sqrt hpos.le)
  · exact oneParticleInner_compCLE_trans (oneParticleInner_spatialRotation m R)
      (oneParticleInner_boost hm _) F G

/-! ### Transport of the vacuum Bell correlation -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local algebras of the transported system at transformed regions: for
`V' = V.lorentz Λ _`, `𝔄'(Λ O) = 𝔄(Λ⁻¹ Λ O) = 𝔄(O)`. -/
theorem FreeFieldVacuum.localAlgebra_lorentz_image {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G)
    (O : Set Spacetime) :
    localAlgebra (V.lorentz Λ hΛ) (Λ '' O) = localAlgebra V O := by
  rw [V.localAlgebra_lorentz Λ hΛ, Set.preimage_image_eq O Λ.injective]

/-- **Covariance of the vacuum Bell correlation.**  For the transported system
`V' = V.lorentz Λ _` (same vacuum vector), the vacuum Bell correlation of `𝔄'(Λ O₁)` and
`𝔄'(Λ O₂)` equals that of `𝔄(O₁)` and `𝔄(O₂)`. -/
theorem FreeFieldVacuum.bellCorrelation_lorentz_image {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G)
    (O₁ O₂ : Set Spacetime) :
    bellCorrelation (vectorState (V.lorentz Λ hΛ).vacuum (V.lorentz Λ hΛ).vacuum_norm)
        (localAlgebra (V.lorentz Λ hΛ) (Λ '' O₁)) (localAlgebra (V.lorentz Λ hΛ) (Λ '' O₂)) =
      bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁)
        (localAlgebra V O₂) := by
  change bellCorrelation (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra (V.lorentz Λ hΛ) (Λ '' O₁)) (localAlgebra (V.lorentz Λ hΛ) (Λ '' O₂)) = _
  rw [V.localAlgebra_lorentz_image Λ hΛ O₁, V.localAlgebra_lorentz_image Λ hΛ O₂]

/-! ### Bounded regions, translations and double cones -/

/-- A continuous linear automorphism maps translates to translates: `Λ (O + c) = Λ O + Λ c`. -/
theorem image_image_add_eq (Λ : Spacetime ≃L[ℝ] Spacetime) (O : Set Spacetime)
    (c : Spacetime) : Λ '' ((fun x => x + c) '' O) = (fun x => x + Λ c) '' (Λ '' O) := by
  rw [Set.image_image, Set.image_image]
  simp only [ContinuousLinearEquiv.map_add]

/-- Every bounded region of spacetime lies in a double cone `D_ρ = {x : |x⁰| + |𝐱| < ρ}` about
the origin with `ρ > 0` (for the max norm `‖x‖ = max |x⁰| |𝐱|` of `Spacetime`, `‖x‖ ≤ r` gives
`|x⁰| + |𝐱| ≤ 2r < 3r`). -/
theorem exists_subset_doubleCone_of_isBounded {S : Set Spacetime}
    (hS : Bornology.IsBounded S) : ∃ ρ : ℝ, 0 < ρ ∧ S ⊆ doubleCone 0 ρ := by
  obtain ⟨r, hr, hb⟩ := hS.exists_pos_norm_le
  refine ⟨3 * r, by linarith, fun x hx => ?_⟩
  have h1 : |x.1| ≤ r := by
    rw [← Real.norm_eq_abs]
    exact (norm_fst_le x).trans (hb x hx)
  have h2 : ‖x.2‖ ≤ r := (norm_snd_le x).trans (hb x hx)
  change |x.1 - 0| + ‖x.2 - 0‖ < 3 * r
  simp only [sub_zero]
  linarith

/-- If `S ⊆ D_ρ`, then the translate `S + c` lies in the translated double cone `D_ρ + c`. -/
theorem image_add_subset_doubleCone {S : Set Spacetime} {ρ : ℝ} (hS : S ⊆ doubleCone 0 ρ)
    (c : Spacetime) : (fun x => x + c) '' S ⊆ doubleCone c ρ := by
  rintro _ ⟨x, hx, rfl⟩
  have h : |x.1 - 0| + ‖x.2 - 0‖ < ρ := hS hx
  change |x.1 + c.1 - c.1| + ‖x.2 + c.2 - c.2‖ < ρ
  simp only [add_sub_cancel_right]
  simpa only [sub_zero] using h

/-! ### Corollary 1.2 -/

/-- **Corollary 1.2 from Theorem 1.1** (the manuscript's proof of Corollary 1.2).  Fix `m > 0`,
bounded regions `O₁, O₂` and a spacelike `a`.  A spatial reflection followed by a boost along
`𝐞₁` (`exists_lorentz_to_e₁_axis`) maps `a` to `(0, ℓ 𝐞₁)` with `ℓ > 0`; it transports every
vacuum system `V` to a vacuum system `V'` of the same mass with the same vacuum vector and
`𝔄'(Λ O) = 𝔄(O)`, and maps `O₂ + t a` to `Λ O₂ + (0, tℓ 𝐞₁)`.  The bounded set `Λ O₁ ∪ Λ O₂` lies
in a double cone `D_ρ`, so by isotony the Bell correlation of `𝔄(O₁)` and `𝔄(O₂ + t a)` is at
most `β_m(ρ, tℓ)` of `V'`, which equals `1` by Theorem 1.1 as soon as `C_* ρ ≤ tℓ`, i.e. for
`t ≥ T₀ = C_* ρ / ℓ`; `T₀` depends only on `O₁, O₂, a` (not on `m`, the Hilbert space or `V`).
The lower bound `1` holds for every pair of algebras. -/
theorem corollary_1_2_of_theorem_1_1 (h : Theorem_1_1) : Corollary_1_2 := by
  obtain ⟨C, -, hC⟩ := h
  intro m hm O₁ O₂ hO₁ hO₂ a ha
  obtain ⟨Λ, ℓ, hℓ, -, hΛa, hΛ⟩ := exists_lorentz_to_e₁_axis a ha
  obtain ⟨ρ, hρ, hsub⟩ := exists_subset_doubleCone_of_isBounded
    ((Λ.lipschitzWith.isBounded_image hO₁).union (Λ.lipschitzWith.isBounded_image hO₂))
  refine ⟨C * ρ / ℓ, ?_⟩
  intro t ht H _ _ _ V
  have hΛm := hΛ m hm.ne'
  have hL : C * ρ ≤ t * ℓ := (div_le_iff₀ hℓ).1 ht
  have hc : Λ (t • a) = (0, (t * ℓ) • e₁) := by
    rw [ContinuousLinearEquiv.map_smul, hΛa]
    refine Prod.ext ?_ ?_
    · change t • (0 : ℝ) = 0
      exact smul_zero t
    · change t • ℓ • e₁ = (t * ℓ) • e₁
      exact smul_smul t ℓ e₁
  have h₁ : Λ '' O₁ ⊆ doubleCone 0 ρ := fun x hx => hsub (Or.inl hx)
  have h₂' : Λ '' O₂ ⊆ doubleCone 0 ρ := fun x hx => hsub (Or.inr hx)
  have h₂ : Λ '' ((fun x => x + t • a) '' O₂) ⊆ doubleCone (0, (t * ℓ) • e₁) ρ := by
    rw [image_image_add_eq Λ O₂ (t • a), hc]
    exact image_add_subset_doubleCone h₂' _
  have hle : bellCorrelation
      (vectorState (V.lorentz Λ hΛm).vacuum (V.lorentz Λ hΛm).vacuum_norm)
      (localAlgebra (V.lorentz Λ hΛm) (Λ '' O₁))
      (localAlgebra (V.lorentz Λ hΛm) (Λ '' ((fun x => x + t • a) '' O₂))) ≤
      freeFieldBell (V.lorentz Λ hΛm) ρ (t * ℓ) :=
    bellCorrelation_mono _ (localAlgebra_mono (V.lorentz Λ hΛm) h₁)
      (localAlgebra_mono (V.lorentz Λ hΛm) h₂)
  rw [V.bellCorrelation_lorentz_image Λ hΛm] at hle
  exact le_antisymm (hle.trans_eq (hC m ρ (t * ℓ) hm hρ hL H (V.lorentz Λ hΛm)))
    (one_le_bellCorrelation _ _ _)

end VacuumBellSeparation
