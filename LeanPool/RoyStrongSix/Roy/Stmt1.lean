/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.Roy.Realize
public import LeanPool.RoyStrongSix.Roy.Subquot
public import LeanPool.RoyStrongSix.Roy.Transport

/-!
# Theorem 1 ⇒ Statement 1 (Roy's Theorem 1bis) for the subquotient system

For an ambient `(E, Y, W, V)` with `Y ⊆ Qbar^{d₀} × 𝓛^{d₁}` and `W` rational over `Qbar`,
Waldschmidt's
Theorem 1 (stated in coordinates) implies Roy's Statement 1 for every object `S ≤ T`: realize
`T/S` in coordinates, apply Theorem 1, and pull the resulting map back to a cokernel.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy

/-- The `F`-points of a `ℂ`-subspace. -/
def ptsOf (F : Type*) [Field F] [Algebra F ℂ] {ι : Type*} (U : Submodule ℂ (ι → ℂ)) :
    Submodule F (ι → ℂ) := U.restrictScalars F ⊓ Fpts F ι

theorem span_ptsOf {F : Type*} [Field F] [Algebra F ℂ] {ι : Type*} {U : Submodule ℂ (ι → ℂ)}
    (h : IsRat F U) : U = span ℂ ((ptsOf F U : Submodule F (ι → ℂ)) : Set (ι → ℂ)) := by
  obtain ⟨A, hA, rfl⟩ := h
  apply le_antisymm
  · exact span_mono (fun x hx => ⟨subset_span hx, hA hx⟩)
  · rw [span_le]; intro x hx; exact hx.1

theorem ptsOf_mono {F : Type*} [Field F] [Algebra F ℂ] {ι : Type*} {U U' : Submodule ℂ (ι → ℂ)}
    (h : U ≤ U') : ptsOf F U ≤ ptsOf F U' := fun _ hx => ⟨h hx.1, hx.2⟩

/-- Realization of one factor: from `S ≤ T` rational, a map `ψ` with the four properties. -/
theorem realize_factor {F : Type*} [Field F] [Algebra F ℂ] {n : ℕ}
    {S T : Submodule ℂ (Fin n → ℂ)} (hS : IsRat F S) (hT : IsRat F T) (hST : S ≤ T) :
    ∃ (k : ℕ) (ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)),
      PresF F ψ ∧ (ptsOf F T).map (ψ.restrictScalars F) = Fpts F (Fin k) ∧
      LinearMap.ker ψ ⊓ T = S ∧ T.map ψ = ⊤ := by
  obtain ⟨k, ψ, hP, hmap, hker, -⟩ := realize (ptsOf F S) (ptsOf F T) (ptsOf_mono hST) inf_le_right
  refine ⟨k, ψ, hP, hmap, ?_, ?_⟩
  · rw [span_ptsOf hT, span_ptsOf hS]
    convert hker using 2
  · conv_lhs => rw [span_ptsOf hT]
    rw [Submodule.map_span, eq_top_iff, ← span_Fpts_eq_top (F := F) (ι := Fin k), ← hmap]
    apply span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- A `ℂ`-linear map on `ℂⁿ` vanishing on the standard basis is zero. -/
theorem linmap_eq_zero_of_single {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : (Fin n → ℂ) →ₗ[ℂ] V) (h : ∀ i, L (Pi.single i 1) = 0) : L = 0 :=
  (Pi.basisFun ℂ (Fin n)).ext fun i => by rw [Pi.basisFun_apply, h, LinearMap.zero_apply]

/-- `μ` commutes with block maps. -/
theorem μ_block {d0 d1 k0 k1 : ℕ} (ψ : E d0 d1 →ₗ[ℂ] E k0 k1) (ψ1 : (Fin d1 → ℂ) →ₗ[ℂ] (Fin k1 → ℂ))
    (h0 : ∀ v, (ψ (0, v)).1 = 0) (h1 : ∀ x, (ψ x).2 = ψ1 x.2) (q : Fin d1 → ℂ) :
    ψ (μ d0 d1 q) = μ k0 k1 (ψ1 q) := by
  rw [μ_apply, μ_apply]
  ext
  · rw [h0]
  · rw [h1, map_smul]

/-- The image of `Ω' ⊆ ℂ^{k₀} × ℂ^{k₁}` under a surjective block map preserving rational points
is `Ω''`. -/
theorem map_Omega_of_block {k0 k1 d0 d1 : ℕ} (s : E k0 k1 →ₗ[ℂ] E d0 d1)
    (s1 : (Fin k1 → ℂ) →ₗ[ℂ] (Fin d1 → ℂ)) (h0 : ∀ v, (s (0, v)).1 = 0) (h1 : ∀ x, (s x).2 = s1 x.2)
    (hP : PresF ℚ s1) (hsurj : Function.Surjective s1) :
    (Omega k0 k1).map (s.restrictScalars ℚ) = Omega d0 d1 := by
  rw [Omega_eq_map, Omega_eq_map, ← map_Fpts_eq_of_surjective s1 hP hsurj, ← Submodule.map_comp,
    ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun q => μ_block s s1 h0 h1 q

end StrongSix.Roy

end

end LeanPool
