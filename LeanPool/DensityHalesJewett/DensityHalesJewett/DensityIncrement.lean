/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.StructuredCorrelation
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The density-increment dichotomy

Tiling a structured insensitive intersection by subspaces and averaging over the tiles turns
structured correlation into a density increment on a subspace.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

variable {N : ℕ}

/-- Relative density in a composite subspace is relative density in the inner subspace of the
outer pullback. -/
lemma Subspace.relativeDensity_compose {α η ζ ι : Type*}
    [Fintype (η → α)] [Fintype (ζ → α)] [DecidableEq (η → α)]
    [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    (relativeDensity (compose V W) A : ℝ) =
      (relativeDensity W (pullback V A) : ℝ) := by
  simp only [relativeDensity, pullback, parameterPreimage, mem_filter, mem_univ, true_and,
    compose_apply]

/-- If `P` has density at least `δ + γ` relative to `C`, of density at least `γ`, then it has
density at least `δ + γ / 2` relative to `C` minus a set of density at most `γ ^ 2 / 2`. -/
lemma add_div_two_mul_dens_sdiff_le {X : Type*} [Fintype X] [DecidableEq X] {P C U : Finset X}
    {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hC : γ ≤ (C.dens : ℝ))
    (hPC : (δ + γ) * (C.dens : ℝ) ≤ ((P ∩ C).dens : ℝ)) (hU : (U.dens : ℝ) ≤ γ ^ 2 / 2) :
    (δ + γ / 2) * ((C \ U).dens : ℝ) ≤ ((P ∩ (C \ U)).dens : ℝ) := by
  have hP : ((P ∩ C).dens : ℝ) ≤ ((P ∩ (C \ U)).dens : ℝ) + (U.dens : ℝ) :=
    mod_cast (dens_le_dens (t := P ∩ (C \ U) ∪ U) fun x ↦ by simp; tauto).trans
      (dens_union_le _ _)
  have hCU : ((C \ U).dens : ℝ) ≤ (C.dens : ℝ) := mod_cast dens_le_dens sdiff_subset
  nlinarith [mul_le_mul_of_nonneg_left hCU (by positivity : 0 ≤ δ + γ / 2),
    mul_le_mul_of_nonneg_left hC hγ]

/-- A structured correlation inside `V` gives a `d`-dimensional subspace on which `A` has relative
density at least `δ + γ / 2`: tile the insensitive intersection by `d`-subspaces with tolerance
`β ≤ γ ^ 2 / (4 * k)`, keep half of the correlation gain on the covered part, average over the
tiles and compose the chosen tile with `V`. -/
lemma exists_density_increment_subspace_of_structured_correlation {k d m n : ℕ} {F : ℝ → ℕ}
    (hk : 2 ≤ k) (hF : IsDHJBound k F) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {β : ℝ} (hβ₀ : 0 < β) (hβ : β ≤ Parameters.γ k N δ ^ 2 / (4 * (k : ℝ)))
    (hm_tiling : IsInsensitive.intersectionTilingBound k F k d β ≤ m)
    {A : Finset (Fin n → Fin (k + 1))}
    {V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)}
    {D : Fin k → Finset (Fin m → Fin (k + 1))}
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k N δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k N δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      δ + Parameters.γ k N δ / 2 ≤ (Subspace.relativeDensity W A : ℝ) := by
  classical
  obtain ⟨𝒱, h𝒱, hU⟩ := IsInsensitive.exists_disjoint_subspaces_iInter hF (by omega) le_rfl hd
    hβ₀ hm_tiling (by simpa using hD)
  have hγ₀ := Parameters.γ_pos hk N hδ₀
  replace hU : ((IsInsensitive.uncovered (IsInsensitive.intersection D) 𝒱).dens : ℝ) ≤
      Parameters.γ k N δ ^ 2 / 2 := by
    linarith [(le_div_iff₀ (by exact_mod_cast (by omega : 0 < 4 * k))).1 hβ]
  have hne : (IsInsensitive.intersection D \
      IsInsensitive.uncovered (IsInsensitive.intersection D) 𝒱).Nonempty :=
    sdiff_nonempty.2 fun hsub ↦ (dens_le_dens hsub).not_gt <| mod_cast hU.trans_lt <|
      (by nlinarith [Parameters.γ_le_three_mul_η k N δ, Parameters.η_le_δ_div_six k N δ] :
        Parameters.γ k N δ ^ 2 / 2 < Parameters.γ k N δ).trans_le hDdense
  obtain ⟨W, -, hW⟩ := h𝒱.exists_le_relativeDensity (A := pullback V A) hne
    (add_div_two_mul_dens_sdiff_le hδ₀.le hγ₀.le hDdense hcorrelation hU)
  exact ⟨Subspace.compose V W, by rwa [Subspace.relativeDensity_compose]⟩

/-- The dimension of the parameter cube on which one density increment towards a `d`-dimensional
subspace is carried out: large enough for the insensitive-intersection construction and for
tiling that intersection by `d`-subspaces. -/
noncomputable def workingDimension (k : ℕ) (F : ℝ → ℕ) (d : ℕ) (δ : ℝ) : ℕ :=
  max (max 1 ⌈(k : ℝ) / Parameters.η k (F (δ / 4)) δ⌉₊)
    (IsInsensitive.intersectionTilingBound k F k d
      (Parameters.γ k (F (δ / 4)) δ ^ 2 / (4 * (k : ℝ))))

/-- An ambient dimension in which a line-free family of density at least `δ` over `k + 1` letters
has a density increment on a `d`-dimensional subspace, given a bound `F` for density Hales--Jewett
over `k` letters. -/
noncomputable def incrementBound (k : ℕ) (F : ℝ → ℕ) (d : ℕ) (δ : ℝ) : ℕ :=
  manyLinesBound k (F (δ / 4)) (workingDimension k F d δ) δ

/-- The density increment in a working dimension `m` and with density Hales--Jewett over `k`
letters applied in dimension `N + 1`. The family may have any density `ρ ≥ δ`, while the
dimensions and the increment are those of the density `δ`. -/
lemma density_increment_of_le {k d m n : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ} (hF : IsDHJBound k F)
    (hd : 1 ≤ d) {δ ρ : ℝ} (hδ₀ : 0 < δ) (hδρ : δ ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hN : IsDHJDimension k (δ / 4) (N + 1)) (hm : 1 ≤ m)
    (hm_large : ⌈(k : ℝ) / Parameters.η k N δ⌉₊ ≤ m)
    (hm_tiling : IsInsensitive.intersectionTilingBound k F k d
      (Parameters.γ k N δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (hn : manyLinesBound k N m δ ≤ n)
    {A : Finset (Fin n → Fin (k + 1))} (hA : ρ ≤ (A.dens : ℝ)) (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      ρ + Parameters.γ k N δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  have hρ₀ : 0 < ρ := hδ₀.trans_le hδρ
  have hη := Parameters.η_mono k N hδ₀ hδρ
  have hγ := Parameters.γ_mono k N hδ₀ hδρ
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Combinatorics.Line (Fin k) (Fin m)) :=
    ⟨Combinatorics.Line.diagonal (Fin k) (Fin m)⟩
  obtain ⟨V, D, hD, hDdense, hcorrelation⟩ :=
    exists_structured_correlation hk hm (hN.mono (by linarith)) hρ₀ hρ₁
      ((div_add_one_pow_le (by omega) (Parameters.η_pos k N hδ₀) hm_large).trans hη)
      ((Subspace.variableCutFibersBound_mono (by omega) le_rfl
        (by positivity [Parameters.η_pos k N hδ₀])
        (by gcongr; positivity [Parameters.η_pos k N hδ₀])).trans hn) hA hfree
  obtain ⟨W, hW⟩ :=
    exists_density_increment_subspace_of_structured_correlation hk hF hd hρ₀ hρ₁
      (by positivity [Parameters.γ_pos hk N hδ₀, (by omega : 0 < k)])
      (by gcongr; positivity [Parameters.γ_pos hk N hδ₀]) hm_tiling hD hDdense hcorrelation
  exact ⟨W, by linarith⟩

/-- A word family of density at least `ρ ≥ δ` contains a line or has density at least `ρ + γ / 2`
on a `d`-dimensional subspace, in every dimension `n ≥ incrementBound k F d δ`. -/
lemma density_increment {k : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ} (hF : IsDHJBound k F)
    {d : ℕ} (hd : 1 ≤ d) {δ ρ : ℝ} (hδ₀ : 0 < δ) (hδρ : δ ≤ ρ) (hρ₁ : ρ ≤ 1)
    {n : ℕ} (hn : incrementBound k F d δ ≤ n)
    {A : Finset (Fin n → Fin (k + 1))} (hA : ρ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        ρ + Parameters.γ k (F (δ / 4)) δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  by_cases hfree : IsLineFree A
  · exact Or.inr <|
      density_increment_of_le hk hF hd hδ₀ hδρ hρ₁
        (hF (δ / 4) (by linarith) _ (Nat.le_succ _))
        ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) hn hA hfree
  · exact Or.inl (by simpa [IsLineFree] using hfree)

end DensityHalesJewett
