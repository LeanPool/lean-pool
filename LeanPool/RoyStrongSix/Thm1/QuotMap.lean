/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import LeanPool.RoyStrongSix.Roy.BaseChange
public import LeanPool.RoyStrongSix.Thm1.Quot

/-!
# Quotient maps with `F`-rational matrices

For a subfield `F ⊂ ℂ` (here `ℚ` or `Qbar`) and an `F`-subspace `h ⊂ F^m`, `qC h : ℂ^m → ℂ^{m − dim
h}`
has `F` entries, is surjective, and has kernel `span_ℂ h`. In particular
`dim_ℂ ker = dim_F h` (`finrank_ker_qC`).
-/

@[expose] public section

namespace LeanPool

open Module Submodule Matrix
open StrongSix.Roy

namespace StrongSix.Thm1

variable {F : Type*} [Field F] [Algebra F ℂ] {m : ℕ}

/-- The inclusion `F^m → ℂ^m`. -/
noncomputable def inclF (F : Type*) [Field F] [Algebra F ℂ] (m : ℕ) : (Fin m → F) →ₗ[F] (Fin m →
  ℂ) :=
  LinearMap.compLeft (Algebra.linearMap F ℂ) (Fin m)

theorem inclF_apply (x : Fin m → F) (i : Fin m) : inclF F m x i = algebraMap F ℂ (x i) := rfl

theorem inclF_injective : Function.Injective (inclF F m) := fun x y h => by
  funext i
  exact (algebraMap F ℂ).injective (congrFun h i)

theorem inclF_mem_Fpts (x : Fin m → F) : inclF F m x ∈ Fpts F (Fin m) := fun i => ⟨x i, rfl⟩

theorem exists_inclF {x : Fin m → ℂ} (hx : x ∈ Fpts F (Fin m)) : ∃ y, inclF F m y = x := by
  choose y hy using hx
  exact ⟨y, funext hy⟩

variable (h : Submodule F (Fin m → F))

/-- A surjection `F^m → F^{m − dim h}` with kernel `h`. -/
noncomputable def qK : (Fin m → F) →ₗ[F] (Fin (m - finrank F h) → F) :=
  (LinearEquiv.ofFinrankEq ((Fin m → F) ⧸ h) (Fin (m - finrank F h) → F)
    (by rw [Submodule.finrank_quotient, finrank_fin_fun, finrank_fin_fun])).toLinearMap ∘ₗ h.mkQ

omit [Algebra F ℂ] in
theorem ker_qK : LinearMap.ker (qK h) = h := by
  rw [qK, LinearEquiv.ker_comp, Submodule.ker_mkQ]

omit [Algebra F ℂ] in
theorem qK_surjective : Function.Surjective (qK h) :=
  (LinearEquiv.surjective _).comp (Submodule.mkQ_surjective h)

/-- `ℂ^m → ℂ^{m − dim h}` with `F` entries. -/
noncomputable def qC : (Fin m → ℂ) →ₗ[ℂ] (Fin (m - finrank F h) → ℂ) :=
  ((LinearMap.toMatrix' (qK h)).map (algebraMap F ℂ)).mulVecLin

theorem qC_inclF (x : Fin m → F) : qC h (inclF F m x) = inclF F _ (qK h x) := by
  funext k
  rw [inclF_apply, qC, Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec (qK h)]
  exact (RingHom.map_mulVec (algebraMap F ℂ) (LinearMap.toMatrix' (qK h)) x k).symm

theorem qC_presF : PresF F (qC h) := fun x hx => by
  obtain ⟨y, rfl⟩ := exists_inclF hx
  rw [qC_inclF]
  exact inclF_mem_Fpts _

theorem qC_surjective : Function.Surjective (qC h) := by
  apply mulVecLin_surjective
  have hrow : (fun k => (LinearMap.toMatrix' (qK h)).map (algebraMap F ℂ) k) =
      fun k => inclF F m (LinearMap.toMatrix' (qK h) k) := rfl
  rw [hrow]
  refine linearIndependent_of_Fpts (F := F) (fun k => inclF_mem_Fpts _) ?_
  refine LinearIndependent.map' (v := fun k => LinearMap.toMatrix' (qK h) k) ?_ (inclF F m)
    (LinearMap.ker_eq_bot.mpr inclF_injective)
  rw [Fintype.linearIndependent_iff]
  intro c hc k0
  obtain ⟨x, hx⟩ := qK_surjective h (Pi.single k0 1)
  have h1 : c ⬝ᵥ (LinearMap.toMatrix' (qK h) *ᵥ x) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : c ᵥ* LinearMap.toMatrix' (qK h) = 0 := by
      funext j
      have := congrFun hc j
      simpa [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm] using this
    rw [this, zero_dotProduct]
  rw [LinearMap.toMatrix'_mulVec, hx, dotProduct_single, mul_one] at h1
  exact h1

/-- The kernel of `qC h` is `span_ℂ h`. -/
theorem ker_qC : LinearMap.ker (qC h) = span ℂ ((h.map (inclF F m) : Submodule F _) : Set (Fin m
  → ℂ)) := by
  apply le_antisymm
  · obtain ⟨A, hA, hker⟩ := isRat_ker (F := F) (qC h) (qC_presF h)
    rw [hker]
    apply span_mono
    intro x hx
    obtain ⟨y, rfl⟩ := exists_inclF (hA hx)
    have hx' : inclF F m y ∈ LinearMap.ker (qC h) := by rw [hker]; exact subset_span hx
    rw [LinearMap.mem_ker, qC_inclF] at hx'
    have hy : qK h y = 0 := inclF_injective (by rw [hx', map_zero])
    exact ⟨y, by rw [← ker_qK h]; exact hy, rfl⟩
  · rw [span_le]
    rintro _ ⟨y, hy, rfl⟩
    change qC h (inclF F m y) = 0
    rw [qC_inclF, show qK h y = 0 by rw [← LinearMap.mem_ker, ker_qK]; exact hy, map_zero]

theorem finrank_ker_qC : finrank ℂ (LinearMap.ker (qC h)) = finrank F h := by
  rw [ker_qC, finrank_span_of_le_Fpts _ (by rintro _ ⟨y, -, rfl⟩; exact inclF_mem_Fpts y)]
  exact ((Submodule.equivMapOfInjective _ inclF_injective h).finrank_eq).symm

end StrongSix.Thm1

end LeanPool
