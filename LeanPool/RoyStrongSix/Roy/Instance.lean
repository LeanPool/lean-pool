/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Stmt1Main
public import LeanPool.RoyStrongSix.Roy.Support

/-!
# The strong six exponentials instance of Roy's Theorem 4 (core)

Data: a `ℚ`-basis `ω₁, …, ω_m` (`m ≥ 1`) of a number field inside `ℂ`; vectors `x ∈ ℂ²`,
`y ∈ ℂ³` linearly independent over `Qbar`; and lifts `ℓ_{kj} ∈ Qbar² × 𝓛^{2m}` with
`φ(ℓ_{kj}) = ω_k y_j x`, where `φ(a, (u_{k,i})) = a + ∑_k ω_k u_{k,·}`.

On `E = ℂ² × ℂ^{2m}` take `W = ker φ`, `V = φ⁻¹(ℂ x)` and `Y = ℚ-span of the ℓ_{kj}`. For the
identity object, Roy's Theorem 2bis gives `(2m + dim Y)/2 ≤ 2m`, while `dim Y ≥ 3m`:
a contradiction.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy

variable {m : ℕ} (ω : Fin m → ℂ)

/-- `ψ(u)_i = ∑_k ω_k u_{(k,i)}`. -/
def psiω : (Fin (m * 2) → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i => ∑ k, ω k • LinearMap.proj (finProdFinEquiv (k, i))

/-- `φ(a, u) = a + ψ(u)`. -/
def phiω : E 2 (m * 2) →ₗ[ℂ] (Fin 2 → ℂ) := LinearMap.coprod LinearMap.id (psiω ω)

theorem phiω_apply (p : E 2 (m * 2)) (i : Fin 2) :
    phiω ω p i = p.1 i + ∑ k, ω k * p.2 (finProdFinEquiv (k, i)) := by
  simp [phiω, psiω, LinearMap.coprod_apply, LinearMap.sum_apply]

theorem phiω_surjective : Function.Surjective (phiω ω) := by
  intro z
  refine ⟨(z, 0), ?_⟩
  funext i
  rw [phiω_apply]
  simp

/-- An algebraic vector on the line `ℂ x` is zero. -/
theorem alg_in_line {x : Fin 2 → ℂ} (hx : QbarIndep x) {u : Fin 2 → ℂ}
    (hu : ∀ i, IsAlgebraic ℚ (u i)) (hux : u ∈ span ℂ {x}) : u = 0 := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hux
  have h := hx ![c • x 1 * 1, -(c • x 0)] (by
    intro i; fin_cases i
    · simpa using hu 1
    · simpa using (hu 0).neg) (by simp [Fin.sum_univ_two]; ring)
  funext i
  fin_cases i
  · have := h 1; simpa using this
  · have := h 0; simpa using this

/-- `W` is rational over `Qbar` when its pullback to sum coordinates is `Qbar`-rational. -/
theorem rationalOverQbar_of_comap {d0 d1 : ℕ} {U : Submodule ℂ (E d0 d1)}
    {A : Submodule Qb ((Fin d0 ⊕ Fin d1) → ℂ)} (hA : A ≤ Fpts Qb (Fin d0 ⊕ Fin d1))
    (h : U.comap (eqv d0 d1).toLinearMap = span ℂ (A : Set ((Fin d0 ⊕ Fin d1) → ℂ))) :
    RationalOverQbar U := by
  rw [rationalOverQbar_iff]
  apply le_antisymm
  · intro u hu
    have h1 : (eqv d0 d1).symm u ∈ span ℂ (A : Set ((Fin d0 ⊕ Fin d1) → ℂ)) := by
      rw [← h]; change (eqv d0 d1) ((eqv d0 d1).symm u) ∈ U; rw [LinearEquiv.apply_symm_apply];
        exact hu
    have h2 := Submodule.apply_mem_span_image_of_mem_span (eqv d0 d1).toLinearMap h1
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine span_mono ?_ h2
    rintro _ ⟨a, ha, rfl⟩
    have haU : (eqv d0 d1) a ∈ U := by
      have : a ∈ U.comap (eqv d0 d1).toLinearMap := by rw [h]; exact subset_span ha
      exact this
    exact ⟨haU, (eqv_fpts a).mp (hA ha)⟩
  · rw [span_le]; intro x hx; exact hx.1

/-- The `ℚ`-submodule of points of `Qbar^{d₀} × 𝓛^{d₁}`. -/
def goodSub (d0 d1 : ℕ) : Submodule ℚ (E d0 d1) where
  carrier := {p | (∀ i, p.1 i ∈ algSub) ∧ ∀ j, p.2 j ∈ logAlgSub}
  add_mem' {_ _} hp hq := ⟨fun i => algSub.add_mem (hp.1 i) (hq.1 i),
    fun j => logAlgSub.add_mem (hp.2 j) (hq.2 j)⟩
  zero_mem' := ⟨fun _ => algSub.zero_mem, fun _ => logAlgSub.zero_mem⟩
  smul_mem' c _ hp := ⟨fun i => algSub.smul_mem c (hp.1 i), fun j => logAlgSub.smul_mem c (hp.2 j)⟩

/-- The zero and full rational product subspaces. -/
def rbot (d0 d1 : ℕ) : RSub d0 d1 :=
  ⟨⊥, ⊥, ⟨⊥, bot_le, by simp⟩, ⟨⊥, bot_le, by simp⟩⟩

/-- The full rational product subspace. -/
def rtop (d0 d1 : ℕ) : RSub d0 d1 :=
  ⟨⊤, ⊤, ⟨Fpts Qb _, le_rfl, span_Fpts_eq_top.symm⟩, ⟨Fpts ℚ _, le_rfl, span_Fpts_eq_top.symm⟩⟩

theorem rbot_sub (d0 d1 : ℕ) : (rbot d0 d1).sub = ⊥ := Submodule.prod_bot
theorem rtop_sub (d0 d1 : ℕ) : (rtop d0 d1).sub = ⊤ := Submodule.prod_top

end StrongSix.Roy

end

end LeanPool
