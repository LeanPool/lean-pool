/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.Roy.Support

/-!
# Transport of Roy's invariants along a coordinate realization

Let `X = (S ≤ T)` be an object and `ψ : ℂ^{d₀} × ℂ^{d₁} → ℂ^{k₀} × ℂ^{k₁}` a `ℂ`-linear map with
`ker ψ ∩ T = S`, `ψ(T) = everything`, `ψ(Ω ∩ T) = Ω'`, whose second component is a map `ψ₁` of the
second factor with `ker ψ₁ ∩ T₁ = S₁` and `ψ₁(T₁) = everything`. Then Roy's invariants of `X` are
the quantities of the coordinate object `(k₀, k₁, ψ(Y ∩ T), ψ(W ∩ T), ψ(V ∩ T))` that appear in
Theorem 1.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy.Amb

variable {M : Amb}

/-- `σ(A ⊓ (B ⊔ K)) = σ A ⊓ σ B` when `A, B ≤ T` and `K = T ⊓ ker σ`. -/
theorem map_inf_sup_ker {V V' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V']
    [Module ℚ V'] (σ : V →ₗ[ℚ] V') (A B T : Submodule ℚ V) (hA : A ≤ T) (hB : B ≤ T) :
    (A ⊓ (B ⊔ (T ⊓ LinearMap.ker σ))).map σ = A.map σ ⊓ B.map σ := by
  apply le_antisymm
  · rintro _ ⟨a, ⟨haA, haBK⟩, rfl⟩
    refine ⟨mem_map_of_mem haA, ?_⟩
    obtain ⟨b, hb, k, hk, rfl⟩ := mem_sup.mp haBK
    rw [map_add, LinearMap.mem_ker.mp hk.2, add_zero]
    exact mem_map_of_mem hb
  · rintro _ ⟨⟨a, haA, rfl⟩, ⟨b, hbB, hab⟩⟩
    refine ⟨a, ⟨haA, ?_⟩, rfl⟩
    have hk : a - b ∈ T ⊓ LinearMap.ker σ :=
      ⟨sub_mem (hA haA) (hB hbB), LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])⟩
    have : a = b + (a - b) := by abel
    rw [this]
    exact add_mem (mem_sup_left hbB) (mem_sup_right hk)

theorem finrank_E (k0 k1 : ℕ) : finrank ℂ (E k0 k1) = k0 + k1 := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Fintype.card_fin]

/-- The transport lemma. -/
theorem transport (X : M.Ob) {k0 k1 : ℕ} (ψ : E M.d0 M.d1 →ₗ[ℂ] E k0 k1)
    (ψ1 : (Fin M.d1 → ℂ) →ₗ[ℂ] (Fin k1 → ℂ)) (_ : ∀ x, (ψ x).2 = ψ1 x.2)
    (hker : LinearMap.ker ψ ⊓ X.1.2.sub = X.1.1.sub) (htop : X.1.2.sub.map ψ = ⊤)
    (hker1 : LinearMap.ker ψ1 ⊓ X.1.2.S1 = X.1.1.S1) (htop1 : X.1.2.S1.map ψ1 = ⊤)
    (hΩ : (Omega M.d0 M.d1 ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ) = Omega k0 k1) :
    r X = k0 + k1 ∧ d1f X = k1 ∧
    vd X = finrank ℂ ↥((M.V ⊓ X.1.2.sub).map ψ) ∧
    wd X = finrank ℂ ↥((M.W ⊓ X.1.2.sub).map ψ) ∧
    c X = finrank ℚ ↥((M.Y ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ)) ∧
    e X = finrank ℚ ↥((M.Y ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ) ⊓ Omega k0 k1) := by
  have hY := M.hYfin
  have hST : X.1.1.sub ≤ X.1.2.sub := RSub.sub_mono X.2
  -- generic rank–nullity on a subspace `A ≤ T`
  have rnC : ∀ A : Submodule ℂ (E M.d0 M.d1), A ≤ X.1.2.sub →
      finrank ℂ ↥(A.map ψ) + finrank ℂ ↥(A ⊓ X.1.1.sub) = finrank ℂ A := by
    intro A hA
    have := finrank_map_add_inf_ker ψ A
    have he : A ⊓ LinearMap.ker ψ = A ⊓ X.1.1.sub := by
      rw [← hker, inf_comm (LinearMap.ker ψ), ← inf_assoc, inf_eq_left.mpr hA]
    rw [he] at this; exact this
  have rnQ : ∀ A : Submodule ℚ (E M.d0 M.d1), A ≤ subQ X.1.2 → [FiniteDimensional ℚ A] →
      finrank ℚ ↥(A.map (ψ.restrictScalars ℚ)) + finrank ℚ ↥(A ⊓ subQ X.1.1) = finrank ℚ A := by
    intro A hA _
    have := finrank_map_add_inf_ker (ψ.restrictScalars ℚ) A
    have he : A ⊓ LinearMap.ker (ψ.restrictScalars ℚ) = A ⊓ subQ X.1.1 := by
      ext x
      constructor
      · rintro ⟨hxA, hxk⟩
        refine ⟨hxA, ?_⟩
        change x ∈ X.1.1.sub
        rw [← hker]; exact ⟨hxk, hA hxA⟩
      · rintro ⟨hxA, hxS⟩
        refine ⟨hxA, ?_⟩
        have : x ∈ LinearMap.ker ψ ⊓ X.1.2.sub := by rw [hker]; exact hxS
        exact this.1
    rw [he] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- r
    have := rnC X.1.2.sub le_rfl
    rw [htop, finrank_top, finrank_E, inf_eq_right.mpr hST] at this
    unfold r; omega
  · -- d₁
    have := finrank_map_add_inf_ker ψ1 X.1.2.S1
    rw [htop1, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      inf_comm, hker1] at this
    unfold d1f; omega
  · -- vd
    have := rnC (M.V ⊓ X.1.2.sub) inf_le_right
    have he : M.V ⊓ X.1.2.sub ⊓ X.1.1.sub = M.V ⊓ X.1.1.sub := by rw [inf_assoc,
      inf_eq_right.mpr hST]
    rw [he] at this
    unfold vd; omega
  · -- wd
    have := rnC (M.W ⊓ X.1.2.sub) inf_le_right
    have he : M.W ⊓ X.1.2.sub ⊓ X.1.1.sub = M.W ⊓ X.1.1.sub := by rw [inf_assoc,
      inf_eq_right.mpr hST]
    rw [he] at this
    unfold wd; omega
  · -- c
    have := rnQ (M.Y ⊓ subQ X.1.2) inf_le_right
    have he : M.Y ⊓ subQ X.1.2 ⊓ subQ X.1.1 = M.Y ⊓ subQ X.1.1 := by
      rw [inf_assoc]; congr 1; exact inf_eq_right.mpr (fun x hx => hST hx)
    rw [he] at this
    unfold c; omega
  · -- e
    have hG : (G X).map (ψ.restrictScalars ℚ) =
        (M.Y ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ) ⊓ Omega k0 k1 := by
      rw [← hΩ]
      have hK : subQ X.1.2 ⊓ LinearMap.ker (ψ.restrictScalars ℚ) = subQ X.1.1 := by
        ext x
        constructor
        · rintro ⟨hxT, hxk⟩
          change x ∈ X.1.1.sub
          rw [← hker]; exact ⟨hxk, hxT⟩
        · intro hxS
          have : x ∈ LinearMap.ker ψ ⊓ X.1.2.sub := by rw [hker]; exact hxS
          exact ⟨this.2, this.1⟩
      have := map_inf_sup_ker (ψ.restrictScalars ℚ) (M.Y ⊓ subQ X.1.2) (Omega M.d0 M.d1 ⊓ subQ
        X.1.2)
        (subQ X.1.2) inf_le_right inf_le_right
      rw [hK] at this
      exact this
    have := rnQ (G X) (fun x hx => (G_le X hx).2)
    have he : G X ⊓ subQ X.1.1 = M.Y ⊓ subQ X.1.1 := by
      apply le_antisymm
      · rintro x ⟨hxG, hxS⟩; exact ⟨(G_le X hxG).1, hxS⟩
      · intro x hx; exact ⟨Y_le_G X hx, hx.2⟩
    rw [he, hG] at this
    unfold e; omega

end StrongSix.Roy.Amb

end

end LeanPool
