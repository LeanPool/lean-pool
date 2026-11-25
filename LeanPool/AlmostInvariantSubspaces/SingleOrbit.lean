/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Families

/-!
# S3, the single-orbit case, from the proved S1

The derivation S1 ⟹ S3: the single orbit is the family `g ↦ gA` indexed by `G` itself; apply the
proved theorem
`KPFamilies.kp_family_one_sided` (file `KPFull/Families.lean`) to it.
-/

@[expose] public section

open Module

namespace KPFamilies

/-- `dim gB / (gB ∩ gC) = dim B / (B ∩ C)` for a linear automorphism `g`. -/
theorem rank_quotient_map_equiv {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (B C : Submodule K V) :
    Module.rank K (B.map (e : V →ₗ[K] V) ⧸
        (C.map (e : V →ₗ[K] V)).submoduleOf (B.map (e : V →ₗ[K] V))) =
      Module.rank K (B ⧸ C.submoduleOf B) := by
  refine (LinearEquiv.rank_eq
    (Submodule.Quotient.equiv (C.submoduleOf B) _ (e.submoduleMap B) ?_)).symm
  ext ⟨y, hy⟩
  constructor
  · intro h
    obtain ⟨⟨z, hzB⟩, hzC, hz⟩ := Submodule.mem_map.mp h
    have hz' : e z = y := by
      have := congrArg Subtype.val hz
      simpa [LinearEquiv.submoduleMap_apply] using this
    change y ∈ C.map (e : V →ₗ[K] V)
    exact Submodule.mem_map.mpr ⟨z, hzC, hz'⟩
  · intro h
    obtain ⟨z, hzC, hzy⟩ := Submodule.mem_map.mp (show y ∈ C.map (e : V →ₗ[K] V) from h)
    obtain ⟨w, hwB, hwy⟩ := Submodule.mem_map.mp hy
    have hwz : w = z := e.injective (hwy.trans hzy.symm)
    subst hwz
    subst hzy
    exact Submodule.mem_map.mpr ⟨⟨w, hwB⟩, hzC, Subtype.ext (by simp
        [LinearEquiv.submoduleMap_apply])⟩

/-- **(S3) The single-orbit corollary**, for any group, any division ring and any dimension: the
family of all `gA`
(statement of `Challenge/StatementFull.lean`, verbatim). If `dim A / (A ∩ gA) ≤ r` for all `g`,
there is an invariant `W` with
`dim W / (W ∩ A) ≤ r` and `dim A / (W ∩ A) ≤ r (r + 1)`. Derived from S1:
the family `g ↦ gA` indexed by `G`, with `G` acting on itself by left multiplication. -/
theorem kp_single_orbit {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Group G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) :
    ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧
      Module.rank K (A ⧸ W.submoduleOf A) ≤ (r * (r + 1) : ℕ) := by
  have hmul : ∀ g h : G, A.map (ρ (g * h) : V →ₗ[K] V) =
      (A.map (ρ h : V →ₗ[K] V)).map (ρ g : V →ₗ[K] V) :=
    fun g h => AlmostInvariant.linearAct_mul_apply ρ g h A
  have hone : A.map (ρ 1 : V →ₗ[K] V) = A := by
    rw [map_one]
    exact Submodule.map_id A
  obtain ⟨W, hW, h⟩ := kp_family_one_sided (X := G) ρ (fun g => A.map (ρ g : V →ₗ[K] V))
    (fun g x => hmul g x) r (by
      intro x y
      have hy : A.map (ρ y : V →ₗ[K] V) =
          (A.map (ρ (x⁻¹ * y) : V →ₗ[K] V)).map (ρ x : V →ₗ[K] V) := by
        rw [← hmul, mul_inv_cancel_left]
      change Module.rank K (A.map (ρ x : V →ₗ[K] V) ⧸
        (A.map (ρ y : V →ₗ[K] V)).submoduleOf (A.map (ρ x : V →ₗ[K] V))) ≤ r
      rw [hy, rank_quotient_map_equiv]
      exact hr _)
  obtain ⟨h1, h2⟩ := h 1
  rw [hone] at h1 h2
  exact ⟨W, hW, h1, h2⟩

end KPFamilies
