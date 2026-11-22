/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

import Mathlib.Tactic.LinearCombination

/-!
# Gluing linear maps along two comaximal localisations

Let `s, t` be comaximal elements of a commutative ring `Λ` and `P, M` two `Λ`-modules with `P`
finitely presented. Linear maps `P_s → M_s` and `P_t → M_t` whose images in `M_st` agree come
from a linear map `P → M`; such a map is unique. If moreover `M` is finitely presented and the two
maps are isomorphisms compatible with an isomorphism `P_st ≅ M_st`, then `P ≅ M`. This is the
final step of Quillen's patching argument (Quillen 1976, proof of Theorem 1, p. 168).

All localisations are given abstractly through `IsLocalizedModule`.

## Main results

* `eq_of_comp_eq_of_isCoprime`: uniqueness of glued maps.
* `exists_glue_linearMap`: existence of glued maps.
* `nonempty_linearEquiv_of_glue`: gluing of isomorphisms.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public section

namespace LeanPool.QuillenSuslin

variable {Λ : Type*} [CommRing Λ] {s t : Λ}

section Unique

variable {P M Ms Mt : Type*} [AddCommGroup P] [Module Λ P] [AddCommGroup M] [Module Λ M]
  [AddCommGroup Ms] [Module Λ Ms] [AddCommGroup Mt] [Module Λ Mt]

/-- Linear maps into `M` that agree after localising away from two comaximal elements are
equal. -/
theorem eq_of_comp_eq_of_isCoprime (hst : IsCoprime s t) (ℓs : M →ₗ[Λ] Ms) (ℓt : M →ₗ[Λ] Mt)
    [IsLocalizedModule (Submonoid.powers s) ℓs] [IsLocalizedModule (Submonoid.powers t) ℓt]
    {f g : P →ₗ[Λ] M} (hs : ℓs ∘ₗ f = ℓs ∘ₗ g) (ht : ℓt ∘ₗ f = ℓt ∘ₗ g) : f = g := by
  ext x
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers s) (f := ℓs)
    (LinearMap.congr_fun hs x)
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers t) (f := ℓt)
    (LinearMap.congr_fun ht x)
  obtain ⟨α, β, hαβ⟩ := hst.pow (m := n) (n := m)
  simp only [Submonoid.smul_def] at hn hm
  calc f x = (α * s ^ n + β * t ^ m) • f x := by rw [hαβ, one_smul]
    _ = (α * s ^ n + β * t ^ m) • g x := by
      rw [add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, hn, hm]
    _ = g x := by rw [hαβ, one_smul]

end Unique

section Exists

variable {P M Ps Pt Ms Mt Mst : Type*} [AddCommGroup P] [Module Λ P] [AddCommGroup M]
  [Module Λ M] [AddCommGroup Ps] [Module Λ Ps] [AddCommGroup Pt] [Module Λ Pt]
  [AddCommGroup Ms] [Module Λ Ms] [AddCommGroup Mt] [Module Λ Mt] [AddCommGroup Mst]
  [Module Λ Mst]

theorem smul_cancel_of_isLocalizedModule (ℓ : M →ₗ[Λ] Ms)
    [IsLocalizedModule (Submonoid.powers s) ℓ] (j : ℕ) {f g : P →ₗ[Λ] Ms}
    (h : s ^ j • f = s ^ j • g) : f = g := by
  have hu := (Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units ℓ
      (⟨s ^ j, Submonoid.pow_mem _ (Submonoid.mem_powers s) j⟩ : Submonoid.powers s))
  ext x
  apply hu.1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
  exact LinearMap.congr_fun h x

/-- Linear maps `P_s → M_s` and `P_t → M_t` whose images in `M_st` agree glue to a linear map
`P → M`, for `P` finitely presented and `s, t` comaximal. -/
theorem exists_glue_linearMap (hst : IsCoprime s t) (ℓPs : P →ₗ[Λ] Ps) (ℓPt : P →ₗ[Λ] Pt)
    (ℓMs : M →ₗ[Λ] Ms) (ℓMt : M →ₗ[Λ] Mt) (ℓMst : M →ₗ[Λ] Mst) (τs : Ms →ₗ[Λ] Mst)
    (τt : Mt →ₗ[Λ] Mst) [IsLocalizedModule (Submonoid.powers s) ℓMs]
    [IsLocalizedModule (Submonoid.powers t) ℓMt] [IsLocalizedModule (Submonoid.powers (s * t)) ℓMst]
    (hτs : τs ∘ₗ ℓMs = ℓMst) (hτt : τt ∘ₗ ℓMt = ℓMst) [Module.FinitePresentation Λ P]
    (φs : Ps →ₗ[Λ] Ms) (φt : Pt →ₗ[Λ] Mt) (h : τs ∘ₗ φs ∘ₗ ℓPs = τt ∘ₗ φt ∘ₗ ℓPt) :
    ∃ φ : P →ₗ[Λ] M, ℓMs ∘ₗ φ = φs ∘ₗ ℓPs ∧ ℓMt ∘ₗ φ = φt ∘ₗ ℓPt := by
  set Ψs := φs ∘ₗ ℓPs
  set Ψt := φt ∘ₗ ℓPt
  obtain ⟨h₁, ⟨_, n, rfl⟩, e₁⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers s) ℓMs Ψs
  obtain ⟨h₂, ⟨_, m, rfl⟩, e₂⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers t) ℓMt Ψt
  simp only [Submonoid.smul_def] at e₁ e₂
  have e₁' : ℓMst ∘ₗ h₁ = s ^ n • (τs ∘ₗ Ψs) := by
    rw [← hτs, LinearMap.comp_assoc, e₁, LinearMap.comp_smul]
  have e₂' : ℓMst ∘ₗ h₂ = t ^ m • (τs ∘ₗ Ψs) := by
    rw [← hτt, LinearMap.comp_assoc, e₂, LinearMap.comp_smul, h]
  have key : ℓMst ∘ₗ (t ^ m • h₁) = ℓMst ∘ₗ (s ^ n • h₂) := by
    rw [LinearMap.comp_smul, e₁', LinearMap.comp_smul, e₂', smul_smul, smul_smul, mul_comm]
  obtain ⟨⟨_, k, rfl⟩, ek⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (Submonoid.powers (s * t)) ℓMst _ _ key
  simp only [Submonoid.smul_def, smul_smul] at ek
  obtain ⟨α, β, hαβ⟩ := hst.pow (m := n + k) (n := m + k)
  refine ⟨(α * s ^ k) • h₁ + (β * t ^ k) • h₂, ?_, ?_⟩
  · have h₂s : ℓMs ∘ₗ (t ^ k • h₂) = t ^ (m + k) • Ψs := by
      apply smul_cancel_of_isLocalizedModule (s := s) ℓMs (n + k)
      have : s ^ (n + k) • t ^ k • h₂ = (s ^ k * t ^ (k + m)) • h₁ := by
        rw [smul_smul]
        convert ek.symm using 2 <;> ring
      rw [← LinearMap.comp_smul, this, LinearMap.comp_smul, e₁, smul_smul, smul_smul]
      congr 1
      ring
    rw [LinearMap.comp_add, LinearMap.comp_smul, mul_smul β, LinearMap.comp_smul ℓMs β, h₂s, e₁,
      smul_smul, smul_smul, ← add_smul]
    convert one_smul Λ Ψs using 2
    linear_combination hαβ
  · have h₁t : ℓMt ∘ₗ (s ^ k • h₁) = s ^ (n + k) • Ψt := by
      apply smul_cancel_of_isLocalizedModule (s := t) ℓMt (m + k)
      have : t ^ (m + k) • s ^ k • h₁ = (t ^ k * s ^ (k + n)) • h₂ := by
        rw [smul_smul]
        convert ek using 2 <;> ring
      rw [← LinearMap.comp_smul, this, LinearMap.comp_smul, e₂, smul_smul, smul_smul]
      congr 1
      ring
    rw [LinearMap.comp_add, mul_smul α, LinearMap.comp_smul ℓMt α, h₁t, LinearMap.comp_smul, e₂,
      smul_smul, smul_smul, ← add_smul]
    convert one_smul Λ Ψt using 2
    linear_combination hαβ

end Exists

section Equiv

variable {P M Ps Pt Pst Ms Mt Mst : Type*} [AddCommGroup P] [Module Λ P] [AddCommGroup M]
  [Module Λ M] [AddCommGroup Ps] [Module Λ Ps] [AddCommGroup Pt] [Module Λ Pt]
  [AddCommGroup Pst] [Module Λ Pst] [AddCommGroup Ms] [Module Λ Ms] [AddCommGroup Mt]
  [Module Λ Mt] [AddCommGroup Mst] [Module Λ Mst]

/-- **Gluing isomorphisms.** For `s, t` comaximal and finitely presented `P, M`, isomorphisms
`P_s ≅ M_s` and `P_t ≅ M_t` that agree over `P_st ≅ M_st` glue to an isomorphism `P ≅ M`. -/
theorem nonempty_linearEquiv_of_glue (hst : IsCoprime s t) (ℓPs : P →ₗ[Λ] Ps)
    (ℓPt : P →ₗ[Λ] Pt) (ℓPst : P →ₗ[Λ] Pst) (τPs : Ps →ₗ[Λ] Pst) (τPt : Pt →ₗ[Λ] Pst)
    (ℓMs : M →ₗ[Λ] Ms) (ℓMt : M →ₗ[Λ] Mt) (ℓMst : M →ₗ[Λ] Mst) (τMs : Ms →ₗ[Λ] Mst)
    (τMt : Mt →ₗ[Λ] Mst)
    [IsLocalizedModule (Submonoid.powers s) ℓPs] [IsLocalizedModule (Submonoid.powers t) ℓPt]
    [IsLocalizedModule (Submonoid.powers (s * t)) ℓPst]
    [IsLocalizedModule (Submonoid.powers s) ℓMs] [IsLocalizedModule (Submonoid.powers t) ℓMt]
    [IsLocalizedModule (Submonoid.powers (s * t)) ℓMst]
    (hPs : τPs ∘ₗ ℓPs = ℓPst) (hPt : τPt ∘ₗ ℓPt = ℓPst) (hMs : τMs ∘ₗ ℓMs = ℓMst)
    (hMt : τMt ∘ₗ ℓMt = ℓMst) [Module.FinitePresentation Λ P] [Module.FinitePresentation Λ M]
    (φs : Ps ≃ₗ[Λ] Ms) (φt : Pt ≃ₗ[Λ] Mt) (φst : Pst ≃ₗ[Λ] Mst)
    (hs : τMs ∘ₗ φs.toLinearMap = φst.toLinearMap ∘ₗ τPs)
    (ht : τMt ∘ₗ φt.toLinearMap = φst.toLinearMap ∘ₗ τPt) :
    Nonempty (P ≃ₗ[Λ] M) := by
  have hs' : τPs ∘ₗ φs.symm.toLinearMap = φst.symm.toLinearMap ∘ₗ τMs := by
    ext x
    have := LinearMap.congr_fun hs (φs.symm x)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply] at this
    simp [this]
  have ht' : τPt ∘ₗ φt.symm.toLinearMap = φst.symm.toLinearMap ∘ₗ τMt := by
    ext x
    have := LinearMap.congr_fun ht (φt.symm x)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply] at this
    simp [this]
  obtain ⟨φ, hφs, hφt⟩ := exists_glue_linearMap hst ℓPs ℓPt ℓMs ℓMt ℓMst τMs τMt hMs hMt
    φs.toLinearMap φt.toLinearMap (by
      rw [← LinearMap.comp_assoc, hs, ← LinearMap.comp_assoc, ht, LinearMap.comp_assoc, hPs,
        LinearMap.comp_assoc, hPt])
  obtain ⟨ψ, hψs, hψt⟩ := exists_glue_linearMap hst ℓMs ℓMt ℓPs ℓPt ℓPst τPs τPt hPs hPt
    φs.symm.toLinearMap φt.symm.toLinearMap (by
      rw [← LinearMap.comp_assoc, hs', ← LinearMap.comp_assoc, ht', LinearMap.comp_assoc, hMs,
        LinearMap.comp_assoc, hMt])
  refine ⟨LinearEquiv.ofLinearMap φ ψ ?_ ?_⟩
  · refine eq_of_comp_eq_of_isCoprime hst ℓMs ℓMt ?_ ?_
    · rw [← LinearMap.comp_assoc, hφs, LinearMap.comp_assoc, hψs, ← LinearMap.comp_assoc]
      simp
    · rw [← LinearMap.comp_assoc, hφt, LinearMap.comp_assoc, hψt, ← LinearMap.comp_assoc]
      simp
  · refine eq_of_comp_eq_of_isCoprime hst ℓPs ℓPt ?_ ?_
    · rw [← LinearMap.comp_assoc, hψs, LinearMap.comp_assoc, hφs, ← LinearMap.comp_assoc]
      simp
    · rw [← LinearMap.comp_assoc, hψt, LinearMap.comp_assoc, hφt, ← LinearMap.comp_assoc]
      simp

end Equiv

end LeanPool.QuillenSuslin

