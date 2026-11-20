/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.Domain
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Resolvent set and spectrum of a partially defined operator

For a partially defined linear map `T : X →ₗ.[ℂ] X` on a complex normed space, a bounded operator
`R` is a resolvent of `T` at `z` when it is a two-sided inverse of `z - T : D(T) → X`.  The
resolvent set and the spectrum are defined from this notion, following the definition of the
spectrum of an unbounded operator used in the paper (Appendix A).  A `DomainOperator` is read as a
partially defined map with domain the range of its embedding, and a `HasResolventOn` yields
resolvents in this sense.  If one resolvent is compact, every resolvent is compact and every point
of the spectrum is an eigenvalue.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

universe u v

namespace LinearPMap

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `R` is a bounded two-sided inverse of `z - T`: it maps `X` into the domain of `T`, solves
`(z - T) (R x) = x`, and satisfies `R ((z - T) y) = y` on the domain. -/
def IsResolvent (T : X →ₗ.[ℂ] X) (z : ℂ) (R : X →L[ℂ] X) : Prop :=
  (∀ x : X, ∃ h : R x ∈ T.domain, z • R x - T ⟨R x, h⟩ = x) ∧
    ∀ y : T.domain, R (z • (y : X) - T y) = y

/-- The resolvent set of a partially defined operator: the points `z` at which `z - T` has a
bounded two-sided inverse. -/
def resolventSet (T : X →ₗ.[ℂ] X) : Set ℂ := {z | ∃ R : X →L[ℂ] X, IsResolvent T z R}

/-- The spectrum of a partially defined operator: the complement of its resolvent set. -/
def spectrum (T : X →ₗ.[ℂ] X) : Set ℂ := (resolventSet T)ᶜ

end LinearPMap

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- A domain operator read as a partially defined linear map: its domain is the range of the
embedding and its value at `ι d` is `A d`. -/
def toLinearPMap (A : DomainOperator X D) : X →ₗ.[ℂ] X where
  domain := LinearMap.range (A.embedding : D →ₗ[ℂ] X)
  toFun := (A.op : D →ₗ[ℂ] X) ∘ₗ
    (LinearEquiv.ofInjective (A.embedding : D →ₗ[ℂ] X) A.embedding_injective).symm.toLinearMap

/-- The domain of `A.toLinearPMap` is the range of the embedding. -/
theorem mem_toLinearPMap_domain_iff (A : DomainOperator X D) (x : X) :
    x ∈ A.toLinearPMap.domain ↔ ∃ d : D, A.embedding d = x :=
  LinearMap.mem_range

/-- `A.toLinearPMap` takes the value `A d` at every point of the domain whose preimage is `d`. -/
theorem toLinearPMap_apply_of_embedding_eq (A : DomainOperator X D) {x : X}
    (hx : x ∈ A.toLinearPMap.domain) {d : D} (hd : A.embedding d = x) :
    A.toLinearPMap ⟨x, hx⟩ = A.op d := by
  have h : (LinearEquiv.ofInjective (A.embedding : D →ₗ[ℂ] X) A.embedding_injective).symm
      ⟨x, hx⟩ = d := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hd.symm
  exact congrArg A.op h

/-- On the image `ι d` of an element of `D`, `A.toLinearPMap` takes the value `A d`. -/
theorem toLinearPMap_apply_embedding (A : DomainOperator X D) (d : D) :
    A.toLinearPMap ⟨A.embedding d, LinearMap.mem_range_self (A.embedding : D →ₗ[ℂ] X) d⟩ =
      A.op d :=
  toLinearPMap_apply_of_embedding_eq A _ rfl

/-- A resolvent of a domain operator in the sense of `HasResolventOn`, composed with the
embedding, is a resolvent of the associated partially defined map. -/
theorem isResolvent_stateResolvent {A : DomainOperator X D} {S : Set ℂ}
    (h : HasResolventOn A S) {z : ℂ} (hz : z ∈ S) :
    LinearPMap.IsResolvent A.toLinearPMap z (h.stateResolvent z) := by
  have hr : ∀ x, A.pencil z (h.inv z x) = x := fun x ↦
    congrArg (fun f : X →L[ℂ] X ↦ f x) (h.right_inv z hz)
  have hl : ∀ d, h.inv z (A.pencil z d) = d := fun d ↦
    congrArg (fun f : D →L[ℂ] D ↦ f d) (h.left_inv z hz)
  have hp : ∀ d, A.pencil z d = z • A.embedding d - A.op d := fun d ↦ by
    simp [pencil]
  refine ⟨fun x ↦ ⟨LinearMap.mem_range_self (A.embedding : D →ₗ[ℂ] X) (h.inv z x), ?_⟩, ?_⟩
  · refine Eq.trans (congrArg (fun v : X ↦ z • (h.stateResolvent z) x - v)
      (toLinearPMap_apply_of_embedding_eq A _ (d := h.inv z x) rfl)) ?_
    change z • A.embedding (h.inv z x) - _ = x
    rw [← hp, hr]
  · rintro ⟨y, d, hd⟩
    subst hd
    refine Eq.trans (congrArg (fun v : X ↦
      (h.stateResolvent z) (z • A.embedding d - v))
      (toLinearPMap_apply_of_embedding_eq A _ (d := d) rfl)) ?_
    change A.embedding (h.inv z (z • A.embedding d - A.op d)) = _
    rw [← hp, hl]
    rfl

end DomainOperator

namespace LinearPMap

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If one resolvent of `T` is compact, every resolvent of `T` is compact: the resolvents are
related by `R' = R + (z - w) R R'`. -/
theorem IsResolvent.isCompactOperator_of_isResolvent {T : X →ₗ.[ℂ] X} {z w : ℂ}
    {R R' : X →L[ℂ] X} (hR : IsResolvent T z R) (hc : IsCompactOperator R)
    (hR' : IsResolvent T w R') : IsCompactOperator R' := by
  have key : R' = R + (z - w) • R.comp R' := by
    ext x
    obtain ⟨h1, h2⟩ := hR'
    obtain ⟨hd, hx⟩ := h1 x
    have := hR.2 ⟨R' x, hd⟩
    have e : z • R' x - T ⟨R' x, hd⟩ = (z - w) • R' x + x := by
      calc z • R' x - T ⟨R' x, hd⟩
          = (z • R' x - w • R' x) + (w • R' x - T ⟨R' x, hd⟩) := by abel
        _ = (z - w) • R' x + x := by rw [hx, sub_smul]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply]
    rw [add_comm]
    rw [e, map_add, map_smul] at this
    exact this.symm
  rw [key]
  exact hc.add ((hc.comp_clm R').smul _)

/-- An eigenvector of `T` in its domain gives a point of the spectrum. -/
theorem mem_spectrum_of_eigenvector {T : X →ₗ.[ℂ] X} {lam : ℂ} (x : T.domain)
    (hx : (x : X) ≠ 0) (h : T x = lam • (x : X)) : lam ∈ spectrum T := by
  rintro ⟨R, -, h2⟩
  apply hx
  have := h2 x
  rw [h, sub_self, map_zero] at this
  exact this.symm

/-- If `T` has a compact resolvent, every point of its spectrum is an eigenvalue with an
eigenvector in the domain. -/
theorem exists_eigenvector_of_mem_spectrum [CompleteSpace X] {T : X →ₗ.[ℂ] X} {r : ℂ}
    {R : X →L[ℂ] X} (hR : IsResolvent T r R) (hc : IsCompactOperator R) {lam : ℂ}
    (hlam : lam ∈ spectrum T) :
    ∃ x : T.domain, (x : X) ≠ 0 ∧ T x = lam • (x : X) := by
  have hne : r - lam ≠ 0 := fun h0 ↦ hlam (by rw [← sub_eq_zero.mp h0]; exact ⟨R, hR⟩)
  set c : ℂ := r - lam with hc_def
  have hcmu : c * c⁻¹ = 1 := mul_inv_cancel₀ hne
  -- `T (R x) = r R x - x`
  have hT : ∀ x : X, ∀ h : R x ∈ T.domain, T ⟨R x, h⟩ = r • R x - x := fun x h ↦ by
    obtain ⟨h', e⟩ := hR.1 x
    calc T ⟨R x, h⟩ = r • R x - (r • R x - T ⟨R x, h'⟩) := by abel
      _ = r • R x - x := by rw [e]
  by_cases hμ : c⁻¹ ∈ _root_.spectrum ℂ R
  · obtain ⟨y, hy⟩ :=
      ((hc.hasEigenvalue_iff_mem_spectrum (inv_ne_zero hne)).2 hμ).exists_hasEigenvector
    have hRy : R y = c⁻¹ • y := hy.apply_eq_smul
    obtain ⟨hd, -⟩ := hR.1 y
    refine ⟨c • ⟨R y, hd⟩, ?_, ?_⟩
    · change c • R y ≠ 0
      rw [hRy, smul_smul, hcmu, one_smul]
      exact hy.2
    · rw [LinearPMap.map_smul, hT]
      change c • (r • R y - y) = lam • (c • R y)
      rw [hRy]
      simp only [smul_sub, smul_smul]
      rw [← sub_smul]
      congr 1
      linear_combination (r - lam) * hcmu - hc_def
  · exfalso
    apply hlam
    rw [_root_.spectrum.mem_iff, not_not] at hμ
    obtain ⟨u, hu⟩ := hμ
    have hV : ∀ x : X, (u : X →L[ℂ] X) x = c⁻¹ • x - R x := fun x ↦ by
      rw [hu]; simp [Algebra.algebraMap_eq_smul_one]
    have hVU : ∀ x : X, (u : X →L[ℂ] X) ((↑u⁻¹ : X →L[ℂ] X) x) = x := fun x ↦
      congrArg (fun f : X →L[ℂ] X ↦ f x) u.mul_inv
    have hUV : ∀ x : X, (↑u⁻¹ : X →L[ℂ] X) ((u : X →L[ℂ] X) x) = x := fun x ↦
      congrArg (fun f : X →L[ℂ] X ↦ f x) u.inv_mul
    have hcomm : ∀ x : X, R ((↑u⁻¹ : X →L[ℂ] X) x) = (↑u⁻¹ : X →L[ℂ] X) (R x) := fun x ↦ by
      have h1 : ∀ x : X, R ((u : X →L[ℂ] X) x) = (u : X →L[ℂ] X) (R x) := fun x ↦ by
        rw [hV, hV, map_sub, map_smul]
      have h2 := h1 ((↑u⁻¹ : X →L[ℂ] X) x)
      rw [hVU] at h2
      have h3 := congrArg (fun v : X ↦ (↑u⁻¹ : X →L[ℂ] X) v) h2
      simp only [hUV] at h3
      exact h3.symm
    have hrc : r = c + lam := by rw [hc_def]; ring
    refine ⟨c⁻¹ • R.comp (↑u⁻¹ : X →L[ℂ] X), fun x ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨hd, -⟩ := hR.1 ((↑u⁻¹ : X →L[ℂ] X) x)
      have hm : (c⁻¹ • R.comp (↑u⁻¹ : X →L[ℂ] X)) x ∈ T.domain :=
        T.domain.smul_mem _ hd
      refine ⟨hm, ?_⟩
      have e1 : T ⟨(c⁻¹ • R.comp (↑u⁻¹ : X →L[ℂ] X)) x, hm⟩ =
          c⁻¹ • T ⟨R ((↑u⁻¹ : X →L[ℂ] X) x), hd⟩ :=
        (LinearPMap.map_smul T c⁻¹ ⟨R ((↑u⁻¹ : X →L[ℂ] X) x), hd⟩)
      rw [e1, hT]
      have e2 := hV ((↑u⁻¹ : X →L[ℂ] X) x)
      rw [hVU] at e2
      conv_rhs => rw [e2]
      simp only [smul_apply, ContinuousLinearMap.comp_apply]
      rw [hrc]
      match_scalars <;> field_simp; ring
    · have hv : lam • (y : X) - T y = (r • (y : X) - T y) - c • (y : X) := by
        rw [hrc]; module
      have hRv : R (lam • (y : X) - T y) = c • (↑u : X →L[ℂ] X) y := by
        rw [hv, map_sub, hR.2 y, hV, map_smul]
        simp only [smul_sub, smul_smul, hcmu, one_smul]
      change c⁻¹ • R ((↑u⁻¹ : X →L[ℂ] X) (lam • (y : X) - T y)) = y
      rw [hcomm, hRv, map_smul, hUV, smul_smul, inv_mul_cancel₀ hne, one_smul]

end LinearPMap

end

end FastDynamo
