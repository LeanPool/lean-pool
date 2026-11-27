/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentCoordinates
public import LeanPool.VacuumBellSeparation.Gaussian.CoherentTotality
public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductTotality

/-!
# Totality of the actual finite-mode coherent family

The successor coherent vector is the genuine product of a one-mode vector
and its tail. The product totality theorem and mode induction prove density
of the actual coherent span, including the zero-mode Hilbert space.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem multiExponentialVector_cons {m : ℕ} (z : ℂ) (w : Fin m → ℂ) :
    l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
      (exponentialVector z) (multiExponentialVector w) =
      multiExponentialVector (Fin.cons z w) := by
  ext k
  change coherentCoefficient z (k 0) * multiCoherentCoefficient w (Fin.tail k) =
    multiCoherentCoefficient (Fin.cons z w) k
  simp only [multiCoherentCoefficient, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- The unnormalized coherent vectors span a dense subspace of the true
full multi-mode oscillator Hilbert space. -/
theorem multiExponentialVector_dense_span (m : ℕ) :
    (Submodule.span ℂ (Set.range (multiExponentialVector (m := m)))).topologicalClosure = ⊤ := by
  classical
  induction m with
  | zero =>
    let z : Fin 0 → ℂ := fun i => Fin.elim0 i
    have hsingle (k : Fin 0 → ℕ) :
        multiModeNumberBasis 0 k = multiExponentialVector z := by
      ext l
      have hkl : l = k := Subsingleton.elim _ _
      subst l
      rw [← multiModeNumberBasis_inner, multiExponentialVector_apply]
      simp [inner_self_eq_norm_sq_to_K, (multiModeNumberBasis 0).orthonormal.norm_eq_one,
        multiCoherentCoefficient]
    have hspan : Submodule.span ℂ (Set.range (multiModeNumberBasis 0)) ≤
        Submodule.span ℂ (Set.range (multiExponentialVector (m := 0))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      rw [hsingle k]
      exact Submodule.subset_span ⟨z, rfl⟩
    have h := Submodule.topologicalClosure_mono hspan
    rw [(multiModeNumberBasis 0).dense_span] at h
    exact top_unique h
  | succ m ih =>
    let e := (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
    have hp := l2Product_dense_span e exponentialVector (multiExponentialVector (m := m))
      exponentialVector_dense_span ih
    have hspan : Submodule.span ℂ (Set.range (fun p : ℂ × (Fin m → ℂ) =>
        l2ProductVector e (exponentialVector p.1) (multiExponentialVector p.2))) ≤
        Submodule.span ℂ (Set.range (multiExponentialVector (m := m + 1))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨z, w⟩, rfl⟩
      change l2ProductVector e (exponentialVector z) (multiExponentialVector w) ∈
        Submodule.span ℂ (Set.range (multiExponentialVector (m := m + 1)))
      rw [show l2ProductVector e (exponentialVector z) (multiExponentialVector w) =
        multiExponentialVector (Fin.cons z w) from multiExponentialVector_cons z w]
      exact Submodule.subset_span ⟨Fin.cons z w, rfl⟩
    have h := Submodule.topologicalClosure_mono hspan
    rw [hp] at h
    exact top_unique h

end VacuumBellSeparation.Gaussian
