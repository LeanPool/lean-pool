/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCanonicalThermalModel
public import LeanPool.VacuumBellSeparation.Gaussian.CanonicalThermalModel
public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductInner

/-!
# Splitting one actual mode from the finite-mode representation

The phase-space norm, Weyl phase and normalized coherent vector all
factor through the literal first coordinate and tail. These identities
prepare operator factorization on the full occupation Hilbert space.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped lp

/-- Prepend the first complex coordinate to the phase-space coordinates of the remaining modes. -/
noncomputable def multiPhaseCons {m : ℕ} (z : ℂ) (w : MultiModePhaseSpace m) :
    MultiModePhaseSpace (m + 1) := WithLp.toLp 2 (Fin.cons z (fun j => w j))

theorem multiPhaseCons_add {m : ℕ} (z a : ℂ) (w b : MultiModePhaseSpace m) :
    multiPhaseCons z w + multiPhaseCons a b = multiPhaseCons (z + a) (w + b) := by
  ext i
  induction i using Fin.cases <;> rfl

theorem multiPhaseCons_norm_sq {m : ℕ} (z : ℂ) (w : MultiModePhaseSpace m) :
    ‖multiPhaseCons z w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, multiPhaseCons, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

theorem inner_multiPhaseCons {m : ℕ} (z a : ℂ) (w b : MultiModePhaseSpace m) :
    inner ℂ (multiPhaseCons z w) (multiPhaseCons a b) = inner ℂ z a + inner ℂ w b := by
  simp only [PiLp.inner_apply, multiPhaseCons, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

theorem weylPhase_multiPhaseCons {m : ℕ} (z a : ℂ) (w b : MultiModePhaseSpace m) :
    weylPhase (id : MultiModePhaseSpace (m + 1) → MultiModePhaseSpace (m + 1))
      (multiPhaseCons z w) (multiPhaseCons a b) =
      weylPhase (id : ℂ → ℂ) z a *
        weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) w b := by
  simp only [weylPhase, id_eq, inner_multiPhaseCons, Complex.add_im,
    Complex.ofReal_add, mul_add, neg_add, Complex.exp_add]

theorem l2ProductVector_smul_smul {ι κ η : Type*} (e : κ ≃ ι × η)
    (a b : ℂ) (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) :
    l2ProductVector e (a • x) (b • y) = (a * b) • l2ProductVector e x y := by
  change l2ProductContinuous e (a • x) (b • y) = (a * b) • l2ProductContinuous e x y
  rw [(l2ProductContinuous e).map_smul a x, smul_apply,
    ((l2ProductContinuous e) x).map_smul b y, smul_smul]

theorem multiCoherentVector_cons {m : ℕ} (z : ℂ) (w : MultiModePhaseSpace m) :
    multiCoherentVector (multiPhaseCons z w) =
      l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
        (coherentVector z) (multiCoherentVector w) := by
  rw [multiCoherentVector, multiPhaseCons_norm_sq]
  have hsplit : -((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) = -(‖z‖ ^ 2 / 2) + -(‖w‖ ^ 2 / 2) := by ring
  rw [hsplit, Complex.ofReal_add, Complex.exp_add]
  rw [coherentVector, multiCoherentVector, l2ProductVector_smul_smul]
  congr 1
  exact (multiExponentialVector_cons z (fun j => w j)).symm

/-- Splitting the occupation number is compatible with the actual number
basis, not just with the coherent family. -/
theorem multiModeNumberBasis_cons {m : ℕ} (n : ℕ) (k : Fin m → ℕ) :
    multiModeNumberBasis (m + 1) (Fin.cons n k) =
      l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
        (numberBasis n) (multiModeNumberBasis m k) := by
  classical
  rw [← (multiModeNumberBasis (m + 1)).repr_symm_single (Fin.cons n k),
    ← numberBasis.repr_symm_single n, ← (multiModeNumberBasis m).repr_symm_single k]
  change lp.single 2 (Fin.cons n k) (1 : ℂ) =
    l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
      (lp.single 2 n 1) (lp.single 2 k 1)
  rw [l2ProductVector_single]
  rfl

end VacuumBellSeparation.Gaussian
