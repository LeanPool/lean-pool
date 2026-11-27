/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.SymmetricTensorTotality
public import LeanPool.VacuumBellSeparation.Fock.RealMultilinearDiagonal
public import LeanPool.VacuumBellSeparation.Gaussian.StandardSubspaceSource

/-!
# Diagonal tensors from an actual standard real subspace are total

Real polarization gives the mixed real tensors. Complex multilinearity
expands x+iy in every slot, and the actual dense standard source map
extends this to all tensor factors. No real-density claim is used.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open Gaussian
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem symmetric_multilinear_eq_zero_of_standard_diagonal (S : StandardSubspace H)
    (n : ℕ) (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) ℂ)
    (hM : MultilinearPermutationInvariant M)
    (hd : ∀ x : S.toClosedSubmodule, M (fun _ => (x : H)) = 0) : M = 0 := by
  classical
  let N := (M.restrictScalars ℝ).compContinuousLinearMap
    (fun _ => (standardRealInclusion S).toContinuousLinearMap)
  have hN : N = 0 := RealPolarization.symmetric_multilinear_eq_zero_of_diagonal n N
    (fun e v => hM e (fun i => (v i : H))) hd
  have hreal (v : Fin n → S.toClosedSubmodule) : M (fun i => (v i : H)) = 0 :=
    congrArg (fun Q : ContinuousMultilinearMap ℝ (fun _ : Fin n => S.toClosedSubmodule) ℂ => Q v) hN
  have hcomplex (v : Fin n → StandardSource S) :
      M (fun i => standardSourceMap S (v i)) = 0 := by
    change M ((fun i => ((v i).re : H)) + (fun i => Complex.I • ((v i).im : H))) = 0
    rw [M.map_add_univ]
    apply Finset.sum_eq_zero
    intro s _
    let w : Fin n → S.toClosedSubmodule := fun i => if i ∈ s then (v i).re else (v i).im
    let c : Fin n → ℂ := fun i => if i ∈ s then 1 else Complex.I
    have he : s.piecewise (fun i => ((v i).re : H))
        (fun i => Complex.I • ((v i).im : H)) = fun i => c i • (w i : H) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, c, w, hi]
    rw [he, M.map_smul_univ, hreal, smul_zero]
  have hdense := DenseRange.piMap (fun _ : Fin n => standardSourceMap_denseRange S)
  apply ContinuousMultilinearMap.ext
  have heq : (fun v => M (Pi.map (fun _ : Fin n => standardSourceMap S) v)) =
      fun _ => (0 : ℂ) := funext hcomplex
  have h := hdense.equalizer M.cont continuous_const heq
  exact congrFun h

omit [CompleteSpace H] in
theorem symmetricTensor_eq_zero_of_standard_diagonal (S : StandardSubspace H)
    (n : ℕ) (x : SymmetricTensorPower H n)
    (hx : ∀ v : S.toClosedSubmodule, inner ℂ x (pureSymmetricTensor H n (v : H)) = 0) :
    x = 0 := by
  have hM := symmetric_multilinear_eq_zero_of_standard_diagonal S n
    (symmetricTensorScalarForm H n x) (symmetricTensorScalarForm_invariant H n x) hx
  apply Subtype.ext
  apply eq_zero_of_inner_mixedTensor_zero H n (x : HilbertTensorPower H n)
  intro v
  exact congrArg (fun M : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) ℂ => M v) hM

end VacuumBellSeparation.Fock
