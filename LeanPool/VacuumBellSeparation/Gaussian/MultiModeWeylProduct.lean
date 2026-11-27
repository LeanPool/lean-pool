/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeSplit

/-!
# Actual mode factorization of the oscillator Weyl operator

The bounded bilinear maps agree on two total coherent families. Their
extension proves the operator product action on all square-summable vectors,
then the number-basis diagonal factors exactly. No tensor implementation
is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- The actual multi-mode Weyl operator acts as the product of the actual
one-mode and tail Weyl operators on every genuine product vector. -/
theorem multiOscillatorWeyl_product {m : ℕ} (z : ℂ) (w : MultiModePhaseSpace m)
    (x : OscillatorSpace) (y : MultiModeOscillatorSpace m) :
    multiOscillatorWeyl (multiPhaseCons z w)
      (l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm x y) =
      l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
        (oscillatorWeyl z x) (multiOscillatorWeyl w y) := by
  let P := l2ProductContinuous (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
  let A := multiOscillatorWeyl (multiPhaseCons z w)
  let L : OscillatorSpace →L[ℂ] MultiModeOscillatorSpace m →L[ℂ]
      MultiModeOscillatorSpace (m + 1) :=
    (ContinuousLinearMap.compL ℂ (MultiModeOscillatorSpace m)
      (MultiModeOscillatorSpace (m + 1)) (MultiModeOscillatorSpace (m + 1)) A).comp P
  let M : OscillatorSpace →L[ℂ] MultiModeOscillatorSpace m →L[ℂ]
      MultiModeOscillatorSpace (m + 1) :=
    ((P.comp (oscillatorWeyl z)).flip.comp (multiOscillatorWeyl w)).flip
  have hLM : L = M := by
    apply continuousBilinear_eq_of_dense_spans coherentVector (multiCoherentVector (m := m))
      coherentVector_dense_span (multiCoherentVector_dense_span m)
    intro a b
    change multiOscillatorWeyl (multiPhaseCons z w)
        (l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
          (coherentVector a) (multiCoherentVector b)) =
      l2ProductVector (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).symm
        (oscillatorWeyl z (coherentVector a)) (multiOscillatorWeyl w (multiCoherentVector b))
    rw [← multiCoherentVector_cons, multiOscillatorWeyl_coherentVector, multiPhaseCons_add,
      weylPhase_multiPhaseCons, multiCoherentVector_cons, oscillatorWeyl_coherentVector,
      multiOscillatorWeyl_coherentVector, l2ProductVector_smul_smul]
  exact congrArg (fun f : OscillatorSpace →L[ℂ] MultiModeOscillatorSpace m →L[ℂ]
    MultiModeOscillatorSpace (m + 1) => f x y) hLM

/-- The number-basis diagonal factors through the actual product Weyl action. -/
theorem multiOscillatorWeyl_number_diagonal_cons {m : ℕ} (z : ℂ) (w : MultiModePhaseSpace m)
    (n : ℕ) (k : Fin m → ℕ) :
    inner ℂ (multiModeNumberBasis (m + 1) (Fin.cons n k))
      (multiOscillatorWeyl (multiPhaseCons z w) (multiModeNumberBasis (m + 1) (Fin.cons n k))) =
      inner ℂ (numberBasis n) (oscillatorWeyl z (numberBasis n)) *
        inner ℂ (multiModeNumberBasis m k) (multiOscillatorWeyl w (multiModeNumberBasis m k)) := by
  rw [multiModeNumberBasis_cons, multiOscillatorWeyl_product, inner_l2ProductVector]

theorem multiOscillatorWeyl_zero (m : ℕ) :
    multiOscillatorWeyl (0 : MultiModePhaseSpace m) = 1 := by
  apply continuousLinearMap_eq_of_dense_span (multiCoherentVector (m := m))
    (multiCoherentVector_dense_span m)
  intro z
  rw [multiOscillatorWeyl_coherentVector,
    weylPhase_zero_left (id : MultiModePhaseSpace m → MultiModePhaseSpace m) (fun _ _ => rfl),
    one_smul, zero_add, one_apply_eq_self]

/-- Full factorization of the actual Weyl number-basis diagonal over all modes. -/
theorem multiOscillatorWeyl_number_diagonal {m : ℕ} (z : MultiModePhaseSpace m)
    (k : Fin m → ℕ) :
    inner ℂ (multiModeNumberBasis m k) (multiOscillatorWeyl z (multiModeNumberBasis m k)) =
      ∏ j, inner ℂ (numberBasis (k j)) (oscillatorWeyl (z j) (numberBasis (k j))) := by
  induction m with
  | zero =>
    have hz : z = 0 := Subsingleton.elim _ _
    rw [hz, multiOscillatorWeyl_zero]
    simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K,
      (multiModeNumberBasis 0).orthonormal.norm_eq_one, RCLike.ofReal_one, one_pow,
      Fin.prod_univ_zero]
  | succ m ih =>
    let w : MultiModePhaseSpace m := WithLp.toLp 2 (Fin.tail (fun j => z j))
    have hz : multiPhaseCons (z 0) w = z := by
      ext i
      induction i using Fin.cases <;> rfl
    calc
      inner ℂ (multiModeNumberBasis (m + 1) k)
          (multiOscillatorWeyl z (multiModeNumberBasis (m + 1) k)) =
        inner ℂ (numberBasis (k 0)) (oscillatorWeyl (z 0) (numberBasis (k 0))) *
          inner ℂ (multiModeNumberBasis m (Fin.tail k))
            (multiOscillatorWeyl w (multiModeNumberBasis m (Fin.tail k))) := by
        simpa only [Fin.cons_self_tail, hz] using
          multiOscillatorWeyl_number_diagonal_cons (z 0) w (k 0) (Fin.tail k)
      _ = _ := by
        rw [ih, Fin.prod_univ_succ]
        rfl

end VacuumBellSeparation.Gaussian
