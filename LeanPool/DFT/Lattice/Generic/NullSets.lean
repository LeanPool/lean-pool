/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.Krylov
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Zero sets of polynomials are null; generic Hohenberg–Kohn (measure version)

* `generic_hk_ae`: under (H*), non-uniquely-v-representable potentials lie in a closed, nowhere
  dense, Lebesgue-null set.
-/

@[expose] public section

namespace DFT

section

open MeasureTheory MvPolynomial

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn modulo trivial shifts, measure version (conditional on (H*)).** -/
theorem generic_hk_ae_mod {Tr : Set (V → ℝ)} {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} (hR : RigidMod Tr n) (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      {v | NonUVMod Tr H0 n v} ⊆ Z := by
  obtain ⟨Q, hQ, hvanish⟩ := exists_krylov_certificate hH0 hR ord hstar
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  exact ⟨_, hcl, hint, MvPolynomial.volume_setOfPred_eval_eq_zero Q hQ, hvanish⟩

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn, measure version (conditional on (H*)).** Non-uniquely-v-representable
potentials lie in a closed, nowhere dense, Lebesgue-null set. -/
theorem generic_hk_ae {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hR : Rigid n)
    (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧ {v | NonUV H0 n v} ⊆ Z :=
  generic_hk_ae_mod (Tr := constPot) hH0 hR ord hstar

end

end DFT
