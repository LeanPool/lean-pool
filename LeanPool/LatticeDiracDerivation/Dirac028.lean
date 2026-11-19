/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac028.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac027

/-!
# DIRAC-028: infinitesimal Wigner/Thomas rotation

Two non-collinear boosts do not commute.  The antisymmetric mixed term in
their second-order composition is one half of their commutator.  This file
proves that the inherited boost algebra turns that term into a spatial
rotation with the Thomas factor `1/2`, and proves the factor is unique on a
nonzero native witness.

This is the local/BCH result.  No exact finite Wigner-angle claim is made.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

def boostCommutator01 (z : Cell4) : Cell4 :=
  fun component =>
    standardC19BoostGenerator 0
        (standardC19BoostGenerator 1 z) component -
      standardC19BoostGenerator 1
        (standardC19BoostGenerator 0 z) component

def boostCommutator12 (z : Cell4) : Cell4 :=
  fun component =>
    standardC19BoostGenerator 1
        (standardC19BoostGenerator 2 z) component -
      standardC19BoostGenerator 2
        (standardC19BoostGenerator 1 z) component

def boostCommutator20 (z : Cell4) : Cell4 :=
  fun component =>
    standardC19BoostGenerator 2
        (standardC19BoostGenerator 0 z) component -
      standardC19BoostGenerator 0
        (standardC19BoostGenerator 2 z) component

def mixedWignerTerm01 (z : Cell4) : Cell4 :=
  fun component => (1 / 2 : ℂ) * boostCommutator01 z component

def mixedWignerTerm12 (z : Cell4) : Cell4 :=
  fun component => (1 / 2 : ℂ) * boostCommutator12 z component

def mixedWignerTerm20 (z : Cell4) : Cell4 :=
  fun component => (1 / 2 : ℂ) * boostCommutator20 z component

theorem mixed_wigner_term_01_is_half_rotation (z : Cell4) :
    mixedWignerTerm01 z =
      fun component => (-I / 2) * standardCubeSpin 2 z component := by
  funext component
  unfold mixedWignerTerm01 boostCommutator01
  rw [congrFun (boost_commutator_01 z) component]
  ring

theorem mixed_wigner_term_12_is_half_rotation (z : Cell4) :
    mixedWignerTerm12 z =
      fun component => (-I / 2) * standardCubeSpin 0 z component := by
  funext component
  unfold mixedWignerTerm12 boostCommutator12
  rw [congrFun (boost_commutator_12 z) component]
  ring

theorem mixed_wigner_term_20_is_half_rotation (z : Cell4) :
    mixedWignerTerm20 z =
      fun component => (-I / 2) * standardCubeSpin 1 z component := by
  funext component
  unfold mixedWignerTerm20 boostCommutator20
  rw [congrFun (boost_commutator_20 z) component]
  ring

theorem boost_commutator_01_witness_nonzero :
    boostCommutator01 cell4Basis0 1 = -I / 2 := by
  unfold boostCommutator01
  rw [congrFun (boost_commutator_01 cell4Basis0) 1]
  simp [standardCubeSpin, standardCubePlaneBivector,
    standardCubeGamma, standardDiracAlphaY,
    standardDiracAlphaZ, cell4Basis0]
  ring

theorem thomas_half_factor_unique (r : ℂ)
    (h : ∀ z, (fun component => r * boostCommutator01 z component) =
      fun component => (1 / 2 : ℂ) * boostCommutator01 z component) :
    r = 1 / 2 := by
  have hw := congrFun (h cell4Basis0) 1
  rw [boost_commutator_01_witness_nonzero] at hw
  have hI : I ≠ (0 : ℂ) := Complex.I_ne_zero
  apply (mul_right_cancel₀ hI)
  linear_combination (-2 : ℂ) * hw

theorem sequential_boost_mixed_decomposition (z : Cell4) :
    (fun component =>
      standardC19BoostGenerator 0
          (standardC19BoostGenerator 1 z) component) =
      fun component =>
        (1 / 2 : ℂ) *
            (standardC19BoostGenerator 0
                (standardC19BoostGenerator 1 z) component +
              standardC19BoostGenerator 1
                (standardC19BoostGenerator 0 z) component) +
          mixedWignerTerm01 z component := by
  funext component
  simp [mixedWignerTerm01, boostCommutator01]
  ring

structure Dirac028WignerThomasCertificate : Prop where
  previousGate : Dirac027PauliLubanskiCertificate
  threeAxisHalfRotation :
    (∀ z, mixedWignerTerm01 z =
      fun component => (-I / 2) * standardCubeSpin 2 z component) ∧
    (∀ z, mixedWignerTerm12 z =
      fun component => (-I / 2) * standardCubeSpin 0 z component) ∧
    (∀ z, mixedWignerTerm20 z =
      fun component => (-I / 2) * standardCubeSpin 1 z component)
  factorIsUnique : ∀ r : ℂ,
    (∀ z, (fun component => r * boostCommutator01 z component) =
      fun component => (1 / 2 : ℂ) * boostCommutator01 z component) →
        r = 1 / 2
  productDecomposition : ∀ z,
    (fun component =>
      standardC19BoostGenerator 0
          (standardC19BoostGenerator 1 z) component) =
      fun component =>
        (1 / 2 : ℂ) *
            (standardC19BoostGenerator 0
                (standardC19BoostGenerator 1 z) component +
              standardC19BoostGenerator 1
                (standardC19BoostGenerator 0 z) component) +
          mixedWignerTerm01 z component

theorem dirac028_wigner_thomas_half_factor :
    Dirac028WignerThomasCertificate where
  previousGate := dirac027_pauli_lubanski_spin_half
  threeAxisHalfRotation :=
    ⟨mixed_wigner_term_01_is_half_rotation,
      mixed_wigner_term_12_is_half_rotation,
      mixed_wigner_term_20_is_half_rotation⟩
  factorIsUnique := thomas_half_factor_unique
  productDecomposition := sequential_boost_mixed_decomposition

end
end LeanDirac
