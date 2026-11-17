/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformOmegaLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeOmegaLevels

/-!
# Uniform Omega Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem ordinal_le_internal {M : ZFSet.{u}} (hM : Transitive M)
    {a b : Ordinal.{u}} (ha : a.toZFSet ∈ M) (hb : b ≤ a) : b.toZFSet ∈ M := by
  exact ordinal_toZFSet_mem_of_le hM ha hb

theorem uniform_omega_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      ∀ c ≤ a, c.toZFSet ∈ level (groundReals M) δ ∧
        (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) δ ∧
        OmegaPowerCertificates (level (groundReals M) δ) c.toZFSet ∧
        ∀ z ∈ level (groundReals M) δ,
          omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
            (cons z (fun _ => c.toZFSet)) ↔ z = (Ordinal.omega0 ^ c).toZFSet := by
  exact omega_certificates_at_levels_uniform M hM hT a ha

end TuringRigidity.OrdinalArithmetic

end OAI
