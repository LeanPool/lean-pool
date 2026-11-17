/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CanonicalRealsSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CanonicalOmegaSyntax
public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeSyntax
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleGroundReals

/-!
# Canonical Reals Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def canonicalReals (r : ℕ) : SentenceForm :=
  .ex (.conj (canonicalOmega 0) (FullSetForcing.ownPower 0 (r+1)))

theorem canonicalReals_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hw : ZFSet.omega.{u} ∈ M)
    (r : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (canonicalReals r).Sat (M : Set ZFSet) e ↔ e r = groundReals M := by
  have hc (w : ZFSet.{u}) (hwM : w ∈ M) : ∀ i, cons w e i ∈ M := by
    intro i
    cases i
    · exact hwM
    · exact he _
  have hpower : (FullSetForcing.ownPower 0 (r+1)).Sat (M : Set ZFSet) (cons ZFSet.omega e) ↔
      e r = groundReals M := by
    rw [FullSetForcing.ownPower_spec M hM 0 (r+1) _ (hc _ hw)]
    simp only [cons_succ,cons_zero]
    constructor
    · intro h
      exact ZFSet.ext fun x => (h x).trans (mem_groundReals M x).symm
    · intro h x
      rw [h,mem_groundReals]
  change (∃ w ∈ M, (canonicalOmega 0).Sat (M : Set ZFSet) (cons w e) ∧
    (FullSetForcing.ownPower 0 (r+1)).Sat (M : Set ZFSet) (cons w e)) ↔ _
  constructor
  · rintro ⟨w,hwM,hwS,hp⟩
    obtain rfl := (canonicalOmega_spec M hM hw 0 _ (hc w hwM)).mp hwS
    exact hpower.mp hp
  · intro h
    exact ⟨_,hw,(canonicalOmega_spec M hM hw 0 _ (hc _ hw)).mpr rfl,hpower.mpr h⟩

theorem groundReals_between (M N : ZFSet.{u}) (hN : Transitive N)
    (hNM : N ⊆ M) (hR : groundReals M ∈ N) : groundReals N = groundReals M := by
  apply ZFSet.ext; intro x
  rw [mem_groundReals,mem_groundReals]
  exact ⟨fun hx => ⟨hNM hx.1,hx.2⟩,
    fun hx => ⟨hN _ hR x ((mem_groundReals M x).mpr hx),hx.2⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
