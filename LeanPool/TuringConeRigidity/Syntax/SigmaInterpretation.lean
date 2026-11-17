/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaInterpretation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.MembershipInterpretation
public import LeanPool.TuringConeRigidity.Representation.GroundInclusion

/-!
# Sigma Interpretation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- Translate a sigma formula into full membership-formula syntax. -/
def SigmaFormula.toMembership : SigmaFormula → RecursiveNames.Formula
  | .bounded φ => φ.toMembership
  | .existsSet φ => .existsSet φ.toMembership

theorem SigmaFormula.realize_toMembership (φ : SigmaFormula) (M : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) :
    φ.toMembership.Realize (M : Set ZFSet.{u}) e ↔ φ.Realize M e := by
  induction φ generalizing e with
  | bounded φ => exact φ.realize_toMembership M e
  | existsSet φ ih =>
    have hc (x : ZFSet.{u}) : (fun n => if n = 0 then x else e (n-1)) = cons x e := by
      funext n; cases n <;> simp [cons]
    simp only [toMembership,RecursiveNames.Formula.Realize,SigmaFormula.Realize,hc]
    exact exists_congr (fun x => and_congr_right (fun _ => ih (cons x e)))

/-- The model admits separation for existential-prefix sigma formulas with model parameters. -/
def SigmaSeparation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) →
    ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x e)

theorem SigmaSeparation.bounded {M : ZFSet.{u}} (h : SigmaSeparation M) : Separation M :=
  fun φ e he a ha => h (.bounded φ) e he a ha

theorem SigmaFormula.upward (φ : SigmaFormula) (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hMN : M ⊆ N)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.Realize M e → φ.Realize N e := by
  induction φ generalizing e with
  | bounded φ =>
    exact fun h => (φ.absolute N hN e (fun i => hMN (he i))).mpr
      ((φ.absolute M hM e he).mp h)
  | existsSet φ ih =>
    rintro ⟨x,hx,hφ⟩
    exact ⟨x,hMN hx,ih (cons x e) (fun i => by cases i <;> simp [cons,he,hx]) hφ⟩

theorem ground_sigma_upward (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : Union M)
    (hPow : PowerSet M) (hS : SigmaSeparation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.Realize M e → φ.Realize (genericExtensionSet M p G) e :=
  φ.upward M _ hM (genericExtensionSet_transitive M p hM G)
    (ground_inclusion_set M p hM hP hU hPow hS.bounded hR hI hp G hG) e he

end TuringRigidity.BoundedSetTheory

end OAI
