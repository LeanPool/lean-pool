/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/BindCanonicalArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CanonicalAdditionSyntax

/-!
# Bind Canonical Arithmetic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

def squareFormula (w d : ℕ) : Formula :=
  .conj (.allMem d (.existsMem (w+1) (.existsMem (w+2) (.orderedPair 2 1 0))))
    (.allMem w (.allMem (w+1) (.existsMem (d+2) (.orderedPair 0 2 1))))

theorem squareFormula_spec (w d : ℕ) (e : ℕ → ZFSet.{u}) :
    (squareFormula w d).Eval e ↔ e d = ZFSet.prod (e w) (e w) := by
  simp only
    [squareFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h1,h2⟩
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      exact ZFSet.mem_prod.mpr (h1 x hx)
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
      obtain ⟨z,hz,rfl⟩ := h2 a ha b hb
      exact hz
  · intro h
    rw [h]
    exact ⟨fun _ hx => ZFSet.mem_prod.mp hx,
      fun a ha b hb => ⟨ZFSet.pair a b,ZFSet.pair_mem_prod.mpr ⟨ha,hb⟩,rfl⟩⟩

noncomputable def bindArithmetic (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalOmega 0)
    (.ex (.conj (fromBounded (squareFormula 1 0))
      (.ex (.conj (fromBounded (additionSystemFormula 2 1 0)) p)))))

theorem bindArithmetic_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hw : ZFSet.omega.{u} ∈ M) (hd : pairNumbers.{u} ∈ M) (ha : additionSet.{u} ∈ M)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (bindArithmetic p).Sat (M : Set ZFSet) e ↔
      p.Sat (M : Set ZFSet) (cons additionSet (cons pairNumbers (cons ZFSet.omega e))) := by
  have hc (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x e i ∈ M := by
    intro i
    cases i
    · exact hx
    · exact he _
  have hwf (x : ZFSet.{u}) (hx : x ∈ M) := canonicalOmega_spec M hM hw 0 (cons x e) (hc x hx)
  have hdf (d : ZFSet.{u}) (hdM : d ∈ M) :
      (fromBounded (squareFormula 1 0)).Sat (M : Set ZFSet) (cons d (cons ZFSet.omega e)) ↔ d =
        pairNumbers := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by
        intro i
        rcases i with _|_|i
        · exact hdM
        · exact hw
        · exact he i),squareFormula_spec]
    rfl
  have haf (a : ZFSet.{u}) (haM : a ∈ M) :
      (fromBounded (additionSystemFormula 2 1 0)).Sat (M : Set ZFSet)
        (cons a (cons pairNumbers (cons ZFSet.omega e))) ↔ a = additionSet := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by
        intro i
        rcases i with _|_|_|i
        · exact haM
        · exact hd
        · exact hw
        · exact he i)]
    exact additionSystemFormula_unique 2 1 0 _ rfl rfl
  change (∃ w ∈ M, (canonicalOmega 0).Sat (M : Set ZFSet) (cons w e) ∧
    ∃ d ∈ M, (fromBounded (squareFormula 1 0)).Sat (M : Set ZFSet) (cons d (cons w e)) ∧
      ∃ a ∈ M, (fromBounded (additionSystemFormula 2 1 0)).Sat (M : Set ZFSet) (cons a (cons d
        (cons w e))) ∧
        p.Sat (M : Set ZFSet) (cons a (cons d (cons w e)))) ↔ _
  constructor
  · rintro ⟨w,hwM,hwS,d,hdM,hdS,a,haM,haS,hp⟩
    obtain rfl := (hwf w hwM).mp hwS
    obtain rfl := (hdf d hdM).mp hdS
    obtain rfl := (haf a haM).mp haS
    exact hp
  · intro hp
    exact ⟨_,hw,(hwf _ hw).mpr rfl,_,hd,(hdf _ hd).mpr rfl,_,ha,(haf _ ha).mpr rfl,hp⟩

end TuringRigidity.RelativeConstructible

end OAI
