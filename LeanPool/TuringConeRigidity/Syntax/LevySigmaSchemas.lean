/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/LevySigmaSchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.LevySigmaNormalization

/-!
# Levy Sigma Schemas
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem levy_sigma_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) :
    LevySigmaSeparation M ∧ LevySigmaReplacement M := by
  have hC := sigma_collection M hM hP hU hPow hS hR hI hAC
  have correct := LevySigma.normalize_correct M hM hP hU hS.bounded hR hI hC
  constructor
  · intro φ e he a ha
    obtain ⟨b,hb,hbdef⟩ := hS φ.normalize e he a ha
    refine ⟨b,hb,?_⟩
    intro x hx
    rw [hbdef x hx,correct φ (cons x e) (by intro i; cases i <;> simp [cons,he,hx])]
  · intro φ e he a ha htotal
    have eq (x y : ZFSet.{u}) (hx : x ∈ M) (hy : y ∈ M) :
        φ.normalize.Realize M (cons y (cons x e)) ↔ φ.Realize M (cons y (cons x e)) :=
      correct φ _ (by
        intro i
        rcases i with _ | i
        · exact hy
        rcases i with _ | i
        · exact hx
        exact he i)
    obtain ⟨b,hb,hbdef⟩ := hR φ.normalize e he a ha (by
      intro x hx
      have hxM := hM a ha x hx
      obtain ⟨y,hy,hφ,hu⟩ := htotal x hx
      exact ⟨y,hy,(eq x y hxM hy).mpr hφ,fun z hz h => hu z hz ((eq x z hxM hz).mp h)⟩)
    refine ⟨b,hb,?_⟩
    intro y hy
    rw [hbdef y hy]
    apply exists_congr; intro x
    exact and_congr_right (fun hx => eq x y (hM a ha x hx) hy)

def SigmaFormula.toLevy : SigmaFormula → LevySigma
  | .bounded φ => .bounded φ
  | .existsSet φ => .existsSet φ.toLevy

theorem SigmaFormula.realize_toLevy (φ : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.toLevy.Realize M e ↔ φ.Realize M e := by
  induction φ generalizing e with
  | bounded φ => rfl
  | existsSet φ ih =>
    simp only [toLevy,LevySigma.Realize,Realize]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

theorem LevySigmaSeparation.finitePrefix {M : ZFSet.{u}} (hS : LevySigmaSeparation M) :
  SigmaSeparation M := by
  intro φ e he a ha
  obtain ⟨b,hb,hbdef⟩ := hS φ.toLevy e he a ha
  exact ⟨b,hb,fun x hx => (hbdef x hx).trans (and_congr_right (fun _ => φ.realize_toLevy M _))⟩

theorem LevySigmaReplacement.finitePrefix {M : ZFSet.{u}} (hR : LevySigmaReplacement M) :
  SigmaReplacement M := by
  intro φ e he a ha htotal
  obtain ⟨b,hb,hbdef⟩ := hR φ.toLevy e he a ha (by
    intro x hx
    obtain ⟨y,hy,hφ,hu⟩ := htotal x hx
    exact ⟨y,hy,(φ.realize_toLevy M _).mpr hφ,fun z hz h => hu z hz ((φ.realize_toLevy M _).mp h)⟩)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy]
  apply exists_congr; intro x
  exact and_congr_right (fun _ => φ.realize_toLevy M _)

end TuringRigidity.BoundedSetTheory

end OAI
