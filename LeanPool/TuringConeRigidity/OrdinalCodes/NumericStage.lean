/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericBinding

/-!
# Numeric Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

def stageSlots (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    match n / 2 with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 3 | _ => 2
  else match n / 2 with | 0 => 3 | 1 => 1 | _ => 0

def stageInputs (e : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u} :=
  cons (e 0) (cons (e 1) (cons (e 2) (cons ZFSet.omega
    (fun _ => ZFSet.prod ZFSet.omega ZFSet.omega))))

theorem stageSlots_comp (B : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega)
      (cons ZFSet.omega e))) ∘ stageSlots = mix (stageInputs e) (params B) := by
  apply parity_ext
  · intro n
    rcases n with _|_|_|_|n <;> simp [stageSlots,stageInputs,mix]
  · intro n
    rcases n with _|_|n <;> simp [stageSlots,params,Nat.add_div,mix]

theorem stage_formula :
    ∃ p : SentenceForm, ∀ N : ZFSet.{u}, Transitive N →
      ZFSet.omega ∈ N → ZFSet.prod ZFSet.omega ZFSet.omega ∈ N →
      (∀ f k, finiteNaturalGraph f k ∈ N) →
      (∃ B ∈ N, PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) →
      ∀ e, (∀ i, e i ∈ N) →
        (p.Sat (N : Set ZFSet) e ↔
          SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (e 2) (e 1) (e 0)) := by
  obtain ⟨p,hp⟩ := seedBoundStage_domainDefinable.{u}
  refine ⟨bindNumbers (p.rename stageSlots),?_⟩
  intro N hN hw hs hfin hex e he
  rw [bindNumbers_spec N hN hw hs _ e he]
  have hbody (B : ZFSet.{u}) (hBN : B ∈ N)
      (hB : PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) :
      (p.rename stageSlots).Sat (N : Set ZFSet)
        (cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega
          e)))) ↔
      SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (e 2) (e 1) (e 0) := by
    rw [SentenceForm.sat_rename]
    change p.Sat (N : Set ZFSet)
      (cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e))) ∘
        stageSlots) ↔ _
    rw [stageSlots_comp]
    apply hp B (covers_of_power hfin hB) N hN
    · intro i
      rcases i with _|_|i
      · exact hw
      · exact hBN
      · exact hN _ hw _ ((mem_omega _).mpr ⟨0,rfl⟩)
    · intro i
      rcases i with _|_|_|_|i
      · exact he 0
      · exact he 1
      · exact he 2
      · exact hw
      · exact hs
  constructor
  · rintro ⟨B,hBN,hB,h⟩
    exact (hbody B hBN hB).mp h
  · intro h
    obtain ⟨B,hBN,hB⟩ := hex
    exact ⟨B,hBN,hB,(hbody B hBN hB).mpr h⟩

end TuringRigidity.NumericSyntax

end OAI
