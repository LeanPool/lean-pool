/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/FullNativePersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.FullSetTruth
public import LeanPool.TuringConeRigidity.Representation.SourceTNativeComparison

/-!
# Full Native Persistence
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm SetModelSatisfaction SetDegreeDecoding SetModelReals
open PersistentRestrictions ArithmeticTree
universe u

/-- Translate internal formula syntax into full set-theoretic sentence syntax. -/
noncomputable def fromInternal : InternalFormula → SentenceForm
  | .bounded p => fromBounded p
  | .conj p q => .conj (fromInternal p) (fromInternal q)
  | .neg p => .neg (fromInternal p)
  | .existsSet p => .ex (fromInternal p)

theorem internal_sat (p : InternalFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromInternal p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | conj p q hp hq => exact and_congr (hp e) (hq e)
  | neg p hp => exact not_congr (hp e)
  | existsSet p hp =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => hp (cons x e))

theorem full_native_persistence_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ SetModelReals.reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ SetModelReals.reals M, ∀ B ∈ SetModelReals.reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M)
    (hct : SetModelCountability.InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    (fromInternal persistenceFormula).Sat (M : Set ZFSet)
      (cons D (cons L (cons (idealSet I) (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔
      Persistent I ρ :=
  (internal_sat persistenceFormula M _).trans
    (native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz)

theorem generic_full_native_truth (M : ZFSet.{u}) (hM : Transitive M) (hV : Valid M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (D L : ZFSet.{u}) (I : CountableIdeal) (ρ : I ≃o I)
    (hvals : (fun i => (e i).val G.carrier) =
      cons D (cons L (cons (idealSet I) (cons (automorphismSet ρ) (fun _ => ZFSet.omega)))))
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ SetModelReals.reals (genericExtensionSet M c G.carrier), x =
      degreeSet (degree A))
    (hL : ∀ A ∈ SetModelReals.reals (genericExtensionSet M c G.carrier),
      ∀ B ∈ SetModelReals.reals (genericExtensionSet M c G.carrier),
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (hct : SetModelCountability.InternallyCountable (genericExtensionSet M c G.carrier) (idealSet
      I))
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    Persistent I ρ ↔ ∃ p ∈ G.carrier, Forces M e (fromInternal persistenceFormula) p := by
  let N := genericExtensionSet M c G.carrier
  have hN := genericExtensionSet_transitive M c hM G.carrier
  have hTN := extension_sourceT M hM (hV.sourceT hM ⟨c,hc⟩) hc hoM ho G hG ht
  have hm (i : ℕ) : cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega)))) i ∈ N := by
    rw [←hvals]
    exact (mem_extensionSet M c G.carrier _).mpr ⟨e i,he i,rfl⟩
  have hn := full_native_persistence_iff N hN hTN (hm 0) (hm 1) hD hL I (hm 2) hct ρ (hm 3) hz
  have hf := full_truth M hM hV hc hoM ho G hG (fromInternal persistenceFormula) e he
  rw [hvals] at hf
  exact hn.symm.trans hf

end TuringRigidity.FullSetForcing

end OAI
