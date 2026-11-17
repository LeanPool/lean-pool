/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeEnumerationConstruction
public import LeanPool.TuringConeRigidity.TuringTwoConeEnumerationTransport
public import LeanPool.TuringConeRigidity.TuringTwoConePersistentLocality

/-!
# One arithmetic graph for a partial two-cone isomorphism

The indexed graph uses all columns, by joining the source base to each input:
Graph rho H (i,j) means rho(a join deg(H_i)) = deg(H_j). Every source point
occurs among these joined inputs, so the graph determines the original map.
A bound on the image of H' yields a single Sigma-5 predicate for all pairs.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation
open BoundedDecoding PersistentRestrictions
open ConePersistence (Cone)
open TwoConeIdealCodes (val)

noncomputable section

/-- The ideal cone element obtained by joining the base with the degree of the selected oracle
column. -/
def idealEntry {J : DegreeIdeal} (a : J) (H : Oracle)
    (hH : degree H ∈ J.carrier) (n : ℕ) : Set.Ici a :=
  ⟨⟨a.val ⊔ degree (columns H n), J.join_mem a.property
    (J.lower (CodingExtraction.column_projection_reduces H n) hH)⟩,
    Set.mem_Ici.mpr (show a.val ≤ a.val ⊔ degree (columns H n) from le_sup_left)⟩

/-- The graph of the ideal cone isomorphism on base-joined input columns and represented
output columns. -/
def IdealGraph {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (H : Oracle) (hH : degree H ∈ I.carrier)
    (v : ℕ) : Prop :=
  val (ρ (idealEntry a H hH (Nat.unpair v).1)) = degree (columns H (Nat.unpair v).2)

/-- A uniform arithmetic graph, not merely separate bounds on its values. -/
theorem graph_sigma_of_bound {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (H : Oracle) (hH : degree H ∈ I.carrier)
    (haH : degreeJump a.val ≤ degree H) (z : Set.Ici a) (hz : val z = degree (jump H))
    (Y : Oracle) (hHY : Reduces H Y) (hbound : val (ρ z) ≤ degree Y) :
    Sigma Y 5 (IdealGraph ρ H hH) ∧
      RecursivePred (iterate Y 5) (IdealGraph ρ H hH) := by
  obtain ⟨A, hA⟩ := degree_surjective a.val
  have hAH : Reduces (jump A) H := by
    change degreeJump (degree A) ≤ degree H
    rw [hA]
    exact haH
  have hc : ∃ c : ConeEnumeration.Enumeration a.val,
      (∀ k, c.output k = a.val ⊔ degree (columns H k)) ∧
      ConeRelativeCoding.RelationAbove c.successor a.val ∧
      ConeRelativeCoding.RelationAbove c.payload a.val ∧
      RelationBelow c.successor (degree (jump H)) ∧
      RelationBelow c.payload (degree (jump H)) := by
    exact hA ▸ TwoConeEnumeration.enumeration_exists A H hAH
  obtain ⟨c, hout, haS, haP, hS, hP⟩ := hc
  obtain ⟨d, hdout, _, _, hdS, hdP⟩ := TwoConeEnumeration.transport_enumeration ρ c z
    haS haP (hz.symm ▸ hS) (hz.symm ▸ hP) (idealEntry a H hH)
    (fun n => (hout n).symm)
  have hg := ConeEnumeration.graph_sigma ((TwoConeIdealCodes.base_le (ρ z)).trans hbound)
    hHY d (hdS.mono hbound) (hdP.mono hbound)
  have h : Sigma Y 5 (IdealGraph ρ H hH) := hg.congr (fun v => by
    simp only [hdout, IdealGraph])
  exact ⟨h, form_recursive h⟩

/-- Joined entries cover the entire source cone, even with repeated columns. -/
def presentationEntry {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier) (n : ℕ) : Cone I a :=
  ⟨a ⊔ degree (columns H n), I.join_mem ha ((hpres _).mpr ⟨n, rfl⟩), le_sup_left⟩

/-- The graph of the countable-ideal cone isomorphism in its base-joined column presentation. -/
def Graph {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (ρ : Cone I a ≃o Cone I b) (hpres : ConePresentation.Presented I H)
    (ha : a ∈ I.carrier) (v : ℕ) : Prop :=
  (ρ (presentationEntry hpres ha (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

/-- The graph of any extension agrees on all the old joined column inputs. -/
theorem graph_agreement {I K : CountableIdeal} {a b : Degree} {H : Oracle}
    (ρ : Cone I a ≃o Cone I b) (σ : Cone K a ≃o Cone K b)
    (hIK : I.carrier ⊆ K.carrier) (he : TwoConePersistence.Extends hIK ρ σ)
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier) (hb : b ∈ I.carrier)
    (hH : degree H ∈ K.carrier) (v : ℕ) :
    IdealGraph (TwoConePersistentLocality.lift σ (hIK ha) (hIK hb)) H hH v ↔
      Graph ρ hpres ha v := by
  let x := presentationEntry hpres ha (Nat.unpair v).1
  change (σ ⟨x.val, hIK x.property.1, x.property.2⟩).val =
    degree (columns H (Nat.unpair v).2) ↔
      (ρ x).val = degree (columns H (Nat.unpair v).2)
  exact Iff.of_eq (congrArg (fun d : Degree => d = degree (columns H (Nat.unpair v).2))
    (he x))

end
end OAI.TuringRigidity.TwoConePresentation
