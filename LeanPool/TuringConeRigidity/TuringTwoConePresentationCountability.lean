/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePresentationCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePersistentPresentation
public import LeanPool.TuringConeRigidity.TuringConePresentationCountability

/-!
# Countability from arithmetic two-cone graph presentations

The joined graph determines the actual partial isomorphism, including when
columns repeat. Persistent maps have graphs recursive in H^(11), so there
are at most countably many of them for a fixed presented ideal and bases.
The arithmetic restriction endpoint does not assume its larger map persistent.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions
open ConePersistence (Cone)

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The Boolean oracle coding the two-cone isomorphism graph in its column presentation. -/
def graphOracle {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier)
    (ρ : Cone I a ≃o Cone I b) : Oracle := fun n => decide (Graph ρ hpres ha n)

/-- Joined inputs still contain every source point, without unique indices. -/
theorem graphOracle_injective {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier) :
    Function.Injective (graphOracle (b := b) hpres ha) := by
  intro ρ σ he
  apply OrderIso.ext
  funext x
  obtain ⟨n, hn⟩ := (hpres x.val).mp x.property.1
  obtain ⟨j, hj⟩ := (hpres (ρ x).val).mp (ρ x).property.1
  have hx : presentationEntry hpres ha n = x := by
    apply Subtype.ext
    change a ⊔ degree (columns H n) = x.val
    rw [hn, sup_eq_right.mpr x.property.2]
  have hp : Graph ρ hpres ha (Nat.pair n j) := by
    simp only [Graph, Nat.unpair_pair, hx, hj]
  have hq : Graph σ hpres ha (Nat.pair n j) := by
    by_contra hn
    have hh := congrFun he (Nat.pair n j)
    simp only [graphOracle, decide_eq_true hp, decide_eq_false hn] at hh
    cases hh
  apply Subtype.ext
  simpa only [Graph, Nat.unpair_pair, hx, hj] using hq.symm

theorem graphOracle_reduces {I : CountableIdeal} {a b : Degree} {H Y : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier)
    (ρ : Cone I a ≃o Cone I b) (h : RecursivePred Y (Graph ρ hpres ha)) :
    Reduces (graphOracle hpres ha ρ) Y := by
  apply RecursiveIn.iff_nat.mpr
  exact h.of_eq (fun n => by simp [oracleFunction, graphOracle])

theorem recursive_maps_countable {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier) (Y : Oracle) :
    {ρ : Cone I a ≃o Cone I b | RecursivePred Y (Graph ρ hpres ha)}.Countable := by
  apply ((countable_reduces Y).preimage (graphOracle_injective hpres ha)).mono
  intro ρ hρ
  exact graphOracle_reduces hpres ha ρ hρ

theorem arithmetic_maps_countable {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier) :
    {ρ : Cone I a ≃o Cone I b |
      ∃ n, RecursivePred (iterate H n) (Graph ρ hpres ha)}.Countable := by
  have he : {ρ : Cone I a ≃o Cone I b |
      ∃ n, RecursivePred (iterate H n) (Graph ρ hpres ha)} =
      ⋃ n : ℕ, {ρ : Cone I a ≃o Cone I b |
        RecursivePred (iterate H n) (Graph ρ hpres ha)} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [he]
  exact Set.countable_iUnion (fun n => recursive_maps_countable hpres ha (iterate H n))

/-- No extra arithmetic-presentation or prescribed-extension hypothesis. -/
theorem persistent_maps_countable (I : CountableIdeal) (a b : Degree)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    {ρ : Cone I a ≃o Cone I b | TwoConePersistence.Persistent I ρ}.Countable := by
  obtain ⟨H, hpres⟩ := ConePresentation.presentation_exists I
  have ha : a ∈ I.carrier := I.lower (degree_le_jump a) hza
  apply (recursive_maps_countable hpres ha (iterate H 11)).mono
  intro ρ hp
  exact (arithmetic_presentation_of_persistent ρ hp hpres ha hza hzb).2

/-- Keep both extension agreements and an arithmetic graph for the restriction.
Neither the larger map nor the resulting restriction is assumed persistent. -/
theorem arithmetic_restriction {I J K : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (τ : Cone K a ≃o Cone K b)
    (hIK : I.carrier ⊆ K.carrier) (he : TwoConePersistence.Extends hIK ρ τ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J))
    {H : Oracle} (hpres : ConePresentation.Presented J H) (ha : a ∈ J.carrier)
    (hH' : degree (jump H) ∈ K.carrier) :
    ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Extends hJK σ τ ∧
      RecursivePred (iterate H 11) (Graph σ hpres ha) := by
  obtain ⟨σ, hρ, hτ⟩ := TwoConePersistentLocality.restrict_extension ρ τ hIK he
    hza hzb hIJ hJK hjump
  exact ⟨σ, hρ, hτ,
    (arithmetic_presentation_of_extension σ τ hJK hτ hpres ha (hIJ hza) (hIJ hzb) hH').2⟩

end
end OAI.TuringRigidity.TwoConePresentation
