/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePersistentPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePresentation

/-!
# Eleven-jump presentations of persistent partial two-cone maps

A larger extension containing H' already supplies the arithmetic graph of
the old map. The larger map need not be persistent, nor must its ambient
ideal contain all degrees arithmetic in H. Persistence of the old map is
one way to obtain such an extension. This separation avoids circularity in
the later countability/obstruction proof of persistent extensions.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation
open PersistentRestrictions
open ConePersistence (Cone)
open TwoConeIdealCodes (val)

noncomputable section

/-- Uniform graph control from any extension whose ideal contains H'. -/
theorem arithmetic_presentation_of_extension {I K : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (σ : Cone K a ≃o Cone K b)
    (hIK : I.carrier ⊆ K.carrier) (he : TwoConePersistence.Extends hIK ρ σ)
    {H : Oracle} (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hH' : degree (jump H) ∈ K.carrier) :
    Sigma (iterate H 6) 5 (Graph ρ hpres ha) ∧
      RecursivePred (iterate H 11) (Graph ρ hpres ha) := by
  have hb : b ∈ I.carrier := I.lower (degree_le_jump b) hzb
  have hH : degree H ∈ K.carrier := K.lower (reduces_jump H) hH'
  let α : PersistentLocality.ideal K := ⟨a, hIK ha⟩
  let β : PersistentLocality.ideal K := ⟨b, hIK hb⟩
  let τ := TwoConePersistentLocality.lift σ (hIK ha) (hIK hb)
  let zb : Cone I b := ⟨degreeJump b, hzb, degree_le_jump b⟩
  let zbK : Set.Ici β :=
    ⟨⟨degreeJump b, hIK hzb⟩, Set.mem_Ici.mpr (degree_le_jump b)⟩
  have hpre : val (τ.symm zbK) ≤ degree H := by
    change (σ.symm ⟨zb.val, hIK zb.property.1, zb.property.2⟩).val ≤ degree H
    rw [TwoConePersistence.extends_inverse he zb]
    exact ConePresentation.presentation_bound hpres (ρ.symm zb).property.1
  have haH : a ≤ degree H := ConePresentation.presentation_bound hpres ha
  let z : Set.Ici α :=
    ⟨⟨degree (jump H), hH'⟩, Set.mem_Ici.mpr (haH.trans (reduces_jump H))⟩
  have hbound : val (τ z) ≤ degree (iterate H 6) := by
    obtain ⟨X, Y, hX, hY, hXY⟩ := TwoConeIdealLocality.image_arithmetic τ zbK rfl z
    have hYH : Reduces Y (jump H) := by
      change degree Y ≤ degree (jump H)
      rw [hY]
      exact sup_le le_rfl (hpre.trans (reduces_jump H))
    rw [← hX]
    exact reduces_trans hXY (iterate_mono hYH 5)
  obtain ⟨hg, hr⟩ := graph_sigma_of_bound τ H hH
    (ConePresentation.presentation_bound hpres hza) z rfl
    (iterate H 6) (ConePresentation.reduces_iterate H 6) hbound
  have hgraph := graph_agreement ρ σ hIK he hpres ha hb hH
  exact ⟨hg.congr hgraph, Form.congr (n := 0) (s := true) hr hgraph⟩

/-- Persistence supplies the extension; no separate locality hypothesis remains. -/
theorem arithmetic_presentation_of_persistent {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    {H : Oracle} (hpres : ConePresentation.Presented I H) (ha : a ∈ I.carrier)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    Sigma (iterate H 6) 5 (Graph ρ hpres ha) ∧
      RecursivePred (iterate H 11) (Graph ρ hpres ha) := by
  obtain ⟨K, hIK, σ, hH', he⟩ := hp (degree (jump H))
  exact arithmetic_presentation_of_extension ρ σ hIK he hpres ha hza hzb hH'

/-- The same result with the base-membership proof derived from its jump. -/
theorem arithmetic_presentation {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    {H : Oracle} (hpres : ConePresentation.Presented I H)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    Sigma (iterate H 6) 5 (Graph ρ hpres (I.lower (degree_le_jump a) hza)) ∧
      RecursivePred (iterate H 11) (Graph ρ hpres (I.lower (degree_le_jump a) hza)) :=
  arithmetic_presentation_of_persistent ρ hp hpres _ hza hzb

end
end OAI.TuringRigidity.TwoConePresentation
