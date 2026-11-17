/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealSelection
public import LeanPool.TuringConeRigidity.Representation.GenericCodingBorel

/-!
# Generic Identity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set

def PrincipalIntersection (U L R : Oracle) : Prop :=
  ∀ b : Degree, b ≤ degree U ↔ b ≤ degree L ∧ b ≤ degree R

theorem principal_iff_countable (U L R : Oracle) :
    PrincipalIntersection U L R ↔ Reduces U L ∧ Reduces U R ∧
      ∀ n, Reduces (programOutput (codeEnumeration n) L) L ∧
        Reduces (programOutput (codeEnumeration n) L) R →
        Reduces (programOutput (codeEnumeration n) L) U := by
  constructor
  · intro h
    have hh := (h (degree U)).mp le_rfl
    exact ⟨hh.1,hh.2,fun n hn => (h (degree (programOutput (codeEnumeration n) L))).mpr hn⟩
  · rintro ⟨hL,hR,h⟩ b
    obtain ⟨B,rfl⟩ := degree_surjective b
    constructor
    · intro hb
      exact ⟨reduces_trans hb hL,reduces_trans hb hR⟩
    · rintro ⟨hbL,hbR⟩
      obtain ⟨n,hn⟩ := exists_programOutput L B hbL
      have hh := h n (by simpa [hn] using And.intro hbL hbR)
      simpa [hn] using hh

theorem principal_measurable {X : Type*} [MeasurableSpace X]
    (U L R : X → Oracle) (hU : Measurable U) (hL : Measurable L) (hR : Measurable R) :
    MeasurableSet {x | PrincipalIntersection (U x) (L x) (R x)} := by
  have hm : MeasurableSet {x | ∀ n, Reduces (programOutput (codeEnumeration n) (L x)) (L x) ∧
      Reduces (programOutput (codeEnumeration n) (L x)) (R x) →
      Reduces (programOutput (codeEnumeration n) (L x)) (U x)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    let C : X → Oracle := fun x => programOutput (codeEnumeration n) (L x)
    have hC : Measurable C := (programOutput_measurable _).comp hL
    have he : {x | Reduces (C x) (L x) ∧ Reduces (C x) (R x) → Reduces (C x) (U x)} =
        ({x | Reduces (C x) (L x)} ∩ {x | Reduces (C x) (R x)})ᶜ ∪ {x | Reduces (C x) (U x)} := by
      ext x; simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]; tauto
    change MeasurableSet {x | Reduces (C x) (L x) ∧ Reduces (C x) (R x) → Reduces (C x) (U x)}
    rw [he]
    exact ((reduces_measurable C L hC hL).inter (reduces_measurable C R hC hR)).compl.union
      (reduces_measurable C U hC hU)
  convert (reduces_measurable U L hU hL).inter ((reduces_measurable U R hU hR).inter hm) using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,principal_iff_countable]

noncomputable def value (p : OracleCode) (P A : Oracle) : Oracle := programOutput p (join A P)

def Total (p : OracleCode) (P A : Oracle) : Prop :=
  ∃ B, OracleCode.eval (oracleFunction (join A P)) p = oracleFunction B

theorem value_measurable (p : OracleCode) (P : Oracle) : Measurable (value p P) :=
  (programOutput_measurable p).comp (join_measurable _ _ measurable_id measurable_const)

theorem total_iff (p : OracleCode) (P A : Oracle) :
    Total p P A ↔ OracleCode.eval (oracleFunction (join A P)) p = oracleFunction (value p P A) := by
  constructor
  · rintro ⟨B,hB⟩
    rw [show value p P A = B from programOutput_eq p _ B hB]
    exact hB
  · intro h; exact ⟨_,h⟩

theorem total_measurable (p : OracleCode) (P : Oracle) : MeasurableSet {A | Total p P A} := by
  simp only [total_iff]
  exact OracleCode.success_measurable p _ _
    (join_measurable _ _ measurable_id measurable_const) (value_measurable p P)

def SourceEquation (p : OracleCode) (P : Oracle) (z : Oracle × Oracle × Oracle) : Prop :=
  Total p P z.1 ∧ Total p P z.2.1 ∧ Total p P z.2.2 ∧
  Total p P (GenericCoding.code z.1 z.2.1) ∧ Total p P (GenericCoding.code z.1 z.2.2) ∧
  PrincipalIntersection (value p P z.1)
    (join (value p P (GenericCoding.code z.1 z.2.1)) (value p P z.2.1))
    (join (value p P (GenericCoding.code z.1 z.2.2)) (value p P z.2.2))

theorem sourceEquation_measurable (p : OracleCode) (P : Oracle) :
    MeasurableSet {z | SourceEquation p P z} := by
  let X : (Oracle × Oracle × Oracle) → Oracle := fun z => z.1
  let G : (Oracle × Oracle × Oracle) → Oracle := fun z => z.2.1
  let H : (Oracle × Oracle × Oracle) → Oracle := fun z => z.2.2
  have hX : Measurable X := measurable_fst
  have hG : Measurable G := measurable_fst.comp measurable_snd
  have hH : Measurable H := measurable_snd.comp measurable_snd
  have hCG : Measurable (fun z => GenericCoding.code (X z) (G z)) :=
    GenericCoding.code_measurable.comp (hX.prodMk hG)
  have hCH : Measurable (fun z => GenericCoding.code (X z) (H z)) :=
    GenericCoding.code_measurable.comp (hX.prodMk hH)
  have hF := value_measurable p P
  have hI := principal_measurable _ _ _ (hF.comp hX)
    (join_measurable _ _ (hF.comp hCG) (hF.comp hG))
    (join_measurable _ _ (hF.comp hCH) (hF.comp hH))
  exact ((total_measurable p P).preimage hX).inter
    (((total_measurable p P).preimage hG).inter
      (((total_measurable p P).preimage hH).inter
        (((total_measurable p P).preimage hCG).inter
          (((total_measurable p P).preimage hCH).inter hI))))

end TuringRigidity.GenericIdentity

end OAI
