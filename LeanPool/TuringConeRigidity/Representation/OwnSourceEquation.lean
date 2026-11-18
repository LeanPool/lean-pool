/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OwnSourceEquation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OwnProgramValue
public import LeanPool.TuringConeRigidity.Representation.OwnDegreeExtensionMeaning
public import LeanPool.TuringConeRigidity.Effective.LocalSourceEquation

/-!
# Own Source Equation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open GenericIdentity ElementaryModel BoundedForcing LocalSourceEquation

theorem sourceEquation_of_own_graph (E : ZFSet.{0}) (I : CountableIdeal) (σ : I ≃o I)
    (p : OracleCode) (P Y L R : Oracle)
    (hL : GenericCoding.InfiniteOdd L) (hR : GenericCoding.InfiniteOdd R)
    (hideal : PrincipalIntersection Y (join Y L) (join Y R))
    (hY : OwnProgramAt E (automorphismSet σ) p P Y)
    (hGL : OwnProgramAt E (automorphismSet σ) p P L)
    (hGR : OwnProgramAt E (automorphismSet σ) p P R)
    (hCL : OwnProgramAt E (automorphismSet σ) p P (GenericCoding.code Y L))
    (hCR : OwnProgramAt E (automorphismSet σ) p P (GenericCoding.code Y R)) :
    SourceEquation p P (Y,L,R) := by
  obtain ⟨hy,hyv⟩ := hY.action E I σ p P Y
  obtain ⟨hl,hlv⟩ := hGL.action E I σ p P L
  obtain ⟨hr,hrv⟩ := hGR.action E I σ p P R
  obtain ⟨hcl,hclv⟩ := hCL.action E I σ p P (GenericCoding.code Y L)
  obtain ⟨hcr,hcrv⟩ := hCR.action E I σ p P (GenericCoding.code Y R)
  have hleft : (σ (⟨degree (join Y L),I.join_mem hy hl⟩ : I)).val =
      degree (join (value p P (GenericCoding.code Y L)) (value p P L)) := by
    have he : (⟨degree (join Y L),I.join_mem hy hl⟩ : I) =
        (⟨degree (GenericCoding.code Y L),hcl⟩ : I) ⊔ ⟨degree L,hl⟩ :=
      Subtype.ext (GenericCoding.join_degree_eq Y L hL).symm
    rw [he,local_map_join,←hclv,←hlv]
    rfl
  have hright : (σ (⟨degree (join Y R),I.join_mem hy hr⟩ : I)).val =
      degree (join (value p P (GenericCoding.code Y R)) (value p P R)) := by
    have he : (⟨degree (join Y R),I.join_mem hy hr⟩ : I) =
        (⟨degree (GenericCoding.code Y R),hcr⟩ : I) ⊔ ⟨degree R,hr⟩ :=
      Subtype.ext (GenericCoding.join_degree_eq Y R hR).symm
    rw [he,local_map_join,←hcrv,←hrv]
    rfl
  refine ⟨hY.1,hGL.1,hGR.1,hCL.1,hCR.1,?_⟩
  have h := local_intersection I σ ⟨degree Y,hy⟩
    ⟨degree (join Y L),I.join_mem hy hl⟩ ⟨degree (join Y R),I.join_mem hy hr⟩ hideal
  rw [←hyv,hleft,hright] at h
  exact h

theorem sourceEquation_of_own_extension (E : ZFSet.{0}) [Countable (Conditions E)]
    (hE : Transitive E) (hTE : SourceT E) (I : CountableIdeal) (ρ : I ≃o I)
    (f : ZFSet.{0}) (hf : OwnDegreeExtension E (idealSet I) (automorphismSet ρ) f)
    (p : OracleCode) (P Y L R : Oracle)
    (hL : GenericCoding.InfiniteOdd L) (hR : GenericCoding.InfiniteOdd R)
    (hideal : PrincipalIntersection Y (join Y L) (join Y R))
    (hY : OwnProgramAt E f p P Y) (hGL : OwnProgramAt E f p P L)
    (hGR : OwnProgramAt E f p P R)
    (hCL : OwnProgramAt E f p P (GenericCoding.code Y L))
    (hCR : OwnProgramAt E f p P (GenericCoding.code Y R)) : SourceEquation p P (Y,L,R) := by
  obtain ⟨_,σ,rfl,_⟩ := (own_degree_extension_iff E hE hTE I ρ f).mp hf
  exact sourceEquation_of_own_graph E _ σ p P Y L R hL hR hideal hY hGL hGR hCL hCR

end TuringRigidity.RelativeConstructible

end OAI
