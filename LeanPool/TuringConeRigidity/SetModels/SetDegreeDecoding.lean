/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetDegreeDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelReals
public import LeanPool.TuringConeRigidity.Constructibility.PersistentPresentation
public import LeanPool.TuringConeRigidity.SetModels.SetPresentationDecoding

/-!
# Set Degree Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetDegreeDecoding
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open PersistentRestrictions PersistentPresentation
universe u
noncomputable section

/-- The set of all real codes whose decoded oracle has degree `a`. -/
def degreeSet (a : Degree) : ZFSet.{u} :=
  ZFSet.sep (fun x => degree (oracleOf x) = a) (ZFSet.powerset ZFSet.omega)

@[simp] theorem real_mem_degreeSet (A : Oracle) (a : Degree) :
    realSet.{u} A ∈ degreeSet a ↔ degree A = a := by
  simp only [degreeSet,ZFSet.mem_sep,ZFSet.mem_powerset,oracleOf_realSet]
  exact and_iff_right (realSet_subset A)

theorem mem_degreeSet (a : Degree) (x : ZFSet.{u}) :
    x ∈ degreeSet a ↔ ∃ A, x = realSet A ∧ degree A = a := by
  constructor
  · intro hx
    obtain ⟨hs,he⟩ := ZFSet.mem_sep.mp hx
    exact ⟨oracleOf x,(realSet_oracleOf (ZFSet.mem_powerset.mp hs)).symm,he⟩
  · rintro ⟨A,rfl,he⟩
    exact (real_mem_degreeSet A a).mpr he

theorem degreeSet_injective : Function.Injective degreeSet.{u} := by
  intro a b he
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact (real_mem_degreeSet A b).mp (he ▸ (real_mem_degreeSet A (degree A)).mpr rfl)

theorem class_eq_degreeSet (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {A : Oracle} (hA : A ∈ reals M) :
    classSet d E (realSet A) = degreeSet (degree A) := by
  apply ZFSet.ext
  intro x
  rw [mem_classSet,mem_degreeSet]
  constructor
  · rintro ⟨hx,hAx⟩
    obtain ⟨B,hB,rfl⟩ := (hd x).mp hx
    exact ⟨B,rfl,((hE A hA B hB).mp hAx).symm⟩
  · rintro ⟨B,rfl,hBA⟩
    have hB : B ∈ reals M := hLower hA ((degree_eq_iff B A).mp hBA).1
    exact ⟨(hd _).mpr ⟨B,hB,rfl⟩,(hE A hA B hB).mpr hBA.symm⟩

/-- The set-coded family of degree sets corresponding to the countable ideal. -/
def idealSet (I : CountableIdeal) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ a ∈ I.carrier, x = degreeSet a)
    (ZFSet.powerset (ZFSet.powerset ZFSet.omega))

@[simp] theorem mem_idealSet (I : CountableIdeal) (x : ZFSet.{u}) :
    x ∈ idealSet I ↔ ∃ a ∈ I.carrier, x = degreeSet a := by
  rw [idealSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨a,ha,rfl⟩
    refine ⟨ZFSet.mem_powerset.mpr ?_,⟨a,ha,rfl⟩⟩
    intro y hy
    exact (ZFSet.mem_sep.mp hy).1

theorem quotient_eq_idealSet (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E a : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A)
    (ha : ∀ x, x ∈ a ↔ ∃ n, x = realSet (EncodedForcing.columns A n))
    (hcols : ∀ n, EncodedForcing.columns A n ∈ reals M) :
    quotientSet d E a = idealSet I := by
  apply ZFSet.ext
  intro x
  rw [mem_quotientSet,mem_idealSet]
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨n,rfl⟩ := (ha y).mp hy
    refine ⟨degree (EncodedForcing.columns A n),(hA _).mpr ⟨n,rfl⟩,?_⟩
    exact hxy.trans (class_eq_degreeSet M hLower hd hE (hcols n))
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨n,hn⟩ := (hA b).mp hb
    refine ⟨realSet (EncodedForcing.columns A n),(ha _).mpr ⟨n,rfl⟩,?_⟩
    rw [class_eq_degreeSet M hLower hd hE (hcols n),hn]

/-- The set-coded graph of the ideal automorphism on degree-set representations. -/
def automorphismSet {I : CountableIdeal} (ρ : I ≃o I) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val))
    (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_automorphismSet {I : CountableIdeal} (ρ : I ≃o I) (z : ZFSet.{u}) :
    z ∈ automorphismSet ρ ↔ ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val) := by
  rw [automorphismSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨b,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_idealSet _ _).mpr ⟨b.val,b.property,rfl⟩,
      (mem_idealSet _ _).mpr ⟨(ρ b).val,(ρ b).property,rfl⟩⟩,⟨b,rfl⟩⟩

theorem action_eq_automorphismSet (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E a R : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (ρ : I ≃o I)
    (ha : ∀ x, x ∈ a ↔ ∃ n, x = realSet (EncodedForcing.columns A n))
    (hcols : ∀ n, EncodedForcing.columns A n ∈ reals M)
    (hR : ∀ n m, ZFSet.pair (realSet (EncodedForcing.columns A n))
      (realSet (EncodedForcing.columns A m)) ∈ R ↔
      (ρ ⟨degree (EncodedForcing.columns A n), (hA _).mpr ⟨n, rfl⟩⟩).val =
        degree (EncodedForcing.columns A m)) :
    actionGraph d E a R = automorphismSet ρ := by
  apply ZFSet.ext
  intro z
  rw [mem_actionGraph,mem_automorphismSet]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,rfl⟩
    obtain ⟨n,rfl⟩ := (ha x).mp hx
    obtain ⟨m,rfl⟩ := (ha y).mp hy
    rw [class_eq_degreeSet M hLower hd hE (hcols n),
      class_eq_degreeSet M hLower hd hE (hcols m)]
    exact ⟨⟨_,(hA _).mpr ⟨n,rfl⟩⟩,by rw [(hR n m).mp hxy]⟩
  · rintro ⟨b,rfl⟩
    obtain ⟨n,hn⟩ := (hA b.val).mp b.property
    obtain ⟨m,hm⟩ := (hA (ρ b).val).mp (ρ b).property
    have hb : (⟨degree (EncodedForcing.columns A n),(hA _).mpr ⟨n,rfl⟩⟩ : I) = b :=
      Subtype.ext hn
    refine ⟨_,(ha _).mpr ⟨n,rfl⟩,_,(ha _).mpr ⟨m,rfl⟩,?_,?_⟩
    · apply (hR n m).mpr
      rw [hb,hm]
    · rw [class_eq_degreeSet M hLower hd hE (hcols n),
        class_eq_degreeSet M hLower hd hE (hcols m),hn,hm]

end
end TuringRigidity.SetDegreeDecoding

end OAI
