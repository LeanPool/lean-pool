/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NoNewOrdinals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory
public import LeanPool.TuringConeRigidity.SetModels.NameEncoding
public import LeanPool.TuringConeRigidity.Syntax.FiniteTerm
public import LeanPool.TuringConeRigidity.OrdinalCodes.RankOrdinal
public import LeanPool.TuringConeRigidity.SetModels.NameExtension

/-!
# No New Ordinals
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory InternalRank
universe u

theorem name_value_rank_le {P : Type u} (l : P → ZFSet.{u}) (G : Set P) (a : Name P) :
    (a.val G).rank ≤ (a.encode l).rank := by
  induction a with
  | mk ι child tag ih =>
    apply ZFSet.rank_le_iff.mpr
    intro x hx
    obtain ⟨i,_,rfl⟩ := (Name.mem_val G ι child tag x).mp hx
    have hp : ZFSet.pair ((child i).encode l) (l (tag i)) ∈
        (Name.mk ι child tag).encode l := ZFSet.mem_range_self i
    exact (ih i).trans_lt ((FiniteTerm.pair_rank_left _ _).trans (ZFSet.rank_lt_of_mem hp))

theorem ordinal_name_value_ground (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Type u} (l : P → ZFSet.{u}) (G : Set P) (a : Name P)
    (ha : a.encode l ∈ M) (δ : Ordinal.{u}) (hv : a.val G = δ.toZFSet) :
    δ.toZFSet ∈ M := by
  have hr := rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ha
  rw [rankSet_eq_ordinal] at hr
  have hle := name_value_rank_le l G a
  rw [hv,Ordinal.rank_toZFSet] at hle
  rcases lt_or_eq_of_le hle with hlt|heq
  · exact hM _ hr _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt)
  · exact heq ▸ hr

theorem extension_ordinal_ground (M c : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (G : Set (Conditions c)) (δ : Ordinal.{u})
    (hδ : δ.toZFSet ∈ genericExtensionSet M c G) : δ.toZFSet ∈ M := by
  obtain ⟨a,ha,hv⟩ := (mem_extensionSet M c G _).mp hδ
  exact ordinal_name_value_ground M hM hT (label c) G a ha δ hv

end TuringRigidity.TransitiveNameModel

end OAI
