/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenRecursiveName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RecursiveNames
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFilterReal

/-!
# Cohen Recursive Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenRecursiveName
open Set CountableForcing RecursiveNames CohenBorelForcing FiniteShuffle ShuffleRequirements

instance : OrderTop Condition where
  top := ⟨[]⟩
  le_top _ := List.nil_prefix

/-- The von Neumann natural number corresponding to `n`. -/
def numeral (n : ℕ) : ZFSet := ZFSet.mk (PSet.ofNat n)

/-- The set of von Neumann numerals at which the oracle is true. -/
noncomputable def realSet (A : Oracle) : ZFSet :=
  ZFSet.range (fun n : {n // A n = true} => numeral n.val)

theorem numeral_mem_omega (n : ℕ) : numeral n ∈ ZFSet.omega := by
  change PSet.ofNat n ∈ PSet.omega
  exact PSet.func_mem PSet.omega ⟨n⟩

theorem realSet_subset_omega (A : Oracle) : realSet A ⊆ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp hx
  exact numeral_mem_omega n.val

/-- The canonical forcing name for the generic binary real. -/
noncomputable def genericReal : Name Condition :=
  .mk {t : Condition × ℕ // t.2 < t.1.word.length ∧ t.1.word.getD t.2 false = true}
    (fun t => Name.check (numeral t.val.2)) (fun t => t.val.1)

theorem val_genericReal (A : Oracle) :
    Name.val (realFilter A).carrier genericReal = realSet A := by
  have htop : (⊤ : Condition) ∈ (realFilter A).carrier := by
    change Realizes [] A
    intro i hi; exact (Nat.not_lt_zero i hi).elim
  apply ZFSet.ext
  intro x
  rw [genericReal, Name.mem_val]
  simp only [Name.val_check _ htop, realSet, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨p,n⟩,hn,hbit⟩,hp,he⟩
    have hA : A n = true := (hp n hn).symm.trans hbit
    exact ⟨⟨n,hA⟩,he⟩
  · rintro ⟨⟨n,hn⟩,he⟩
    let p : Condition := ⟨initial A (n+1)⟩
    have hp : p ∈ (realFilter A).carrier :=
      (realizes_initial A A (n+1)).mpr (fun _ _ => rfl)
    have hlen : n < p.word.length := by simp [p,initial]
    exact ⟨⟨(p,n),hlen,(hp n hlen).trans hn⟩,hp,he⟩

theorem genericReal_from_filter (G : GenericFilter Condition)
    (hG : CountableForcing.GenericFor CohenFilterReal.Long G) :
    ∃ A : Oracle, G = realFilter A ∧ Name.val G.carrier genericReal = realSet A := by
  obtain ⟨A,rfl⟩ := CohenFilterReal.exists_realFilter G hG
  exact ⟨A,rfl,val_genericReal A⟩

theorem exists_generic_real (E : ℕ → Set Condition)
    (hE : ∀ n, CountableForcing.Dense (E n)) (p : Condition) :
    ∃ (G : GenericFilter Condition) (A : Oracle), p ∈ G.carrier ∧
      CountableForcing.GenericFor E G ∧ G = realFilter A ∧
      Name.val G.carrier genericReal = realSet A := by
  obtain ⟨G,hp,hG⟩ := exists_generic
    (mergeRequirements CohenFilterReal.Long E)
    (mergeRequirements_dense _ _ CohenFilterReal.long_dense hE) p
  obtain ⟨hL,hE⟩ := (generic_merge_iff _ _ G).mp hG
  obtain ⟨A,hA,hname⟩ := genericReal_from_filter G hL
  exact ⟨G,A,hp,hE,hA,hname⟩

end TuringRigidity.CohenRecursiveName

end OAI
