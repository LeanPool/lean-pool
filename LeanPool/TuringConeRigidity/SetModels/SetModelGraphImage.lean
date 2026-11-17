/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelGraphImage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelColumns

/-!
# Set Model Graph Image
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

def graphImage (A G : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n m, G (Nat.pair n m) = true ∧
    z = ZFSet.pair (realSet (columns A n)) (realSet (columns A m)))
    (ZFSet.prod (columnRange A) (columnRange A))

@[simp] theorem mem_graphImage (A G : Oracle) (z : ZFSet.{u}) :
    z ∈ graphImage A G ↔ ∃ n m, G (Nat.pair n m) = true ∧
      z = ZFSet.pair (realSet (columns A n)) (realSet (columns A m)) := by
  rw [graphImage,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,m,hG,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_columnRange _ _).mpr ⟨n,rfl⟩,
      (mem_columnRange _ _).mpr ⟨m,rfl⟩⟩,⟨n,m,hG,rfl⟩⟩

def graphImageFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 4 (.existsMem 5 (.existsMem 10 (.existsMem 7
    (.conj (.orderedPair 6 5 4) (.conj (.pairMem 3 5 9) (.conj (.pairMem 2 4 9)
      (.conj (.orderedPair 1 3 2) (.conj (.pairMem 1 0 11) (.member 0 10)))))))))))

theorem eval_graphImageFormula (A G : Oracle) (p : ZFSet.{u}) (hpdef : PairingCode p)
    (z : ZFSet.{u}) :
    graphImageFormula.Eval (cons z (cons (columnRange A) (cons ZFSet.omega
      (cons (sequenceSet (columns A)) (cons (realSet G) (cons p
        (fun _ => ZFSet.prod ZFSet.omega ZFSet.omega))))))) ↔
      ∃ n m, G (Nat.pair n m) = true ∧
        z = ZFSet.pair (realSet (columns A n)) (realSet (columns A m)) := by
  simp only [graphImageFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨x,hx,y,hy,n,hn,m,hm,t,ht,v,hv,hz,hnx,hmy,htnm,htv,hvG⟩
    obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega m).mp hm
    obtain ⟨k,rfl⟩ := (mem_omega v).mp hv
    have hxn := (pair_mem_sequenceSet (columns A) i x).mp hnx
    have hym := (pair_mem_sequenceSet (columns A) j y).mp hmy
    rw [htnm] at htv
    have hk := (hpdef i j k).mp htv
    refine ⟨i,j,?_,by simpa only [hxn,hym] using hz⟩
    simpa only [hk] using (nat_mem_realSet G k).mp hvG
  · rintro ⟨n,m,hG,hz⟩
    have hn : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
    have hm : natSet.{u} m ∈ ZFSet.omega := (mem_omega _).mpr ⟨m,rfl⟩
    refine ⟨_,(mem_columnRange A _).mpr ⟨n,rfl⟩,_,(mem_columnRange A _).mpr ⟨m,rfl⟩,
      _,hn,_,hm,_,ZFSet.pair_mem_prod.mpr ⟨hn,hm⟩,_,(mem_omega _).mpr ⟨Nat.pair n m,rfl⟩,
      hz,(pair_mem_sequenceSet (columns A) n _).mpr rfl,
      (pair_mem_sequenceSet (columns A) m _).mpr rfl,rfl,
      (hpdef n m (Nat.pair n m)).mpr rfl,(nat_mem_realSet G _).mpr hG⟩

theorem graphImage_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {p : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p)
    {A G : Oracle} (hseq : sequenceSet (columns A) ∈ M)
    (ha : columnRange A ∈ M) (hG : G ∈ reals M) : graphImage A G ∈ M := by
  have hω := omega_mem M hM hS hI
  have hd := product_mem M hM hP hU hPow hS hω hω
  have hprod := product_mem M hM hP hU hPow hS ha ha
  let e := cons (columnRange A) (cons ZFSet.omega (cons (sequenceSet (columns A))
    (cons (realSet G) (cons p (fun _ => ZFSet.prod ZFSet.omega ZFSet.omega)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact ha
    · exact hω
    · exact hseq
    · exact hG
    · exact hp
    · exact hd
  have hs := sep_mem M hM hS graphImageFormula e he hprod
  have eq : ZFSet.sep (fun z => graphImageFormula.Eval (cons z e))
      (ZFSet.prod (columnRange A) (columnRange A)) = graphImage A G := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,show graphImageFormula.Eval (cons z e) ↔ _ from
      eval_graphImageFormula A G p hpdef z]
    simp only [graphImage,ZFSet.mem_sep]
  exact eq ▸ hs

end
end TuringRigidity.SetModelColumns

end OAI
