/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelColumns.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelSequences
public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing
public import LeanPool.TuringConeRigidity.Effective.CodingExtraction

/-!
# Set Model Columns
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

/-- Bounded formula describing one oracle column through the natural-pairing graph. -/
def columnFormula (n b a p w d : ℕ) : Formula :=
  .allMem w (.allMem (w+1) (.allMem (d+2)
    (.imp (.conj (.orderedPair 0 (n+3) 2) (.pairMem 0 1 (p+3)))
      (.iff (.member 2 (b+3)) (.member 1 (a+3))))))

theorem eval_columnFormula (n b a p w d : ℕ) (e : ℕ → ZFSet.{u})
    (k : ℕ) (A B : Oracle) (hn : e n = natSet k) (hb : e b = realSet B)
    (ha : e a = realSet A) (hw : e w = ZFSet.omega)
    (hd : e d = ZFSet.prod ZFSet.omega ZFSet.omega) (hp : PairingCode (e p)) :
    (columnFormula n b a p w d).Eval e ↔ B = columns A k := by
  simp only [columnFormula,Formula.eval_allMem,Formula.eval_imp,Formula.Eval,
    Formula.eval_orderedPair,Formula.eval_pairMem,Formula.eval_iff,cons_zero,cons_succ,
    hn,hb,ha,hw,hd]
  constructor
  · intro h
    funext i
    have hi : natSet.{u} i ∈ ZFSet.omega := (mem_omega _).mpr ⟨i,rfl⟩
    have hm : natSet.{u} (Nat.pair k i) ∈ ZFSet.omega := (mem_omega _).mpr ⟨_,rfl⟩
    have hk : natSet.{u} k ∈ ZFSet.omega := (mem_omega _).mpr ⟨k,rfl⟩
    have hbit := h _ hi _ hm _ (ZFSet.pair_mem_prod.mpr ⟨hk,hi⟩)
      ⟨rfl,(hp k i (Nat.pair k i)).mpr rfl⟩
    simp only [nat_mem_realSet] at hbit
    change B i = A (Nat.pair k i)
    cases hbi : B i <;> cases hai : A (Nat.pair k i) <;> simp_all
  · intro h i hi m hm t ht hcond
    obtain ⟨j,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨l,rfl⟩ := (mem_omega m).mp hm
    obtain ⟨rfl,hpkl⟩ := hcond
    have hl := (hp k j l).mp hpkl
    simp only [nat_mem_realSet,h,columns,hl]

/-- Bounded formula describing membership in the graph of all oracle columns. -/
def columnsFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (columnFormula 1 0 5 6 3 7)))

theorem columns_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hL : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {p : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p)
    {A : Oracle} (hA : A ∈ reals M) : sequenceSet (columns A) ∈ M := by
  obtain ⟨r,hr,hrdef⟩ := internal_reals M hM hPow hS hI
  have hω := omega_mem M hM hS hI
  let d := ZFSet.prod ZFSet.omega ZFSet.omega
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hω
  have hprod := product_mem M hM hP hU hPow hS hω hr
  let e := cons ZFSet.omega (cons r (cons (realSet A) (cons p (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hr
    · exact hA
    · exact hp
    · exact hd
  have hs := sep_mem M hM hS columnsFormula e he hprod
  have hφ (z : ZFSet.{u}) : columnsFormula.Eval (cons z e) ↔
      ∃ n, z = ZFSet.pair (natSet n) (realSet (columns A n)) := by
    simp only [columnsFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    rw [omega_exists]
    constructor
    · rintro ⟨n,b,hb,hz,hcol⟩
      obtain ⟨B,hB,rfl⟩ := (hrdef b).mp hb
      have heq := (eval_columnFormula 1 0 5 6 3 7 (cons (realSet B) (cons (natSet n) (cons z e)))
        n A B rfl rfl rfl rfl rfl hpdef).mp hcol
      exact ⟨n,by simpa only [heq] using hz⟩
    · rintro ⟨n,rfl⟩
      have hcn := hL hA (CodingExtraction.column_projection_reduces A n)
      refine ⟨n,realSet (columns A n),(hrdef _).mpr ⟨_,hcn,rfl⟩,rfl,?_⟩
      exact (eval_columnFormula 1 0 5 6 3 7 (cons (realSet (columns A n)) (cons (natSet n)
        (cons (ZFSet.pair (natSet n) (realSet (columns A n))) e))) n A (columns A n) rfl rfl rfl
          rfl rfl hpdef).mpr rfl
  have eq : ZFSet.sep (fun z => columnsFormula.Eval (cons z e)) (ZFSet.prod ZFSet.omega r) =
      sequenceSet (columns A) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hφ,mem_sequenceSet]
    constructor
    · exact And.right
    · rintro ⟨n,rfl⟩
      have hcn := hL hA (CodingExtraction.column_projection_reduces A n)
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨n,rfl⟩,
        (hrdef _).mpr ⟨_,hcn,rfl⟩⟩,⟨n,rfl⟩⟩
  exact eq ▸ hs

/-- The set of real codes of all columns of `A`. -/
def columnRange (A : Oracle) : ZFSet.{u} := ZFSet.range (fun n : ℕ => realSet (columns A n))

@[simp] theorem mem_columnRange (A : Oracle) (x : ZFSet.{u}) :
    x ∈ columnRange A ↔ ∃ n, x = realSet (columns A n) := by
  rw [columnRange,ZFSet.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem columnRange_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M) (hI : Infinity M)
    {A : Oracle} (hcols : ∀ n, columns A n ∈ reals M)
    (hseq : sequenceSet (columns A) ∈ M) : columnRange A ∈ M := by
  obtain ⟨r,hr,hrdef⟩ := internal_reals M hM hPow hS hI
  have hω := omega_mem M hM hS hI
  let e := cons ZFSet.omega (fun _ => sequenceSet (columns A))
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> simp [e,hω,hseq]
  let φ : Formula := .existsMem 1 (.pairMem 0 1 3)
  have hs := sep_mem M hM hS φ e he hr
  have eq : ZFSet.sep (fun x => φ.Eval (cons x e)) r = columnRange A := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
    rw [omega_exists]
    simp only [pair_mem_sequenceSet,mem_columnRange]
    constructor
    · exact And.right
    · rintro ⟨n,rfl⟩
      exact ⟨(hrdef _).mpr ⟨_,hcols n,rfl⟩,⟨n,rfl⟩⟩
  exact eq ▸ hs

end
end TuringRigidity.SetModelColumns

end OAI
