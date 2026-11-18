/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenColumns.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenConservative
public import LeanPool.TuringConeRigidity.Effective.CodingExtraction

/-!
# Cohen Columns
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenColumns
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CohenHalting EffectiveCohen

/-- Replace column `i` of an oracle by zeros while preserving all other columns. -/
def erase (i : ℕ) (G : Oracle) : Oracle := fun m => if (Nat.unpair m).1 = i then false else G m

/-- Erase column `i` in a finite word without changing its length. -/
def eraseWord (i : ℕ) (s : List Bool) : List Bool :=
  (List.range s.length).map (fun m => if (Nat.unpair m).1 = i then false else s.getD m false)

@[simp] theorem eraseWord_length (i : ℕ) (s : List Bool) : (eraseWord i s).length = s.length := by
  simp [eraseWord]

theorem eraseWord_getD (i : ℕ) (s : List Bool) (m : ℕ) (hm : m < s.length) :
    (eraseWord i s).getD m false = if (Nat.unpair m).1 = i then false else s.getD m false := by
  simp [eraseWord,List.getD_eq_getElem?_getD,List.getElem?_range hm]

theorem eraseWord_primrec (i : ℕ) : Primrec (eraseWord i) := by
  apply Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
  exact Primrec.ite (Primrec.eq.comp ((Primrec.fst.comp Primrec.unpair).comp Primrec.snd)
    (Primrec.const i))
    (Primrec.const false) ((Primrec.list_getD false).comp Primrec.fst Primrec.snd)

theorem eraseWord_initial (i : ℕ) (G : Oracle) (N : ℕ) :
    eraseWord i (initial G N) = initial (erase i G) N := by
  apply List.ext_getElem
  · simp
  · intro n hn hm
    have hn' : n < N := by simpa using hn
    have h := eraseWord_getD i (initial G N) n (by simpa using hn')
    rw [initial_getD G hn'] at h
    have he := initial_getD (erase i G) hn'
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem hm,Option.getD_some] using h.trans he.symm

theorem eraseWord_prefix {i : ℕ} {G : Oracle} {s : List Bool} (hs : Prefix G s) :
    Prefix (erase i G) (eraseWord i s) := by
  rw [prefix_initial hs,eraseWord_initial]
  exact initial_prefix _ _

theorem eraseWord_set (i : ℕ) (s : List Bool) (m : ℕ) (hi : (Nat.unpair m).1 = i) (b : Bool) :
    eraseWord i (s.set m b) = eraseWord i s := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    have hns : n < s.length := by simpa using hn'
    have h₀ := eraseWord_getD i (s.set m b) n (by simpa using hns)
    have h₁ := eraseWord_getD i s n hns
    have he : (eraseWord i (s.set m b)).getD n false = (eraseWord i s).getD n false := by
      rw [h₀,h₁]
      by_cases hni : (Nat.unpair n).1 = i
      · simp only [ite_eq_left hni]
      · have hmn : m ≠ n := by rintro rfl; exact hni hi
        simp only [ite_eq_right hni,List.getD_eq_getElem?_getD,List.getElem?_set_ne hmn]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem hn',Option.getD_some] using he

/-- A finite computation using `B` and a word with column `i` zeroed disagrees with a bit
assigned in that column. -/
def Disagrees (B : Oracle) (i : ℕ) (e : OracleCode) (p : ℕ) : Prop :=
  ∃ n a, Nat.pair i n < (word p).length ∧
    a ∈ CommonIdeal.run B e (eraseWord i (word p)) n ∧
    a ≠ CommonIdeal.bit ((word p).getD (Nat.pair i n) false)

theorem disagrees_sigma (B : Oracle) (i : ℕ) (e : OracleCode) : Sigma B 1 (Disagrees B i e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := f.comp f
  let n := r.comp f
  let m := Primrec₂.natPair.comp (Primrec.const i) n
  have hr := (CohenRun.run_mem_sigma B e).comp
    (Primrec₂.natPair.comp (Primrec.encode.comp ((eraseWord_primrec i).comp (word_primrec.comp p)))
      (Primrec₂.natPair.comp n r))
  have hl := recursive_primrecPred B (Primrec.nat_lt.comp m (Primrec.list_length.comp
    (word_primrec.comp p)))
  have hv := recursive_primrecPred B ((Primrec.eq.comp r (CommonIdeal.bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp p) m))).not)
  have h := ((Form.raise (n := 0) (s := true) hl).and (hr.and (Form.raise (n := 0) (s := true)
    hv))).ex.ex
  apply h.congr
  intro v
  simp only [Disagrees,Nat.unpair_pair,word,encodek,Option.getD_some]

theorem column_not_reduces {B G : Oracle} (hg : OneGeneric B G) (i : ℕ) :
    ¬ Reduces (columns G i) (join B (erase i G)) := by
  intro h
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨p,hp,hd⟩ := hg.decides (disagrees_sigma B i e)
  rcases hd with ⟨n,a,hlen,ha,hne⟩ | hd
  · have hv := CommonIdeal.run_total (eraseWord_prefix hp) n a (by simpa [word] using ha)
    rw [he] at hv
    have hav : a = CommonIdeal.bit (G (Nat.pair i n)) := Part.mem_some_iff.mp hv
    apply hne
    rw [hav]
    simpa only [word,encodek,Option.getD_some] using congrArg CommonIdeal.bit (hp _ (by simpa
      [word] using hlen))
  · let n := p.length
    let m := Nat.pair i n
    have hm : p.length ≤ m := Nat.right_le_pair i n
    have hv : CommonIdeal.bit (G m) ∈ OracleCode.eval (oracleFunction (join B (erase i G))) e n :=
      by
      rw [he]; exact Part.mem_some _
    obtain ⟨L,hL⟩ := (CommonIdeal.run_approximates B (erase i G) e n).2 _ hv
    let N := max (m+1) L
    let q := initial G N
    have hN : m < N := (Nat.lt_succ_self m).trans_le (le_max_left _ _)
    have hpq : p <+: q := by
      rw [prefix_initial hp]
      exact initial_mono G (hm.trans (Nat.le_of_lt hN))
    have hrun : CommonIdeal.bit (G m) ∈ CommonIdeal.run B e (eraseWord i q) n := by
      rw [show eraseWord i q = initial (erase i G) N from eraseWord_initial i G N]
      exact hL N (le_max_right _ _)
    let q' := q.set m (!(G m))
    have hpq' : p <+: q' := CodingOnePoint.prefix_set_of_le hpq m hm _
    apply hd q' hpq'
    refine ⟨n,CommonIdeal.bit (G m),?_,?_,?_⟩
    · simpa [word,q',q,m] using hN
    · have heq : eraseWord i q' = eraseWord i q := eraseWord_set i q m (by simp [m]) _
      simpa only [word,encodek,Option.getD_some,heq] using hrun
    · have hbit : q'.getD m false = !(G m) := by
        simp [q',List.getD_eq_getElem?_getD,show m < q.length by simpa [q] using hN]
      simp only [word,encodek,Option.getD_some]
      change CommonIdeal.bit (G m) ≠ CommonIdeal.bit (q'.getD m false)
      rw [hbit]
      cases G m <;> decide

theorem column_reduces_erase (G : Oracle) (i j : ℕ) (hji : j ≠ i) :
    Reduces (columns G j) (erase i G) := by
  have he : columns (erase i G) j = columns G j := by
    funext n
    simp [columns,erase,hji]
  rw [← he]
  exact CodingExtraction.column_projection_reduces _ _

theorem finite_conservative {B G : Oracle} (hg : OneGeneric B G) (F : Finset ℕ)
    (a y : Degree) (ha : a ≤ degree B) (hy : y ≤ degree B)
    (h : y ≤ a ⊔ F.sup (fun i => degree (columns G i))) : y ≤ a := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  obtain ⟨Y,rfl⟩ := degree_surjective y
  apply CohenConservative.oneGeneric_conservative hg A Y ha hy
  change degree Y ≤ degree A ⊔ degree G
  apply le_trans h
  apply sup_le_sup_left
  apply Finset.sup_le
  intro i _
  exact CodingExtraction.column_projection_reduces G i

theorem independence {B G : Oracle} (hg : OneGeneric B G)
    (a₀ a₁ : Degree) (h₀ : a₀ ≤ degree B) (h₁ : a₁ ≤ degree B)
    (i : ℕ) (F : Finset ℕ) :
    a₀ ⊔ degree (columns G i) ≤ a₁ ⊔ F.sup (fun j => degree (columns G j)) ↔
      a₀ ≤ a₁ ∧ i ∈ F := by
  constructor
  · intro h
    refine ⟨finite_conservative hg F a₁ a₀ h₁ h₀ (le_sup_left.trans h),?_⟩
    by_contra hi
    apply column_not_reduces hg i
    change degree (columns G i) ≤ degree B ⊔ degree (erase i G)
    apply le_trans le_sup_right (le_trans h (sup_le_sup h₁ ?_))
    apply Finset.sup_le
    intro j hj
    exact column_reduces_erase G i j (fun he => hi (he ▸ hj))
  · rintro ⟨ha,hi⟩
    exact sup_le_sup ha (Finset.le_sup (f := fun j => degree (columns G j)) hi)

theorem uniform_low_independent (B : Oracle) : ∃ G : Oracle,
    Reduces G (OracleJump.jump B) ∧
    degree (OracleJump.jump (join B G)) = degree (OracleJump.jump B) ∧
    ∀ a₀ a₁ : Degree, a₀ ≤ degree B → a₁ ≤ degree B → ∀ i (F : Finset ℕ),
      a₀ ⊔ degree (columns G i) ≤ a₁ ⊔ F.sup (fun j => degree (columns G j)) ↔
        a₀ ≤ a₁ ∧ i ∈ F := by
  obtain ⟨G,hG,hgen,hlow⟩ := CohenLowness.relative_low_generic B
  exact ⟨G,hG,hlow,independence hgen⟩

end TuringRigidity.CohenColumns

end OAI
