/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteShuffle.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericCoding

/-!
# Finite Shuffle
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

/-- Two oracles agree on their first `n` bits. -/
def Agree (n : ℕ) (A B : Oracle) : Prop := ∀ i, i < n → A i = B i

theorem Agree.mono {n m : ℕ} {A B : Oracle} (h : Agree n A B) (hm : m ≤ n) :
    Agree m A B := fun i hi => h i (by omega)

theorem Agree.symm {n : ℕ} {A B : Oracle} (h : Agree n A B) : Agree n B A :=
  fun i hi => (h i hi).symm

theorem Agree.trans {n : ℕ} {A B C : Oracle} (h : Agree n A B) (h' : Agree n B C) :
    Agree n A C := fun i hi => (h i hi).trans (h' i hi)

/-- The first `n` bits of the oracle as a finite word. -/
def initial (A : Oracle) (n : ℕ) : List Bool := (List.range n).map A

@[simp] theorem prefix_length (A : Oracle) (n : ℕ) : (initial A n).length = n := by
  simp [initial]

/-- A bounded entry of the initial oracle word is the corresponding oracle bit. -/
@[simp] theorem prefix_getElem (A : Oracle) (n i : ℕ) (hi : i < n) :
    (initial A n)[i]'(by simpa using hi) = A i := by
  simp [initial]

theorem prefix_getD (A : Oracle) (n i : ℕ) (hi : i < n) :
    (initial A n).getD i false = A i := by
  simp [initial,List.getD,hi]

theorem prefix_default (s : List Bool) : initial (fun i => s.getD i false) s.length = s := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [initial,List.getD,hj]

theorem prefix_agree {A B : Oracle} {n : ℕ} (h : Agree n A B) : initial A n = initial B n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < n := by simpa using hi
    simpa [initial] using h i hi'

/-- All odd-coordinate bits from index `n` onward are false. -/
def OddBound (n : ℕ) (G : Oracle) : Prop := ∀ i, n ≤ i → G (2*i+1) = false

theorem count_agree {n : ℕ} {G H : Oracle} (h : ∀ i, i < n → G (2 * i + 1) = H (2 * i + 1)) :
    count G n = count H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) = count H n + bit H (2*n+1)
    rw [ih (fun i hi => h i (by omega))]
    simp [bit,h n (by omega)]

theorem count_constant {n : ℕ} {G : Oracle} (h : OddBound n G) {m : ℕ} (hm : n ≤ m) :
    count G m = count G n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    change count G m + bit G (2*m+1) = count G n
    simp [bit,h m hm,ih]

theorem code_agree {n : ℕ} {A B G H : Oracle} (ha : Agree n A B) (hg : Agree (2 * n) G H) :
    Agree n (code A G) (code B H) := by
  intro i hi
  have hc : count G i = count H i := count_agree (fun j hj => hg (2*j+1) (by omega))
  have ho := hg (2*i+1) (by omega)
  have hl := count_le G i
  simp only [code,←hc,←ho]
  split
  · exact ha _ (by omega)
  · exact hg _ (by omega)

theorem code_agree_inserted {n : ℕ} {A B G : Oracle} (hg : OddBound n G) (ha : Agree n A B) :
    code A G = code B G := by
  funext i
  unfold code
  split
  · rename_i hb
    have hi : i < n := by
      by_contra hi
      have := hg i (by omega)
      simp_all
    exact ha _ (lt_of_le_of_lt (count_le G i) hi)
  · rfl

/-- Preserve the even coordinates and the initial odd coordinates, clearing the remaining odd
coordinates. -/
def freeze (n : ℕ) (G : Oracle) : Oracle :=
  join (fun i => G (2*i)) (fun i => if i < n then G (2*i+1) else false)

theorem freeze_bound (n : ℕ) (G : Oracle) : OddBound n (freeze n G) := by
  intro i hi
  simp [freeze,show ¬i<n by omega]

theorem agree_of_columns {n : ℕ} {G H : Oracle}
    (he : ∀ i, i < n → G (2 * i) = H (2 * i))
    (ho : ∀ i, i < n → G (2 * i + 1) = H (2 * i + 1)) : Agree (2 * n) G H := by
  intro i hi
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have hh : i = 2*(i/2) := by omega
    rw [hh]
    exact he _ (by omega)
  · have hh : i = 2*(i/2)+1 := by omega
    rw [hh]
    exact ho _ (by omega)

theorem freeze_agree (n : ℕ) (G : Oracle) : Agree (2*n) G (freeze n G) := by
  apply agree_of_columns
  · intro i hi; simp [freeze]
  · intro i hi; simp [freeze,hi]

/-- Preserve the initial even coordinates, fill later even coordinates from shifted `T`, and
retain odd coordinates. -/
def extendEven (n : ℕ) (G T : Oracle) : Oracle :=
  join (fun i => if i < n then G (2*i) else T (i + count G n)) (fun i => G (2*i+1))

theorem extendEven_count (n : ℕ) (G T : Oracle) (i : ℕ) :
    count (extendEven n G T) i = count G i :=
  count_agree (fun j hj => by simp [extendEven])

theorem extendEven_agree (n : ℕ) (G T : Oracle) : Agree (2*n) G (extendEven n G T) := by
  apply agree_of_columns
  · intro i hi; simp [extendEven,hi]
  · intro i hi; simp [extendEven]

theorem extendEven_bound {k n : ℕ} {G T : Oracle} (hg : OddBound k G) :
    OddBound k (extendEven n G T) := by
  intro i hi
  simpa [extendEven] using hg i hi

theorem extendEven_code (n : ℕ) (A G T : Oracle) (hg : OddBound n G)
    (ht : Agree (n + count G n) (code A G) T) : code A (extendEven n G T) = T := by
  funext i
  simp only [code]
  rw [extendEven_count]
  simp only [extendEven,join_odd,join_even]
  have hcn := count_le G n
  by_cases hi : i < n + count G n
  · rw [←ht i hi]
    unfold code
    split
    · rfl
    · have hsub : i - count G i < n := by
        by_cases hin : i < n
        · omega
        · rw [count_constant hg (by omega)]
          omega
      simp [hsub]
  · have hin : n ≤ i := by omega
    have hc := count_constant hg hin
    rw [hg i hin]
    simp only [Bool.false_eq_true,↓reduceIte,hc]
    have hl := count_le G n
    have hn : ¬i-count G n<n := by omega
    rw [ite_eq_right hn]
    congr 1
    omega

theorem initial_prefix {A B : Oracle} {n m : ℕ} (hnm : n ≤ m) (h : Agree n A B) :
    initial A n <+: initial B m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using hnm,?_⟩
  intro i hi
  simpa [initial] using h i (by simpa using hi)

theorem agree_of_prefix {A : Oracle} {n : ℕ} {t : List Bool} (h : initial A n <+: t) :
    Agree n A (fun i => t.getD i false) := by
  obtain ⟨u,hu⟩ := h
  intro i hi
  rw [←hu]
  simp [List.getD,List.getElem?_append,hi]

/-- A word family is dense under extension and closed under further extension. -/
def DenseOpen (D : List Bool → Prop) : Prop :=
  (∀ s, ∃ t, s <+: t ∧ D t) ∧ (∀ s t, s <+: t → D s → D t)

theorem odd_null_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (n : ℕ) (A G : Oracle) (hg : OddBound n G) :
    ∃ m H, n < m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧ D (initial (code A H) m) := by
  obtain ⟨t,ht,hD⟩ := hd.1 (initial (code A G) (n + count G n + 1))
  let T : Oracle := fun i => t.getD i false
  have ha : Agree (n + count G n) (code A G) T :=
    (agree_of_prefix ht).mono (by omega)
  have he := extendEven_code n A G T hg ha
  refine ⟨t.length,extendEven n G T,?_,extendEven_agree n G T,?_,?_⟩
  · have hl := ht.length_le
    simp only [prefix_length] at hl
    omega
  · intro i; simp [extendEven]
  · rw [he]
    change D (initial (fun i => t.getD i false) t.length)
    rw [prefix_default]
    exact hD

theorem finite_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (S : Finset Oracle) (n : ℕ) (G : Oracle) (hg : OddBound n G) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧
      ∀ A ∈ S, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  induction S using Finset.induction_on generalizing n G with
  | empty => exact ⟨n,G,le_rfl,fun _ _ => rfl,fun _ => rfl,by simp⟩
  | @insert A S hAS ih =>
    obtain ⟨m,H,hnm,hGH,hoH,hS⟩ := ih n G hg
    have hb : OddBound m H := by
      intro i hi
      rw [hoH i]
      exact hg i (by omega)
    obtain ⟨k,K,hmk,hHK,hoK,hD⟩ := odd_null_extension D hd m A H hb
    refine ⟨k,K,by omega,hGH.trans (hHK.mono (by omega)),
      fun i => (hoK i).trans (hoH i),?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨k,le_rfl,hD⟩
    · obtain ⟨l,hl,hDl⟩ := hS B hB
      refine ⟨l,by omega,?_⟩
      have hc : Agree l (code B H) (code B K) :=
        code_agree (fun _ _ => rfl) (hHK.mono (by omega))
      rwa [←prefix_agree hc]

theorem all_extension (D : List Bool → Prop) (hd : DenseOpen D) (n : ℕ) (G : Oracle) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧ OddBound n H ∧
      ∀ A, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  let f : (Fin n → Bool) → Oracle := fun s i => if hi : i < n then s ⟨i,hi⟩ else false
  let S : Finset Oracle := Finset.univ.image f
  obtain ⟨m,H,hnm,hGH,ho,hS⟩ := finite_extension D hd S n (freeze n G) (freeze_bound n G)
  have hb : OddBound n H := fun i hi => (ho i).trans (freeze_bound n G i hi)
  refine ⟨m,H,hnm,(freeze_agree n G).trans hGH,hb,?_⟩
  intro A
  let a : Fin n → Bool := fun i => A i
  have ha : f a ∈ S := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  obtain ⟨l,hl,hD⟩ := hS (f a) ha
  have he : code (f a) H = code A H := code_agree_inserted hb (by
    intro i hi
    simp [f,a,hi])
  exact ⟨l,hl,by simpa [he] using hD⟩

end TuringRigidity.FiniteShuffle

end OAI
