/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.TwoAdic

/-!
# Strings, basic open sets, and some concrete tt-functionals
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-! ### Strings and cylinders -/

/-- Concatenation `τ⌢W` of a finite string and an oracle. -/
def prep (τ : List Bool) (W : Oracle) : Oracle :=
  fun n => if h : n < τ.length then τ[n] else W (n - τ.length)

/-- `dropF k X = S^k(X)`, i.e. `n ↦ X (n + k)`. -/
def dropF (k : ℕ) (X : Oracle) : Oracle := fun n => X (n + k)

/-- The basic open set `N_τ`. -/
def Ncyl (τ : List Bool) : Set Oracle := {X | pre X τ.length = τ}

theorem getD_pre (X : Oracle) {M j : ℕ} (h : j < M) : (pre X M).getD j false = X j := by
  rw [List.getD_eq_getElem?_getD, getElem?_pre, ite_eq_left h]; rfl

theorem pre_eq_iff {X Y : Oracle} {k : ℕ} : pre Y k = pre X k ↔ ∀ i < k, Y i = X i := by
  constructor
  · intro h i hi
    have := congrArg (·[i]?) h
    simp only [getElem?_pre, ite_eq_left hi, Option.some.injEq] at this
    exact this
  · intro h
    exact pre_eq_of_mem_cyl h

theorem mem_Ncyl_pre {X Y : Oracle} {k : ℕ} : Y ∈ Ncyl (pre X k) ↔ Y ∈ cyl X k := by
  simp only [Ncyl, Set.mem_ofPred_eq, length_pre, pre_eq_iff, cyl]

theorem Ncyl_pre (X : Oracle) (k : ℕ) : Ncyl (pre X k) = cyl X k := by
  ext Y; exact mem_Ncyl_pre

theorem cyl_antitone (X : Oracle) {k k' : ℕ} (h : k ≤ k') : cyl X k' ⊆ cyl X k :=
  fun _ hY i hi => hY i (by omega)

theorem prep_lt (τ : List Bool) (W : Oracle) {n : ℕ} (h : n < τ.length) :
    prep τ W n = τ[n] := by simp [prep, h]

theorem prep_ge (τ : List Bool) (W : Oracle) {n : ℕ} (h : τ.length ≤ n) :
    prep τ W n = W (n - τ.length) := by simp [prep, show ¬ n < τ.length by omega]

theorem pre_prep (τ : List Bool) (W : Oracle) : pre (prep τ W) τ.length = τ := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_pre]
  split_ifs with h
  · rw [prep_lt τ W h, List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by omega)]

theorem prep_mem (τ : List Bool) (W : Oracle) : prep τ W ∈ Ncyl τ := pre_prep τ W

theorem mem_Ncyl_iff {τ : List Bool} {X : Oracle} :
    X ∈ Ncyl τ ↔ X ∈ cyl (prep τ zzero) τ.length := by
  conv_lhs => rw [show Ncyl τ = Ncyl (pre (prep τ zzero) τ.length) by rw [pre_prep]]
  rw [mem_Ncyl_pre]

theorem Ncyl_eq_cyl (τ : List Bool) : Ncyl τ = cyl (prep τ zzero) τ.length := by
  ext X; exact mem_Ncyl_iff

theorem isOpen_Ncyl (τ : List Bool) : IsOpen (Ncyl τ) := by
  rw [Ncyl_eq_cyl]; exact isOpen_cyl _ _

theorem mem_Ncyl {τ : List Bool} {X : Oracle} :
    X ∈ Ncyl τ ↔ ∀ i (h : i < τ.length), X i = τ[i] := by
  constructor
  · intro hX i h
    have := congrArg (·[i]?) hX
    simp only [getElem?_pre, ite_eq_left h, List.getElem?_eq_getElem h, Option.some.injEq] at this
    exact this
  · intro h
    apply List.ext_getElem?
    intro i
    rw [getElem?_pre]
    split_ifs with hi
    · rw [h i hi, List.getElem?_eq_getElem hi]
    · rw [List.getElem?_eq_none (by omega)]

theorem Ncyl_antitone {τ τ' : List Bool} (h : τ <+: τ') : Ncyl τ' ⊆ Ncyl τ := by
  intro X hX
  rw [mem_Ncyl] at hX ⊢
  intro i hi
  rw [hX i (by have := h.length_le; omega), h.getElem hi]

theorem eq_prep_of_mem {τ : List Bool} {X : Oracle} (hX : X ∈ Ncyl τ) :
    X = prep τ (dropF τ.length X) := by
  funext n
  by_cases h : n < τ.length
  · rw [prep_lt τ _ h]
    have := congrArg (·[n]?) hX
    simp only [getElem?_pre, ite_eq_left h, List.getElem?_eq_getElem h, Option.some.injEq] at this
    exact this
  · rw [prep_ge τ _ (by omega)]
    simp only [dropF]
    congr 1
    omega

theorem prep_append_mem (τ : List Bool) (W : Oracle) : prep τ W ∈ Ncyl (τ ++ [W 0]) := by
  rw [Ncyl, Set.mem_ofPred_eq]
  apply List.ext_getElem?
  intro i
  rw [getElem?_pre]
  simp only [List.length_append, List.length_singleton]
  split_ifs with h
  · by_cases h' : i < τ.length
    · rw [prep_lt τ W h', List.getElem?_append_left h', List.getElem?_eq_getElem h']
    · obtain rfl : i = τ.length := by omega
      rw [prep_ge τ W le_rfl, List.getElem?_append_right le_rfl]
      simp
  · rw [List.getElem?_eq_none (by simp; omega)]

theorem prep_prep (τ : List Bool) (b : Bool) (W : Oracle) :
    prep τ (prep [b] W) = prep (τ ++ [b]) W := by
  funext n
  rcases Nat.lt_trichotomy n τ.length with h | h | h
  · rw [prep_lt τ _ h, prep_lt _ _ (by simp; omega), List.getElem_append_left h]
  · subst h
    rw [prep_ge τ _ le_rfl, prep_lt _ _ (by simp)]
    simp [prep]
  · rw [prep_ge τ _ h.le, prep_ge _ _ (by simp; omega), prep_ge _ _ (by simp; omega)]
    simp only [List.length_singleton, List.length_append]
    congr 1

theorem exists_cyl_subset {U : Set Oracle} (hU : IsOpen U) {X : Oracle} (hX : X ∈ U) :
    ∃ k, cyl X k ⊆ U := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU X hX
  refine ⟨I.sup id + 1, fun Y hY => hsub ?_⟩
  intro a ha
  have hlt : a < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  rw [hY a hlt]
  exact (hu a ha).2

theorem exists_cyl_prod_subset {U : Set (Oracle × Oracle)} (hU : IsOpen U) {x y : Oracle}
    (h : (x, y) ∈ U) : ∃ k, cyl x k ×ˢ cyl y k ⊆ U := by
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := isOpen_prod_iff.mp hU x y h
  obtain ⟨k₁, hk₁⟩ := exists_cyl_subset hu hxu
  obtain ⟨k₂, hk₂⟩ := exists_cyl_subset hv hyv
  refine ⟨max k₁ k₂, fun p hp => huv ⟨?_, ?_⟩⟩
  · exact hk₁ (cyl_antitone x (le_max_left _ _) hp.1)
  · exact hk₂ (cyl_antitone y (le_max_right _ _) hp.2)

/-! ### Some concrete tt-functionals -/

theorem pow_primrec : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem getD_primrec : Primrec₂ fun (L : List Bool) (n : ℕ) => L.getD n false :=
  Primrec.list_getD false

theorem isTTFunctional_prep (τ : List Bool) : IsTTFunctional (prep τ) := by
  refine isTTFunctional_of_use (u := fun n => n + 1)
    (t := fun n L => if n < τ.length then τ.getD n false else L.getD (n - τ.length) false)
    Primrec.succ ?_ ?_
  · exact Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const _))
      (getD_primrec.comp (Primrec.const τ) Primrec.fst)
      (getD_primrec.comp Primrec.snd (Primrec.nat_sub.comp Primrec.fst (Primrec.const _)))
  · intro X n
    by_cases h : n < τ.length
    · simp [prep, h, List.getD_eq_getElem?_getD]
    · simp only [prep, h, dite_eq_right, ite_false, not_false_eq_true]
      rw [getD_pre X (by omega)]

theorem isTTFunctional_dropF (k : ℕ) : IsTTFunctional (dropF k) := by
  refine isTTFunctional_of_use (u := fun n => n + k + 1) (t := fun n L => L.getD (n + k) false)
    (Primrec.succ.comp (Primrec.nat_add.comp Primrec.id (Primrec.const k)))
    (getD_primrec.comp Primrec.snd (Primrec.nat_add.comp Primrec.fst (Primrec.const k))) ?_
  intro X n
  rw [getD_pre X (by omega)]; rfl

theorem isTTFunctional_shift : IsTTFunctional shift := isTTFunctional_dropF 1

theorem isTTFunctional_cons (b : Bool) : IsTTFunctional (cons b) := by
  have : cons b = prep [b] := by
    funext X n
    rcases n with _ | n
    · simp [cons, prep]
    · simp [cons, prep]
  rw [this]; exact isTTFunctional_prep _

theorem isTTFunctional_xor (b : Bool) : IsTTFunctional fun X n => xor b (X n) := by
  refine isTTFunctional_of_use (u := fun n => n + 1) (t := fun n L => xor b (L.getD n false))
    Primrec.succ ?_ ?_
  · exact (Primrec.dom_bool₂ xor).comp (Primrec.const b) (getD_primrec.comp Primrec.snd Primrec.fst)
  · intro X n; rw [getD_pre X (by omega)]

/-- `val L = ∑ L[i] 2^i`. -/
def val (L : List Bool) : ℕ := L.foldr (fun b s => bv b + 2 * s) 0

theorem val_append_singleton (L : List Bool) (b : Bool) :
    val (L ++ [b]) = val L + bv b * 2 ^ L.length := by
  induction L with
  | nil => simp [val]
  | cons a L ih =>
    simp only [val, List.foldr_cons, List.cons_append, List.length_cons] at ih ⊢
    rw [ih, pow_succ]; ring

theorem val_pre (X : Oracle) (k : ℕ) : val (pre X k) = trunc X k := by
  induction k with
  | zero => simp [val, pre]
  | succ k ih =>
    rw [show pre X (k + 1) = pre X k ++ [X k] by simp [pre, List.range_succ],
      val_append_singleton, ih, trunc_succ, length_pre]

theorem val_primrec : Primrec val :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (bv_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂

theorem ofSeq_apply (s : ℕ → ℕ) (n : ℕ) : ofSeq s n = (s (n + 1) / 2 ^ n == 1) := by
  by_cases h : s (n + 1) / 2 ^ n = 1 <;> simp [ofSeq, h]

/-- Even part of a list, of length `n + 1`. -/
def evensL (n : ℕ) (L : List Bool) : List Bool := (List.range (n +
  1)).map fun i => L.getD (2 * i) false
/-- Odd part of a list, of length `n + 1`. -/
def oddsL (n : ℕ) (L : List Bool) : List Bool :=
  (List.range (n + 1)).map fun i => L.getD (2 * i + 1) false

theorem evensL_primrec : Primrec₂ evensL :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    (getD_primrec.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂

theorem oddsL_primrec : Primrec₂ oddsL :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    (getD_primrec.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))).to₂

/-- The even half of an oracle. -/
def evens (A : Oracle) : Oracle := fun n => A (2 * n)
/-- The odd half of an oracle. -/
def odds (A : Oracle) : Oracle := fun n => A (2 * n + 1)

theorem isTTFunctional_evens : IsTTFunctional evens := by
  refine isTTFunctional_of_use (u := fun n => 2 * n + 1) (t := fun n L => L.getD (2 * n) false)
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (getD_primrec.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) ?_
  intro X n; rw [getD_pre X (by omega)]; rfl

theorem isTTFunctional_odds : IsTTFunctional odds := by
  refine isTTFunctional_of_use (u := fun n => 2 * n + 2) (t := fun n L => L.getD (2 * n + 1) false)
    (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
    (getD_primrec.comp Primrec.snd
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))) ?_
  intro X n; rw [getD_pre X (by omega)]; rfl

/-- Definition by cases on bit `j` of a tt-functional is a tt-functional. -/
theorem IsTTFunctional.ite_eq {C Φ Ψ : Oracle → Oracle} (hC : IsTTFunctional C)
    (hΦ : IsTTFunctional Φ) (hΨ : IsTTFunctional Ψ) (j : ℕ) (b : Bool) :
    IsTTFunctional fun B n => if C B j = b then Φ B n else Ψ B n := by
  have hsel : IsTTFunctional fun Q n =>
      if Q (2 * j) = b then Q (2 * (2 * n) + 1) else Q (2 * (2 * n + 1) + 1) := by
    refine isTTFunctional_of_use (u := fun n => 4 * n + 2 * j + 4)
      (t := fun n L => if L.getD (2 * j) false = b then L.getD (4 * n + 1) false
        else L.getD (4 * n + 3) false) ?_ ?_ ?_
    · exact Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id) (Primrec.const (2 * j)))
        (Primrec.const 4)
    · exact Primrec.ite (Primrec.eq.comp (getD_primrec.comp Primrec.snd (Primrec.const _))
        (Primrec.const b))
        (getD_primrec.comp Primrec.snd (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst) (Primrec.const 1)))
        (getD_primrec.comp Primrec.snd (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst) (Primrec.const 3)))
    · intro X n
      rw [getD_pre X (by omega), getD_pre X (by omega), getD_pre X (by omega)]
      congr 2 <;> omega
  have := hsel.comp (hC.join (hΦ.join hΨ))
  convert this using 1
  funext B n
  simp only [Function.comp, ojoin_even, ojoin_odd]

/-- Definition by cases on the truth of a bit of a tt-functional. -/
theorem IsTTFunctional.ite {C Φ Ψ : Oracle → Oracle} (hC : IsTTFunctional C)
    (hΦ : IsTTFunctional Φ) (hΨ : IsTTFunctional Ψ) (j : ℕ) :
    IsTTFunctional fun B n => if C B j = true then Φ B n else Ψ B n :=
  hC.ite_eq hΦ hΨ j true

/-- Selecting, according to bit `2j` of the argument, the even or the odd half. -/
theorem isTTFunctional_select (j : ℕ) (b : Bool) :
    IsTTFunctional fun B n => if B (2 * j) = b then B (2 * n) else B (2 * n + 1) :=
  isTTFunctional_evens.ite_eq isTTFunctional_evens isTTFunctional_odds j b

@[simp] theorem evens_ojoin (A B : Oracle) : evens (ojoin A B) = A := by
  funext n; exact ojoin_even A B n

@[simp] theorem odds_ojoin (A B : Oracle) : odds (ojoin A B) = B := by
  funext n; exact ojoin_odd A B n

theorem evensL_pre (A : Oracle) (n : ℕ) : evensL n (pre A (2 * n + 2)) = pre (evens A) (n + 1) := by
  simp only [evensL, pre]
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.mp hi
  rw [← pre, getD_pre A (by omega)]; rfl

theorem oddsL_pre (A : Oracle) (n : ℕ) : oddsL n (pre A (2 * n + 2)) = pre (odds A) (n + 1) := by
  simp only [oddsL, pre]
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.mp hi
  rw [← pre, getD_pre A (by omega)]; rfl

/-- 2-adic addition of the two halves of the argument is a tt-functional. -/
theorem isTTFunctional_addHalves :
    IsTTFunctional fun A => (Z2.of (evens A) + Z2.of (odds A) : Z2) := by
  refine isTTFunctional_of_use (u := fun n => 2 * n + 2)
    (t := fun n L => ((val (evensL n L) + val (oddsL n L)) % 2 ^ (n + 1) / 2 ^ n == 1)) ?_ ?_ ?_
  · exact Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  · refine Primrec.beq.comp (Primrec.nat_div.comp (Primrec.nat_mod.comp
      (Primrec.nat_add.comp (val_primrec.comp evensL_primrec) (val_primrec.comp oddsL_primrec))
      (pow_primrec.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst)))
      (pow_primrec.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 1)
  · intro X n
    rw [evensL_pre, oddsL_pre, val_pre, val_pre]
    exact ofSeq_apply (fun k => (trunc (evens X) k + trunc (odds X) k) % 2 ^ k) n

/-- 2-adic negation is a tt-functional. -/
theorem isTTFunctional_neg : IsTTFunctional fun A => (-Z2.of A : Z2) := by
  refine isTTFunctional_of_use (u := fun n => n + 1)
    (t := fun n L => ((2 ^ (n + 1) - val L) % 2 ^ (n + 1) / 2 ^ n == 1)) Primrec.succ ?_ ?_
  · refine Primrec.beq.comp (Primrec.nat_div.comp (Primrec.nat_mod.comp
      (Primrec.nat_sub.comp (pow_primrec.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst))
        (val_primrec.comp Primrec.snd))
      (pow_primrec.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst)))
      (pow_primrec.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 1)
  · intro X n
    rw [val_pre]
    exact ofSeq_apply (fun k => (2 ^ k - trunc X k) % 2 ^ k) n

theorem IsTTFunctional.add {Φ Ψ : Oracle → Oracle} (hΦ : IsTTFunctional Φ)
    (hΨ : IsTTFunctional Ψ) : IsTTFunctional fun A => (Z2.of (Φ A) + Z2.of (Ψ A) : Z2) := by
  have := isTTFunctional_addHalves.comp (hΦ.join hΨ)
  simpa [Function.comp_def] using this

theorem IsTTFunctional.neg {Φ : Oracle → Oracle} (hΦ : IsTTFunctional Φ) :
    IsTTFunctional fun A => (-Z2.of (Φ A) : Z2) :=
  isTTFunctional_neg.comp hΦ

theorem IsTTFunctional.sub {Φ Ψ : Oracle → Oracle} (hΦ : IsTTFunctional Φ)
    (hΨ : IsTTFunctional Ψ) : IsTTFunctional fun A => (Z2.of (Φ A) - Z2.of (Ψ A) : Z2) := by
  simp only [sub_eq_add_neg]
  exact hΦ.add hΨ.neg

end TT
