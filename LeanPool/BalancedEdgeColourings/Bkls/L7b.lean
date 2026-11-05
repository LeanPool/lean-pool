/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L7a
public import LeanPool.BalancedEdgeColourings.Bkls.LP7

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 7

`lemma7`: let `S₋ ⊆ S₀ ⊆ S₊ \ {a}`, `a ∈ S₊`, `d = |S₀|`, `s = d - |S₋| ≥ 2`, `r = |S₊| - |S₋|`. If
`n_{S₀} = 2` in an optimal colouring and `[S₋ ∪ {a}, S₊]_d` has at least
`C(r - 1, s - 1) / (s - 1) - 1` empty squares, then an `(S₊ \ (S₋ ∪ {a}))`-recolouring keeps
`n_{S₀} = 2` and empties a square of `[S₋ ∪ {a}, S₊]_d` at distance one from `S₀`.

At a maximum of the potential with no empty square at distance one, the injective assignment of
worsenings to improvements (`imp_image`, `partner_inj`) gives the cumulative constraints
(`cumulative`), and the linear-programming bound `LP7.lp7_bound` contradicts the hypothesis.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L7

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm Sp : Finset (Fin k)} {a : Fin k} {S0 : Finset (Fin k)}

open Classical in
theorem exists_max_nat {α : Type*} (P : α → Prop) (f : α → ℕ) (N : ℕ)
    (hb : ∀ x, P x → f x ≤ N) {x0 : α} (h0 : P x0) : ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by
  by_contra hne
  push Not at hne
  have : ∀ n, ∃ x, P x ∧ n ≤ f x := by
    intro n
    induction n with
    | zero => exact ⟨x0, h0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨x, hx, hn⟩ := ih
      obtain ⟨y, hy, hlt⟩ := hne x hx
      exact ⟨y, hy, by omega⟩
  obtain ⟨x, hx, hn⟩ := this (N + 1)
  have := hb x hx
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Phi_le (c : PEC G (Fin k)) :
    Phi Sm Sp a S0 c ≤ Fintype.card (Finset (Fin k)) * (#S0 - #Sm + 1) ^ 2 := by
  classical
  unfold Phi
  calc ∑ T, fT Sm Sp a S0 c T ≤ ∑ _T : Finset (Fin k), (#S0 - #Sm + 1) ^ 2 :=
        sum_le_sum fun T _ => by
          unfold fT
          split_ifs
          · exact Nat.pow_le_pow_left (Nat.sub_le _ _) 2
          · exact Nat.zero_le _
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul]

open Classical in
/-- Empty squares of `𝒯` with `lo ≤ dist < hi`. -/
noncomputable def Band (Sm Sp : Finset (Fin k)) (a : Fin k) (S0 : Finset (Fin k))
    (c : PEC G (Fin k)) (lo hi : ℕ) : Finset (Finset (Fin k)) :=
  univ.filter fun T => In7 Sm Sp a S0 T ∧ cnt c T = 0 ∧ lo ≤ #(T \ S0) ∧ #(T \ S0) < hi

open Classical in
/-- Empty squares of `𝒯` at distance `j`. -/
noncomputable def oo (Sm Sp : Finset (Fin k)) (a : Fin k) (S0 : Finset (Fin k))
    (c : PEC G (Fin k)) (j : ℕ) : ℕ :=
  #(univ.filter fun T => In7 Sm Sp a S0 T ∧ cnt c T = 0 ∧ #(T \ S0) = j)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem band_sum (c : PEC G (Fin k)) (lo hi : ℕ) (g : ℕ → ℕ) :
    ∑ T ∈ Band Sm Sp a S0 c lo hi, g #(T \ S0) = ∑ j ∈ Ico lo hi, oo Sm Sp a S0 c j * g j := by
  classical
  rw [← sum_fiberwise_of_maps_to' (g := fun T => #(T \ S0)) (t := Ico lo hi)
    (fun T hT => by
      obtain ⟨-, -, -, h1, h2⟩ := mem_filter.1 hT
      exact mem_Ico.2 ⟨h1, h2⟩)]
  apply sum_congr rfl
  intro j hj
  rw [sum_const, smul_eq_mul]
  congr 1
  unfold oo Band
  congr 1
  ext T
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h5⟩; exact ⟨h1, h2, h5⟩
  · rintro ⟨h1, h2, h5⟩; rw [mem_Ico] at hj; exact ⟨⟨h1, h2, h5 ▸ hj.1, h5 ▸ hj.2⟩, h5⟩
open Classical in
theorem card_A (hSm : Sm ⊆ S0) {Z : Finset (Fin k)} (hZ : In7 Sm Sp a S0 Z) :
    #((Z ∩ S0) \ Sm) + #Sm + #(Z \ S0) = #S0 := by
  have h1 := card_sdiff_add_card_inter Z S0
  have h2 := card_sdiff_add_card_eq_card (show Sm ⊆ Z ∩ S0 from subset_inter hZ.1 hSm)
  have h3 := hZ.2.2.2
  omega

open Classical in
theorem card_B (hS0 : S0 ⊆ Sp) {Z : Finset (Fin k)} (hZ : In7 Sm Sp a S0 Z) :
    #(Rc Sm Sp a \ (Z ∪ S0)) + #S0 + #(Z \ S0) = #Sp := by
  have e : Rc Sm Sp a \ (Z ∪ S0) = Sp \ (Z ∪ S0) := by
    ext x
    simp only [mem_sdiff, mem_union, mem_Rc]
    constructor
    · rintro ⟨⟨h1, -, -⟩, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩
      exact ⟨⟨h1, fun h => h4 (Or.inl (hZ.1 h)), fun e => h4 (Or.inl (e ▸ hZ.2.1))⟩, h4⟩
  rw [e]
  have h1 := card_sdiff_add_card_eq_card (union_subset hZ.2.2.1 hS0)
  have h2 := card_union_add_card_inter Z S0
  have h3 := card_sdiff_add_card_inter Z S0
  have h4 := hZ.2.2.2
  omega

open Classical in
theorem card_B0 (hSm : Sm ⊆ S0) (hS0 : S0 ⊆ Sp) (haS0 : a ∉ S0) (ha : a ∈ Sp) :
    #(Rc Sm Sp a \ (S0 ∪ S0)) + #S0 + 1 = #Sp := by
  rw [union_self]
  have e : Rc Sm Sp a \ S0 = (Sp \ S0).erase a := by
    ext x
    simp only [mem_sdiff, mem_erase, mem_Rc]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h3, h1, h4⟩
    · rintro ⟨h3, h1, h4⟩; exact ⟨⟨h1, fun h => h4 (hSm h), h3⟩, h4⟩
  rw [e, card_erase_of_mem (mem_sdiff.2 ⟨ha, haS0⟩)]
  have := card_sdiff_add_card_eq_card hS0
  have : 0 < #(Sp \ S0) := card_pos.2 ⟨a, mem_sdiff.2 ⟨ha, haS0⟩⟩
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The cumulative constraint at level `t`.** -/
theorem cumulative (hSm : Sm ⊆ S0) (hS0 : S0 ⊆ Sp) (haS0 : a ∉ S0) (ha : a ∈ Sp)
    {c : PEC G (Fin k)} (hopt : IsOptimal c) (h2 : cnt c S0 = 2)
    (hmax : ∀ c'', Rec (Rc Sm Sp a) c c'' → cnt c'' S0 = 2 →
      Phi Sm Sp a S0 c'' ≤ Phi Sm Sp a S0 c)
    (hno1 : ∀ T, In7 Sm Sp a S0 T → #(T \ S0) = 1 → cnt c T ≠ 0) (t : ℕ) :
    ∑ Y ∈ Band Sm Sp a S0 c 2 (t + 1), (#(Y \ S0) - 1) * #(Y \ S0) ≤
      (#S0 - #Sm) * (#Sp - #S0 - 1) + ∑ Z ∈ Band Sm Sp a S0 c 2 t,
        (#S0 - #Sm - #(Z \ S0)) * (#Sp - #S0 - #(Z \ S0)) := by
  classical
  set E := Band Sm Sp a S0 c 2 (t + 1)
  set F := Band Sm Sp a S0 c 2 t
  set Imp := E.biUnion fun Y => (((Y \ S0).erase a) ×ˢ (S0 \ Y)).image
    fun p : Fin k × Fin k => (Y, p.1, p.2)
  set Wor := (insert S0 F).biUnion fun Z => (((Z ∩ S0) \ Sm) ×ˢ (Rc Sm Sp a \ (Z ∪ S0))).image
    fun p : Fin k × Fin k => (Z, p.1, p.2)
  have hinjp : ∀ Y : Finset (Fin k), Function.Injective fun p : Fin k × Fin k => (Y, p.1, p.2) :=
    fun Y p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2
  have hImp : #Imp = ∑ Y ∈ E, (#(Y \ S0) - 1) * #(Y \ S0) := by
    rw [card_biUnion]
    · apply sum_congr rfl
      intro Y hY
      rw [card_image_of_injective _ (hinjp Y), card_product]
      have hY7 := (mem_filter.1 hY).2.1
      rw [card_erase_of_mem (mem_sdiff.2 ⟨hY7.2.1, haS0⟩), card_sdiff_symm hY7.2.2.2]
    · intro Y _ Y' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨q, -, rfl⟩ := mem_image.1 hp
      obtain ⟨q', -, hq'⟩ := mem_image.1 hp'
      exact hne (congrArg Prod.fst hq').symm
  have hS0F : S0 ∉ F := fun h => haS0 (mem_filter.1 h).2.1.2.1
  have hWor : #Wor ≤ (#S0 - #Sm) * (#Sp - #S0 - 1) + ∑ Z ∈ F,
      (#S0 - #Sm - #(Z \ S0)) * (#Sp - #S0 - #(Z \ S0)) := by
    refine card_biUnion_le.trans (le_of_eq ?_)
    rw [sum_insert hS0F]
    congr 1
    · rw [card_image_of_injective _ (hinjp S0), card_product, inter_self,
        card_sdiff_of_subset hSm]
      have := card_B0 hSm hS0 haS0 ha
      congr 1; omega
    · apply sum_congr rfl
      intro Z hZ
      have hZ7 := (mem_filter.1 hZ).2.1
      rw [card_image_of_injective _ (hinjp Z), card_product]
      have h1 := card_A hSm hZ7
      have h2 := card_B hS0 hZ7
      congr 1 <;> omega
  -- the injection
  have himg : ∀ p ∈ Imp, ∃ Z, ImpData (Sm := Sm) (Sp := Sp) (a := a) (S0 := S0) c p.1 p.2.1
      p.2.2 Z := by
    intro p hp
    obtain ⟨Y, hY, hp⟩ := mem_biUnion.1 hp
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    obtain ⟨-, hY7, hY0, hj, -⟩ := mem_filter.1 hY
    exact imp_image hSm hS0 haS0 hopt h2 hmax hno1 hY7 hY0 hj hq1 hq2
  choose! Zf hZf using himg
  have hmaps : ∀ p ∈ Imp, (Zf p, p.2.2, p.2.1) ∈ Wor := by
    intro p hp
    have hd := hZf p hp
    obtain ⟨Y, hY, hp'⟩ := mem_biUnion.1 hp
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp'
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    obtain ⟨-, hY7, hY0, hj, hYt⟩ := mem_filter.1 hY
    obtain ⟨hZw, hyZ, hxZ, -⟩ := hd
    obtain ⟨hxa, hxY, hxS⟩ : q.1 ≠ a ∧ q.1 ∈ Y ∧ q.1 ∉ S0 := by
      rw [mem_erase, mem_sdiff] at hq1; exact ⟨hq1.1, hq1.2.1, hq1.2.2⟩
    obtain ⟨hyS, hyY⟩ := mem_sdiff.1 hq2
    refine mem_biUnion.2 ⟨Zf (Y, q.1, q.2), ?_, mem_image.2 ⟨(q.2, q.1), mem_product.2 ⟨?_, ?_⟩,
      rfl⟩⟩
    · rcases hZw with e | ⟨h7, h0, h2', hlt⟩
      · rw [e]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, h7, h0, h2', by simp only at hlt; omega⟩)
    · exact mem_sdiff.2 ⟨mem_inter.2 ⟨hyZ, hyS⟩, fun h => hyY (hY7.1 h)⟩
    · exact mem_sdiff.2 ⟨mem_Rc.2 ⟨hY7.2.2.1 hxY, fun h => hxS (hSm h), hxa⟩,
        fun h => (mem_union.1 h).elim hxZ hxS⟩
  have hinj : Set.InjOn (fun p => (Zf p, p.2.2, p.2.1)) (Imp : Set _) := by
    intro p hp q hq heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hZ, hy, hx⟩ := heq
    have hdp := hZf p hp
    have hdq := hZf q hq
    obtain ⟨Y1, -, hp1⟩ := mem_biUnion.1 hp
    obtain ⟨u1, -, rfl⟩ := mem_image.1 hp1
    obtain ⟨Y2, -, hq2⟩ := mem_biUnion.1 hq
    obtain ⟨u2, -, rfl⟩ := mem_image.1 hq2
    simp only at hZ hy hx hdp hdq ⊢
    obtain ⟨x, y⟩ := u1
    obtain ⟨x', y'⟩ := u2
    simp only at hy hx hZ hdp hdq ⊢
    subst hy hx
    rw [← hZ] at hdq
    set Z := Zf (Y1, x, y)
    suffices hYY : Y1 = Y2 by rw [hYY]
    obtain ⟨-, -, -, t1⟩ := hdp
    obtain ⟨-, -, -, t2⟩ := hdq
    rcases t1 with ⟨hA1, hA1'⟩ | ⟨hxy1, hS1, hU1, hc1⟩ <;>
      rcases t2 with ⟨hA2, hA2'⟩ | ⟨hxy2, hS2, hU2, hc2⟩
    · rw [← swapSet_swapSet x y Y1, ← hA1, hA2, swapSet_swapSet]
    · omega
    · omega
    · obtain ⟨-, -, -, -, hcU1, -⟩ := lemma2_one' hopt hxy1 hS1
      obtain ⟨-, -, -, -, hcU2, -⟩ := lemma2_one' hopt hxy1 hS2
      have hU2' : Z = partner c hxy1 (swapSet x y Y2) ∨
          swapSet x y Z = partner c hxy1 (swapSet x y Y2) := hU2
      have hUU : partner c hxy1 (swapSet x y Y1) = partner c hxy1 (swapSet x y Y2) := by
        rcases hU1 with e1 | e1 <;> rcases hU2' with e2 | e2
        · rw [← e1, ← e2]
        · exfalso
          rw [← e1] at hcU1
          rw [← e2, swapSet_swapSet] at hcU2
          omega
        · exfalso
          rw [← e1, swapSet_swapSet] at hcU1
          rw [← e2] at hcU2
          omega
        · rw [← e1, ← e2]
      have := partner_inj hopt hxy1 hS1 hS2 hUU
      rw [← swapSet_swapSet x y Y1, this, swapSet_swapSet]
  have := card_le_card_of_injOn _ (fun p hp => hmaps p hp) hinj
  rw [hImp] at this
  exact this.trans hWor

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 7.** -/
theorem lemma7 (hSm : Sm ⊆ S0) (hS0 : S0 ⊆ Sp) (haS0 : a ∉ S0) (ha : a ∈ Sp)
    (hs : 2 ≤ #S0 - #Sm) {c : PEC G (Fin k)} (hopt : IsOptimal c) (h2 : cnt c S0 = 2)
    (ho : (((#Sp - #Sm - 1).choose (#S0 - #Sm - 1) : ℕ) : ℚ) / (((#S0 - #Sm : ℕ) : ℚ) - 1) - 1 ≤
      #(univ.filter fun T => In7 Sm Sp a S0 T ∧ cnt c T = 0)) :
    ∃ c', Rec (Rc Sm Sp a) c c' ∧ cnt c' S0 = 2 ∧
      ∃ T, In7 Sm Sp a S0 T ∧ #(T \ S0) = 1 ∧ cnt c' T = 0 := by
  classical
  obtain ⟨cs, ⟨hrec, hcs2⟩, hmax⟩ := exists_max_nat
    (fun c' => Rec (Rc Sm Sp a) c c' ∧ cnt c' S0 = 2) (Phi Sm Sp a S0)
    (Fintype.card (Finset (Fin k)) * (#S0 - #Sm + 1) ^ 2) (fun c' _ => Phi_le c')
    (x0 := c) ⟨Rec.self hopt, h2⟩
  by_cases hdone : ∃ T, In7 Sm Sp a S0 T ∧ #(T \ S0) = 1 ∧ cnt cs T = 0
  · exact ⟨cs, hrec, hcs2, hdone⟩
  exfalso
  push Not at hdone
  have hopts := hrec.opt
  have hmax' : ∀ c'', Rec (Rc Sm Sp a) cs c'' → cnt c'' S0 = 2 →
      Phi Sm Sp a S0 c'' ≤ Phi Sm Sp a S0 cs := fun c'' h h2'' => hmax c'' ⟨hrec.trans h, h2''⟩
  -- the parameters of the linear program
  set s := #S0 - #Sm with hsdef
  set r := #Sp - #Sm with hrdef
  have hSmS0 := card_le_card hSm
  have hS0Sp : #S0 + 1 ≤ #Sp := by
    have := card_le_card (insert_subset ha hS0)
    rwa [card_insert_of_notMem haS0] at this
  have hrs : s + 1 ≤ r := by omega
  set o : ℕ → ℚ := fun j => (oo Sm Sp a S0 cs j : ℚ)
  have hC : ∀ t, 2 ≤ t → t ≤ s → ∑ j ∈ Ico 2 (t + 1), LP7.D j * o j ≤
      (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) + ∑ i ∈ Ico 2 t, LP7.W r s i * o i := by
    intro t ht2 hts
    have hcum := cumulative hSm hS0 haS0 ha hopts hcs2 hmax' hdone t
    rw [band_sum cs 2 (t + 1) (fun j => (j - 1) * j), band_sum cs 2 t
      (fun j => (s - j) * (#Sp - #S0 - j))] at hcum
    have hq : ((∑ j ∈ Ico 2 (t + 1), oo Sm Sp a S0 cs j * ((j - 1) * j) : ℕ) : ℚ) ≤
        (((#S0 - #Sm) * (#Sp - #S0 - 1) + ∑ j ∈ Ico 2 t,
          oo Sm Sp a S0 cs j * ((s - j) * (#Sp - #S0 - j)) : ℕ) : ℚ) := by exact_mod_cast hcum
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum] at hq
    have eL : ∑ j ∈ Ico 2 (t + 1), LP7.D j * o j = ∑ j ∈ Ico 2 (t + 1),
        (oo Sm Sp a S0 cs j : ℚ) * (((j - 1 : ℕ) : ℚ) * (j : ℚ)) := by
      apply sum_congr rfl
      intro j hj
      have : 1 ≤ j := by rw [mem_Ico] at hj; omega
      simp only [o, LP7.D]
      rw [Nat.cast_sub this]; push_cast; ring
    have eR : ∑ i ∈ Ico 2 t, LP7.W r s i * o i = ∑ i ∈ Ico 2 t,
        (oo Sm Sp a S0 cs i : ℚ) * (((s - i : ℕ) : ℚ) * ((#Sp - #S0 - i : ℕ) : ℚ)) := by
      apply sum_congr rfl
      intro i _
      simp only [o, LP7.W]
      rw [show r - s - i = #Sp - #S0 - i by omega]
      ring
    rw [eL, eR, show r - s - 1 = #Sp - #S0 - 1 by omega]
    linarith
  have hlp := LP7.lp7_bound (r := r) (s := s) hs hrs o (fun j => by positivity) hC
  -- all empty squares are at distance `2..s`
  have hall : ∑ j ∈ Ico 2 (s + 1), o j =
      (#(univ.filter fun T => In7 Sm Sp a S0 T ∧ cnt cs T = 0) : ℚ) := by
    have := band_sum (Sm := Sm) (Sp := Sp) (a := a) (S0 := S0) cs 2 (s + 1) (fun _ => 1)
    simp only [mul_one, sum_const, smul_eq_mul] at this
    simp only [o]
    rw [← Nat.cast_sum, ← this]
    congr 2
    unfold Band
    ext T
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2', -, -⟩; exact ⟨h1, h2'⟩
    · rintro ⟨h1, h2'⟩
      have hb := dist_bounds hSm haS0 h1
      refine ⟨h1, h2', ?_, by omega⟩
      by_contra hlt
      exact hdone T h1 (by omega) h2'
  have hinv := hrec.card_filter (In7 Sm Sp a S0) (fun T T' hc h => In7_iff_of T T' hc h) 0
  rw [hall, hinv] at hlp
  -- the contradiction
  have hs1 : (0 : ℚ) < (s : ℚ) - 1 := by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hs
    linarith
  have key : (((r - 1).choose (s - 1) : ℕ) - (s : ℚ)) / ((s : ℚ) - 1) <
      (((r - 1).choose (s - 1) : ℕ) : ℚ) / ((s : ℚ) - 1) - 1 := by
    rw [sub_div, div_eq_mul_inv (s : ℚ)]
    have : (s : ℚ) * ((s : ℚ) - 1)⁻¹ > 1 := by
      rw [gt_iff_lt, ← div_eq_mul_inv, one_lt_div hs1]; linarith
    linarith
  linarith
end Bkls.L7

end LeanPool.BalancedEdgeColourings
