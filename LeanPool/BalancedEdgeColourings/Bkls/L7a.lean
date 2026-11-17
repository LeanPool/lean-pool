/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Rec

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 7, part (a): improvements and worsenings

Setting: `S₋ ⊆ S₀ ⊆ S₊`, `a ∈ S₊ \ S₀`, `d = |S₀|`, `n_{S₀} = 2`. The squares are
`𝒯 = [S₋ ∪ {a}, S₊]_d` (`In7`), at distance `dist T = |T \ S₀|` from `S₀`; recolourings use the
colours `Rc = S₊ \ (S₋ ∪ {a})`. Among the recolourings with `n_{S₀} = 2` take one maximising
`Φ = Σ_{T ∈ 𝒯 empty} (s + 1 - dist T)²` (a stand-in for the paper's lexicographic order; only the
strictly decreasing gaps are used). If no square at distance `1` is empty, every improvement
`(Y, x, y)` of an empty square `Y` at distance `j ≥ 2` (`Y' = Y - x + y` closer) comes with a
worsening `Z → Z - y + x` where `Z = S₀` or `Z` is an empty square at distance in `[2, j)`
(`imp_image`), with enough information to make the assignment injective.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L7

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

section Setup

variable (Sm Sp : Finset (Fin k)) (a : Fin k) (S0 : Finset (Fin k))

open Classical in
/-- The recolouring colours `S₊ \ (S₋ ∪ {a})`. -/
def Rc : Finset (Fin k) := (Sp \ Sm).erase a

open Classical in
/-- `T ∈ [S₋ ∪ {a}, S₊]_d`. -/
def In7 (T : Finset (Fin k)) : Prop := Sm ⊆ T ∧ a ∈ T ∧ T ⊆ Sp ∧ #T = #S0

open Classical in
/-- The potential term of `T`. -/
noncomputable def fT (c : PEC G (Fin k)) (T : Finset (Fin k)) : ℕ :=
  if In7 Sm Sp a S0 T ∧ cnt c T = 0 then (#S0 - #Sm + 1 - #(T \ S0)) ^ 2 else 0

open Classical in
/-- The potential. -/
noncomputable def Phi (c : PEC G (Fin k)) : ℕ := ∑ T, fT Sm Sp a S0 c T

end Setup

variable {Sm Sp : Finset (Fin k)} {a : Fin k} {S0 : Finset (Fin k)}

open Classical in
theorem mem_Rc {x : Fin k} : x ∈ Rc Sm Sp a ↔ x ∈ Sp ∧ x ∉ Sm ∧ x ≠ a := by
  unfold Rc; rw [mem_erase, mem_sdiff]; tauto

open Classical in
theorem In7_iff_of (T T' : Finset (Fin k)) (hc : #T = #T')
    (h : ∀ x, x ∉ Rc Sm Sp a → (x ∈ T ↔ x ∈ T')) : In7 Sm Sp a S0 T ↔ In7 Sm Sp a S0 T' := by
  have hR : ∀ x, x ∉ Sp ∨ x ∈ Sm ∨ x = a → x ∉ Rc Sm Sp a := fun x hx hR => by
    rw [mem_Rc] at hR; tauto
  unfold In7
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun x hx => (h x (hR x (Or.inr (Or.inl hx)))).1 (h1 hx),
      (h a (hR a (Or.inr (Or.inr rfl)))).1 h2, fun x hx => ?_, hc ▸ h4⟩
    by_contra hxp
    exact hxp (h3 ((h x (hR x (Or.inl hxp))).2 hx))
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun x hx => (h x (hR x (Or.inr (Or.inl hx)))).2 (h1 hx),
      (h a (hR a (Or.inr (Or.inr rfl)))).2 h2, fun x hx => ?_, hc ▸ h4⟩
    by_contra hxp
    exact hxp (h3 ((h x (hR x (Or.inl hxp))).1 hx))

open Classical in
theorem In7_swap {x y : Fin k} (hx : x ∈ Rc Sm Sp a) (hy : y ∈ Rc Sm Sp a) (T : Finset (Fin k)) :
    In7 Sm Sp a S0 (swapSet x y T) ↔ In7 Sm Sp a S0 T :=
  In7_iff_of _ _ (card_swapSet x y T) fun z hz => by
    have hzx : z ≠ x := fun e => hz (e ▸ hx)
    have hzy : z ≠ y := fun e => hz (e ▸ hy)
    rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hzx hzy]

open Classical in
theorem swap_ne_iff {x y : Fin k} (_ : x ≠ y) {T : Finset (Fin k)} :
    swapSet x y T ≠ T ↔ (x ∈ T ↔ y ∉ T) := by
  constructor
  · intro h
    by_contra h'
    exact h (swapSet_eq_of_iff (by tauto))
  · intro h e
    by_cases hx : x ∈ T
    · have hy : y ∉ T := h.1 hx
      have : y ∈ swapSet x y T := by rw [mem_swapSet, Equiv.swap_apply_right]; exact hx
      rw [e] at this; exact hy this
    · have hy : y ∈ T := by by_contra hy; exact hx (h.2 hy)
      have : x ∈ swapSet x y T := by rw [mem_swapSet, Equiv.swap_apply_left]; exact hy
      rw [e] at this; exact hx this

open Classical in
/-- Moving `x ∉ S₀` out and `y ∈ S₀` in brings `T` closer. -/
theorem dist_closer {x y : Fin k} {T : Finset (Fin k)} (hx : x ∈ T) (hxS : x ∉ S0) (hy : y ∉ T)
    (hyS : y ∈ S0) : #(swapSet x y T \ S0) + 1 = #(T \ S0) := by
  rw [swapSet_eq_insert_erase hx hy]
  have : insert y (T.erase x) \ S0 = (T \ S0).erase x := by
    ext z; simp only [mem_sdiff, mem_insert, mem_erase]
    constructor
    · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
      · exact absurd (h1 ▸ hyS) h3
      · exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
  rw [this, card_erase_of_mem (mem_sdiff.2 ⟨hx, hxS⟩)]
  have : 0 < #(T \ S0) := card_pos.2 ⟨x, mem_sdiff.2 ⟨hx, hxS⟩⟩
  omega

open Classical in
/-- Moving `y ∈ S₀` out and `x ∉ S₀` in moves `T` away. -/
theorem dist_farther {x y : Fin k} {T : Finset (Fin k)} (hy : y ∈ T) (hyS : y ∈ S0) (hx : x ∉ T)
    (hxS : x ∉ S0) : #(swapSet x y T \ S0) = #(T \ S0) + 1 := by
  rw [swapSet_comm, swapSet_eq_insert_erase hy hx]
  have : insert x (T.erase y) \ S0 = insert x (T \ S0) := by
    ext z; simp only [mem_sdiff, mem_insert, mem_erase]
    constructor
    · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h2, h3⟩
    · rintro (rfl | ⟨h2, h3⟩)
      · exact ⟨Or.inl rfl, hxS⟩
      · exact ⟨Or.inr ⟨fun e => h3 (e ▸ hyS), h2⟩, h3⟩
  rw [this, card_insert_of_notMem (fun h => hx (mem_sdiff.1 h).1)]

open Classical in
/-- Squares of `𝒯` are at distance `1 ≤ dist ≤ s`. -/
theorem dist_bounds (hSm : Sm ⊆ S0) (haS0 : a ∉ S0) {T : Finset (Fin k)}
    (hT : In7 Sm Sp a S0 T) : 1 ≤ #(T \ S0) ∧ #(T \ S0) ≤ #S0 - #Sm := by
  obtain ⟨h1, h2, -, h4⟩ := hT
  refine ⟨card_pos.2 ⟨a, mem_sdiff.2 ⟨h2, haS0⟩⟩, ?_⟩
  have hsub : T \ S0 ⊆ T \ Sm := sdiff_subset_sdiff le_rfl hSm
  have := card_le_card hsub
  have := card_sdiff_add_card_eq_card h1
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Phi_diff {c c' : PEC G (Fin k)} (D : Finset (Finset (Fin k)))
    (hD : ∀ T, T ∉ D → cnt c' T = cnt c T) :
    (Phi Sm Sp a S0 c' : ℤ) - Phi Sm Sp a S0 c =
      ∑ T ∈ D, ((fT Sm Sp a S0 c' T : ℤ) - fT Sm Sp a S0 c T) := by
  classical
  unfold Phi
  push_cast
  rw [← sum_sub_distrib]
  symm
  apply sum_subset (subset_univ D)
  intro T _ hT
  simp [fT, hD T hT]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem fT_of_ne {c : PEC G (Fin k)} {T : Finset (Fin k)} (h : cnt c T ≠ 0) :
    fT Sm Sp a S0 c T = 0 := by
  classical
  unfold fT; rw [ite_eq_right (fun h' => h h'.2)]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem fT_of_not {c : PEC G (Fin k)} {T : Finset (Fin k)} (h : ¬ In7 Sm Sp a S0 T) :
    fT Sm Sp a S0 c T = 0 := by
  classical
  unfold fT; rw [ite_eq_right (fun h' => h h'.1)]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem fT_of_zero {c : PEC G (Fin k)} {T : Finset (Fin k)} (hT : In7 Sm Sp a S0 T)
    (h : cnt c T = 0) : fT Sm Sp a S0 c T = (#S0 - #Sm + 1 - #(T \ S0)) ^ 2 := by
  classical
  unfold fT; rw [ite_eq_left ⟨hT, h⟩]
open Classical in
theorem w_gap (s j j' : ℤ) (h : j' + 1 = j) :
    (s + 1 - j') ^ 2 - (s + 1 - j) ^ 2 = 2 * (s + 1 - j) + 1 := by
  subst h; ring

open Classical in
theorem cast_w {s i : ℕ} (h : i ≤ s + 1) :
    (((s + 1 - i) ^ 2 : ℕ) : ℤ) = ((s : ℤ) + 1 - i) ^ 2 := by
  rw [Nat.cast_pow, Nat.cast_sub h]; push_cast; ring

open Classical in
/-- The data attached to an improvement `(Y, x, y)`: a worsening of `Z`. -/
def ImpData (c : PEC G (Fin k)) (Y : Finset (Fin k)) (x y : Fin k) (Z : Finset (Fin k)) :
    Prop :=
  (Z = S0 ∨ (In7 Sm Sp a S0 Z ∧ cnt c Z = 0 ∧ 2 ≤ #(Z \ S0) ∧ #(Z \ S0) < #(Y \ S0))) ∧
    y ∈ Z ∧ x ∉ Z ∧
    ((Z = swapSet x y Y ∧ cnt c (swapSet x y Z) = 0) ∨
      (∃ hxy : x ≠ y, cnt c (swapSet x y Y) = cnt c (swapSet x y (swapSet x y Y)) + 1 ∧
        (Z = partner c hxy (swapSet x y Y) ∨ swapSet x y Z = partner c hxy (swapSet x y Y)) ∧
        1 ≤ cnt c (swapSet x y Z)))

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Every improvement is matched with a worsening.** -/
theorem imp_image (hSm : Sm ⊆ S0) (hS0 : S0 ⊆ Sp) (haS0 : a ∉ S0) {c : PEC G (Fin k)}
    (hopt : IsOptimal c) (h2 : cnt c S0 = 2)
    (hmax : ∀ c'', Rec (Rc Sm Sp a) c c'' → cnt c'' S0 = 2 →
      Phi Sm Sp a S0 c'' ≤ Phi Sm Sp a S0 c)
    (hno1 : ∀ T, In7 Sm Sp a S0 T → #(T \ S0) = 1 → cnt c T ≠ 0)
    {Y : Finset (Fin k)} (hY : In7 Sm Sp a S0 Y) (hY0 : cnt c Y = 0) (hj : 2 ≤ #(Y \ S0))
    {x y : Fin k} (hx : x ∈ (Y \ S0).erase a) (hy : y ∈ S0 \ Y) :
    ∃ Z, ImpData (Sm := Sm) (Sp := Sp) (a := a) (S0 := S0) c Y x y Z := by
  obtain ⟨hxa, hxY, hxS⟩ : x ≠ a ∧ x ∈ Y ∧ x ∉ S0 := by
    rw [mem_erase, mem_sdiff] at hx; exact ⟨hx.1, hx.2.1, hx.2.2⟩
  obtain ⟨hyS, hyY⟩ := mem_sdiff.1 hy
  have hxy : x ≠ y := fun e => hyY (e ▸ hxY)
  have hxR : x ∈ Rc Sm Sp a := mem_Rc.2 ⟨hY.2.2.1 hxY, fun h => hxS (hSm h), hxa⟩
  have hyR : y ∈ Rc Sm Sp a := mem_Rc.2 ⟨hS0 hyS, fun h => hyY (hY.1 h),
    fun e => haS0 (e ▸ hyS)⟩
  set Y' := swapSet x y Y with hY'def
  have hiY' : swapSet x y Y' = Y := swapSet_swapSet x y Y
  have hY'7 : In7 Sm Sp a S0 Y' := (In7_swap hxR hyR Y).2 hY
  have hdY' : #(Y' \ S0) + 1 = #(Y \ S0) := dist_closer hxY hxS hyY hyS
  have hyY' : y ∈ Y' := by rw [hY'def, swapSet_eq_insert_erase hxY hyY]; exact mem_insert_self _ _
  have hxY' : x ∉ Y' := by
    rw [hY'def, swapSet_eq_insert_erase hxY hyY, mem_insert, mem_erase]
    rintro (h | ⟨h, -⟩)
    · exact hxy h
    · exact h rfl
  have hS0Y : S0 ≠ Y := fun e => haS0 (e ▸ hY.2.1)
  have hS0Y' : S0 ≠ Y' := fun e => haS0 (e ▸ hY'7.2.1)
  have hYY' : Y' ≠ Y := fun e => hyY (e ▸ hyY')
  have hds := dist_bounds hSm haS0 hY
  -- the weight gap
  set s := #S0 - #Sm
  have hle := lemma2_le hopt x y Y'
  rw [hiY', hY0] at hle
  rcases (show cnt c Y' = 0 ∨ cnt c Y' = 1 ∨ cnt c Y' = 2 by omega) with h0 | h1 | h2'
  · -- type A: `Y'` itself is empty
    refine ⟨Y', Or.inr ⟨hY'7, h0, ?_, by omega⟩, hyY', hxY', Or.inl ⟨rfl, by rw [hiY', hY0]⟩⟩
    have := (dist_bounds hSm haS0 hY'7).1
    by_contra hlt
    exact hno1 Y' hY'7 (by omega) h0
  · -- difference one
    obtain ⟨n1, n2, n3, n4, hU, c'', hrec, e1, e2, e3, e4, e5⟩ :=
      rec_one hopt hxy hxR hyR (S := Y') (by rw [h1, hiY', hY0])
    set U := partner c hxy Y' with hUdef
    rw [hiY'] at n2 n4 e1 e2 e5
    have hU1 : 1 ≤ cnt c U := by omega
    by_cases hS0U : S0 = U ∨ S0 = swapSet x y U
    · refine ⟨S0, Or.inl rfl, hyS, hxS, Or.inr ⟨hxy, by rw [hiY', hY0, h1], ?_, ?_⟩⟩
      · rcases hS0U with e | e
        · exact Or.inl e
        · right; rw [e, swapSet_swapSet]
      · rcases hS0U with e | e
        · rw [e]; rw [← e] at hU ⊢; omega
        · rw [e, swapSet_swapSet]; exact hU1
    push Not at hS0U
    obtain ⟨hS0U1, hS0U2⟩ := hS0U
    have hc2 : cnt c'' S0 = 2 := by rw [e5 S0 hS0Y' hS0Y hS0U1 hS0U2, h2]
    have hmx := hmax c'' hrec hc2
    have hiUU : swapSet x y U ≠ U := by
      intro e; rw [e] at hU; omega
    have hdiff := Phi_diff (Sm := Sm) (Sp := Sp) (a := a) (S0 := S0) (c := c) (c' := c'')
      {Y', Y, U, swapSet x y U} (fun T hT => by
        simp only [mem_insert, mem_singleton, not_or] at hT
        exact e5 T hT.1 hT.2.1 hT.2.2.1 hT.2.2.2)
    rw [sum_insert (by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨hYY', Ne.symm n1, Ne.symm n3⟩),
      sum_insert (by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm n2, Ne.symm n4⟩),
      sum_pair (Ne.symm hiUU)] at hdiff
    rw [fT_of_zero hY'7 (by rw [e1, hY0]), fT_of_ne (by omega : cnt c Y' ≠ 0),
      fT_of_ne (by rw [e2, h1]; omega : cnt c'' Y ≠ 0), fT_of_zero hY hY0,
      fT_of_ne (c := c) (by omega : cnt c U ≠ 0),
      fT_of_ne (c := c'') (by rw [e4]; omega : cnt c'' (swapSet x y U) ≠ 0),
      cast_w (by omega), cast_w (by omega)] at hdiff
    have hUiU : In7 Sm Sp a S0 U ↔ In7 Sm Sp a S0 (swapSet x y U) := (In7_swap hxR hyR U).symm
    have hmx' : (Phi Sm Sp a S0 c'' : ℤ) ≤ Phi Sm Sp a S0 c := by exact_mod_cast hmx
    have hY'Y : (#(Y' \ S0) : ℤ) + 1 = #(Y \ S0) := by exact_mod_cast hdY'
    have hjs : (#(Y \ S0) : ℤ) ≤ s := by exact_mod_cast hds.2
    -- the other pair must be a worsening of an empty square
    by_cases hZ : In7 Sm Sp a S0 (swapSet x y U) ∧ cnt c (swapSet x y U) = 0
    swap
    · exfalso
      have f1 : fT Sm Sp a S0 c'' U = 0 := by
        unfold fT; rw [ite_eq_right]; rintro ⟨h7, hc⟩; rw [e3] at hc; exact hZ ⟨hUiU.1 h7, hc⟩
      have f2 : fT Sm Sp a S0 c (swapSet x y U) = 0 := by
        unfold fT; rw [ite_eq_right hZ]
      rw [f1, f2] at hdiff
      simp only [Nat.cast_zero, sub_zero, zero_sub] at hdiff
      have g1 := (w_gap (s : ℤ) (#(Y \ S0) : ℤ) (#(Y' \ S0) : ℤ) hY'Y); linarith
    obtain ⟨hZ7, hZ0⟩ := hZ
    set Z := swapSet x y U with hZdef
    have hZU : swapSet x y Z = U := by rw [hZdef, swapSet_swapSet]
    have hZne : swapSet x y Z ≠ Z := by rw [hZU]; exact Ne.symm hiUU
    have hdZ := dist_bounds hSm haS0 hZ7
    have hdU := dist_bounds hSm haS0 (hUiU.2 hZ7)
    rw [fT_of_zero (c := c'') (hUiU.2 hZ7) (by rw [e3, hZ0]), fT_of_zero (c := c) hZ7 hZ0,
      cast_w (by omega), cast_w (by omega)] at hdiff
    simp only [Nat.cast_zero, sub_zero, zero_sub] at hdiff
    have hZs : (#(Z \ S0) : ℤ) ≤ s := by exact_mod_cast hdZ.2
    have hUs : (#(U \ S0) : ℤ) ≤ s := by exact_mod_cast hdU.2
    -- which of `x, y` lies in `Z`
    have hxyZ := (swap_ne_iff hxy).1 hZne
    by_cases hxZ : x ∈ Z
    · exfalso
      have hyZ : y ∉ Z := hxyZ.1 hxZ
      have hd := dist_closer hxZ hxS hyZ hyS
      rw [hZU] at hd
      have hd' : (#(U \ S0) : ℤ) + 1 = #(Z \ S0) := by exact_mod_cast hd
      have g1 := (w_gap (s : ℤ) (#(Y \ S0) : ℤ) (#(Y' \ S0) : ℤ) hY'Y)
      have g2 := w_gap (s : ℤ) (#(Z \ S0) : ℤ) (#(U \ S0) : ℤ) hd'; linarith
    have hyZ : y ∈ Z := by by_contra h; exact hxZ (hxyZ.2 h)
    have hd := dist_farther hyZ hyS hxZ hxS
    rw [hZU] at hd
    have hd' : (#(U \ S0) : ℤ) = #(Z \ S0) + 1 := by exact_mod_cast hd
    refine ⟨Z, Or.inr ⟨hZ7, hZ0, ?_, ?_⟩, hyZ, hxZ, Or.inr ⟨hxy, by rw [hiY', hY0, h1], Or.inr hZU,
      by rw [hZU]; exact hU1⟩⟩
    · by_contra hlt
      exact hno1 Z hZ7 (by omega) hZ0
    · by_contra hge
      push Not at hge
      have hge' : (#(Y \ S0) : ℤ) ≤ #(Z \ S0) := by exact_mod_cast hge
      have g1 := (w_gap (s : ℤ) (#(Y \ S0) : ℤ) (#(Y' \ S0) : ℤ) hY'Y)
      have g2 := w_gap (s : ℤ) (#(U \ S0) : ℤ) (#(Z \ S0) : ℤ) hd'.symm; linarith
  · -- difference two: moving the 2-pile improves `Φ`
    exfalso
    obtain ⟨c'', hrec, e1, e2, e3⟩ := rec_two hopt hxy hxR hyR (S := Y') (by rw [h2', hiY', hY0])
    rw [hiY'] at e1 e2 e3
    have hc2 : cnt c'' S0 = 2 := by rw [e3 S0 hS0Y' hS0Y, h2]
    have hmx := hmax c'' hrec hc2
    have hdiff := Phi_diff (Sm := Sm) (Sp := Sp) (a := a) (S0 := S0) (c := c) (c' := c'')
      {Y', Y} (fun T hT => by
        simp only [mem_insert, mem_singleton, not_or] at hT
        exact e3 T hT.1 hT.2)
    rw [sum_pair hYY', fT_of_zero hY'7 (by rw [e1, hY0]), fT_of_ne (by omega : cnt c Y' ≠ 0),
      fT_of_ne (by rw [e2]; omega : cnt c'' Y ≠ 0), fT_of_zero hY hY0,
      cast_w (by omega), cast_w (by omega)] at hdiff
    have hmx' : (Phi Sm Sp a S0 c'' : ℤ) ≤ Phi Sm Sp a S0 c := by exact_mod_cast hmx
    have hY'Y : (#(Y' \ S0) : ℤ) + 1 = #(Y \ S0) := by exact_mod_cast hdY'
    have hjs : (#(Y \ S0) : ℤ) ≤ s := by exact_mod_cast hds.2
    simp only [Nat.cast_zero, sub_zero, zero_sub] at hdiff
    have g1 := (w_gap (s : ℤ) (#(Y \ S0) : ℤ) (#(Y' \ S0) : ℤ) hY'Y); linarith
end Bkls.L7

end LeanPool.BalancedEdgeColourings
