/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordRules

/-!
# Blocks of a word

A handle `u v u⁻¹ v⁻¹`, a cross-cap `y y` and a hole `t s t⁻¹` can be moved past any part of a word
(`slide_block`). For a product of blocks `H` this gives `slide`: the two parts before `H` can be
exchanged.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

universe uu

theorem WEq.of_eq {a b : List Letter} (h : a = b) : WEq.{uu} a b := by rw [h]; exact WEq.refl _

theorem WEq.rot' {w w' : List Letter} (a b : List Letter) (h : w = a ++ b) (h' : w'
  = b ++ a) : WEq.{uu} w w' := by
  rw [h, h']
  exact WEq.rot a b

theorem ruleA' (x : Letter) (u₁ u₂ v₁ v₂ : List Letter) (h1 : NoLab u₁ x.1) (h2 : NoLab u₂ x.1)
    (h3 : NoLab v₁ x.1) (h4 : NoLab v₂ x.1) {w w' : List Letter}
    (h : w = u₁ ++ x :: (u₂ ++ v₁ ++ linv x :: v₂)) (h' : w' = u₂ ++ x ::
      (u₁ ++ v₂ ++ linv x :: v₁)) :
    WEq.{uu} w w' := by
  rw [h, h']
  exact ruleA x h1 h2 h3 h4

theorem ruleB' (x : Letter) (u₁ u₂ v₁ v₂ : List Letter) (h1 : NoLab u₁ x.1) (h2 : NoLab u₂ x.1)
    (h3 : NoLab v₁ x.1) (h4 : NoLab v₂ x.1) {w w' : List Letter}
    (h : w = u₁ ++ x :: (u₂ ++ v₁ ++ x :: v₂)) (h' : w' = u₂ ++ x :: (u₁ ++ winv v₁ ++ x :: winv
      v₂)) :
    WEq.{uu} w w' := by
  rw [h, h']
  exact ruleB x h1 h2 h3 h4

/-- A hole slides. -/
theorem slide_hole (t : Letter) {s A B : List Letter} (hs : NoLab s t.1) (hA : NoLab A t.1)
  (hB : NoLab B t.1) :
    WEq.{uu} (A ++ B ++ t :: s ++ [linv t]) (B ++ A ++ t :: s ++ [linv t]) := by
  have hAB : NoLab (A ++ B) t.1 := noLab_append.mpr ⟨hA, hB⟩
  have c0 : WEq.{uu} (A ++ B ++ t :: s ++ [linv t]) (t :: s ++ linv t :: (A ++ B)) :=
    WEq.rot' (A ++ B) (t :: s ++ [linv t]) (by simp) (by simp)
  have c1 : WEq.{uu} (t :: s ++ linv t :: (A ++ B)) (t :: (A ++ B ++ linv t :: s)) :=
    ruleA' t [] [] s (A ++ B) noLab_nil noLab_nil hs hAB (by simp) (by simp)
  have c2 : WEq.{uu} (t :: (A ++ B ++ linv t :: s)) (A ++ t :: (s ++ linv t :: B)) :=
    ruleA' t [] A B s noLab_nil hA hB hs (by simp) (by simp)
  have c3 : WEq.{uu} (A ++ t :: (s ++ linv t :: B)) (B ++ A ++ t :: s ++ [linv t]) :=
    WEq.rot' (A ++ t :: s ++ [linv t]) B (by simp) (by simp)
  exact c0.trans (c1.trans (c2.trans c3))

/-- The fixed flip of one label. -/
def flipAt (c : ℕ) : ℕ → Bool := fun n => decide (n = c)

theorem map_flipAt_of_noLab {w : List Letter} {c : ℕ} (h : NoLab w c) : w.map (flipL (flipAt c))
  = w := by
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun l hl => ?_
  have := h l hl
  simp [flipL, flipAt, this]

theorem flipL_self (l : Letter) : flipL (flipAt l.1) l = linv l := by
  simp [flipL, flipAt, linv]

theorem flipL_linv (l : Letter) : flipL (flipAt l.1) (linv l) = l := by
  simp [flipL, flipAt, linv]

/-- A cross-cap slides. -/
theorem slide_cap (y : Letter) {A B : List Letter} (hA : NoLab A y.1) (hB : NoLab B y.1) :
    WEq.{uu} (A ++ B ++ [y, y]) (B ++ A ++ [y, y]) := by
  have hB' := noLab_winv.mpr hB
  have hA' := noLab_winv.mpr hA
  have c0 : WEq.{uu} (A ++ B ++ [y, y]) (y :: (A ++ B ++ [y])) :=
    WEq.rot' (A ++ B ++ [y]) [y] (by simp) (by simp)
  have c1 : WEq.{uu} (y :: (A ++ B ++ [y])) (A ++ y :: (winv B ++ [y])) :=
    ruleB' y [] A B [] noLab_nil hA hB noLab_nil (by simp) (by simp [winv])
  have c2 : WEq.{uu} (A ++ y :: (winv B ++ [y])) (y :: (winv B ++ y :: A)) :=
    WEq.rot' A (y :: (winv B ++ [y])) rfl (by simp)
  have c3 : WEq.{uu} (y :: (winv B ++ y :: A)) (winv B ++ y :: y :: winv A) :=
    ruleB' y [] (winv B) [] A noLab_nil hB' noLab_nil hA (by simp) (by simp [winv])
  have c4 : WEq.{uu} (winv B ++ y :: y :: winv A) (y :: y :: (winv A ++ winv B)) :=
    WEq.rot' (winv B) (y :: y :: winv A) rfl (by simp)
  have c5 : WEq.{uu} (y :: y :: (winv A ++ winv B)) (B ++ A ++ [linv y, linv y]) := by
    have := WEq.rev (y :: y :: (winv A ++ winv B))
    refine this.trans (WEq.of_eq ?_)
    simp [winv_append, winv_cons, winv_winv]
  have c6 : WEq.{uu} (B ++ A ++ [linv y, linv y]) (B ++ A ++ [y, y]) := by
    refine (WEq.flip _ (flipAt y.1)).trans (WEq.of_eq ?_)
    rw [List.map_append, List.map_append, map_flipAt_of_noLab hB, map_flipAt_of_noLab hA]
    simp [flipL_linv]
  exact c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))))

/-- The handle on the letters `u`, `v`. -/
def hndB (u v : Letter) : List Letter := [u, v, linv u, linv v]

/-- A handle slides. -/
theorem slide_hnd {u v : Letter} (huv : u.1 ≠ v.1) {A B : List Letter} (hA : NoLab A u.1)
  (hB : NoLab B u.1)
    (hA' : NoLab A v.1) (hB' : NoLab B v.1) :
    WEq.{uu} (A ++ B ++ hndB u v) (B ++ A ++ hndB u v) := by
  have hvu : v.1 ≠ u.1 := fun h => huv h.symm
  have n1 : NoLab [linv v] u.1 := noLab_cons.mpr ⟨hvu, noLab_nil⟩
  have n2 : NoLab [v] u.1 := noLab_cons.mpr ⟨hvu, noLab_nil⟩
  have n3 : NoLab [u] v.1 := noLab_cons.mpr ⟨huv, noLab_nil⟩
  have n4 : NoLab [linv u] v.1 := noLab_cons.mpr ⟨huv, noLab_nil⟩
  have c0 : WEq.{uu} (A ++ B ++ hndB u v) (B ++ u :: v :: linv u :: linv v :: A) :=
    WEq.rot' A (B ++ hndB u v) (by simp) (by simp [hndB])
  have c1 : WEq.{uu} (B ++ u :: v :: linv u :: linv v :: A) (u :: (B ++ linv v :: A ++ linv u ::
    [v])) :=
    ruleA' u B [] [v] (linv v :: A) hB noLab_nil n2 (noLab_cons.mpr ⟨hvu, hA⟩) (by simp) (by simp)
  have c2 : WEq.{uu} (u :: (B ++ linv v :: A ++ linv u :: [v])) (linv u :: v :: u ::
    (B ++ linv v :: A)) :=
    WEq.rot' (u :: (B ++ linv v :: A)) (linv u :: [v]) (by simp) (by simp)
  have c3 : WEq.{uu} (linv u :: v :: u :: (B ++ linv v :: A)) (u :: v :: linv u ::
    (A ++ linv v :: B)) :=
    ruleA' v [linv u] [u] B A n4 n3 hB' hA' (by simp) (by simp)
  have c4 : WEq.{uu} (u :: v :: linv u :: (A ++ linv v :: B)) (linv v ::
    (B ++ u :: v :: linv u :: A)) :=
    WEq.rot' (u :: v :: linv u :: A) (linv v :: B) (by simp) (by simp)
  have c5 : WEq.{uu} (linv v :: (B ++ u :: v :: linv u :: A)) (u :: (linv v :: B ++ A ++ linv u ::
    [v])) :=
    ruleA' u (linv v :: B) [] [v] A (noLab_cons.mpr ⟨hvu, hB⟩) noLab_nil n2 hA (by simp) (by simp)
  have c6 : WEq.{uu} (u :: (linv v :: B ++ A ++ linv u :: [v])) (B ++ A ++ [linv u, v, u, linv v])
    :=
    WEq.rot' [u, linv v] (B ++ A ++ [linv u, v]) (by simp) (by simp)
  have c7 : WEq.{uu} (B ++ A ++ [linv u, v, u, linv v]) (B ++ A ++ hndB u v) := by
    refine (WEq.flip _ (flipAt u.1)).trans (WEq.of_eq ?_)
    rw [List.map_append, List.map_append, map_flipAt_of_noLab hB, map_flipAt_of_noLab hA]
    simp [hndB, flipL, flipAt, linv, hvu]
  exact c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))))

/-- `w` has no label of `H`. -/
def DisjL (H w : List Letter) : Prop := ∀ l ∈ H, NoLab w l.1

/-- The blocks of a word. -/
inductive IsBlock : List Letter → Prop
  | hnd (u v : Letter) (h : u.1 ≠ v.1) : IsBlock (hndB u v)
  | cap (y : Letter) : IsBlock [y, y]
  | hole (t : Letter) (s : List Letter) (h : NoLab s t.1) : IsBlock (t :: s ++ [linv t])

/-- Any block slides. -/
theorem slide_block {U A B : List Letter} (hU : IsBlock U) (hA : DisjL U A) (hB : DisjL U B) :
    WEq.{uu} (A ++ B ++ U) (B ++ A ++ U) := by
  cases hU with
  | hnd u v h =>
    have h1 : u ∈ hndB u v := by simp [hndB]
    have h2 : v ∈ hndB u v := by simp [hndB]
    exact slide_hnd h (hA u h1) (hB u h1) (hA v h2) (hB v h2)
  | cap y => exact slide_cap y (hA y (by simp)) (hB y (by simp))
  | hole t s h =>
    have h1 : t ∈ t :: s ++ [linv t] := by simp
    have := slide_hole.{uu} t h (hA t h1) (hB t h1)
    simpa [List.append_assoc] using this

/-- Products of blocks with pairwise disjoint labels. -/
inductive Blocks : List Letter → Prop
  | nil : Blocks []
  | cons {U H : List Letter} : IsBlock U → DisjL U H → Blocks H → Blocks (U ++ H)

theorem DisjL.symm {a b : List Letter} (h : DisjL a b) : DisjL b a := by
  intro l hl m hm he
  exact h m hm l hl he.symm

theorem DisjL.append_left {a b c : List Letter} (h : DisjL a c) (h' : DisjL b c) : DisjL (a ++ b) c
  := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact h l hl
  · exact h' l hl

theorem DisjL.append_right {a b c : List Letter} (h : DisjL c a) (h' : DisjL c b) : DisjL c
  (a ++ b) :=
  fun l hl => noLab_append.mpr ⟨h l hl, h' l hl⟩

theorem DisjL.left {a b c : List Letter} (h : DisjL (a ++ b) c) : DisjL a c :=
  fun l hl => h l (List.mem_append_left _ hl)

theorem DisjL.right {a b c : List Letter} (h : DisjL (a ++ b) c) : DisjL b c :=
  fun l hl => h l (List.mem_append_right _ hl)

theorem DisjL.inl {a b c : List Letter} (h : DisjL c (a ++ b)) : DisjL c a :=
  fun l hl => (noLab_append.mp (h l hl)).1

theorem DisjL.inr {a b c : List Letter} (h : DisjL c (a ++ b)) : DisjL c b :=
  fun l hl => (noLab_append.mp (h l hl)).2

/-- **Slide.** The two parts before a product of blocks can be exchanged. -/
theorem slide {H : List Letter} (hH : Blocks H) {A B : List Letter} (hA : DisjL H A)
  (hB : DisjL H B) :
    WEq.{uu} (A ++ B ++ H) (B ++ A ++ H) := by
  induction hH generalizing A B with
  | nil => simpa using WEq.rot A B
  | @cons U H' hU hd _ ih =>
    have a1 : DisjL U A := hA.left
    have a2 : DisjL U B := hB.left
    have a3 : DisjL H' A := hA.right
    have a4 : DisjL H' B := hB.right
    have c0 : WEq.{uu} (A ++ B ++ (U ++ H')) (H' ++ A ++ B ++ U) :=
      WEq.rot' (A ++ B ++ U) H' (by simp) (by simp)
    have c1 : WEq.{uu} (H' ++ A ++ B ++ U) (B ++ (H' ++ A) ++ U) :=
      slide_block hU (hd.append_right a1) a2
    have c2 : WEq.{uu} (B ++ (H' ++ A) ++ U) (A ++ U ++ B ++ H') :=
      WEq.rot' (B ++ H') (A ++ U) (by simp) (by simp)
    have c3 : WEq.{uu} (A ++ U ++ B ++ H') (B ++ (A ++ U) ++ H') :=
      ih (a3.append_right hd.symm) a4
    exact c0.trans (c1.trans (c2.trans (c3.trans (WEq.of_eq (by simp)))))

/-- A block moves past any part of a word. -/
theorem move_block {U P Q Z : List Letter} (hU : IsBlock U) (hP : DisjL U P) (hQ : DisjL U Q)
  (hZ : DisjL U Z) :
    WEq.{uu} (P ++ U ++ Q ++ Z) (P ++ Q ++ U ++ Z) := by
  have c0 : WEq.{uu} (P ++ U ++ Q ++ Z) (Q ++ (Z ++ P) ++ U) :=
    WEq.rot' (P ++ U) (Q ++ Z) (by simp) (by simp)
  have c1 : WEq.{uu} (Q ++ (Z ++ P) ++ U) (Z ++ P ++ Q ++ U) := by
    simpa using slide_block hU hQ (hZ.append_right hP)
  have c2 : WEq.{uu} (Z ++ P ++ Q ++ U) (P ++ Q ++ U ++ Z) :=
    WEq.rot' Z (P ++ Q ++ U) (by simp) (by simp)
  exact c0.trans (c1.trans c2)

theorem Blocks.append {X Y : List Letter} (hX : Blocks X) (hY : Blocks Y) (h : DisjL X Y) : Blocks
  (X ++ Y) := by
  induction hX with
  | nil => simpa using hY
  | @cons U H hU hd _ ih =>
    rw [List.append_assoc]
    exact .cons hU (hd.append_right h.left) (ih h.right)

/-- The number of letters with label `c`. -/
def cnt (w : List Letter) (c : ℕ) : ℕ := w.countP fun l => l.1 == c

theorem cnt_append (a b : List Letter) (c : ℕ) : cnt (a ++ b) c = cnt a c + cnt b c :=
  List.countP_append ..

theorem cnt_cons (x : Letter) (b : List Letter) (c : ℕ) :
    cnt (x :: b) c = (if x.1 = c then 1 else 0) + cnt b c := by
  simp [cnt, List.countP_cons]
  omega

theorem noLab_iff_cnt {w : List Letter} {c : ℕ} : NoLab w c ↔ cnt w c = 0 := by
  simp [NoLab, cnt, List.countP_eq_zero]

theorem cnt_pos {w : List Letter} {l : Letter} (h : l ∈ w) : 0 < cnt w l.1 :=
  List.countP_pos_iff.mpr ⟨l, h, by simp⟩

theorem cnt_winv (w : List Letter) (c : ℕ) : cnt (winv w) c = cnt w c := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [winv_cons, cnt_append, cnt_cons, ih, cnt_cons]
    have e1 : (linv x).1 = x.1 := rfl
    have e2 : cnt [] c = 0 := rfl
    rw [e1, e2]
    omega

theorem exists_of_cnt_pos {w : List Letter} {c : ℕ} (h : 0 < cnt w c) :
    ∃ a m b, w = a ++ m :: b ∧ m.1 = c := by
  obtain ⟨m, hm, hc⟩ := List.countP_pos_iff.mp h
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hm
  exact ⟨a, m, b, rfl, by simpa using hc⟩

theorem eq_or_linv {m l : Letter} (h : m.1 = l.1) : m = l ∨ m = linv l := by
  obtain ⟨a, b⟩ := m
  obtain ⟨c, d⟩ := l
  obtain rfl : a = c := h
  cases b <;> cases d <;> simp [linv]

/-- Each label occurs at most twice. -/
def Good (w : List Letter) : Prop := ∀ c, cnt w c ≤ 2

/-- **Case analysis of a word.** A word with labels used at most twice has a pair with equal signs,
or two
interleaved pairs, or a pair around letters that occur once, or only letters that occur once. -/
theorem pair_cases {R : List Letter} (hR : Good R) :
    ∀ n (P B Z : List Letter) (x x' : Letter), B.length ≤ n → R = P ++ x :: B ++ x' :: Z → x'.1
      = x.1 →
    (∃ P Q S x, R = P ++ x :: Q ++ x :: S) ∨
    (∃ P Q S T Z x y, x.1 ≠ y.1 ∧ R = P ++ x :: Q ++ y :: S ++ linv x :: T ++ linv y :: Z) ∨
    (∃ P B Z x, R = P ++ x :: B ++ linv x :: Z ∧ ∀ l ∈ B, cnt R l.1 = 1) := by
  intro n
  induction n with
  | zero =>
    intro P B Z x x' hB hE hx
    have hB0 : B = [] := List.length_eq_zero_iff.mp (by omega)
    subst hB0
    obtain ⟨c, e⟩ := x
    obtain ⟨c', e'⟩ := x'
    obtain rfl : c' = c := hx
    by_cases he : e' = e
    · subst he
      exact .inl ⟨P, [], Z, (c', e'), by simpa using hE⟩
    · refine .inr (.inr ⟨P, [], Z, (c', e), ?_, by simp⟩)
      have : e' = !e := by cases e <;> cases e' <;> simp_all
      simpa [linv, this] using hE
  | succ n ih =>
    intro P B Z x x' hB hE hx
    obtain ⟨c, e⟩ := x
    obtain ⟨c', e'⟩ := x'
    obtain rfl : c' = c := hx
    by_cases he : e' = e
    · subst he
      exact .inl ⟨P, B, Z, (c', e'), by simpa using hE⟩
    have hee : e' = !e := by
      cases e <;> cases e' <;> first | rfl | exact absurd rfl he
    subst hee
    have hcnt : cnt R c' = cnt P c' + 2 + cnt B c' + cnt Z c' := by
      rw [hE]
      simp only [cnt_append, cnt_cons, ite_true]
      omega
    have h2 := hR c'
    by_cases hall : ∀ l ∈ B, cnt R l.1 = 1
    · exact .inr (.inr ⟨P, B, Z, (c', e), by simpa [linv] using hE, hall⟩)
    push Not at hall
    obtain ⟨l, hl, hl1⟩ := hall
    obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hl
    have hlc : c' ≠ l.1 := by
      rintro h
      have h3 := cnt_pos (w := B₁ ++ l :: B₂) (l := l) hl
      rw [← h] at h3
      omega
    have hc : cnt R l.1 = cnt P l.1 + cnt B₁ l.1 + 1 + cnt B₂ l.1 + cnt Z l.1 := by
      rw [hE]
      simp only [cnt_append, cnt_cons, ite_eq_right hlc, ite_true]
      omega
    have hge : 1 ≤ cnt R l.1 := cnt_pos (w := R) (l := l) (by rw [hE]; simp)
    have hsum : 0 < cnt P l.1 + cnt B₁ l.1 + cnt B₂ l.1 + cnt Z l.1 := by omega
    have hEl : R = P ++ (c', e) :: B₁ ++ l :: B₂ ++ (c', !e) :: Z := by simpa using hE
    have hlen : B₁.length + B₂.length ≤ n := by
      simp at hB
      omega
    by_cases h3 : 0 < cnt B₂ l.1
    · obtain ⟨B₃, m, B₄, rfl, hm⟩ := exists_of_cnt_pos h3
      simp only [List.length_append, List.length_cons] at hlen
      exact ih (P ++ (c', e) :: B₁) B₃ (B₄ ++ (c', !e) :: Z) l m (by omega) (by simpa using hEl) hm
    by_cases h4 : 0 < cnt B₁ l.1
    · obtain ⟨B₃, m, B₄, rfl, hm⟩ := exists_of_cnt_pos h4
      simp only [List.length_append, List.length_cons] at hlen
      exact ih (P ++ (c', e) :: B₃) B₄ (B₂ ++ (c', !e) :: Z) m l (by omega)
        (by simpa using hEl) hm.symm
    by_cases h5 : 0 < cnt Z l.1
    · obtain ⟨Z₁, m, Z₂, rfl, hm⟩ := exists_of_cnt_pos h5
      rcases eq_or_linv hm with rfl | rfl
      · exact .inl ⟨P ++ (c', e) :: B₁, B₂ ++ (c', !e) :: Z₁, Z₂, m, by simpa using hEl⟩
      · exact .inr (.inl ⟨P, B₁, B₂, Z₁, Z₂, (c', e), l, hlc, by simpa [linv] using hEl⟩)
    · have h6 : 0 < cnt P l.1 := by omega
      obtain ⟨P₁, m, P₂, rfl, hm⟩ := exists_of_cnt_pos h6
      rcases eq_or_linv hm with rfl | rfl
      · exact .inl ⟨P₁, P₂ ++ (c', e) :: B₁, B₂ ++ (c', !e) :: Z, m, by simpa using hEl⟩
      · refine .inr (.inl ⟨P₁, P₂, B₁, B₂, Z, linv l, (c', e),
          fun he => hlc he.symm, ?_⟩)
        simpa [linv_linv, linv] using hEl

end GraphMinor.Surface
