/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.HoleLoop

/-!
# Normal forms of glued words

When a surface is cut along an arc, the surface before cutting has a word with one pair of letters
more than a normal
word. Here we compute its normal form, in each of the cases that arise. Each lemma follows the steps
of `normalize` by
hand. The product `BC` lists blocks in any order; `BC.nf` puts them in normal order, and this is
what we need when two
words are glued.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

universe uu

/-- A product of blocks in any order, with `a` handles, `b` cross-caps and `c` holes. -/
inductive BC : List Letter → ℕ → ℕ → ℕ → Prop
  | nil : BC [] 0 0 0
  | hnd {H : List Letter} {a b c : ℕ} (u v : Letter) (h : u.1 ≠ v.1) (hX : DisjL (hndB u v) H) :
      BC H a b c → BC (hndB u v ++ H) (a + 1) b c
  | cap {H : List Letter} {a b c : ℕ} (y : Letter) (hX : DisjL [y, y] H) : BC H a b c → BC
    ([y, y] ++ H) a (b + 1) c
  | hole {H : List Letter} {a b c : ℕ} (t r : Letter) (h : t.1 ≠ r.1) (hX : DisjL (holB t r) H) :
      BC H a b c → BC (holB t r ++ H) a b (c + 1)

theorem BC.append {A B : List Letter} {a b c a' b' c' : ℕ} (hA : BC A a b c) (hB : BC B a' b' c')
  (h : DisjL A B) :
    BC (A ++ B) (a + a') (b + b') (c + c') := by
  induction hA with
  | nil => simpa using hB
  | hnd u v hu hX _ ih =>
    rw [List.append_assoc, show ∀ a : ℕ, a + 1 + a' = a + a' + 1 by omega]
    exact .hnd u v hu (hX.append_right h.left) (ih h.right)
  | cap y hX _ ih =>
    rw [List.append_assoc, show ∀ b : ℕ, b + 1 + b' = b + b' + 1 by omega]
    exact .cap y (hX.append_right h.left) (ih h.right)
  | hole t r hu hX _ ih =>
    rw [List.append_assoc, show ∀ c : ℕ, c + 1 + c' = c + c' + 1 by omega]
    exact .hole t r hu (hX.append_right h.left) (ih h.right)

theorem HL.bc {a : ℕ} {X : List Letter} (h : HL a X) : BC X a 0 0 := by
  induction h with
  | nil => exact .nil
  | cons u v h hX _ ih => exact .hnd u v h hX ih

theorem CL.bc {b : ℕ} {X : List Letter} (h : CL b X) : BC X 0 b 0 := by
  induction h with
  | nil => exact .nil
  | cons y hX _ ih => exact .cap y hX ih

theorem TL.bc {c : ℕ} {X : List Letter} (h : TL c X) : BC X 0 0 c := by
  induction h with
  | nil => exact .nil
  | cons t r h hX _ ih => exact .hole t r h hX ih

theorem IsNF.bc {w : List Letter} {a b c : ℕ} (h : IsNF w a b c) : BC w a b c := by
  obtain ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩ := h
  simpa using (h1.bc.append h2.bc h4).append h3.bc (h5.append_left h6)

theorem noLab_winv' {a : List Letter} {c : ℕ} (h : NoLab a c) : NoLab (winv a) c := noLab_winv.mpr h

theorem DisjL.winv_right {A B : List Letter} (h : DisjL A B) : DisjL A (winv B) := fun l hl
  => noLab_winv' (h l hl)

theorem DisjL.winv_left {A B : List Letter} (h : DisjL A B) : DisjL (winv A) B :=
  (h.symm.winv_right).symm

theorem winv_hndB (u v : Letter) : winv (hndB u v) = hndB v u := by simp [winv, hndB, linv]

theorem winv_cap (y : Letter) : winv [y, y] = [linv y, linv y] := by simp [winv]

theorem winv_holB (t r : Letter) : winv (holB t r) = holB t (linv r) := by simp [winv, holB, linv]

theorem BC.winv {H : List Letter} {a b c : ℕ} (h : BC H a b c) : BC (winv H) a b c := by
  induction h with
  | nil => exact .nil
  | @hnd H a b c u v hu hX _ ih =>
    rw [winv_append]
    have e := winv_hndB u v
    rw [e]
    have h1 : BC (hndB v u) 1 0 0 := by
      simpa using BC.hnd v u (Ne.symm hu) (by simp [DisjL, NoLab]) .nil
    have h2 : DisjL (GraphMinor.Surface.winv H) (hndB v u) := by
      rw [← e]
      exact hX.symm.winv_left.winv_right
    simpa using ih.append h1 h2
  | @cap H a b c y hX _ ih =>
    rw [winv_append]
    have e := winv_cap y
    rw [e]
    have h1 : BC [linv y, linv y] 0 1 0 := by
      simpa using BC.cap (linv y) (by simp [DisjL, NoLab]) .nil
    have h2 : DisjL (GraphMinor.Surface.winv H) [linv y, linv y] := by
      rw [← e]
      exact hX.symm.winv_left.winv_right
    simpa using ih.append h1 h2
  | @hole H a b c t r ht hX _ ih =>
    rw [winv_append]
    have e := winv_holB t r
    rw [e]
    have h1 : BC (holB t (linv r)) 0 0 1 := by
      simpa using BC.hole t (linv r) ht (by simp [DisjL, NoLab]) .nil
    have h2 : DisjL (GraphMinor.Surface.winv H) (holB t (linv r)) := by
      rw [← e]
      exact hX.symm.winv_left.winv_right
    simpa using ih.append h1 h2

/-- Blocks in any order can be put in normal order, after any word without their labels. -/
theorem BC.nf {H : List Letter} {a b c : ℕ} (h : BC H a b c) :
    ∃ w, IsNF w a b c ∧ (∀ k, cnt w k = cnt H k) ∧ ∀ P, DisjL H P → WEq.{uu} (P ++ H) (P ++ w) := by
  induction h with
  | nil =>
    refine ⟨[], ⟨[], [], [], rfl, .nil, .nil, .nil, by simp [DisjL], by simp [DisjL],
      by simp [DisjL]⟩, fun _ => rfl, fun P _ => WEq.refl _⟩
  | @hnd H a b c u v hu hX _ ih =>
    obtain ⟨w, ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩, hc, hw⟩ := ih
    have hd : DisjL (hndB u v) (X ++ Y ++ Z) := hX.mono fun k => by rw [hc]
    refine ⟨(hndB u v ++ X) ++ Y ++ Z, ⟨_, Y, Z, rfl, .cons u v hu hd.inl.inl h1, h2, h3,
      DisjL.append_left hd.inl.inr h4,
      DisjL.append_left hd.inr h5, h6⟩, fun k => ?_, fun P hP => ?_⟩
    · have := hc k
      simp only [cnt_append] at this ⊢
      omega
    · have := hw (P ++ hndB u v) (DisjL.append_right hP.right hX.symm)
      simpa using this
  | @cap H a b c y hX _ ih =>
    obtain ⟨w, ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩, hc, hw⟩ := ih
    have hd : DisjL [y, y] (X ++ Y ++ Z) := hX.mono fun k => by rw [hc]
    refine ⟨X ++ ([y, y] ++ Y) ++ Z, ⟨X, _, Z, rfl, h1, .cons y hd.inl.inr h2, h3,
      DisjL.append_right hd.inl.inl.symm h4, h5,
      DisjL.append_left hd.inr h6⟩, fun k => ?_, fun P hP => ?_⟩
    · have := hc k
      simp only [cnt_append] at this ⊢
      omega
    · have c1 := hw (P ++ [y, y]) (DisjL.append_right hP.right hX.symm)
      have c2 := move_block.{uu} (U := [y, y]) (P := P) (Q := X) (Z := Y ++ Z)
        (.cap y) hP.left hd.inl.inl
        (DisjL.append_right hd.inl.inr hd.inr)
      have e1 : P ++ ([y, y] ++ H) = (P ++ [y, y]) ++ H := by simp
      have e2 : (P ++ [y, y]) ++ (X ++ Y ++ Z) = P ++ [y, y] ++ X ++ (Y ++ Z) := by simp
      have e3 : P ++ X ++ [y, y] ++ (Y ++ Z) = P ++ (X ++ ([y, y] ++ Y) ++ Z) := by simp
      rw [e1, ← e3]
      exact c1.trans (e2 ▸ c2)
  | @hole H a b c t r ht hX _ ih =>
    obtain ⟨w, ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩, hc, hw⟩ := ih
    have hd : DisjL (holB t r) (X ++ Y ++ Z) := hX.mono fun k => by rw [hc]
    refine ⟨X ++ Y ++ (holB t r ++ Z), ⟨X, Y, _, rfl, h1, h2, .cons t r ht hd.inr h3, h4,
      DisjL.append_right hd.inl.inl.symm h5,
      DisjL.append_right hd.inl.inr.symm h6⟩, fun k => ?_, fun P hP => ?_⟩
    · have := hc k
      simp only [cnt_append] at this ⊢
      omega
    · have c1 := hw (P ++ holB t r) (DisjL.append_right hP.right hX.symm)
      have c2 := move_block.{uu} (U := holB t r) (P := P) (Q := X ++ Y) (Z := Z)
        (isBlock_holB ht) hP.left hd.inl hd.inr
      have e1 : P ++ (holB t r ++ H) = (P ++ holB t r) ++ H := by simp
      have e2 : (P ++ holB t r) ++ (X ++ Y ++ Z) = P ++ holB t r ++ (X ++ Y) ++ Z := by simp
      have e3 : P ++ (X ++ Y) ++ holB t r ++ Z = P ++ (X ++ Y ++ (holB t r ++ Z)) := by simp
      rw [e1, ← e3]
      exact c1.trans (e2 ▸ c2)

/-- A state gives a normal form. -/
theorem Inv.isNF {R X Y Z : List Letter} {a b c : ℕ} (h : Inv R X Y Z a b c) : IsNF
  (X ++ Y ++ Z) a b c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩

theorem cnt_nil (c : ℕ) : cnt [] c = 0 := rfl

/-- A pair of letters with different labels, each once. -/
theorem cnt_pair {g g' : Letter} (h : g.1 ≠ g'.1) : ∀ l ∈ [g, g'], cnt [g, g'] l.1 = 1 := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [cnt_cons, cnt_nil, Ne.symm h]
  · simp [cnt_cons, cnt_nil, h]

section cases

variable {X Y Z : List Letter} {a b c : ℕ} {x t t₁ t₂ p g₁ g₂ : Letter}

/-- Different cuffs, opposite signs. -/
theorem nf_caseA_neg (hI : Inv [x, linv x, t₁, p, g₁, linv t₁, t₂, linv p, g₂, linv t₂] X Y Z a b
  c) (h1 : t₁.1 ≠ p.1)
    (h2 : g₁.1 ≠ g₂.1) :
    ∃ w, IsNF w (a + 1) b (c + 1) ∧ WEq.{uu} ([x, linv x, t₁, p, g₁, linv t₁, t₂, linv p, g₂, linv
      t₂] ++ X ++ Y ++ Z) w := by
  have s1 := step_hnd.{uu} (P := [x, linv x]) (Q := []) (S := [g₁]) (T := [t₂]) (V
    := [g₂, linv t₂]) hI h1 rfl
  have s2 := step_fold.{uu} (P := [g₂, linv t₂]) (V := [t₂, g₁]) s1.1 rfl (by simp)
  have s3 := step_fold.{uu} (P := [g₂]) (V := [g₁]) (x := linv t₂) s2.1 (by simp [linv]) (by simp)
  obtain ⟨u, s4, s5⟩ := step_last.{uu} (R := [g₂] ++ [g₁]) (q := g₂) (Q := [g₁]) s3.1 rfl (cnt_pair
    (Ne.symm h2))
  exact ⟨_, s4.isNF, s1.2.trans (s2.2.trans (s3.2.trans (by simpa using s5)))⟩

/-- Different cuffs, equal signs. -/
theorem nf_caseA_pos (hI : Inv [x, linv x, t₁, p, g₁, linv t₁, t₂, p, g₂, linv t₂] X Y Z a b c)
  (h2 : (linv g₁).1 ≠ g₂.1) :
    ∃ w, IsNF w a (b + 2) (c + 1) ∧ WEq.{uu} ([x, linv x, t₁, p, g₁, linv t₁, t₂, p, g₂, linv t₂]
      ++ X ++ Y ++ Z) w := by
  have s1 := step_cap.{uu} (P := [x, linv x, t₁]) (Q := [g₁, linv t₁, t₂]) (S := [g₂, linv t₂]) (x
    := p) hI rfl
  have e1 : [g₂, linv t₂] ++ [x, linv x, t₁] ++ winv [g₁, linv t₁, t₂] =
      [g₂, linv t₂, x, linv x] ++ t₁ :: [linv t₂] ++ t₁ :: [linv g₁] := by simp [winv, linv_linv]
  rw [e1] at s1
  have s2 := step_cap.{uu} (P := [g₂, linv t₂, x, linv x]) (Q := [linv t₂]) (S := [linv g₁]) (x
    := t₁) s1.1 rfl
  have e2 : [linv g₁] ++ [g₂, linv t₂, x, linv x] ++ winv [linv t₂] = [linv g₁, g₂, linv t₂] ++ x
    :: linv x :: [t₂] := by
    simp [winv, linv_linv]
  rw [e2] at s2
  have s3 := step_fold.{uu} (P := [linv g₁, g₂, linv t₂]) (V := [t₂]) s2.1 rfl (by simp)
  have s4 := step_fold.{uu} (P := [linv g₁, g₂]) (V := []) (x := linv t₂) s3.1
    (by simp [linv_linv]) (by simp)
  obtain ⟨u, s5, s6⟩ := step_last.{uu} (R := [linv g₁, g₂] ++ []) (q := linv g₁) (Q
    := [g₂]) s4.1 rfl (cnt_pair h2)
  exact ⟨_, s5.isNF, s1.2.trans (s2.2.trans (s3.2.trans (s4.2.trans (by simpa using s6))))⟩

/-- The same cuff, opposite signs. -/
theorem nf_caseB_neg (hI : Inv [x, linv x, t, p, g₁, linv p, g₂, linv t] X Y Z a b c)
    (h1 : cnt [x, linv x, t, p, g₁, linv p, g₂, linv t] g₁.1 = 1) (h2 : cnt [t, g₂, linv t] g₂.1
      = 1) :
    ∃ w, IsNF w a b (c + 2) ∧ WEq.{uu} ([x, linv x, t, p, g₁, linv p, g₂, linv t] ++ X ++ Y ++ Z) w
      := by
  have s1 := step_hole.{uu} (P := [x, linv x, t]) (x := p) (q := g₁) (Q := []) (V
    := [g₂, linv t]) hI rfl (by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    exact h1)
  have s2 := step_fold.{uu} (P := []) (V := [t, g₂, linv t]) s1.1 rfl (by simp)
  have s3 := step_hole.{uu} (P := []) (x := t) (q := g₂) (Q := []) (V := []) s2.1 rfl (by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    exact h2)
  exact ⟨_, s3.1.isNF, s1.2.trans (s2.2.trans (by simpa using s3.2))⟩

/-- The same cuff, equal signs. -/
theorem nf_caseB_pos (hI : Inv [x, linv x, t, p, g₁, p, g₂, linv t] X Y Z a b c) (h2 : g₂.1 ≠
  (linv g₁).1) :
    ∃ w, IsNF w a (b + 1) (c + 1) ∧ WEq.{uu} ([x, linv x, t, p, g₁, p, g₂, linv t] ++ X ++ Y ++ Z)
      w := by
  have s1 := step_cap.{uu} (P := [x, linv x, t]) (Q := [g₁]) (S := [g₂, linv t]) (x := p) hI rfl
  have e1 : [g₂, linv t] ++ [x, linv x, t] ++ winv [g₁] = [g₂, linv t] ++ x :: linv x :: [t, linv
    g₁] := by simp [winv]
  rw [e1] at s1
  have s2 := step_fold.{uu} (P := [g₂, linv t]) (V := [t, linv g₁]) s1.1 rfl (by simp)
  have s3 := step_fold.{uu} (P := [g₂]) (V := [linv g₁]) (x := linv t) s2.1 (by simp [linv_linv])
    (by simp)
  obtain ⟨u, s4, s5⟩ := step_last.{uu} (R := [g₂] ++ [linv g₁]) (q := g₂) (Q := [linv g₁]) s3.1 rfl
    (cnt_pair h2)
  exact ⟨_, s4.isNF, s1.2.trans (s2.2.trans (s3.2.trans (by simpa using s5)))⟩

/-- Two components, glued along an arc with opposite signs. -/
theorem nf_caseC_neg {x₁ x₂ : Letter}
    (hI : Inv [g₂, linv t₂, x₂, linv x₂, t₂, g₁, linv t₁, x₁, linv x₁, t₁] X Y Z a b c)
      (h2 : g₂.1 ≠ g₁.1) :
    ∃ w, IsNF w a b (c + 1) ∧ WEq.{uu} ([g₂, linv t₂, x₂, linv x₂, t₂, g₁, linv t₁, x₁, linv x₁,
      t₁] ++ X ++ Y ++ Z) w := by
  have s1 := step_fold.{uu} (P := [g₂, linv t₂]) (V := [t₂, g₁, linv t₁, x₁, linv x₁, t₁]) hI rfl
    (by simp)
  have s2 := step_fold.{uu} (P := [g₂]) (V := [g₁, linv t₁, x₁, linv x₁, t₁]) (x := linv t₂) s1.1
    (by simp [linv_linv]) (by simp)
  have s3 := step_fold.{uu} (P := [g₂, g₁, linv t₁]) (V := [t₁]) (x := x₁) s2.1 rfl (by simp)
  have s4 := step_fold.{uu} (P := [g₂, g₁]) (V := []) (x := linv t₁) s3.1 (by simp [linv_linv])
    (by simp)
  obtain ⟨u, s5, s6⟩ := step_last.{uu} (R := [g₂, g₁] ++ []) (q := g₂) (Q := [g₁]) s4.1 rfl
    (cnt_pair h2)
  exact ⟨_, s5.isNF, s1.2.trans (s2.2.trans (s3.2.trans (s4.2.trans (by simpa using s6))))⟩

/-- Two components, glued along an arc with equal signs. -/
theorem nf_caseC_pos {x₁ x₂ : Letter}
    (hI : Inv [linv t₂, x₂, linv x₂, t₂, g₂, g₁, linv t₁, x₁, linv x₁, t₁] X Y Z a b c)
      (h2 : g₂.1 ≠ g₁.1) :
    ∃ w, IsNF w a b (c + 1) ∧ WEq.{uu} ([linv t₂, x₂, linv x₂, t₂, g₂, g₁, linv t₁, x₁, linv x₁,
      t₁] ++ X ++ Y ++ Z) w := by
  have s1 := step_fold.{uu} (P := [linv t₂]) (V := [t₂, g₂, g₁, linv t₁, x₁, linv x₁, t₁]) hI rfl
    (by simp)
  have s2 := step_fold.{uu} (P := []) (V := [g₂, g₁, linv t₁, x₁, linv x₁, t₁]) (x := linv t₂) s1.1
    (by simp [linv_linv]) (by simp)
  have s3 := step_fold.{uu} (P := [g₂, g₁, linv t₁]) (V := [t₁]) (x := x₁) s2.1 rfl (by simp)
  have s4 := step_fold.{uu} (P := [g₂, g₁]) (V := []) (x := linv t₁) s3.1 (by simp [linv_linv])
    (by simp)
  obtain ⟨u, s5, s6⟩ := step_last.{uu} (R := [g₂, g₁] ++ []) (q := g₂) (Q := [g₁]) s4.1 rfl
    (cnt_pair h2)
  exact ⟨_, s5.isNF, s1.2.trans (s2.2.trans (s3.2.trans (s4.2.trans (by simpa using s6))))⟩

/-- A one-sided `O`-arc. -/
theorem nf_caseD (hI : Inv [x, linv x, t, p, p, linv t] X Y Z a b c) :
    ∃ w, IsNF w a (b + 1) c ∧ WEq.{uu} ([x, linv x, t, p, p, linv t] ++ X ++ Y ++ Z) w := by
  have s1 := step_cap.{uu} (P := [x, linv x, t]) (Q := []) (S := [linv t]) (x := p) hI rfl
  have e1 : [linv t] ++ [x, linv x, t] ++ winv [] = [linv t] ++ x :: linv x :: [t] := by simp [winv]
  rw [e1] at s1
  have s2 := step_fold.{uu} (P := [linv t]) (V := [t]) s1.1 rfl (by simp)
  have s3 := step_fold.{uu} (P := []) (V := []) (x := linv t) s2.1 (by simp [linv_linv]) (by simp)
  exact ⟨_, s3.1.isNF, s1.2.trans (s2.2.trans (by simpa using s3.2))⟩

/-- Two cuffs glued along `O`-arcs, opposite signs. -/
theorem nf_caseE_neg (hI : Inv [x, linv x, t₁, p, linv t₁, t₂, linv p, linv t₂] X Y Z a b c)
  (h1 : t₁.1 ≠ p.1) :
    ∃ w, IsNF w (a + 1) b c ∧ WEq.{uu} ([x, linv x, t₁, p, linv t₁, t₂, linv p, linv t₂] ++ X ++ Y
      ++ Z) w := by
  have s1 := step_hnd.{uu} (P := [x, linv x]) (Q := []) (S := []) (T := [t₂]) (V
    := [linv t₂]) hI h1 rfl
  have s2 := step_fold.{uu} (P := [linv t₂]) (V := [t₂]) s1.1 rfl (by simp [hndB])
  have s3 := step_fold.{uu} (P := []) (V := []) (x := linv t₂) s2.1 (by simp [linv_linv])
    (by simp [hndB])
  exact ⟨_, s3.1.isNF, s1.2.trans (s2.2.trans (by simpa using s3.2))⟩

/-- Two cuffs glued along `O`-arcs, equal signs. -/
theorem nf_caseE_pos (hI : Inv [x, linv x, t₁, p, linv t₁, t₂, p, linv t₂] X Y Z a b c) :
    ∃ w, IsNF w a (b + 2) c ∧ WEq.{uu} ([x, linv x, t₁, p, linv t₁, t₂, p, linv t₂] ++ X ++ Y ++ Z)
      w := by
  have s1 := step_cap.{uu} (P := [x, linv x, t₁]) (Q := [linv t₁, t₂]) (S := [linv t₂]) (x
    := p) hI rfl
  have e1 : [linv t₂] ++ [x, linv x, t₁] ++ winv [linv t₁, t₂] = [linv t₂, x, linv x] ++ t₁ ::
    [linv t₂] ++ t₁ :: [] := by
    simp [winv, linv_linv]
  rw [e1] at s1
  have s2 := step_cap.{uu} (P := [linv t₂, x, linv x]) (Q := [linv t₂]) (S := []) (x := t₁) s1.1 rfl
  have e2 : [] ++ [linv t₂, x, linv x] ++ winv [linv t₂] = [linv t₂] ++ x :: linv x :: [t₂] := by
    simp [winv, linv_linv]
  rw [e2] at s2
  have s3 := step_fold.{uu} (P := [linv t₂]) (V := [t₂]) s2.1 rfl (by simp)
  have s4 := step_fold.{uu} (P := []) (V := []) (x := linv t₂) s3.1 (by simp [linv_linv]) (by simp)
  exact ⟨_, s4.1.isNF, s1.2.trans (s2.2.trans (s3.2.trans (by simpa using s4.2)))⟩

/-- Two components, glued along `O`-arcs. -/
theorem nf_caseF {x₁ x₂ : Letter} (hI : Inv [linv t₂, x₂, linv x₂, t₂, linv t₁, x₁, linv x₁, t₁] X
  Y Z a b c) :
    (∃ w, IsNF w a b c ∧ WEq.{uu} ([linv t₂, x₂, linv x₂, t₂, linv t₁, x₁, linv x₁, t₁] ++ X ++ Y
      ++ Z) w) ∨
      (a = 0 ∧ b = 0 ∧ c = 0 ∧ ∃ y, WEq.{uu} ([linv t₂, x₂, linv x₂, t₂, linv t₁, x₁, linv x₁, t₁]
        ++ X ++ Y ++ Z) [y, linv y]) := by
  have s1 := step_fold.{uu} (P := [linv t₂]) (V := [t₂, linv t₁, x₁, linv x₁, t₁]) hI rfl (by simp)
  have s2 := step_fold.{uu} (P := []) (V := [linv t₁, x₁, linv x₁, t₁]) (x := linv t₂) s1.1
    (by simp [linv_linv]) (by simp)
  have s3 := step_fold.{uu} (P := [linv t₁]) (V := [t₁]) (x := x₁) s2.1 rfl (by simp)
  have c1 := s1.2.trans (s2.2.trans s3.2)
  by_cases hne : X ++ Y ++ Z = []
  · right
    have hX : X = [] := by
      simpa using (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hne).1).1
    have hY : Y = [] := by
      simpa using (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hne).1).2
    have hZ : Z = [] := (List.append_eq_nil_iff.mp hne).2
    subst hX hY hZ
    obtain ⟨h1, h2, h3, -⟩ := id hI
    have ha : a = 0 := by
      cases h1
      rfl
    have hb : b = 0 := by
      cases h2
      rfl
    have hc : c = 0 := by
      cases h3
      rfl
    refine ⟨ha, hb, hc, linv t₁, ?_⟩
    simpa [linv_linv] using c1
  · left
    have s4 := step_fold.{uu} (P := []) (V := []) (x := linv t₁) s3.1 (by simp [linv_linv]) (by
      simpa [List.append_assoc] using hne)
    exact ⟨_, s4.1.isNF, c1.trans (by simpa using s4.2)⟩

end cases

/-- A space presented by a word equivalent to a normal form is the model. -/
theorem homeo_of_nf {T : Type uu} [TopologicalSpace T] [T2Space T] [Nonempty T] {w₀ w : List
  Letter} {a b c : ℕ} {f : ℕ × ℂ → T}
    (hf : Presents (sW w₀) f) (hn : IsNF w a b c) (he : WEq.{uu} w₀ w) : Nonempty
      (T ≃ₜ SurfaceModel a b c) := by
  obtain ⟨w'', hp, h3⟩ := exists_modelW_nf.{uu} a b c
  rcases h3 with ⟨hnf', -⟩ | ⟨h0', rfl⟩
  · obtain ⟨g', hg'⟩ := (((show PEq.{uu} (sW w₀) (sW w) from he).trans (PEq.trans
    (nf_eq hn hnf') hp.symm)) T).mp ⟨f, hf⟩
    exact model_homeo a b c hg'
  · exfalso
    obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    obtain ⟨X, Y, Z, rfl, h1, h2, h3, -⟩ := hn
    cases h1
    cases h2
    cases h3
    obtain ⟨g', hg'⟩ := ((show PEq.{uu} (sW w₀) (sW ([] ++ [] ++ [])) from he) T).mp ⟨f, hf⟩
    obtain ⟨x⟩ : Nonempty T := inferInstance
    have h4 : x ∈ g' '' Dsk (sW ([] ++ [] ++ [])) := hg'.2.1 ▸ mem_univ x
    obtain ⟨y, hy, -⟩ := h4
    exact absurd (by simp [sW, nW, Function.update]) hy.1

/-- A space presented by a word equivalent to `y y⁻¹` is the sphere model. -/
theorem homeo_of_sphere {T : Type uu} [TopologicalSpace T] [T2Space T] {w₀ : List Letter} {y :
  Letter} {f : ℕ × ℂ → T}
    (hf : Presents (sW w₀) f) (he : WEq.{uu} w₀ [y, linv y]) : Nonempty (T ≃ₜ SurfaceModel 0 0 0)
      := by
  obtain ⟨w', hp, h3⟩ := exists_modelW_nf.{uu} 0 0 0
  rcases h3 with ⟨-, h4⟩ | ⟨-, rfl⟩
  · exact absurd rfl h4
  · have h5 : WEq.{uu} [y, linv y] [linv (segL 0), segL 0] := by
      refine Iso.weq ⟨fun _ => 0, fun _ => y.2, ?_, ?_⟩
      · intro l hl l' hl' _
        have e1 : l.1 = y.1 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> rfl
        have e2 : l'.1 = y.1 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
          rcases hl' with rfl | rfl <;> rfl
        rw [e1, e2]
      · obtain ⟨k, e⟩ := y
        cases e <;> simp [linv, segL]
    obtain ⟨g', hg'⟩ := ((show PEq.{uu} (sW w₀) (sW [y, linv y]) from he).trans
      (PEq.trans h5 hp.symm) T).mp ⟨f, hf⟩
    exact model_homeo 0 0 0 hg'

end GraphMinor.Surface
