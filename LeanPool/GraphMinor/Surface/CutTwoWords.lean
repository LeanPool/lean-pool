/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutTwo

/-!
# Words for two components

The two components of a cut surface have the words `rW`, up to a shift of the labels of the second
word. Pasting one side of
the first word to a side of the second word gives a family of two words. Here we find the surface
that this family presents
(`homeo_of_two_arc`, `homeo_of_two_loop`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set

universe uu

/-- The word with labels shifted by `M`. -/
def shW (M : ℕ) (w : List Letter) : List Letter := w.map fun l => (l.1 + M, l.2)

theorem shW_append (M : ℕ) (a b : List Letter) : shW M (a ++ b) = shW M a ++ shW M b := by
  simp [shW]

theorem shW_cons (M : ℕ) (x : Letter) (b : List Letter) : shW M (x :: b) =
  (x.1 + M, x.2) :: shW M b := by simp [shW]

theorem shW_hndB (M : ℕ) (u v : Letter) : shW M (hndB u v) = hndB (u.1 + M, u.2) (v.1 + M, v.2)
  := by simp [shW, hndB, linv]

theorem shW_holB (M : ℕ) (t r : Letter) : shW M (holB t r) = holB (t.1 + M, t.2) (r.1 + M, r.2)
  := by simp [shW, holB, linv]

theorem noLab_shW_of {w : List Letter} {M k : ℕ} (h : ∀ k', k = k' + M → NoLab w k') : NoLab
  (shW M w) k := by
  intro l hl he
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  exact h l'.1 he.symm l' hl' rfl

theorem disjL_shW {A B : List Letter} (M : ℕ) (h : DisjL A B) : DisjL (shW M A) (shW M B) := by
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  refine noLab_shW_of fun k' he => ?_
  have : l'.1 = k' := by simpa using he
  exact this ▸ h l' hl'

theorem BC.shift {H : List Letter} {a b c : ℕ} (M : ℕ) (h : BC H a b c) : BC (shW M H) a b c := by
  induction h with
  | nil => exact .nil
  | hnd u v hu hX _ ih =>
    rw [shW_append, shW_hndB]
    refine .hnd _ _ (by simpa using hu) ?_ ih
    rw [← shW_hndB]
    exact disjL_shW M hX
  | cap y hX _ ih =>
    rw [shW_append]
    have e : shW M [y, y] = [(y.1 + M, y.2), (y.1 + M, y.2)] := rfl
    rw [e]
    refine .cap _ ?_ ih
    rw [← e]
    exact disjL_shW M hX
  | hole t r hu hX _ ih =>
    rw [shW_append, shW_holB]
    refine .hole _ _ (by simpa using hu) ?_ ih
    rw [← shW_holB]
    exact disjL_shW M hX

theorem relab_sW_shift (M : ℕ) (w : List Letter) : relab (· + M) (sW w) = sW (shW M w) := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [relab, sW_zero, shW]
  · simp [relab, sW, hi, nW]

theorem presents_shW {T : Type*} [TopologicalSpace T] (M : ℕ) {w : List Letter} {f : ℕ × ℂ → T}
  (hf : Presents (sW w) f) :
    Presents (sW (shW M w)) f := by
  rw [← relab_sW_shift]
  exact (presents_relab (fun _ _ _ _ _ _ h => Nat.add_right_cancel h) f).mp hf

theorem SideVal.shW {T : Type*} {w : List Letter} {f : ℕ × ℂ → T} {k : ℕ} {ρ : ℝ → T} (h : SideVal
  (sW w) f k ρ) (M : ℕ) :
    SideVal (sW (shW M w)) f (k + M) ρ := by
  obtain ⟨i, p, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  rw [sW_zero] at h2
  refine ⟨0, p, ?_, fun u hu => ?_⟩
  · rw [sW_zero]
    simp [GraphMinor.Surface.shW, h3]
  · rw [sW_zero]
    have : (GraphMinor.Surface.shW M w).length = w.length := by simp [GraphMinor.Surface.shW]
    rw [this]
    exact h2 u hu

/-- All blocks of the normal word without the two last letters. -/
def hH (a b : ℕ) (L : List ℕ) : List Letter := hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L

theorem rW_eq (a b c : ℕ) (L : List ℕ) : rW a b c L = hH a b L ++ eW a b c := rfl

theorem bc_hH (a b : ℕ) {L : List ℕ} (hL : L.Nodup) : BC (hH a b L) a b L.length := by
  have h1 := (hL_hW 0 a).bc
  have h2 := (cL_cW (2 * a) b).bc
  have h3 := (tL_hlW (2 * a + b) hL).bc
  have d1 : DisjL (hW 0 a) (cW (2 * a) b) := by
    intro l hl m hm he
    have h4 := (hW_labels _ _ l hl).2
    have h5 := (cW_labels _ _ m hm).1
    omega
  have d2 : DisjL (hW 0 a) (hlW (2 * a + b) L) := by
    intro l hl
    have h4 := (hW_labels _ _ l hl).2
    exact noLab_hlW fun m _ => by omega
  have d3 : DisjL (cW (2 * a) b) (hlW (2 * a + b) L) := by
    intro l hl
    have h4 := (cW_labels _ _ l hl).2
    exact noLab_hlW fun m _ => by omega
  simpa [hH] using (h1.append h2 d1).append h3 (d2.append_left d3)

theorem noLab_hH {a b k : ℕ} {L : List ℕ} (h1 : 2 * a + b ≤ k)
    (h3 : ∀ m ∈ L, k ≠ 2 * a + b + 2 * m ∧ k ≠ 2 * a + b + 2 * m + 1) : NoLab (hH a b L) k := by
  refine noLab_append.mpr ⟨noLab_append.mpr ⟨fun l hl he => ?_, fun l hl he => ?_⟩, noLab_hlW h3⟩
  · have := (hW_labels 0 a l hl).2
    omega
  · have := (cW_labels (2 * a) b l hl).2
    omega

theorem winv_eW (a b c : ℕ) : winv (eW a b c) = eW a b c := by simp [winv, eW, linv]

section

variable {a₁ b₁ c₁ a₂ b₂ c₂ i j : ℕ} {L₁ L₂ : List ℕ} {σ : Bool} {T : Type uu} [TopologicalSpace T]
  [T2Space T] [Nonempty T]
  {f : ℕ × ℂ → T}

/-- The first word for an arc. -/
def wArc₁ (a b c i : ℕ) (L : List ℕ) : List Letter :=
  [tL a b i, rL a b i, (frL a b c, true), linv (tL a b i)] ++ rW a b c L

/-- The second word for an arc, with `s` in place of the side to paste. -/
def wArc₂ (a b c i : ℕ) (L : List ℕ) (M : ℕ) (s : Letter) : List Letter :=
  [((tL a b i).1 + M, true)] ++ s :: ((frL a b c + M, true) :: ((tL a b i).1 + M, false) :: shW M
    (rW a b c L))

/-- The first word for an `O`-arc. -/
def wLoop₁ (a b c i : ℕ) (L : List ℕ) : List Letter := hB a b i ++ rW a b c L

/-- The second word for an `O`-arc, with `s` in place of the side to paste. -/
def wLoop₂ (a b c i : ℕ) (L : List ℕ) (M : ℕ) (s : Letter) : List Letter :=
  [((tL a b i).1 + M, true)] ++ s :: (((tL a b i).1 + M, false) :: shW M (rW a b c L))

theorem noLab_two {M k : ℕ} (hk1 : 2 * a₁ + b₁ ≤ k) (hk2 : ∀ m ∈ L₁, k ≠ 2 * a₁ + b₁ + 2 * m
  ∧ k ≠ 2 * a₁ + b₁ + 2 * m + 1)
    (hk3 : ∀ k', k = k' + M → 2 * a₂ + b₂ ≤ k' ∧ ∀ m ∈ L₂, k' ≠ 2 * a₂ + b₂ + 2 * m
      ∧ k' ≠ 2 * a₂ + b₂ + 2 * m + 1) :
    NoLab (shW M (hH a₂ b₂ L₂) ++ hH a₁ b₁ L₁) k :=
  noLab_append.mpr ⟨noLab_shW_of fun k' he => noLab_hH (hk3 k' he).1 (hk3 k' he).2, noLab_hH hk1
    hk2⟩

theorem noLab_two' {M k : ℕ} (hk1 : 2 * a₁ + b₁ ≤ k) (hk2 : ∀ m ∈ L₁, k ≠ 2 * a₁ + b₁ + 2 * m
  ∧ k ≠ 2 * a₁ + b₁ + 2 * m + 1)
    (hk3 : ∀ k', k = k' + M → 2 * a₂ + b₂ ≤ k' ∧ ∀ m ∈ L₂, k' ≠ 2 * a₂ + b₂ + 2 * m
      ∧ k' ≠ 2 * a₂ + b₂ + 2 * m + 1) :
    NoLab (winv (shW M (hH a₂ b₂ L₂)) ++ hH a₁ b₁ L₁) k :=
  noLab_append.mpr ⟨noLab_winv' (noLab_shW_of fun k' he => noLab_hH (hk3 k' he).1
    (hk3 k' he).2), noLab_hH hk1 hk2⟩

theorem disj_hH (hL₁ : ∀ m ∈ L₁, m < c₁) {M : ℕ} (hM : 2 * a₁ + b₁ + 2 * c₁ ≤ M) : DisjL (shW M
  (hH a₂ b₂ L₂)) (hH a₁ b₁ L₁) := by
  refine fun l hl => ?_
  obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
  refine noLab_hH (by simp only; omega) fun m hm => ?_
  have := hL₁ m hm
  simp only
  omega

theorem winv_nil : winv [] = [] := rfl

theorem shW_eW (M a b c : ℕ) : shW M (eW a b c) = [(2 * a + b + 2 * c + M, true),
  (2 * a + b + 2 * c + M, false)] := rfl

theorem winv_shW_eW (M a b c : ℕ) : winv (shW M (eW a b c)) = shW M (eW a b c) := by
  simp [shW_eW, winv, linv]

/-- The letters of the second word, read in the order of the first word. -/
theorem homeo_of_two_arc (hi : i < c₁) (hj : j < c₂) (hN₁ : L₁.Nodup) (hN₂ : L₂.Nodup)
  (hL₁ : ∀ m ∈ L₁, m < c₁ ∧ m ≠ i)
    (hL₂ : ∀ m ∈ L₂, m < c₂ ∧ m ≠ j)
    (hf : Presents (dW (wArc₁ a₁ b₁ c₁ i L₁) (wArc₂ a₂ b₂ c₂ j L₂ (frL a₁ b₁ c₁ + 1)
      ((rL a₁ b₁ i).1, σ))) f) :
    Nonempty (T ≃ₜ SurfaceModel (a₂ + a₁) (b₂ + b₁) (L₂.length + L₁.length + 1)) := by
  have bc₁ := bc_hH a₁ b₁ hN₁
  have bc₂ := (bc_hH a₂ b₂ hN₂).shift (frL a₁ b₁ c₁ + 1)
  have hd : DisjL (shW (frL a₁ b₁ c₁ + 1) (hH a₂ b₂ L₂)) (hH a₁ b₁ L₁) :=
    disj_hH (fun m hm => (hL₁ m hm).1) (by simp only [frL]; omega)
  have c1 : cnt (rW a₁ b₁ c₁ L₁) (2 * a₁ + b₁ + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega
  have c2 : cnt (shW (frL a₁ b₁ c₁ + 1) (rW a₂ b₂ c₂ L₂)) (2 * a₁ + b₁ + 2 * i + 1) = 0 :=
    noLab_iff_cnt.mp (noLab_shW_of fun k' he => by simp only [frL] at he; omega)
  obtain ⟨h1, h2⟩ := two_to_one (T := T) (A₁ := [tL a₁ b₁ i]) (B₁ := (frL a₁ b₁ c₁, true) :: linv
    (tL a₁ b₁ i) :: rW a₁ b₁ c₁ L₁)
    (A₂ := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true)])
    (B₂ := (frL a₂ b₂ c₂ + (frL a₁ b₁ c₁ + 1), true) :: ((tL a₂ b₂ j).1 +
      (frL a₁ b₁ c₁ + 1), false) :: shW (frL a₁ b₁ c₁ + 1) (rW a₂ b₂ c₂ L₂))
    (r := (rL a₁ b₁ i).1) (σ := σ) (noLab_iff_cnt.mpr (by
      simp only [List.cons_append, List.nil_append, List.append_assoc, cnt_append, cnt_cons,
        cnt_nil, tL, rL, frL, linv, c1, c2] at *
      split_ifs <;> omega)) hf (by simp) (by simp)
  cases σ with
  | false =>
    obtain ⟨f', hf'⟩ := h1 rfl
    obtain ⟨X, Y, Z, h3, h4⟩ := state_merge bc₁ bc₂ hd
      (P := [(frL a₂ b₂ c₂ + (frL a₁ b₁ c₁ + 1), true), ((tL a₂ b₂ j).1 +
        (frL a₁ b₁ c₁ + 1), false)])
      (Q := shW (frL a₁ b₁ c₁ + 1) (eW a₂ b₂ c₂) ++ [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true),
        (frL a₁ b₁ c₁, true), linv (tL a₁ b₁ i)])
      (Q' := eW a₁ b₁ c₁ ++ [tL a₁ b₁ i]) (DisjL.symm (by
        intro l hl
        simp only [shW_eW] at hl
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · dsimp only
            exact noLab_two (M := frL a₁ b₁ c₁ + 1) (by omega)
              (fun m hm => by
                have := hL₁ m hm
                omega)
              (fun k' he => by
                simp only [frL] at he
                exact ⟨by omega, fun m hm => by have := hL₂ m hm; omega⟩))) (by
        intro k
        simp only [shW_eW]
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          cnt_cons, cnt_nil]
        split_ifs <;> omega)
    obtain ⟨w, h5, h6⟩ := nf_caseC_neg.{uu} (x₁ := (2 * a₁ + b₁ + 2 * c₁, true)) (x₂ :=
      (2 * a₂ + b₂ + 2 * c₂ + (frL a₁ b₁ c₁ + 1), true))
      (g₂ := (frL a₂ b₂ c₂ + (frL a₁ b₁ c₁ + 1), true)) (g₁ := (frL a₁ b₁ c₁, true)) (t₂ :=
        ((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true))
      (t₁ := tL a₁ b₁ i) h3 (by simp only [frL]; omega)
    refine homeo_of_nf (w₀ := _) (f := f') ?_ h5 (h4.trans h6)
    convert hf' using 2
    simp [rW_eq, shW_append]
  | true =>
    obtain ⟨f', hf'⟩ := h2 rfl
    obtain ⟨X, Y, Z, h3, h4⟩ := state_merge bc₁ bc₂.winv hd.winv_left
      (P := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false)] ++ shW (frL a₁ b₁ c₁ + 1) (eW a₂ b₂ c₂))
      (Q := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true), (frL a₂ b₂ c₂ +
        (frL a₁ b₁ c₁ + 1), false), (frL a₁ b₁ c₁, true), linv (tL a₁ b₁ i)])
      (Q' := eW a₁ b₁ c₁ ++ [tL a₁ b₁ i]) (DisjL.symm (by
        intro l hl
        simp only [shW_eW] at hl
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · dsimp only
            exact noLab_two' (M := frL a₁ b₁ c₁ + 1) (by omega)
              (fun m hm => by
                have := hL₁ m hm
                omega)
              (fun k' he => by
                simp only [frL] at he
                exact ⟨by omega, fun m hm => by have := hL₂ m hm; omega⟩))) (by
        intro k
        simp only [shW_eW]
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          cnt_cons, cnt_nil]
        split_ifs <;> omega)
    obtain ⟨w, h5, h6⟩ := nf_caseC_pos.{uu} (x₁ := (2 * a₁ + b₁ + 2 * c₁, true)) (x₂ :=
      (2 * a₂ + b₂ + 2 * c₂ + (frL a₁ b₁ c₁ + 1), true))
      (g₂ := (frL a₂ b₂ c₂ + (frL a₁ b₁ c₁ + 1), false)) (g₁ := (frL a₁ b₁ c₁, true)) (t₂ :=
        ((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true))
      (t₁ := tL a₁ b₁ i) h3 (by simp only [frL]; omega)
    refine homeo_of_nf (w₀ := _) (f := f') ?_ h5 (h4.trans h6)
    convert hf' using 2
    simp [rW_eq, shW_append, winv_append, winv_cons, winv_shW_eW, winv_nil, linv]

/-- The surface with two components glued along a whole cuff. -/
theorem homeo_of_two_loop (hi : i < c₁) (hj : j < c₂) (hN₁ : L₁.Nodup) (hN₂ : L₂.Nodup)
  (hL₁ : ∀ m ∈ L₁, m < c₁ ∧ m ≠ i)
    (hL₂ : ∀ m ∈ L₂, m < c₂ ∧ m ≠ j)
    (hf : Presents (dW (wLoop₁ a₁ b₁ c₁ i L₁) (wLoop₂ a₂ b₂ c₂ j L₂ (frL a₁ b₁ c₁ + 1)
      ((rL a₁ b₁ i).1, σ))) f) :
    Nonempty (T ≃ₜ SurfaceModel (a₂ + a₁) (b₂ + b₁) (L₂.length + L₁.length)) := by
  have bc₁ := bc_hH a₁ b₁ hN₁
  have bc₂ := (bc_hH a₂ b₂ hN₂).shift (frL a₁ b₁ c₁ + 1)
  have hd : DisjL (shW (frL a₁ b₁ c₁ + 1) (hH a₂ b₂ L₂)) (hH a₁ b₁ L₁) :=
    disj_hH (fun m hm => (hL₁ m hm).1) (by simp only [frL]; omega)
  have c1 : cnt (rW a₁ b₁ c₁ L₁) (2 * a₁ + b₁ + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega
  have c2 : cnt (shW (frL a₁ b₁ c₁ + 1) (rW a₂ b₂ c₂ L₂)) (2 * a₁ + b₁ + 2 * i + 1) = 0 :=
    noLab_iff_cnt.mp (noLab_shW_of fun k' he => by simp only [frL] at he; omega)
  obtain ⟨h1, h2⟩ := two_to_one (T := T) (A₁ := [tL a₁ b₁ i]) (B₁ := linv
    (tL a₁ b₁ i) :: rW a₁ b₁ c₁ L₁)
    (A₂ := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true)])
    (B₂ := ((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false) :: shW (frL a₁ b₁ c₁ + 1) (rW a₂ b₂ c₂ L₂))
    (r := (rL a₁ b₁ i).1) (σ := σ) (noLab_iff_cnt.mpr (by
      simp only [List.cons_append, List.nil_append, List.append_assoc, cnt_append, cnt_cons,
        cnt_nil, tL, rL, frL, linv, c1, c2] at *
      split_ifs <;> omega)) hf (by simp) (by simp)
  have key : ∀ {w₀ : List Letter} {f' : ℕ × ℂ → T}, Presents (sW w₀) f' → ∀ {X Y Z : List Letter},
      Inv [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false), (2 * a₂ + b₂ + 2 * c₂ +
        (frL a₁ b₁ c₁ + 1), true),
        (2 * a₂ + b₂ + 2 * c₂ + (frL a₁ b₁ c₁ + 1), false), ((tL a₂ b₂ j).1 +
          (frL a₁ b₁ c₁ + 1), true), linv (tL a₁ b₁ i),
        (2 * a₁ + b₁ + 2 * c₁, true), (2 * a₁ + b₁ + 2 * c₁, false), tL a₁ b₁ i] X Y Z (a₂ + a₁)
          (b₂ + b₁) (L₂.length + L₁.length) →
      WEq.{uu} w₀ ([((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false), (2 * a₂ + b₂ + 2 * c₂ +
        (frL a₁ b₁ c₁ + 1), true),
        (2 * a₂ + b₂ + 2 * c₂ + (frL a₁ b₁ c₁ + 1), false), ((tL a₂ b₂ j).1 +
          (frL a₁ b₁ c₁ + 1), true), linv (tL a₁ b₁ i),
        (2 * a₁ + b₁ + 2 * c₁, true), (2 * a₁ + b₁ + 2 * c₁, false), tL a₁ b₁ i] ++ X ++ Y ++ Z) →
      Nonempty (T ≃ₜ SurfaceModel (a₂ + a₁) (b₂ + b₁) (L₂.length + L₁.length)) := by
    intro w₀ f' hf' X Y Z h3 h4
    rcases nf_caseF.{uu} (x₁ := (2 * a₁ + b₁ + 2 * c₁, true)) (x₂ := (2 * a₂ + b₂ + 2 * c₂ +
      (frL a₁ b₁ c₁ + 1), true))
      (t₂ := ((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true)) (t₁ := tL a₁ b₁ i) h3 with ⟨w, h5, h6⟩ |
        ⟨h5, h6, h7, y, h8⟩
    · exact homeo_of_nf hf' h5 (h4.trans h6)
    · rw [h5, h6, h7]
      exact homeo_of_sphere hf' (h4.trans h8)
  cases σ with
  | false =>
    obtain ⟨f', hf'⟩ := h1 rfl
    obtain ⟨X, Y, Z, h3, h4⟩ := state_merge bc₁ bc₂ hd
      (P := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false)])
      (Q := shW (frL a₁ b₁ c₁ + 1) (eW a₂ b₂ c₂) ++ [((tL a₂ b₂ j).1 +
        (frL a₁ b₁ c₁ + 1), true), linv (tL a₁ b₁ i)])
      (Q' := eW a₁ b₁ c₁ ++ [tL a₁ b₁ i]) (DisjL.symm (by
        intro l hl
        simp only [shW_eW] at hl
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · dsimp only
            exact noLab_two (M := frL a₁ b₁ c₁ + 1) (by omega)
              (fun m hm => by
                have := hL₁ m hm
                omega)
              (fun k' he => by
                simp only [frL] at he
                exact ⟨by omega, fun m hm => by have := hL₂ m hm; omega⟩))) (by
        intro k
        simp only [shW_eW]
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          cnt_cons, cnt_nil]
        split_ifs <;> omega)
    refine key (f' := f') ?_ h3 h4
    convert hf' using 2
    simp [rW_eq, shW_append]
  | true =>
    obtain ⟨f', hf'⟩ := h2 rfl
    obtain ⟨X, Y, Z, h3, h4⟩ := state_merge bc₁ bc₂.winv hd.winv_left
      (P := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), false)] ++ shW (frL a₁ b₁ c₁ + 1) (eW a₂ b₂ c₂))
      (Q := [((tL a₂ b₂ j).1 + (frL a₁ b₁ c₁ + 1), true), linv (tL a₁ b₁ i)])
      (Q' := eW a₁ b₁ c₁ ++ [tL a₁ b₁ i]) (DisjL.symm (by
        intro l hl
        simp only [shW_eW] at hl
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · dsimp only
            exact noLab_two' (M := frL a₁ b₁ c₁ + 1) (by omega)
              (fun m hm => by
                have := hL₁ m hm
                omega)
              (fun k' he => by
                simp only [frL] at he
                exact ⟨by omega, fun m hm => by have := hL₂ m hm; omega⟩))) (by
        intro k
        simp only [shW_eW]
        simp only [eW, tL, frL, linv, List.cons_append, List.nil_append,
          cnt_cons, cnt_nil]
        split_ifs <;> omega)
    refine key (f' := f') ?_ h3 h4
    convert hf' using 2
    simp [rW_eq, shW_append, winv_append, winv_cons, winv_shW_eW, winv_nil, linv]

end

end GraphMinor.Surface
