/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordNormal

/-!
# Comparing normal forms

Two normal forms with the same numbers `a`, `b`, `c` are equal up to names and signs of labels
(`nf_eq`). A handle
next to a cross-cap can be replaced by two cross-caps (`nf_tp`). The list `nfW a b c` is a normal
form for each `a`,
`b`, `c`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

universe uu

/-- Equal words up to names and signs of labels. -/
def Iso (w w' : List Letter) : Prop :=
  ∃ (r : ℕ → ℕ) (f : ℕ → Bool), (∀ l ∈ w, ∀ l' ∈ w, r l.1 = r l'.1 → l.1 = l'.1) ∧
    w.map (fun l => (r l.1, xor (f l.1) l.2)) = w'

theorem Iso.weq {w w' : List Letter} (h : Iso w w') : WEq.{uu} w w' := by
  obtain ⟨r, f, hr, rfl⟩ := h
  have h1 := WEq.flip.{uu} w f
  have hm : ∀ {l : Letter}, l ∈ w.map (flipL f) → ∃ m ∈ w, m.1 = l.1 := fun hl => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    exact ⟨m, hm, rfl⟩
  have h2 := peq_relab.{uu} (r := r) (W := sW (w.map (flipL f))) (by
    intro i j l hl l' hl' he
    have hmem : ∀ i, ∀ l ∈ sW (w.map (flipL f)) i, l ∈ w.map (flipL f) := by
      intro i l hl
      by_cases hi : i = 0
      · subst hi
        simpa [sW] using hl
      · simp [sW, update_of_ne hi, nW] at hl
    obtain ⟨m, hm1, hm2⟩ := hm (hmem _ _ hl)
    obtain ⟨m', hm1', hm2'⟩ := hm (hmem _ _ hl')
    rw [← hm2, ← hm2'] at he ⊢
    exact hr m hm1 m' hm1' he)
  have e : relab r (sW (w.map (flipL f))) = sW (w.map fun l => (r l.1, xor (f l.1) l.2)) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [relab, sW, flipL, Function.comp_def]
    · simp [relab, sW, update_of_ne hi, nW]
  rw [e] at h2
  exact h1.trans h2

theorem Iso.nil : Iso [] [] := ⟨id, fun _ => false, by simp, rfl⟩

theorem Iso.append {a a' b b' : List Letter} (ha : Iso a a') (hb : Iso b b') (hd : DisjL a b)
  (hd' : DisjL a' b') :
    Iso (a ++ b) (a' ++ b') := by
  classical
  obtain ⟨r, f, hr, rfl⟩ := ha
  obtain ⟨r', f', hr', rfl⟩ := hb
  let A : Set ℕ := {c | ∃ l ∈ a, l.1 = c}
  have hmap : ∀ l ∈ a, (fun l : Letter => ((if l.1 ∈ A then r l.1 else r' l.1),
      xor (if l.1 ∈ A then f l.1 else f' l.1) l.2)) l = (r l.1, xor (f l.1) l.2) := fun l hl => by
    have : l.1 ∈ A := ⟨l, hl, rfl⟩
    simp [this]
  have hmap' : ∀ l ∈ b, (fun l : Letter => ((if l.1 ∈ A then r l.1 else r' l.1),
      xor (if l.1 ∈ A then f l.1 else f' l.1) l.2)) l = (r' l.1, xor (f' l.1) l.2) := fun l hl => by
    have : l.1 ∉ A := by
      rintro ⟨m, hm, he⟩
      exact hd m hm l hl he.symm
    simp [this]
  refine ⟨fun c => if c ∈ A then r c else r' c, fun c => if c ∈ A then f c else f' c, ?_, ?_⟩
  · have key : ∀ l ∈ a, ∀ l' ∈ b, r l.1 ≠ r' l'.1 := fun l hl l' hl' he => by
      have h1 : (r l.1, xor (f l.1) l.2) ∈ a.map (fun l => (r l.1, xor (f l.1) l.2)) :=
        List.mem_map.mpr ⟨l, hl, rfl⟩
      have h2 : (r' l'.1, xor (f' l'.1) l'.2) ∈ b.map (fun l => (r' l.1, xor (f' l.1) l.2)) :=
        List.mem_map.mpr ⟨l', hl', rfl⟩
      exact hd' _ h1 _ h2 he.symm
    intro l hl l' hl' he
    have ga : ∀ m ∈ a, (if m.1 ∈ A then r m.1 else r' m.1) = r m.1 := fun m hm => by
      have : m.1 ∈ A := ⟨m, hm, rfl⟩
      simp [this]
    have gb : ∀ m ∈ b, (if m.1 ∈ A then r m.1 else r' m.1) = r' m.1 := fun m hm => by
      have : m.1 ∉ A := by
        rintro ⟨n, hn, he⟩
        exact hd n hn m hm he.symm
      simp [this]
    dsimp only at he
    rcases List.mem_append.mp hl with h1 | h1 <;> rcases List.mem_append.mp hl' with h2 | h2
    · rw [ga l h1, ga l' h2] at he
      exact hr l h1 l' h2 he
    · rw [ga l h1, gb l' h2] at he
      exact absurd he (key l h1 l' h2)
    · rw [gb l h1, ga l' h2] at he
      exact absurd he.symm (key l' h2 l h1)
    · rw [gb l h1, gb l' h2] at he
      exact hr' l h1 l' h2 he
  · rw [List.map_append]
    congr 1
    · exact List.map_congr_left hmap
    · exact List.map_congr_left hmap'

theorem iso_hnd {u v u' v' : Letter} (h : u.1 ≠ v.1) (h' : u'.1 ≠ v'.1) : Iso (hndB u v)
  (hndB u' v') := by
  classical
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  obtain ⟨a', b'⟩ := u'
  obtain ⟨c', d'⟩ := v'
  have h1 : a ≠ c := h
  have h2 : c ≠ a := fun e => h e.symm
  refine ⟨fun n => if n = a then a' else c', fun n => if n = a then xor b b' else xor d d', ?_, ?_⟩
  · intro l hl l' hl' he
    simp only [hndB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl hl'
    have ha' : a' ≠ c' := h'
    rcases hl with rfl | rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl | rfl <;>
      simp_all
  · simp only [hndB, linv, List.map_cons, List.map_nil, ite_true, ite_eq_right h2]
    cases b <;> cases b' <;> cases d <;> cases d' <;> simp

theorem iso_cap (y y' : Letter) : Iso [y, y] [y', y'] := by
  refine ⟨fun _ => y'.1, fun _ => xor y.2 y'.2, ?_, ?_⟩
  · intro l hl l' hl' _
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl hl'
    rw [hl, hl']
  · obtain ⟨a, b⟩ := y
    obtain ⟨c, d⟩ := y'
    cases b <;> cases d <;> simp

theorem iso_hol {u v u' v' : Letter} (h : u.1 ≠ v.1) (h' : u'.1 ≠ v'.1) : Iso (holB u v)
  (holB u' v') := by
  classical
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  obtain ⟨a', b'⟩ := u'
  obtain ⟨c', d'⟩ := v'
  have h1 : a ≠ c := h
  have h2 : c ≠ a := fun e => h e.symm
  refine ⟨fun n => if n = a then a' else c', fun n => if n = a then xor b b' else xor d d', ?_, ?_⟩
  · intro l hl l' hl' he
    simp only [holB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl hl'
    have ha' : a' ≠ c' := h'
    rcases hl with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;> simp_all
  · simp only [holB, linv, List.map_cons, List.map_nil, ite_true, ite_eq_right h2]
    cases b <;> cases b' <;> cases d <;> cases d' <;> simp

theorem HL.iso {a : ℕ} {X X' : List Letter} (h : HL a X) (h' : HL a X') : Iso X X' := by
  induction h generalizing X' with
  | nil =>
    cases h'
    exact Iso.nil
  | cons u v huv hX _ ih =>
    cases h' with
    | cons u' v' huv' hX' h'' => exact (iso_hnd huv huv').append (ih h'') hX hX'

theorem CL.iso {a : ℕ} {X X' : List Letter} (h : CL a X) (h' : CL a X') : Iso X X' := by
  induction h generalizing X' with
  | nil =>
    cases h'
    exact Iso.nil
  | cons u hX _ ih =>
    cases h' with
    | cons u' hX' h'' => exact (iso_cap u u').append (ih h'') hX hX'

theorem TL.iso {a : ℕ} {X X' : List Letter} (h : TL a X) (h' : TL a X') : Iso X X' := by
  induction h generalizing X' with
  | nil =>
    cases h'
    exact Iso.nil
  | cons u v huv hX _ ih =>
    cases h' with
    | cons u' v' huv' hX' h'' => exact (iso_hol huv huv').append (ih h'') hX hX'

/-- **Equal numbers give equivalent normal forms.** -/
theorem nf_eq {w w' : List Letter} {a b c : ℕ} (h : IsNF w a b c) (h' : IsNF w' a b c) : WEq.{uu} w
  w' := by
  obtain ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨X', Y', Z', rfl, h1', h2', h3', h4', h5', h6'⟩ := h'
  exact (((h1.iso h1').append (h2.iso h2') h4 h4').append (h3.iso h3') (h5.append_left h6)
    (h5'.append_left h6')).weq

/-- The handles with labels from `k` on. -/
def hW (k : ℕ) : ℕ → List Letter
  | 0 => []
  | a + 1 => hndB (k, true) (k + 1, true) ++ hW (k + 2) a

/-- The cross-caps with labels from `k` on. -/
def cW (k : ℕ) : ℕ → List Letter
  | 0 => []
  | a + 1 => [(k, true), (k, true)] ++ cW (k + 1) a

/-- The holes with labels from `k` on. -/
def tW (k : ℕ) : ℕ → List Letter
  | 0 => []
  | a + 1 => holB (k, true) (k + 1, true) ++ tW (k + 2) a

theorem hW_labels (k a : ℕ) : ∀ l ∈ hW k a, k ≤ l.1 ∧ l.1 < k + 2 * a := by
  induction a generalizing k with
  | zero => simp [hW]
  | succ a ih =>
    intro l hl
    simp only [hW, hndB, linv, List.cons_append, List.mem_cons, List.nil_append] at hl
    rcases hl with rfl | rfl | rfl | rfl | hl
    · simp
    · simp; omega
    · simp
    · simp; omega
    · have := ih (k + 2) l hl
      omega

theorem cW_labels (k a : ℕ) : ∀ l ∈ cW k a, k ≤ l.1 ∧ l.1 < k + a := by
  induction a generalizing k with
  | zero => simp [cW]
  | succ a ih =>
    intro l hl
    simp only [cW, List.cons_append, List.mem_cons, List.nil_append] at hl
    rcases hl with rfl | rfl | hl
    · simp
    · simp
    · have := ih (k + 1) l hl
      omega

theorem tW_labels (k a : ℕ) : ∀ l ∈ tW k a, k ≤ l.1 ∧ l.1 < k + 2 * a := by
  induction a generalizing k with
  | zero => simp [tW]
  | succ a ih =>
    intro l hl
    simp only [tW, holB, linv, List.cons_append, List.mem_cons, List.nil_append] at hl
    rcases hl with rfl | rfl | rfl | hl
    · simp
    · simp; omega
    · simp
    · have := ih (k + 2) l hl
      omega

theorem hL_hW (k a : ℕ) : HL a (hW k a) := by
  induction a generalizing k with
  | zero => exact .nil
  | succ a ih =>
    refine .cons _ _ (by simp) ?_ (ih (k + 2))
    intro l hl m hm he
    have := (hW_labels _ _ m hm).1
    simp only [hndB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> simp at he <;> omega

theorem cL_cW (k a : ℕ) : CL a (cW k a) := by
  induction a generalizing k with
  | zero => exact .nil
  | succ a ih =>
    refine .cons _ ?_ (ih (k + 1))
    intro l hl m hm he
    have := (cW_labels _ _ m hm).1
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
    subst hl
    simp at he
    omega

theorem tL_tW (k a : ℕ) : TL a (tW k a) := by
  induction a generalizing k with
  | zero => exact .nil
  | succ a ih =>
    refine .cons _ _ (by simp) ?_ (ih (k + 2))
    intro l hl m hm he
    have := (tW_labels _ _ m hm).1
    simp only [holB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> simp at he <;> omega

/-- The chosen normal form. -/
def nfW (a b c : ℕ) : List Letter := hW 0 a ++ cW (2 * a) b ++ tW (2 * a + b) c

theorem isNF_nfW (a b c : ℕ) : IsNF (nfW a b c) a b c := by
  refine ⟨_, _, _, rfl, hL_hW _ _, cL_cW _ _, tL_tW _ _, ?_, ?_, ?_⟩
  · intro l hl m hm he
    have h1 := (hW_labels _ _ l hl).2
    have h2 := (cW_labels _ _ m hm).1
    omega
  · intro l hl m hm he
    have h1 := (hW_labels _ _ l hl).2
    have h2 := (tW_labels _ _ m hm).1
    omega
  · intro l hl m hm he
    have h1 := (cW_labels _ _ l hl).2
    have h2 := (tW_labels _ _ m hm).1
    omega

/-- A handle and a cross-cap are three cross-caps. -/
theorem weq_tp {u v y : Letter} (C : List Letter) (huv : u.1 ≠ v.1) (huy : u.1 ≠ y.1)
  (hvy : v.1 ≠ y.1)
    (hu : NoLab C u.1) (hv : NoLab C v.1) (hy : NoLab C y.1) :
    WEq.{uu} (C ++ hndB u v ++ [y, y]) (C ++ [linv v, linv v] ++ [u, u] ++ [y, y]) := by
  have hvu : v.1 ≠ u.1 := fun e => huv e.symm
  have hyu : y.1 ≠ u.1 := fun e => huy e.symm
  have hyv : y.1 ≠ v.1 := fun e => hvy e.symm
  have c0 : WEq.{uu} (C ++ hndB u v ++ [y, y]) (y :: C ++ u :: v :: linv u :: linv v :: [y]) :=
    WEq.rot' (C ++ hndB u v ++ [y]) [y] (by simp [hndB]) (by simp [hndB])
  have c1 : WEq.{uu} (y :: C ++ u :: v :: linv u :: linv v :: [y]) (u ::
    ((y :: C) ++ [linv v, y] ++ linv u :: [v])) :=
    ruleA' u (y :: C) [] [v] [linv v, y] (noLab_cons.mpr ⟨hyu, hu⟩) noLab_nil
      (noLab_cons.mpr ⟨hvu, noLab_nil⟩)
      (noLab_cons.mpr ⟨hvu, noLab_cons.mpr ⟨hyu, noLab_nil⟩⟩) (by simp) (by simp)
  have c2 : WEq.{uu} (u :: ((y :: C) ++ [linv v, y] ++ linv u :: [v])) (C ++ linv v :: y ::
    (linv u :: v :: u :: [y])) :=
    WEq.rot' [u, y] (C ++ linv v :: y :: linv u :: [v]) (by simp) (by simp)
  have c3 : WEq.{uu} (C ++ linv v :: y :: (linv u :: v :: u :: [y]))
      (y :: (C ++ [linv v] ++ winv [linv u, v, u] ++ [y])) :=
    ruleB' y (C ++ [linv v]) [] [linv u, v, u] [] (noLab_append.mpr ⟨hy, noLab_cons.mpr ⟨hvy,
      noLab_nil⟩⟩) noLab_nil
      (noLab_cons.mpr ⟨huy, noLab_cons.mpr ⟨hvy, noLab_cons.mpr ⟨huy, noLab_nil⟩⟩⟩) noLab_nil
        (by simp)
      (by simp [winv])
  have e : winv [linv u, v, u] = [linv u, linv v, u] := by simp [winv, linv_linv]
  rw [e] at c3
  have c4 : WEq.{uu} (y :: (C ++ [linv v] ++ [linv u, linv v, u] ++ [y]))
      (linv v :: ([u, y, y] ++ C ++ linv v :: [linv u])) :=
    WEq.rot' (y :: C ++ [linv v, linv u]) [linv v, u, y] (by simp) (by simp)
  have n1 : NoLab ([u, y, y] ++ C) (linv v).1 := noLab_append.mpr
    ⟨noLab_cons.mpr ⟨huv, noLab_cons.mpr ⟨hyv, noLab_cons.mpr ⟨hyv, noLab_nil⟩⟩⟩, hv⟩
  have c5 : WEq.{uu} (linv v :: ([u, y, y] ++ C ++ linv v :: [linv u]))
      ([u, y, y] ++ C ++ linv v :: linv v :: winv [linv u]) :=
    ruleB' (linv v) [] ([u, y, y] ++ C) [] [linv u] noLab_nil n1 noLab_nil
      (noLab_cons.mpr ⟨huv, noLab_nil⟩) (by simp) (by simp [winv])
  have e2 : winv [linv u] = [u] := by simp [winv, linv_linv]
  rw [e2] at c5
  have c6 : WEq.{uu} ([u, y, y] ++ C ++ linv v :: linv v :: [u]) (C ++ [linv v, linv v] ++ [u, u]
    ++ [y, y]) :=
    WEq.rot' [u, y, y] (C ++ linv v :: linv v :: [u]) (by simp) (by simp)
  exact c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))))

/-- **A handle and a cross-cap are three cross-caps.** -/
theorem nf_tp {w w' : List Letter} {a b c : ℕ} (h : IsNF w (a + 1) (b + 1) c) (h' : IsNF w' a
  (b + 3) c) :
    WEq.{uu} w w' := by
  obtain ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩ := h
  cases h1 with
  | cons u v huv hX h1 =>
    cases h2 with
    | cons y hY h2 =>
      rename_i X₀ Y₀
      have hu : u ∈ hndB u v := by simp [hndB]
      have hv : v ∈ hndB u v := by simp [hndB]
      have hyy : y ∈ [y, y] := by simp
      have d1 : DisjL (hndB u v) ([y, y] ++ Y₀) := h4.left
      have d2 : DisjL X₀ ([y, y] ++ Y₀) := h4.right
      have d3 : DisjL (hndB u v) Z := h5.left
      have d4 : DisjL X₀ Z := h5.right
      have d5 : DisjL [y, y] Z := h6.left
      have d6 : DisjL Y₀ Z := h6.right
      have n1 := d1 u hu
      have n2 := d1 v hv
      have huy : u.1 ≠ y.1 := (noLab_cons.mp n1).1.symm
      have hvy : v.1 ≠ y.1 := (noLab_cons.mp n2).1.symm
      have huY := (noLab_append.mp n1).2
      have hvY := (noLab_append.mp n2).2
      have hxy : DisjL X₀ [y, y] := d2.inl
      have hyX : NoLab X₀ y.1 := hxy.symm y hyy
      have c0 : WEq.{uu} (hndB u v ++ X₀ ++ ([y, y] ++ Y₀) ++ Z) (X₀ ++ hndB u v ++ [y, y] ++
        (Y₀ ++ Z)) := by
        have := move_block.{uu} (P := []) (Q := X₀) (Z := [y, y] ++ Y₀ ++ Z) (.hnd u v huv)
          (by simp [DisjL, NoLab])
          hX (DisjL.append_right d1 d3)
        simpa using this
      have hC : (∀ l ∈ hndB u v ++ [y, y], NoLab (Y₀ ++ Z ++ X₀) l.1) := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact noLab_append.mpr ⟨noLab_append.mpr ⟨(d1.inr) l hl, d3 l hl⟩, hX l hl⟩
        · exact noLab_append.mpr ⟨noLab_append.mpr ⟨hY l hl, d5 l hl⟩, hxy.symm l hl⟩
      have c1 : WEq.{uu} (X₀ ++ hndB u v ++ [y, y] ++ (Y₀ ++ Z)) ((Y₀ ++ Z ++ X₀) ++ hndB u v ++
        [y, y]) :=
        WEq.rot' (X₀ ++ hndB u v ++ [y, y]) (Y₀ ++ Z) (by simp) (by simp)
      have c2 := weq_tp.{uu} (Y₀ ++ Z ++ X₀) huv huy hvy (hC u (by simp [hndB])) (hC v
        (by simp [hndB]))
        (hC y (by simp))
      set Y' := [linv v, linv v] ++ [u, u] ++ [y, y] ++ Y₀ with hY'
      have c3 : WEq.{uu} ((Y₀ ++ Z ++ X₀) ++ [linv v, linv v] ++ [u, u] ++ [y, y]) (X₀ ++ Y' ++ Z)
        :=
        WEq.rot' (Y₀ ++ Z) (X₀ ++ [linv v, linv v] ++ [u, u] ++ [y, y]) (by simp) (by simp [hY'])
      have hNF : IsNF (X₀ ++ Y' ++ Z) a (b + 3) c := by
        have hvu : v.1 ≠ u.1 := fun e => huv e.symm
        have dv : ∀ {w : List Letter}, NoLab w v.1 → DisjL [linv v, linv v] w := fun h l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
          subst hl
          exact h
        have du : ∀ {w : List Letter}, NoLab w u.1 → DisjL [u, u] w := fun h l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
          subst hl
          exact h
        have dy : ∀ {w : List Letter}, NoLab w y.1 → DisjL [y, y] w := fun h l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
          subst hl
          exact h
        have hnX : NoLab X₀ u.1 := hX u hu
        have hnX' : NoLab X₀ v.1 := hX v hv
        have e1 : Y' = [linv v, linv v] ++ ([u, u] ++ ([y, y] ++ Y₀)) := by simp [hY']
        have cl3 : CL (b + 1) ([y, y] ++ Y₀) := .cons y hY h2
        have cl2 : CL (b + 2) ([u, u] ++ ([y, y] ++ Y₀)) := .cons u (du n1) cl3
        have cl1 : CL (b + 3) Y' := by
          rw [e1]
          refine .cons (linv v) (dv ?_) cl2
          exact noLab_cons.mpr ⟨huv, noLab_cons.mpr ⟨huv, n2⟩⟩
        have hs : ∀ c, cnt Y' c ≤ cnt (hndB u v ++ ([y, y] ++ Y₀)) c := fun c => by
          rw [e1]
          simp only [hndB, cnt_append, cnt_cons, show cnt [] c = 0 from rfl, linv]
          omega
        have d7 : DisjL X₀ (hndB u v ++ ([y, y] ++ Y₀)) := DisjL.append_right hX.symm d2
        have d8 : DisjL Z (hndB u v ++ ([y, y] ++ Y₀)) := DisjL.append_right d3.symm h6.symm
        exact ⟨X₀, Y', Z, rfl, h1, cl1, h3, d7.mono hs, d4, (d8.mono hs).symm⟩
      exact c0.trans (c1.trans (c2.trans (c3.trans (nf_eq hNF h'))))

end GraphMinor.Surface
