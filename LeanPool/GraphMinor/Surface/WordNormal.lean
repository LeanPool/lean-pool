/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordSlide

/-!
# Normal form of a word

Every nonempty word with labels used at most twice is equivalent to a product of handles, cross-caps
and holes
(`exists_nf`), or to `x x⁻¹`. We keep a word in the form `R H`, with `H` a sorted product of blocks,
and each step
moves letters of `R` into `H`: a pair with equal signs gives a cross-cap (`step_cap`), two
interleaved pairs give a
handle (`step_hnd`), an innermost pair around letters that occur once gives a hole (`step_hole`) or
folds
(`step_fold`), and finally the letters that occur once form one more hole (`step_last`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

universe uu

/-- The hole with the tether `t` around the letter `r`. -/
def holB (t r : Letter) : List Letter := [t, r, linv t]

/-- Products of `a` handles. -/
inductive HL : ℕ → List Letter → Prop
  | nil : HL 0 []
  | cons {a : ℕ} {X : List Letter} (u v : Letter) (h : u.1 ≠ v.1) (hX : DisjL (hndB u v) X) :
      HL a X → HL (a + 1) (hndB u v ++ X)

/-- Products of `b` cross-caps. -/
inductive CL : ℕ → List Letter → Prop
  | nil : CL 0 []
  | cons {b : ℕ} {X : List Letter} (y : Letter) (hX : DisjL [y, y] X) : CL b X → CL (b + 1)
    ([y, y] ++ X)

/-- Products of `c` holes. -/
inductive TL : ℕ → List Letter → Prop
  | nil : TL 0 []
  | cons {c : ℕ} {X : List Letter} (t r : Letter) (h : t.1 ≠ r.1) (hX : DisjL (holB t r) X) :
      TL c X → TL (c + 1) (holB t r ++ X)

theorem isBlock_holB {t r : Letter} (h : t.1 ≠ r.1) : IsBlock (holB t r) := by
  have := IsBlock.hole t [r] (noLab_cons.mpr ⟨fun e => h e.symm, noLab_nil⟩)
  simpa [holB] using this

theorem HL.blocks {a : ℕ} {X : List Letter} (h : HL a X) : Blocks X := by
  induction h with
  | nil => exact .nil
  | cons u v h hX _ ih => exact .cons (.hnd u v h) hX ih

theorem CL.blocks {b : ℕ} {X : List Letter} (h : CL b X) : Blocks X := by
  induction h with
  | nil => exact .nil
  | cons y hX _ ih => exact .cons (.cap y) hX ih

theorem TL.blocks {c : ℕ} {X : List Letter} (h : TL c X) : Blocks X := by
  induction h with
  | nil => exact .nil
  | cons t r h hX _ ih => exact .cons (isBlock_holB h) hX ih

/-- The normal forms: a product of handles, cross-caps and holes. -/
def IsNF (w : List Letter) (a b c : ℕ) : Prop :=
  ∃ X Y Z, w = X ++ Y ++ Z ∧ HL a X ∧ CL b Y ∧ TL c Z ∧ DisjL X Y ∧ DisjL X Z ∧ DisjL Y Z

/-- The state of the procedure. -/
def Inv (R X Y Z : List Letter) (a b c : ℕ) : Prop :=
  HL a X ∧ CL b Y ∧ TL c Z ∧ DisjL X Y ∧ DisjL X Z ∧ DisjL Y Z ∧ DisjL X R ∧ DisjL Y R ∧ DisjL Z R
    ∧ Good R

theorem DisjL.mono {L a b : List Letter} (h : DisjL L a) (hs : ∀ c, cnt b c ≤ cnt a c) : DisjL L b
  := by
  intro l hl
  have h1 := noLab_iff_cnt.mp (h l hl)
  have h2 := hs l.1
  exact noLab_iff_cnt.mpr (by omega)

theorem DisjL.mono_left {L a b : List Letter} (h : DisjL a L) (hs : ∀ c, cnt b c
  ≤ cnt a c) : DisjL b L :=
  (h.symm.mono hs).symm

theorem Good.mono {a b : List Letter} (h : Good a) (hs : ∀ c, cnt b c ≤ cnt a c) : Good b :=
  fun c => (hs c).trans (h c)

theorem noLab_of_cnt {w : List Letter} {c : ℕ} (h : cnt w c = 0) : NoLab w c := noLab_iff_cnt.mpr h

theorem Inv.blocks {R X Y Z : List Letter} {a b c : ℕ} (h : Inv R X Y Z a b c) : Blocks
  (X ++ Y ++ Z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact (h1.blocks.append h2.blocks h4).append h3.blocks (h5.append_left h6)

theorem Inv.disj {R X Y Z : List Letter} {a b c : ℕ} (h : Inv R X Y Z a b c) : DisjL
  (X ++ Y ++ Z) R := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, -⟩ := h
  exact (h7.append_left h8).append_left h9

/-- A pair with equal signs gives a cross-cap. -/
theorem step_cap {R X Y Z P Q S : List Letter} {x : Letter} {a b c : ℕ} (hI : Inv R X Y Z a b c)
    (hR : R = P ++ x :: Q ++ x :: S) :
    Inv (S ++ P ++ winv Q) X ([x, x] ++ Y) Z a (b + 1) c ∧
      WEq.{uu} (R ++ X ++ Y ++ Z) ((S ++ P ++ winv Q) ++ X ++ ([x, x] ++ Y) ++ Z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hI
  have hc : ∀ c, cnt R c = cnt P c + cnt Q c + cnt S c + 2 * (if x.1 = c then 1 else 0) := by
    intro c
    rw [hR]
    simp only [cnt_append, cnt_cons]
    omega
  have hx := h10 x.1
  rw [hc] at hx
  simp only [ite_true] at hx
  have hP : NoLab P x.1 := noLab_of_cnt (by omega)
  have hQ : NoLab Q x.1 := noLab_of_cnt (by omega)
  have hS : NoLab S x.1 := noLab_of_cnt (by omega)
  have hsub : ∀ c, cnt (S ++ P ++ winv Q) c ≤ cnt R c := fun c => by
    rw [hc]
    simp only [cnt_append, cnt_winv]
    omega
  have hcp : ∀ c, cnt [x, x] c ≤ cnt R c := fun c => by
    rw [hc]
    simp only [cnt_cons, show cnt [] c = 0 from rfl]
    omega
  have hxH : NoLab (X ++ Y ++ Z) x.1 := by
    have h11 := hI.disj.symm x (by rw [hR]; simp)
    exact h11
  have hB := hI.blocks
  set H := X ++ Y ++ Z with hH
  have hXYZ := noLab_append.mp hxH
  have hXY := noLab_append.mp hXYZ.1
  have hSP : NoLab (S ++ P ++ winv Q) x.1 := noLab_append.mpr ⟨noLab_append.mpr ⟨hS, hP⟩,
    noLab_winv.mpr hQ⟩
  refine ⟨⟨h1, .cons x (fun l hl => ?_) h2, h3, ?_, h5, ?_, h7.mono hsub, ?_, h9.mono hsub,
    h10.mono hsub⟩, ?_⟩
  · exact (h8.mono hcp).symm l hl
  · exact DisjL.append_right (h7.mono hcp) h4
  · exact DisjL.append_left (fun l hl => by
      have hlx : l = x := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hl
      have : l.1 = x.1 := congrArg Prod.fst hlx
      rw [this]
      exact hXYZ.2) h6
  · exact DisjL.append_left (fun l hl => by
      have hlx : l = x := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hl
      have : l.1 = x.1 := congrArg Prod.fst hlx
      rw [this]
      exact hSP) (h8.mono hsub)
  · have c0 : WEq.{uu} (R ++ X ++ Y ++ Z) (S ++ H ++ P ++ x :: Q ++ [x]) :=
      WEq.rot' (P ++ x :: Q ++ [x]) (S ++ H) (by simp [hR, hH]) (by simp)
    have c1 : WEq.{uu} (S ++ H ++ P ++ x :: Q ++ [x]) (x :: (S ++ H ++ P ++ winv Q ++ [x])) :=
      ruleB' x (S ++ H ++ P) [] Q [] (noLab_append.mpr ⟨noLab_append.mpr ⟨hS, hxH⟩, hP⟩) noLab_nil
        hQ noLab_nil
        (by simp) (by simp [winv])
    have c2 : WEq.{uu} (x :: (S ++ H ++ P ++ winv Q ++ [x])) (P ++ winv Q ++ [x, x] ++ S ++ H) :=
      WEq.rot' (x :: S ++ H) (P ++ winv Q ++ [x]) (by simp) (by simp)
    have hdA : DisjL H (P ++ winv Q ++ [x, x]) := hI.disj.mono fun c => by
      rw [hc]
      simp only [cnt_append, cnt_winv, cnt_cons, show cnt [] c = 0 from rfl]
      omega
    have hdS : DisjL H S := hI.disj.mono fun c => by
      rw [hc]
      omega
    have c3 : WEq.{uu} (P ++ winv Q ++ [x, x] ++ S ++ H) (S ++ (P ++ winv Q ++ [x, x]) ++ H) :=
      slide hB hdA hdS
    have hd1 : DisjL [x, x] (S ++ P ++ winv Q) := fun l hl => by
      have hlx : l = x := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hl
      have : l.1 = x.1 := congrArg Prod.fst hlx
      rw [this]
      exact hSP
    have hd2 : DisjL [x, x] X := fun l hl => by
      have hlx : l = x := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hl
      have : l.1 = x.1 := congrArg Prod.fst hlx
      rw [this]
      exact hXY.1
    have hd3 : DisjL [x, x] (Y ++ Z) := fun l hl => by
      have hlx : l = x := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hl
      have : l.1 = x.1 := congrArg Prod.fst hlx
      rw [this]
      exact noLab_append.mpr ⟨hXY.2, hXYZ.2⟩
    have c4 := move_block.{uu} (.cap x) hd1 hd2 hd3
    refine c0.trans (c1.trans (c2.trans (c3.trans ((WEq.of_eq ?_).trans (c4.trans
      (WEq.of_eq ?_))))))
    · simp [hH]
    · simp

/-- Two interleaved pairs give a handle. -/
theorem step_hnd {R X Y Z P Q S T V : List Letter} {x y : Letter} {a b c : ℕ}
  (hI : Inv R X Y Z a b c)
    (hxy : x.1 ≠ y.1) (hR : R = P ++ x :: Q ++ y :: S ++ linv x :: T ++ linv y :: V) :
    Inv (V ++ P ++ T ++ S ++ Q) (hndB y (linv x) ++ X) Y Z (a + 1) b c ∧
      WEq.{uu} (R ++ X ++ Y ++ Z) ((V ++ P ++ T ++ S ++ Q) ++ (hndB y (linv x) ++ X) ++ Y ++ Z)
        := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hI
  have hc : ∀ c, cnt R c = cnt P c + cnt Q c + cnt S c + cnt T c + cnt V c +
      2 * (if x.1 = c then 1 else 0) + 2 * (if y.1 = c then 1 else 0) := by
    intro c
    rw [hR]
    simp only [cnt_append, cnt_cons, linv]
    omega
  have hx := h10 x.1
  have hy := h10 y.1
  rw [hc] at hx hy
  simp only [ite_true] at hx hy
  have nx : ∀ {w}, cnt w x.1 = 0 → NoLab w x.1 := noLab_of_cnt
  have ny : ∀ {w}, cnt w y.1 = 0 → NoLab w y.1 := noLab_of_cnt
  have hP : NoLab P x.1 := nx (by omega)
  have hQ : NoLab Q x.1 := nx (by omega)
  have hS : NoLab S x.1 := nx (by omega)
  have hT : NoLab T x.1 := nx (by omega)
  have hV : NoLab V x.1 := nx (by omega)
  have hP' : NoLab P y.1 := ny (by omega)
  have hQ' : NoLab Q y.1 := ny (by omega)
  have hS' : NoLab S y.1 := ny (by omega)
  have hT' : NoLab T y.1 := ny (by omega)
  have hV' : NoLab V y.1 := ny (by omega)
  have hsub : ∀ c, cnt (V ++ P ++ T ++ S ++ Q) c ≤ cnt R c := fun c => by
    rw [hc]
    simp only [cnt_append]
    omega
  have hU : ∀ c, cnt (hndB y (linv x)) c ≤ cnt R c := fun c => by
    rw [hc]
    simp only [hndB, cnt_cons, show cnt [] c = 0 from rfl, linv]
    split_ifs <;> omega
  have hxH : NoLab (X ++ Y ++ Z) x.1 := hI.disj.symm x (by rw [hR]; simp)
  have hyH : NoLab (X ++ Y ++ Z) y.1 := hI.disj.symm y (by rw [hR]; simp)
  have hB := hI.blocks
  have hd := hI.disj
  have hXn := noLab_append.mp (noLab_append.mp hxH).1
  set H := X ++ Y ++ Z with hH
  have hyx : y.1 ≠ x.1 := fun e => hxy e.symm
  have hU1 : DisjL (hndB y (linv x)) (V ++ P ++ T ++ S ++ Q) := by
    intro l hl
    simp only [hndB, List.mem_cons, List.not_mem_nil, or_false, linv] at hl
    have hn : ∀ {w : List Letter}, NoLab w x.1 → NoLab w y.1 → NoLab w l.1 := fun {w} a1 a2 => by
      rcases hl with rfl | rfl | rfl | rfl
      · exact a2
      · exact a1
      · exact a2
      · simpa [linv_linv] using a1
    refine hn ?_ ?_
    · exact noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨hV, hP⟩, hT⟩,
        hS⟩, hQ⟩
    · exact noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨hV', hP'⟩,
        hT'⟩, hS'⟩, hQ'⟩
  have hhx : DisjL X (hndB y (linv x)) := h7.mono hU
  refine ⟨⟨.cons y (linv x) hyx hhx.symm h1, h2, h3, DisjL.append_left ((h8.mono hU).symm) h4,
    DisjL.append_left ((h9.mono hU).symm) h5, h6, DisjL.append_left hU1
      (h7.mono hsub), h8.mono hsub, h9.mono hsub,
    h10.mono hsub⟩, ?_⟩
  set C := V ++ H ++ P with hCd
  have hCx : NoLab C x.1 := noLab_append.mpr ⟨noLab_append.mpr ⟨hV, hxH⟩, hP⟩
  have hCy : NoLab C y.1 := noLab_append.mpr ⟨noLab_append.mpr ⟨hV', hyH⟩, hP'⟩
  have c0 : WEq.{uu} (R ++ X ++ Y ++ Z) (C ++ x :: Q ++ y :: S ++ linv x :: T ++ [linv y]) :=
    WEq.rot' (P ++ x :: Q ++ y :: S ++ linv x :: T ++ [linv y]) (V ++ H) (by simp [hR, hH])
      (by simp [hCd])
  have c1 : WEq.{uu} (C ++ x :: Q ++ y :: S ++ linv x :: T ++ [linv y])
      (Q ++ x :: (C ++ (T ++ [linv y]) ++ linv x :: y :: S)) :=
    ruleA' x C Q (y :: S) (T ++ [linv y]) hCx hQ (noLab_cons.mpr ⟨hyx, hS⟩)
      (noLab_append.mpr ⟨hT, noLab_cons.mpr ⟨hyx, noLab_nil⟩⟩) (by simp) (by simp)
  have c2 : WEq.{uu} (Q ++ x :: (C ++ (T ++ [linv y]) ++ linv x :: y :: S))
      (x :: C ++ T ++ linv y :: linv x :: y :: (S ++ Q)) :=
    WEq.rot' Q (x :: (C ++ (T ++ [linv y]) ++ linv x :: y :: S)) rfl (by simp)
  have c3 : WEq.{uu} (x :: C ++ T ++ linv y :: linv x :: y :: (S ++ Q))
      (linv y :: ((x :: C ++ T) ++ (S ++ Q) ++ y :: [linv x])) :=
    ruleA' (linv y) (x :: C ++ T) [] [linv x] (S ++ Q)
      (noLab_append.mpr ⟨noLab_cons.mpr ⟨hxy, hCy⟩, hT'⟩) noLab_nil
      (noLab_cons.mpr ⟨hxy, noLab_nil⟩) (noLab_append.mpr ⟨hS', hQ'⟩) (by simp [linv_linv])
        (by simp [linv_linv])
  have c4 : WEq.{uu} (linv y :: ((x :: C ++ T) ++ (S ++ Q) ++ y :: [linv x]))
      ((P ++ T ++ S ++ Q ++ hndB y (linv x)) ++ V ++ H) :=
    WEq.rot' ([linv y, x] ++ V ++ H) (P ++ T ++ S ++ Q ++ [y, linv x]) (by simp [hCd])
      (by simp [hndB, linv_linv])
  have hdA : DisjL H (P ++ T ++ S ++ Q ++ hndB y (linv x)) := hd.mono fun c => by
    rw [hc]
    simp only [hndB, cnt_append, cnt_cons, show cnt [] c = 0 from rfl, linv]
    split_ifs <;> omega
  have hdV : DisjL H V := hd.mono fun c => by
    rw [hc]
    omega
  have c5 := slide.{uu} hB hdA hdV
  exact c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (WEq.of_eq (by simp [hH])))))))

/-- Merging letters in a word. -/
theorem merge_all {A C : List Letter} {q : Letter} (B : List Letter)
    (hG : ∀ l ∈ q :: B, cnt (A ++ q :: B ++ C) l.1 = 1) :
    WEq.{uu} (A ++ q :: B ++ C) (A ++ q :: C) := by
  induction B with
  | nil => exact WEq.of_eq (by simp)
  | cons m B ih =>
    have hq := hG q (by simp)
    have hm := hG m (by simp)
    simp only [cnt_append, cnt_cons] at hq hm
    simp only [ite_true] at hq hm
    have hqm : q.1 ≠ m.1 := by
      intro he
      rw [ite_eq_left he] at hm
      omega
    have hn : NoLab (B ++ C ++ A) q.1 := noLab_of_cnt (by
      simp only [cnt_append]
      rw [ite_eq_right (fun e : m.1 = q.1 => hqm e.symm)] at hq
      omega)
    have hn' : NoLab (B ++ C ++ A) m.1 := noLab_of_cnt (by
      simp only [cnt_append]
      rw [ite_eq_right hqm] at hm
      omega)
    have c0 : WEq.{uu} (A ++ q :: (m :: B) ++ C) (q :: m :: (B ++ C ++ A)) :=
      WEq.rot' A (q :: m :: (B ++ C)) (by simp) (by simp)
    have c1 : WEq.{uu} (q :: m :: (B ++ C ++ A)) (q :: (B ++ C ++ A)) :=
      (WEq.merge (p := q.1) (q := m.1) (e := q.2) (e' := m.2) hqm hn hn').symm
    have c2 : WEq.{uu} (q :: (B ++ C ++ A)) (A ++ q :: B ++ C) :=
      WEq.rot' (q :: (B ++ C)) A (by simp) (by simp)
    refine c0.trans (c1.trans (c2.trans (ih fun l hl => ?_)))
    have h1 := hG l (by
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · simp [hl])
    have h2 : l.1 ≠ m.1 := by
      rcases List.mem_cons.mp hl with rfl | hl
      · exact hqm
      · intro he
        have := cnt_pos hl
        rw [he] at this
        omega
    simp only [cnt_append, cnt_cons, ite_eq_right (fun e : m.1 = l.1 => h2 e.symm)] at h1 ⊢
    omega

/-- An innermost pair around letters that occur once gives a hole. -/
theorem step_hole {R X Y Z P Q V : List Letter} {x q : Letter} {a b c : ℕ} (hI : Inv R X Y Z a b c)
    (hR : R = P ++ x :: q :: Q ++ linv x :: V) (hB : ∀ l ∈ q :: Q, cnt R l.1 = 1) :
    Inv (P ++ V) X Y (holB x q ++ Z) a b (c + 1) ∧
      WEq.{uu} (R ++ X ++ Y ++ Z) ((P ++ V) ++ X ++ Y ++ (holB x q ++ Z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hI
  have hc : ∀ c, cnt R c = cnt P c + (if q.1 = c then 1 else 0) + cnt Q c + cnt V c +
      2 * (if x.1 = c then 1 else 0) := by
    intro c
    rw [hR]
    simp only [cnt_append, cnt_cons, linv]
    omega
  have hx := h10 x.1
  rw [hc] at hx
  simp only [ite_true] at hx
  have hqq := hB q (by simp)
  rw [hc] at hqq
  simp only [ite_true] at hqq
  have hxq : x.1 ≠ q.1 := by
    intro he
    rw [ite_eq_left he] at hqq
    omega
  have hqx : q.1 ≠ x.1 := fun e => hxq e.symm
  rw [ite_eq_right hqx] at hx
  have hPx : NoLab P x.1 := noLab_of_cnt (by omega)
  have hQx : NoLab Q x.1 := noLab_of_cnt (by omega)
  have hVx : NoLab V x.1 := noLab_of_cnt (by omega)
  have hPq : NoLab P q.1 := noLab_of_cnt (by omega)
  have hVq : NoLab V q.1 := noLab_of_cnt (by omega)
  have hsub : ∀ c, cnt (P ++ V) c ≤ cnt R c := fun c => by
    rw [hc, cnt_append]
    omega
  have hU : ∀ c, cnt (holB x q) c ≤ cnt R c := fun c => by
    rw [hc]
    simp only [holB, cnt_cons, show cnt [] c = 0 from rfl, linv]
    split_ifs <;> omega
  have hUd : DisjL (holB x q) (P ++ V) := by
    intro l hl
    simp only [holB, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact noLab_append.mpr ⟨hPx, hVx⟩
    · exact noLab_append.mpr ⟨hPq, hVq⟩
    · exact noLab_append.mpr ⟨hPx, hVx⟩
  have hd := hI.disj
  have hdU : DisjL (X ++ Y ++ Z) (holB x q) := hd.mono hU
  refine ⟨⟨h1, h2, .cons x q hxq (h9.mono hU).symm h3, h4, DisjL.append_right (h7.mono hU) h5,
    DisjL.append_right (h8.mono hU) h6, h7.mono hsub, h8.mono hsub, DisjL.append_left hUd
      (h9.mono hsub),
    h10.mono hsub⟩, ?_⟩
  have hmerge : WEq.{uu} ((P ++ [x]) ++ q :: Q ++ (linv x :: (V ++ X ++ Y ++ Z)))
      ((P ++ [x]) ++ q :: (linv x :: (V ++ X ++ Y ++ Z))) := by
    refine merge_all Q fun l hl => ?_
    have h11 := hB l hl
    have hlR : l ∈ R := by
      rw [hR]
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · simp [hl]
    have h12 := noLab_iff_cnt.mp (hd.symm l hlR)
    have e : (P ++ [x]) ++ q :: Q ++ (linv x :: (V ++ X ++ Y ++ Z)) = R ++ (X ++ Y ++ Z) := by
      simp [hR]
    rw [e, cnt_append, h11, h12]
  have hx1 : DisjL (holB x q) P := hUd.inl
  have hx2 : DisjL (holB x q) (V ++ X ++ Y) := by
    refine DisjL.append_right (DisjL.append_right hUd.inr ?_) ?_
    · exact (h7.mono hU).symm
    · exact (h8.mono hU).symm
  have c2 := move_block.{uu} (isBlock_holB hxq) hx1 hx2 (h9.mono hU).symm
  refine (WEq.of_eq (by simp [hR])).trans (hmerge.trans ((WEq.of_eq (by simp [holB])).trans
    (c2.trans (WEq.of_eq (by simp)))))

theorem WEq.fold (x : Letter) {u : List Letter} (hu : u ≠ []) (hy : NoLab u x.1) :
    WEq.{uu} u (x :: linv x :: u) :=
  peq_fold finW_nW x.2 hu (freshIn_sW hy)

/-- A pair of adjacent letters is folded. -/
theorem step_fold {R X Y Z P V : List Letter} {x : Letter} {a b c : ℕ} (hI : Inv R X Y Z a b c)
    (hR : R = P ++ x :: linv x :: V) (hne : P ++ V ++ X ++ Y ++ Z ≠ []) :
    Inv (P ++ V) X Y Z a b c ∧ WEq.{uu} (R ++ X ++ Y ++ Z) ((P ++ V) ++ X ++ Y ++ Z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hI
  have hc : ∀ c, cnt R c = cnt P c + cnt V c + 2 * (if x.1 = c then 1 else 0) := by
    intro c
    rw [hR]
    simp only [cnt_append, cnt_cons, linv]
    omega
  have hx := h10 x.1
  rw [hc] at hx
  simp only [ite_true] at hx
  have hPx : NoLab P x.1 := noLab_of_cnt (by omega)
  have hVx : NoLab V x.1 := noLab_of_cnt (by omega)
  have hsub : ∀ c, cnt (P ++ V) c ≤ cnt R c := fun c => by
    rw [hc, cnt_append]
    omega
  have hxH : NoLab (X ++ Y ++ Z) x.1 := hI.disj.symm x (by rw [hR]; simp)
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7.mono hsub, h8.mono hsub, h9.mono hsub, h10.mono hsub⟩, ?_⟩
  set H := X ++ Y ++ Z with hH
  have c0 : WEq.{uu} (R ++ X ++ Y ++ Z) (x :: linv x :: (V ++ H ++ P)) :=
    WEq.rot' P (x :: linv x :: (V ++ H)) (by simp [hR, hH]) (by simp)
  have hne' : V ++ H ++ P ≠ [] := by
    intro he
    apply hne
    simp only [List.append_eq_nil_iff] at he ⊢
    simp only [hH, List.append_eq_nil_iff] at he
    tauto
  have c1 := (WEq.fold.{uu} x hne' (noLab_append.mpr ⟨noLab_append.mpr ⟨hVx, hxH⟩, hPx⟩)).symm
  have c2 : WEq.{uu} (V ++ H ++ P) (P ++ V ++ X ++ Y ++ Z) := WEq.rot' (V ++ H) P (by simp)
    (by simp [hH])
  exact c0.trans (c1.trans c2)

/-- The letters that occur once form the last hole. -/
theorem step_last {R X Y Z Q : List Letter} {q : Letter} {a b c : ℕ} (hI : Inv R X Y Z a b c)
    (hR : R = q :: Q) (hB : ∀ l ∈ R, cnt R l.1 = 1) :
    ∃ t, Inv [] X Y (holB t q ++ Z) a b (c + 1) ∧
      WEq.{uu} (R ++ X ++ Y ++ Z) ([] ++ X ++ Y ++ (holB t q ++ Z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hI
  have hd := hI.disj
  have hB' := hI.blocks
  have hqH : NoLab (X ++ Y ++ Z) q.1 := hd.symm q (by rw [hR]; simp)
  obtain ⟨y, -, hy⟩ := exists_fresh (q :: (X ++ Y ++ Z))
  let t : Letter := (y, true)
  have hyq : q.1 ≠ y := (noLab_cons.mp hy).1
  have hyH : NoLab (X ++ Y ++ Z) t.1 := (noLab_cons.mp hy).2
  have hyXYZ := noLab_append.mp hyH
  have hyXY := noLab_append.mp hyXYZ.1
  have hqXYZ := noLab_append.mp hqH
  have hqXY := noLab_append.mp hqXYZ.1
  have hmerge : WEq.{uu} ([] ++ q :: Q ++ (X ++ Y ++ Z)) ([] ++ q :: (X ++ Y ++ Z)) := by
    refine merge_all Q fun l hl => ?_
    have h11 := hB l (by rw [hR]; exact hl)
    have hlR : l ∈ R := by rw [hR]; exact hl
    have h12 := noLab_iff_cnt.mp (hd.symm l hlR)
    have e : [] ++ q :: Q ++ (X ++ Y ++ Z) = R ++ (X ++ Y ++ Z) := by simp [hR]
    rw [e, cnt_append, h11, h12]
  have hUX : ∀ {w : List Letter}, NoLab w t.1 → NoLab w q.1 → DisjL (holB t q) w := by
    intro w a1 a2 l hl
    simp only [holB, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact a1
    · exact a2
    · exact a1
  have ht1 : t.1 ≠ q.1 := fun e => hyq e.symm
  refine ⟨t, ⟨h1, h2, .cons t q ht1 (hUX hyXYZ.2 hqXYZ.2) h3, h4, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact DisjL.append_right (hUX hyXY.1 hqXY.1).symm h5
  · exact DisjL.append_right (hUX hyXY.2 hqXY.2).symm h6
  · simp [DisjL, NoLab]
  · simp [DisjL, NoLab]
  · simp [DisjL, NoLab]
  · simp [Good, cnt]
  · have c1 := WEq.fold.{uu} (linv t) (u := q :: (X ++ Y ++ Z)) (by simp)
      (noLab_cons.mpr ⟨hyq, hyH⟩)
    have d1 : DisjL (X ++ Y ++ Z) [linv t] := fun l hl m hm he => by
      simp only [List.mem_singleton] at hm
      subst hm
      exact hyH l hl he.symm
    have d2 : DisjL (X ++ Y ++ Z) [t, q] := fun l hl m hm he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hyH l hl he.symm
      · exact hqH l hl he.symm
    have c2 := slide.{uu} hB' d1 d2
    have c3 := move_block.{uu} (P := []) (isBlock_holB ht1) (by simp [DisjL, NoLab]) (hUX
      (noLab_append.mpr ⟨hyXY.1, hyXY.2⟩) (noLab_append.mpr ⟨hqXY.1, hqXY.2⟩)) (hUX hyXYZ.2 hqXYZ.2)
    refine (WEq.of_eq (by simp [hR])).trans (hmerge.trans ((WEq.of_eq (by simp)).trans (c1.trans
      ((WEq.of_eq (by simp [linv_linv])).trans (c2.trans ((WEq.of_eq (by simp [holB])).trans
        (c3.trans
      (WEq.of_eq (by simp)))))))))

/-- Reaching a normal form from a state. -/
theorem normalize (n : ℕ) : ∀ (R X Y Z : List Letter) (a b c : ℕ), R.length ≤ n → Inv R X Y Z a b c
  →
    R ++ X ++ Y ++ Z ≠ [] →
    (∃ a' b' c' w', IsNF w' a' b' c' ∧ WEq.{uu} (R ++ X ++ Y ++ Z) w') ∨
      ∃ x, WEq.{uu} (R ++ X ++ Y ++ Z) [x, linv x] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R X Y Z a b c hn hI hne
  have good := hI.2.2.2.2.2.2.2.2.2
  have len : ∀ (R' : List Letter), R'.length < R.length → R'.length < R.length := fun _ h => h
  have recur : ∀ (R' X' Y' Z' : List Letter) (a' b' c' : ℕ), R'.length < R.length →
      Inv R' X' Y' Z' a' b' c' → WEq.{uu} (R ++ X ++ Y ++ Z) (R' ++ X' ++ Y' ++ Z') →
      R' ++ X' ++ Y' ++ Z' ≠ [] →
      (∃ a' b' c' w', IsNF w' a' b' c' ∧ WEq.{uu} (R ++ X ++ Y ++ Z) w') ∨
      ∃ x, WEq.{uu} (R ++ X ++ Y ++ Z) [x, linv x] := by
    intro R' X' Y' Z' a' b' c' hl hI' he hne'
    have hR0 : 0 < R.length := by omega
    cases n with
    | zero => omega
    | succ m =>
      rcases ih m (by omega) R' X' Y' Z' a' b' c' (by omega) hI' hne' with
        ⟨a'', b'', c'', w', h1, h2⟩ | ⟨x, h2⟩
      · exact .inl ⟨a'', b'', c'', w', h1, he.trans h2⟩
      · exact .inr ⟨x, he.trans h2⟩
  by_cases hone : ∀ l ∈ R, cnt R l.1 = 1
  · cases R with
    | nil =>
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hI
      exact .inl ⟨a, b, c, _, ⟨X, Y, Z, rfl, h1, h2, h3, h4, h5, h6⟩, WEq.of_eq (by simp)⟩
    | cons q Q =>
      obtain ⟨t, hI', he⟩ := step_last.{uu} hI rfl hone
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hI'
      exact .inl ⟨a, b, c + 1, _, ⟨X, Y, _, rfl, h1, h2, h3, h4, h5, h6⟩,
        he.trans (WEq.of_eq (by simp))⟩
  push Not at hone
  obtain ⟨l, hl, hl1⟩ := hone
  have hpos := cnt_pos hl
  obtain ⟨P₀, Q₀, hsplit⟩ := List.append_of_mem hl
  have hcR : cnt R l.1 = cnt P₀ l.1 + 1 + cnt Q₀ l.1 := by
    rw [hsplit, cnt_append, cnt_cons, ite_eq_left rfl]
    omega
  have hcases : ∃ P B V x x', R = P ++ x :: B ++ x' :: V ∧ x'.1 = x.1 := by
    by_cases h : 0 < cnt Q₀ l.1
    · obtain ⟨B, m, V, rfl, hm⟩ := exists_of_cnt_pos h
      exact ⟨P₀, B, V, l, m, by simpa using hsplit, hm⟩
    · have h' : 0 < cnt P₀ l.1 := by omega
      obtain ⟨P, m, B, rfl, hm⟩ := exists_of_cnt_pos h'
      exact ⟨P, B, Q₀, m, l, by simpa using hsplit, hm.symm⟩
  obtain ⟨P, B, V, x, x', hE, hx⟩ := hcases
  rcases pair_cases good _ P B V x x' le_rfl hE hx with ⟨P, Q, S, x, hE⟩ |
    ⟨P, Q, S, T, V, x, y, hxy, hE⟩ | ⟨P, B, V, x, hE, hB⟩
  · obtain ⟨h1, h2⟩ := step_cap.{uu} hI hE
    refine recur _ _ _ _ _ _ _ ?_ h1 h2 (by simp)
    rw [hE]
    simp [winv]
    omega
  · obtain ⟨h1, h2⟩ := step_hnd.{uu} hI hxy hE
    refine recur _ _ _ _ _ _ _ ?_ h1 h2 (by simp [hndB])
    rw [hE]
    simp
    omega
  · cases B with
    | nil =>
      by_cases hempty : P ++ V ++ X ++ Y ++ Z = []
      · simp only [List.append_eq_nil_iff] at hempty
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hempty
        exact .inr ⟨x, WEq.of_eq (by simp [hE])⟩
      · have hE' : R = P ++ x :: linv x :: V := by simpa using hE
        obtain ⟨h1, h2⟩ := step_fold.{uu} hI hE' hempty
        refine recur _ _ _ _ _ _ _ ?_ h1 h2 hempty
        rw [hE']
        simp
    | cons q Q =>
      obtain ⟨h1, h2⟩ := step_hole.{uu} hI hE hB
      refine recur _ _ _ _ _ _ _ ?_ h1 h2 (by simp [holB])
      rw [hE]
      simp
      omega

/-- **Normal form of a word.** -/
theorem exists_nf {w : List Letter} (hw : w ≠ []) (hG : Good w) :
    (∃ a b c w', IsNF w' a b c ∧ WEq.{uu} w w') ∨ ∃ x, WEq.{uu} w [x, linv x] := by
  have hI : Inv w [] [] [] 0 0 0 := ⟨.nil, .nil, .nil, by simp [DisjL], by simp [DisjL], by simp
    [DisjL],
    by simp [DisjL], by simp [DisjL], by simp [DisjL], hG⟩
  simpa using normalize.{uu} _ w [] [] [] 0 0 0 le_rfl hI (by simpa using hw)

end GraphMinor.Surface
