/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordIso

/-!
# The words of the model surfaces

`modelW a b c` is the pair of words that we get from the model surface $\Sigma(a, b, c)$ by cutting
along the real
axis: `W₀` runs along the upper side and `W₁` along the lower side. `peq_modelW` shows that this
pair is equivalent to
the normal form `nfW a b c`. We peel off the holes from the last one to the first one.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

universe uu

/-- The label of the segment number `k` of the real axis. -/
def segL (k : ℕ) : Letter := (4 * k, true)

/-- The label of the rest of the real axis. -/
def zL : Letter := (3, true)

/-- The label of the upper half of the circle `k`. -/
def holeA (a k : ℕ) : Letter :=
  if k < 2 * a ∧ k % 2 = 1 then (4 * (k - 1) + 2, true) else (4 * k + 1, true)

/-- The label of the lower half of the circle `k`. -/
def holeB (a b k : ℕ) : Letter :=
  if k < 2 * a then
    if k % 2 = 0 then (4 * k + 2, true) else (4 * (k - 1) + 1, true)
  else if k < 2 * a + b then (4 * k + 1, false) else (4 * k + 2, true)

/-- The upper side up to the circle `k`. -/
def pw (a : ℕ) : ℕ → List Letter
  | 0 => []
  | k + 1 => pw a k ++ [segL k, holeA a k]

/-- The lower side up to the circle `k`. -/
def qw (a b : ℕ) : ℕ → List Letter
  | 0 => []
  | k + 1 => qw a b k ++ [segL k, holeB a b k]

/-- The two words of the model surface with `n` circles. -/
def modelW (a b n : ℕ) : ℕ → List Letter :=
  dW (pw a n ++ [segL n, zL]) (qw a b n ++ [segL n, zL])

/-- The inner part of the glued word. -/
def fw (a b k : ℕ) : List Letter := winv (qw a b k) ++ pw a k

theorem fw_succ (a b k : ℕ) :
    fw a b (k + 1) = linv (holeB a b k) :: linv (segL k) :: fw a b k ++ [segL k, holeA a k] := by
  simp [fw, pw, qw, winv]

theorem pw_lt (a k : ℕ) : ∀ l ∈ pw a k, l.1 < 4 * k := by
  induction k with
  | zero => simp [pw]
  | succ k ih =>
    intro l hl
    simp only [pw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | rfl | rfl
    · have := ih l hl
      omega
    · simp [segL]
    · simp only [holeA]
      split_ifs <;> simp <;> omega

theorem qw_lt (a b k : ℕ) : ∀ l ∈ qw a b k, l.1 < 4 * k := by
  induction k with
  | zero => simp [qw]
  | succ k ih =>
    intro l hl
    simp only [qw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | rfl | rfl
    · have := ih l hl
      omega
    · simp [segL]
    · simp only [holeB]
      split_ifs <;> simp <;> omega

theorem fw_lt (a b k : ℕ) : ∀ l ∈ fw a b k, l.1 < 4 * k := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · simp only [winv, List.mem_map, List.mem_reverse] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    exact qw_lt a b k m hm
  · exact pw_lt a k l hl

/-- The labels of `H` are not smaller than `4 * k`. -/
def LabGe (H : List Letter) (k : ℕ) : Prop := ∀ l ∈ H, 4 * k ≤ l.1

theorem noLab_of_lt {w : List Letter} {c n : ℕ} (h : ∀ l ∈ w, l.1 < n) (hc : n ≤ c) : NoLab w c :=
  fun l hl he => by
    have := h l hl
    omega

theorem noLab_of_ge {H : List Letter} {k c : ℕ} (h : LabGe H k) (hc : c < 4 * k) : NoLab H c :=
  fun l hl he => by
    have := h l hl
    omega

theorem disjL_of_ge {H F : List Letter} {k : ℕ} (h : LabGe H k) (hF : ∀ l ∈ F, l.1 < 4 * k) : DisjL
  H F :=
  fun l hl => noLab_of_lt hF (h l hl)

/-- Peeling a free hole. -/
theorem peel_free {F H : List Letter} {s p q : Letter} (hH : Blocks H) (hd : DisjL H F)
    (_h1 : NoLab F s.1) (h2 : NoLab F p.1) (h3 : NoLab F q.1) (h4 : NoLab H s.1) (h5 : NoLab H p.1)
    (h6 : NoLab H q.1) (h7 : s.1 ≠ p.1) (h8 : s.1 ≠ q.1) (h9 : p.1 ≠ q.1) :
    WEq.{uu} (linv q :: linv s :: F ++ s :: p :: H) (F ++ holB s p ++ H) := by
  have hsp : p.1 ≠ s.1 := fun e => h7 e.symm
  have hsq : q.1 ≠ s.1 := fun e => h8 e.symm
  have hqp : q.1 ≠ p.1 := fun e => h9 e.symm
  have dA : DisjL H [linv q, linv s] := fun l hl => by
    exact noLab_cons.mpr ⟨fun e => h6 l hl e.symm, noLab_cons.mpr ⟨fun e => h4 l hl e.symm,
      noLab_nil⟩⟩
  have dB : DisjL H (F ++ [s, p]) := DisjL.append_right hd fun l hl =>
    noLab_cons.mpr ⟨fun e => h4 l hl e.symm, noLab_cons.mpr ⟨fun e => h5 l hl e.symm, noLab_nil⟩⟩
  have c1 := slide.{uu} hH dA dB
  have c2 : WEq.{uu} ((F ++ [s]) ++ p :: [linv q] ++ (linv s :: H)) ((F ++ [s]) ++ p ::
    (linv s :: H)) := by
    have hc : ∀ c, cnt ((F ++ [s]) ++ p :: [linv q] ++ (linv s :: H)) c = cnt F c + cnt H c +
        2 * (if s.1 = c then 1 else 0) + (if p.1 = c then 1 else 0) + (if q.1 = c then 1 else 0)
          := by
      intro c
      simp only [cnt_append, cnt_cons, linv, show cnt [] c = 0 from rfl]
      omega
    refine merge_all [linv q] fun l hl => ?_
    rw [hc]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | hl
    · rw [hl, noLab_iff_cnt.mp h2, noLab_iff_cnt.mp h5, ite_eq_right h7, ite_eq_right hqp,
      ite_eq_left rfl]
    · have e : l.1 = q.1 := by rw [hl]; rfl
      rw [e, noLab_iff_cnt.mp h3, noLab_iff_cnt.mp h6, ite_eq_right h8, ite_eq_right h9,
        ite_eq_left rfl]
  refine (WEq.of_eq (by simp)).trans (c1.trans ((WEq.of_eq (by simp)).trans (c2.trans
    (WEq.of_eq ?_))))
  simp [holB]

/-- Peeling a cross-cap. -/
theorem peel_cap {F H : List Letter} {s y : Letter} (hH : Blocks H) (hd : DisjL H F)
    (h1 : NoLab F s.1) (h2 : NoLab F y.1) (h4 : NoLab H s.1) (h5 : NoLab H y.1) (h7 : s.1 ≠ y.1) :
    WEq.{uu} (y :: linv s :: F ++ s :: y :: H) (F ++ [y, y] ++ H) := by
  have dY : DisjL H [y] := fun l hl => noLab_cons.mpr ⟨fun e => h5 l hl e.symm, noLab_nil⟩
  have dS : DisjL H [linv s] := fun l hl => noLab_cons.mpr ⟨fun e => h4 l hl e.symm, noLab_nil⟩
  have dS' : DisjL H [s] := fun l hl => noLab_cons.mpr ⟨fun e => h4 l hl e.symm, noLab_nil⟩
  have c1 := slide.{uu} (A := [y]) (B := linv s :: F ++ [s, y]) hH dY
    (DisjL.append_right (DisjL.append_right dS hd) (DisjL.append_right dS' dY))
  have hH2 : Blocks ([y, y] ++ H) := .cons (.cap y) (fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
    subst hl
    exact h5) hH
  have dd : ∀ {w : List Letter}, DisjL H w → NoLab w y.1 → DisjL ([y, y] ++ H) w := fun a1 a2 => by
    refine DisjL.append_left (fun l hl => ?_) a1
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
    subst hl
    exact a2
  have hyn : NoLab [linv s] y.1 := noLab_cons.mpr ⟨h7, noLab_nil⟩
  have c2 := slide.{uu} (A := [linv s]) (B := F ++ [s]) hH2 (dd dS hyn)
    (dd (DisjL.append_right hd dS') (noLab_append.mpr ⟨h2, noLab_cons.mpr ⟨h7, noLab_nil⟩⟩))
  have c3 := (WEq.fold.{uu} s (u := [y, y] ++ H ++ F) (by simp)
    (noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_cons.mpr ⟨fun e => h7 e.symm, noLab_cons.mpr
      ⟨fun e => h7 e.symm, noLab_nil⟩⟩, h4⟩, h1⟩)).symm
  have c4 : WEq.{uu} (F ++ [s] ++ [linv s] ++ ([y, y] ++ H)) (s :: linv s :: ([y, y] ++ H ++ F)) :=
    WEq.rot' F ([s, linv s] ++ [y, y] ++ H) (by simp) (by simp)
  have c5 : WEq.{uu} ([y, y] ++ H ++ F) (F ++ [y, y] ++ H) := WEq.rot' ([y, y] ++ H) F rfl (by simp)
  exact (WEq.of_eq (by simp)).trans (c1.trans ((WEq.of_eq (by simp)).trans (c2.trans (c4.trans
    (c3.trans c5)))))

/-- Peeling a handle. -/
theorem peel_hnd {F H : List Letter} {p q s t : Letter} (hH : Blocks H) (hd : DisjL H F)
    (hc : ∀ l ∈ [p, q, s, t], NoLab F l.1 ∧ NoLab H l.1) (h1 : p.1 ≠ q.1) (h2 : p.1 ≠ s.1)
      (h3 : p.1 ≠ t.1)
    (h4 : q.1 ≠ s.1) (h5 : q.1 ≠ t.1) (h6 : s.1 ≠ t.1) :
    WEq.{uu} (linv p :: linv s :: linv q :: linv t :: F ++ t :: p :: s :: q :: H)
      (F ++ hndB (linv t) s ++ H) := by
  have hpa := hc p (by simp)
  have hqa := hc q (by simp)
  have hsa := hc s (by simp)
  have hta := hc t (by simp)
  set C := F ++ H with hC
  have hp : NoLab C p.1 := noLab_append.mpr hpa
  have hq : NoLab C q.1 := noLab_append.mpr hqa
  have hs : NoLab C s.1 := noLab_append.mpr hsa
  have ht : NoLab C t.1 := noLab_append.mpr hta
  have n : ∀ {x y : Letter}, x.1 ≠ y.1 → ∀ {w : List Letter}, NoLab w y.1 → NoLab (x :: w) y.1 :=
    fun h _ a => noLab_cons.mpr ⟨h, a⟩
  have n' : ∀ {x y : Letter}, x.1 ≠ y.1 → ∀ {w : List Letter}, NoLab w y.1 → NoLab
    (linv x :: w) y.1 :=
    fun h _ a => noLab_cons.mpr ⟨h, a⟩
  have s1 := Ne.symm h1
  have s2 := Ne.symm h2
  have s3 := Ne.symm h3
  have s6 := Ne.symm h6
  have dg : ∀ {w : List Letter} {x : Letter}, DisjL H w → NoLab H x.1 → DisjL H (linv x :: w)
    := fun a1 a2 l hl =>
    noLab_cons.mpr ⟨fun e => a2 l hl e.symm, a1 l hl⟩
  have da : ∀ {w : List Letter} {x : Letter}, DisjL H w → NoLab H x.1 → DisjL H (x :: w)
    := fun a1 a2 l hl =>
    noLab_cons.mpr ⟨fun e => a2 l hl e.symm, a1 l hl⟩
  have dn : DisjL H [] := fun _ _ => noLab_nil
  have d1 : DisjL H [linv p, linv s, linv q, linv t] :=
    dg (dg (dg (dg dn hta.2) hqa.2) hsa.2) hpa.2
  have d2 : DisjL H (t :: p :: s :: q :: []) :=
    da (da (da (da dn hqa.2) hsa.2) hpa.2) hta.2
  have c0 := slide.{uu} (A := [linv p, linv s, linv q, linv t] ++ F) (B
    := t :: p :: s :: q :: []) hH
    (DisjL.append_right d1 hd) d2
  have c1 : WEq.{uu} ((t :: p :: s :: q :: []) ++ ([linv p, linv s, linv q, linv t] ++ F) ++ H)
      ((C ++ [t]) ++ p :: (s :: q :: linv p :: linv s :: linv q :: [linv t])) :=
    WEq.rot' ((t :: p :: s :: q :: []) ++ [linv p, linv s, linv q, linv t]) C (by simp [hC])
      (by simp)
  have c2 : WEq.{uu} ((C ++ [t]) ++ p :: (s :: q :: linv p :: linv s :: linv q :: [linv t]))
      (p :: ((C ++ [t]) ++ [linv s, linv q, linv t] ++ linv p :: [s, q])) :=
    ruleA' p (C ++ [t]) [] [s, q] [linv s, linv q, linv t]
      (noLab_append.mpr ⟨hp, n s3 noLab_nil⟩) noLab_nil (n s2 (n s1 noLab_nil))
      (n' s2 (n' s1 (n' s3 noLab_nil))) (by simp) (by simp)
  have c3 : WEq.{uu} (p :: ((C ++ [t]) ++ [linv s, linv q, linv t] ++ linv p :: [s, q]))
      ((C ++ [t]) ++ linv s :: ([linv q, linv t] ++ [linv p] ++ s :: [q, p])) :=
    WEq.rot' [p] ((C ++ [t]) ++ linv s :: ([linv q, linv t] ++ [linv p] ++ s :: [q])) (by simp)
      (by simp)
  have c4 : WEq.{uu} ((C ++ [t]) ++ linv s :: ([linv q, linv t] ++ [linv p] ++ s :: [q, p]))
      ([linv q, linv t] ++ linv s :: ((C ++ [t]) ++ [q, p] ++ s :: [linv p])) :=
    ruleA' (linv s) (C ++ [t]) [linv q, linv t] [linv p] [q, p]
      (noLab_append.mpr ⟨hs, n s6 noLab_nil⟩) (n' h4 (n' s6 noLab_nil)) (n' s2.symm noLab_nil)
        (n h4 (n s2.symm noLab_nil))
      (by simp [linv_linv]) (by simp [linv_linv])
  have c5 : WEq.{uu} ([linv q, linv t] ++ linv s :: ((C ++ [t]) ++ [q, p] ++ s :: [linv p]))
      ((linv s :: C) ++ t :: ([q, p] ++ [s, linv p, linv q] ++ linv t :: [])) :=
    WEq.rot' [linv q, linv t] (linv s :: ((C ++ [t]) ++ [q, p] ++ s :: [linv p])) rfl (by simp)
  have c6 : WEq.{uu} ((linv s :: C) ++ t :: ([q, p] ++ [s, linv p, linv q] ++ linv t :: []))
      ([q, p] ++ t :: ((linv s :: C) ++ [] ++ linv t :: [s, linv p, linv q])) :=
    ruleA' t (linv s :: C) [q, p] [s, linv p, linv q] [] (n' h6 ht) (n h5 (n h3 noLab_nil))
      (n h6 (n' h3 (n' h5 noLab_nil))) noLab_nil (by simp) (by simp)
  set D := t :: linv s :: (C ++ [linv t, s]) with hD
  have c7 : WEq.{uu} ([q, p] ++ t :: ((linv s :: C) ++ [] ++ linv t :: [s, linv p, linv q]))
      (linv q :: q :: p :: (D ++ [linv p])) :=
    WEq.rot' ([q, p] ++ D ++ [linv p]) [linv q] (by simp [hD]) (by simp)
  have hnD : ∀ {x : Letter}, x.1 ≠ t.1 → x.1 ≠ s.1 → NoLab C x.1 → NoLab D x.1 := fun a1 a2 a3 =>
    noLab_cons.mpr ⟨Ne.symm a1, noLab_cons.mpr ⟨Ne.symm a2, noLab_append.mpr ⟨a3, noLab_cons.mpr
      ⟨Ne.symm a1,
      noLab_cons.mpr ⟨Ne.symm a2, noLab_nil⟩⟩⟩⟩⟩
  have c8 : WEq.{uu} (linv q :: q :: p :: (D ++ [linv p])) (p :: (D ++ [linv p])) := by
    have := WEq.fold.{uu} (linv q) (u := p :: (D ++ [linv p])) (by simp)
      (noLab_cons.mpr ⟨h1, noLab_append.mpr ⟨hnD h5 h4 hq, noLab_cons.mpr ⟨h1, noLab_nil⟩⟩⟩)
    simpa [linv_linv] using this.symm
  have c9 : WEq.{uu} (p :: (D ++ [linv p])) (linv p :: p :: D) :=
    WEq.rot' (p :: D) [linv p] (by simp) (by simp)
  have c10 : WEq.{uu} (linv p :: p :: D) D := by
    have := WEq.fold.{uu} (linv p) (u := D) (by simp [hD]) (hnD h3 h2 hp)
    simpa [linv_linv] using this.symm
  have c11 : WEq.{uu} D (hndB (linv t) s ++ F ++ H) :=
    WEq.rot' (t :: linv s :: C) [linv t, s] (by simp [hD]) (by simp [hC, hndB, linv_linv])
  have hdU : DisjL H (hndB (linv t) s) := dg (da (dg (dg dn hsa.2) (x := linv t) hta.2) hsa.2) hta.2
  have c12 := slide.{uu} hH hdU hd
  exact (WEq.of_eq (by simp)).trans (c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans
    (c6.trans
    (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans c12))))))))))))

theorem fw_cast_lt {a b k n : ℕ} (h : k ≤ n) : ∀ l ∈ fw a b k, l.1 < 4 * n := fun l hl => by
  have := fw_lt a b k l hl
  omega

theorem cross_label {F H : List Letter} {k c : ℕ} (hF : ∀ l ∈ F, l.1 < 4 * k) (hH : LabGe H (k + 1))
    (h1 : 4 * k ≤ c) (h2 : c < 4 * (k + 1)) : NoLab F c ∧ NoLab H c :=
  ⟨noLab_of_lt hF h1, noLab_of_ge hH h2⟩

/-- Peel all free holes. -/
theorem peel_c (a b : ℕ) (c : ℕ) : ∀ (Z : List Letter) (c₀ : ℕ), TL c₀ Z → LabGe Z (2 * a + b + c) →
    ∃ Z', TL (c₀ + c) Z' ∧ LabGe Z' (2 * a + b) ∧ WEq.{uu} (fw a b (2 * a + b + c) ++ Z) (fw a b
      (2 * a + b) ++ Z') := by
  induction c with
  | zero => exact fun Z c₀ h1 h2 => ⟨Z, h1, h2, WEq.refl _⟩
  | succ c ih =>
    intro Z c₀ hT hL
    set k := 2 * a + b + c with hk
    have hF := fw_lt a b k
    have hL' : LabGe Z (k + 1) := hL
    have hA : holeA a k = (4 * k + 1, true) := by
      simp only [holeA]
      rw [ite_eq_right (by omega)]
    have hB : holeB a b k = (4 * k + 2, true) := by
      simp only [holeB]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have l1 := cross_label (c := 4 * k) hF hL' (by omega) (by omega)
    have l2 := cross_label (c := 4 * k + 1) hF hL' (by omega) (by omega)
    have l3 := cross_label (c := 4 * k + 2) hF hL' (by omega) (by omega)
    have e : fw a b (k + 1) = linv (4 * k + 2, true) :: linv (segL k) :: fw a b k ++ segL k ::
      (4 * k + 1, true) :: [] := by
      rw [fw_succ, hA, hB]
    have p1 := peel_free.{uu} (s := segL k) (p := (4 * k + 1, true)) (q :=
      (4 * k + 2, true)) hT.blocks
      (disjL_of_ge hL' (fw_cast_lt (by omega))) l1.1 l2.1 l3.1 l1.2 l2.2 l3.2
      (by simp [segL]) (by simp [segL]) (by simp)
    have hU : DisjL (holB (segL k) (4 * k + 1, true)) Z := fun l hl => by
      simp only [holB, linv, segL, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact l1.2
      · exact l2.2
      · exact l1.2
    have hT' : TL (c₀ + 1) (holB (segL k) (4 * k + 1, true) ++ Z) := .cons _ _
      (by simp [segL]) hU hT
    have hL'' : LabGe (holB (segL k) (4 * k + 1, true) ++ Z) k := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · simp only [holB, linv, segL, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> simp
      · have := hL' l hl
        omega
    obtain ⟨Z', a1, a2, a3⟩ := ih _ (c₀ + 1) hT' hL''
    refine ⟨Z', by rwa [show c₀ + (c + 1) = c₀ + 1 + c by omega], a2, ?_⟩
    have e2 : 2 * a + b + (c + 1) = k + 1 := by omega
    rw [e2, e]
    refine (WEq.of_eq (by simp)).trans (p1.trans ((WEq.of_eq (by simp)).trans a3))

theorem LabGe.mono {H : List Letter} {k k' : ℕ} (h : LabGe H k) (hk : k' ≤ k) : LabGe H k'
  := fun l hl => by
  have := h l hl
  omega

/-- Peel all cross-caps. -/
theorem peel_b (a b : ℕ) (b' : ℕ) : b' ≤ b → ∀ (Y Z : List Letter) (b₀ : ℕ), CL b₀ Y → Blocks Z
  → DisjL Y Z →
    LabGe Y (2 * a + b') → LabGe Z (2 * a + b') →
    ∃ Y', CL (b₀ + b') Y' ∧ DisjL Y' Z ∧ LabGe Y' (2 * a) ∧
      WEq.{uu} (fw a b (2 * a + b') ++ Y ++ Z) (fw a b (2 * a) ++ Y' ++ Z) := by
  induction b' with
  | zero => exact fun _ Y Z b₀ h1 _ h3 h4 _ => ⟨Y, h1, h3, h4, WEq.refl _⟩
  | succ b' ih =>
    intro hb Y Z b₀ hC hZ hd hY hZl
    set k := 2 * a + b' with hk
    have hF := fw_lt a b k
    have hY' : LabGe Y (k + 1) := hY
    have hZ' : LabGe Z (k + 1) := hZl
    have hH : LabGe (Y ++ Z) (k + 1) := fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hY' l hl
      · exact hZ' l hl
    have hA : holeA a k = (4 * k + 1, true) := by
      simp only [holeA]
      rw [ite_eq_right (by omega)]
    have hB : holeB a b k = linv (4 * k + 1, true) := by
      simp only [holeB]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl
    have l1 := cross_label (c := 4 * k) hF hH (by omega) (by omega)
    have l2 := cross_label (c := 4 * k + 1) hF hH (by omega) (by omega)
    have e : fw a b (k + 1) = (4 * k + 1, true) :: linv (segL k) :: fw a b k ++ segL k ::
      (4 * k + 1, true) :: [] := by
      rw [fw_succ, hA, hB, linv_linv]
    have hBl : Blocks (Y ++ Z) := hC.blocks.append hZ hd
    have p1 := peel_cap.{uu} (s := segL k) (y := (4 * k + 1, true)) hBl
      (disjL_of_ge hH (fw_cast_lt (by omega))) l1.1 l2.1 l1.2 l2.2 (by simp [segL])
    have l3 := noLab_append.mp l2.2
    have hU : DisjL [((4 * k + 1, true) : Letter), (4 * k + 1, true)] Y := fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
      subst hl
      exact l3.1
    have hC' : CL (b₀ + 1) ([(4 * k + 1, true), (4 * k + 1, true)] ++ Y) := .cons _ hU hC
    have hd' : DisjL ([(4 * k + 1, true), (4 * k + 1, true)] ++ Y) Z := by
      refine DisjL.append_left (fun l hl => ?_) hd
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
      subst hl
      exact l3.2
    have hL : LabGe ([(4 * k + 1, true), (4 * k + 1, true)] ++ Y) k := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
        subst hl
        simp
      · have := hY' l hl
        omega
    obtain ⟨Y', a1, a2, a3, a4⟩ := ih (by omega) _ Z (b₀ + 1) hC' hZ hd' hL (hZ'.mono (by omega))
    refine ⟨Y', by rwa [show b₀ + (b' + 1) = b₀ + 1 + b' by omega], a2, a3, ?_⟩
    have e2 : 2 * a + (b' + 1) = k + 1 := by omega
    rw [e2, e]
    refine (WEq.of_eq (by simp)).trans (p1.trans ((WEq.of_eq (by simp)).trans a4))

/-- Peel all handles. -/
theorem peel_a (a b : ℕ) (a' : ℕ) : a' ≤ a → ∀ (X T : List Letter) (a₀ : ℕ), HL a₀ X → Blocks T
  → DisjL X T →
    LabGe X (2 * a') → LabGe T (2 * a') →
    ∃ X', HL (a₀ + a') X' ∧ DisjL X' T ∧ WEq.{uu} (fw a b (2 * a') ++ X ++ T) (X' ++ T) := by
  induction a' with
  | zero => exact fun _ X T a₀ h1 _ h3 _ _ => ⟨X, h1, h3, WEq.of_eq (by simp [fw, pw, qw, winv])⟩
  | succ a' ih =>
    intro hb X T a₀ hH hT hd hX hTl
    set k := 2 * a' with hk
    have hF := fw_lt a b k
    have e2 : 2 * (a' + 1) = k + 2 := by omega
    rw [e2] at hX hTl ⊢
    have hH2 : LabGe (X ++ T) (k + 2) := fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hX l hl
      · exact hTl l hl
    have hA : holeA a k = (4 * k + 1, true) := by
      simp only [holeA]
      rw [ite_eq_right (by omega)]
    have hB : holeB a b k = (4 * k + 2, true) := by
      simp only [holeB]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    have hA' : holeA a (k + 1) = (4 * k + 2, true) := by
      simp only [holeA]
      rw [ite_eq_left (by omega)]
      simp
    have hB' : holeB a b (k + 1) = (4 * k + 1, true) := by
      simp only [holeB]
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      simp
    have e : fw a b (k + 2) = linv (4 * k + 1, true) :: linv (segL (k + 1)) :: linv
      (4 * k + 2, true) ::
        linv (segL k) :: fw a b k ++ segL k :: (4 * k + 1, true) :: segL (k + 1) ::
          (4 * k + 2, true) :: [] := by
      rw [fw_succ, fw_succ, hA, hB, hA', hB']
      simp
    have hc : ∀ l ∈ [((4 * k + 1, true) : Letter), (4 * k + 2, true), segL (k + 1), segL k],
        NoLab (fw a b k) l.1 ∧ NoLab (X ++ T) l.1 := by
      intro l hl
      have hl' : 4 * k ≤ l.1 ∧ l.1 < 4 * (k + 2) := by
        simp only [segL, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> simp <;> omega
      exact ⟨noLab_of_lt hF hl'.1, noLab_of_ge hH2 hl'.2⟩
    have hBl : Blocks (X ++ T) := hH.blocks.append hT hd
    have p1 := peel_hnd.{uu} (s := segL (k + 1)) (t := segL k) (p := (4 * k + 1, true)) (q :=
      (4 * k + 2, true))
      hBl (disjL_of_ge (hH2.mono (by omega)) hF) hc (by simp) (by simp [segL]; omega)
        (by simp [segL])
      (by simp [segL]; omega) (by simp [segL]) (by simp [segL])
    have hs1 := noLab_append.mp (hc (segL (k + 1)) (by simp)).2
    have hs2 := noLab_append.mp (hc (segL k) (by simp)).2
    have hU : ∀ {w : List Letter}, NoLab w (segL k).1 → NoLab w (segL (k + 1)).1 →
        DisjL (hndB (linv (segL k)) (segL (k + 1))) w := fun a1 a2 l hl => by
      simp only [hndB, List.mem_cons, List.not_mem_nil, or_false, linv_linv] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact a1
      · exact a2
      · exact a1
      · exact a2
    have hH' : HL (a₀ + 1) (hndB (linv (segL k)) (segL (k + 1)) ++ X) :=
      .cons _ _ (by simp [segL, linv]) (hU hs2.1 hs1.1) hH
    have hd' : DisjL (hndB (linv (segL k)) (segL (k + 1)) ++ X) T :=
      DisjL.append_left (hU hs2.2 hs1.2) hd
    have hL : LabGe (hndB (linv (segL k)) (segL (k + 1)) ++ X) k := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · simp only [hndB, List.mem_cons, List.not_mem_nil, or_false, segL, linv] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> simp
      · have := hX l hl
        omega
    obtain ⟨X', a1, a2, a3⟩ := ih (by omega) _ T (a₀ + 1) hH' hT hd' hL (hTl.mono (by omega))
    refine ⟨X', by rwa [show a₀ + (a' + 1) = a₀ + 1 + a' by omega], a2, ?_⟩
    rw [e]
    refine (WEq.of_eq (by simp)).trans (p1.trans ((WEq.of_eq (by simp)).trans a3))

/-- The inner word is equivalent to a normal form. -/
theorem fw_nf (a b c : ℕ) : ∃ w, IsNF w a b c ∧ WEq.{uu} (fw a b (2 * a + b + c)) w := by
  obtain ⟨Z, h1, h2, h3⟩ := peel_c.{uu} a b c [] 0 .nil (by simp [LabGe])
  obtain ⟨Y, h4, h5, h6, h7⟩ := peel_b.{uu} a b b le_rfl [] Z 0 .nil h1.blocks (by simp [DisjL])
    (by simp [LabGe]) h2
  have hZ : Blocks Z := h1.blocks
  have hY : Blocks Y := h4.blocks
  have hT : Blocks (Y ++ Z) := hY.append hZ h5
  have hL : LabGe (Y ++ Z) (2 * a) := fun l hl => by
    rcases List.mem_append.mp hl with hl | hl
    · exact h6 l hl
    · exact h2.mono (by omega) l hl
  obtain ⟨X, h8, h9, h10⟩ := peel_a.{uu} a b a le_rfl [] (Y ++ Z) 0 .nil hT (by simp [DisjL])
    (by simp [LabGe]) hL
  refine ⟨X ++ Y ++ Z, ⟨X, Y, Z, rfl, by simpa using h8, by simpa using h4, by simpa using h1,
    h9.inl, h9.inr, h5⟩, ?_⟩
  simp only [zero_add] at h4 h8
  refine (WEq.of_eq (by simp)).trans (h3.trans ((WEq.of_eq (by simp)).trans (h7.trans ?_)))
  refine (WEq.of_eq (by simp)).trans (h10.trans (WEq.of_eq (by simp)))

theorem labels_mod (a b k : ℕ) : (∀ l ∈ pw a k, l.1 % 4 ≠ 3) ∧ ∀ l ∈ qw a b k, l.1 % 4 ≠ 3 := by
  induction k with
  | zero => simp [pw, qw]
  | succ k ih =>
    constructor
    · intro l hl
      simp only [pw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl | rfl
      · exact ih.1 l hl
      · simp [segL]
      · simp only [holeA]
        split_ifs <;> simp
    · intro l hl
      simp only [qw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl | rfl
      · exact ih.2 l hl
      · simp [segL]
      · simp only [holeB]
        split_ifs <;> simp

theorem dW_rev_right (a c : List Letter) : PEq.{uu} (dW c a) (dW c (winv a)) :=
  peq_rev (finW_sW c) 1 a

/-- Gluing the two words along the last letter. -/
theorem peq_modelW_glue (a b n : ℕ) :
    PEq.{uu} (modelW a b n) (sW (linv (segL n) :: fw a b n ++ [segL n])) := by
  have h1 := dW_rot_left.{uu} (pw a n ++ [segL n]) [zL] (qw a b n ++ [segL n, zL])
  have h2 := dW_rev_right.{uu} (qw a b n ++ [segL n, zL]) ([zL] ++ (pw a n ++ [segL n]))
  have hm := labels_mod a b n
  have hn : NoLab ((linv (segL n) :: winv (qw a b n)) ++ (pw a n ++ [segL n])) zL.1 := by
    refine noLab_append.mpr ⟨noLab_cons.mpr ⟨?_, noLab_winv.mpr ?_⟩, noLab_append.mpr ⟨?_,
      noLab_cons.mpr ⟨?_, noLab_nil⟩⟩⟩
    · simp [segL, linv, zL]
      omega
    · exact fun l hl he => hm.2 l hl (by rw [he]; rfl)
    · exact fun l hl he => hm.1 l hl (by rw [he]; rfl)
    · simp [segL, zL]
      omega
  have h3 := peq_cut_sW.{uu} (y := zL.1) (u := pw a n ++ [segL n]) (v := linv (segL n) :: winv
    (qw a b n)) true
    (by simp) (by simp) hn
  have e1 : pw a n ++ [segL n, zL] = (pw a n ++ [segL n]) ++ [zL] := by simp
  have e2 : winv (qw a b n ++ [segL n, zL]) = (zL.1, !true) :: (linv (segL n) :: winv (qw a b n))
    := by
    simp [winv, zL, linv]
  have h4 : PEq.{uu} (modelW a b n) (dW ([zL] ++ (pw a n ++ [segL n])) (qw a b n ++ [segL n, zL]))
    := by
    simp only [modelW]
    rw [e1]
    exact h1
  rw [e2] at h2
  have e3 : (linv (segL n) :: winv (qw a b n)) ++ (pw a n ++ [segL n]) =
      linv (segL n) :: fw a b n ++ [segL n] := by
    simp [fw]
  rw [e3] at h3
  exact h4.trans (h2.trans h3.symm)

/-- **The model words are normal forms.** -/
theorem exists_modelW_nf (a b c : ℕ) :
    ∃ w, PEq.{uu} (modelW a b (2 * a + b + c)) (sW w) ∧
      ((IsNF w a b c ∧ 2 * a + b + c ≠ 0) ∨ (2 * a + b + c = 0 ∧ w = [linv (segL 0), segL 0])) := by
  by_cases hn : 2 * a + b + c = 0
  · refine ⟨_, peq_modelW_glue a b _, .inr ⟨hn, ?_⟩⟩
    rw [hn]
    simp [fw, pw, qw, winv]
  · obtain ⟨w, h1, h2⟩ := fw_nf.{uu} a b c
    set n := 2 * a + b + c with hN
    have hne : fw a b n ≠ [] := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hm, Nat.succ_eq_add_one, fw_succ]
      simp
    have h3 : WEq.{uu} (linv (segL n) :: fw a b n ++ [segL n]) (segL n :: linv
      (segL n) :: fw a b n) :=
      WEq.rot' (linv (segL n) :: fw a b n) [segL n] rfl (by simp)
    have h4 := (WEq.fold.{uu} (segL n) hne (noLab_of_lt (fw_lt a b n) (by simp [segL]))).symm
    exact ⟨w, (peq_modelW_glue a b n).trans (h3.trans (h4.trans h2)), .inl ⟨h1, hn⟩⟩

end GraphMinor.Surface
