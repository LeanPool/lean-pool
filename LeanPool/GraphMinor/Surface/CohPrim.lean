/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordCover
public import LeanPool.GraphMinor.Surface.NormalVolt

/-!
# Primitives on the polygon of the normal word

Let `Y` be presented by the word `ew a b c`, and let `g` be a primitive on the polygon of a local
cocycle. On a pair of
pasted sides the difference of `g` is constant (`side_const`). So the change of `g` along a side is
a function of its
label (`volt_eq`), and the values of `g` at the corners are the sums of `Sm` (`g_cor`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

/-- The corner `j` of the polygon. -/
noncomputable def cor (a b c j : ℕ) : ℂ := per (4 * a + 2 * b + 3 * c + 2) j

/-- The map from the polygon of a word. -/
def pmap {Y : Type u} (f : ℕ × ℂ → Y) (z : ℂ) : Y := f (0, z)

theorem norm_per_sub {n : ℕ} (hn : 0 < n) (x y : ℝ) : ‖per n x - per n y‖ ≤ 8 * |x - y| := by
  have h1 : per n x - per n y = per n y * (cis' (2 * Real.pi * (x - y) / n) - 1) := by
    rw [mul_sub, ← per_add]
    simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [h1, norm_mul, norm_per, one_mul]
  have h2 : ‖cis' (2 * Real.pi * (x - y) / n) - 1‖ ≤ ‖2 * Real.pi * (x - y) / n‖ := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y) / n)
    simpa [cis', mul_comm] using this
  refine h2.trans ?_
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, Nat.abs_cast, abs_of_pos (by positivity :
    (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos, div_le_iff₀ hn0]
  have h3 := Real.pi_lt_four
  have h4 := abs_nonneg (x - y)
  nlinarith

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y} {A : Type} [AddCommGroup A]

theorem spt_ew (p : ℕ) (u : ℝ) : spt (sW (ew a b c)) 0 p u = (0, per (4 * a + 2 * b + 3 * c + 2)
  (p + u)) := by
  simp [spt, sW_zero, ew_length]

theorem mem_ball_per (n : ℕ) (x : ℝ) : per n x ∈ closedBall (0 : ℂ) 1 := by simp [norm_per]

theorem per_st (a b c p : ℕ) : per (4 * a + 2 * b + 3 * c + 2) (p + ofs (sgn a b c p) 0)
  = cor a b c (st a b c p) := by
  unfold cor st
  cases sgn a b c p <;> simp [ofs]

theorem per_en (a b c p : ℕ) : per (4 * a + 2 * b + 3 * c + 2) (p + ofs (sgn a b c p) 1)
  = cor a b c (en a b c p) := by
  unfold cor en
  cases sgn a b c p <;> simp [ofs]

theorem flp_ofs (e e' : Bool) (t : ℝ) : flp e e' (ofs e t) = ofs e' t := by
  cases e <;> cases e' <;> simp [flp, ofs]

theorem ofs_mem' {e : Bool} {t : ℝ} (ht : t = 0 ∨ t = 1) : ofs e t ∈ Icc (0 : ℝ) 1 :=
  ofs_mem (by rcases ht with rfl | rfl <;> simp)

/-- A step between two sides with the same label. -/
theorem stp_pair {p q : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 * c +
  2) (hne : p ≠ q)
    (hl : lab a b c p = lab a b c q) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Stp (sW (ew a b c)) (0, per (4 * a + 2 * b + 3 * c + 2) (p + u))
      (0, per (4 * a + 2 * b + 3 * c + 2) (q + flp (sgn a b c p) (sgn a b c q) u)) := by
  rw [← spt_ew, ← spt_ew]
  refine stp_iff.mpr ⟨0, 0, p, q, lab a b c p, _, _, u, ?_, ?_, fun h => hne (Prod.mk.inj h).2,
    hu, rfl, rfl⟩
  · rw [sW_zero]
    exact ew_get a b c hp
  · rw [sW_zero, hl]
    exact ew_get a b c hq

theorem pair_F (hf : Presents (sW (ew a b c)) f) {p q : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2)
    (hq : q < 4 * a + 2 * b + 3 * c + 2) (hne : p ≠ q) (hl : lab a b c p = lab a b c q) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    pmap f (per (4 * a + 2 * b + 3 * c + 2) (q + flp (sgn a b c p) (sgn a b c q) u)) =
      pmap f (per (4 * a + 2 * b + 3 * c + 2) (p + u)) :=
  (presents_eq_of_stp hf (stp_pair hp hq hne hl hu)).symm

theorem pair_cor (hf : Presents (sW (ew a b c)) f) {p q : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2)
    (hq : q < 4 * a + 2 * b + 3 * c + 2) (hne : p ≠ q) (hl : lab a b c p = lab a b c q) :
    pmap f (cor a b c (st a b c q)) = pmap f (cor a b c (st a b c p)) ∧
      pmap f (cor a b c (en a b c q)) = pmap f (cor a b c (en a b c p)) := by
  have h0 := pair_F hf hp hq hne hl (u := ofs (sgn a b c p) 0) (ofs_mem' (.inl rfl))
  have h1 := pair_F hf hp hq hne hl (u := ofs (sgn a b c p) 1) (ofs_mem' (.inr rfl))
  rw [flp_ofs, per_st, per_st] at h0
  rw [flp_ofs, per_en, per_en] at h1
  exact ⟨h0, h1⟩

/-- On two pasted sides the difference of a primitive is constant. -/
theorem side_const {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g) {p q : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 * c + 2) (hne : p ≠ q)
    (hl : lab a b c p = lab a b c q) : ∃ c', ∀ u ∈ Icc (0 : ℝ) 1,
      g (per (4 * a + 2 * b + 3 * c + 2) (q + flp (sgn a b c p) (sgn a b c q) u)) =
        g (per (4 * a + 2 * b + 3 * c + 2) (p + u)) + c' := by
  obtain ⟨ε, h0, h1⟩ := hg
  simp only [neg_add_eq_sub] at h1
  set n := 4 * a + 2 * b + 3 * c + 2 with hn
  have hn0 : 0 < n := by omega
  let v : ℝ → A := fun u => g (per n (q + flp (sgn a b c p) (sgn a b c q) u)) - g (per n (p + u))
  have hflp : ∀ s t : ℝ, |flp (sgn a b c p) (sgn a b c q) s - flp (sgn a b c p) (sgn a b c q) t|
    = |s - t| := by
    intro s t
    unfold flp
    split_ifs
    · rfl
    · rw [show 1 - s - (1 - t) = -(s - t) by ring, abs_neg]
  have hc := const_of_near (v := v) (ε := ε / 9) (by positivity) (fun s hs t ht hst => by
    have hlip : ∀ (m : ℕ) (x y : ℝ), |x - y| < ε / 9 → ‖per n (m + x) - per n (m + y)‖ < ε := by
      intro m x y hxy
      have h2 := norm_per_sub hn0 (m + x) (m + y)
      rw [show (m : ℝ) + x - (m + y) = x - y by ring] at h2
      linarith
    have e1 := h1 _ (mem_ball_per n (p + t)) _ (mem_ball_per n (p + s)) (hlip p t s
      (by rwa [abs_sub_comm]))
    have e2 := h1 _ (mem_ball_per n (q + flp _ _ t)) _ (mem_ball_per n (q + flp _ _ s))
      (hlip q (flp (sgn a b c p) (sgn a b c q) t) (flp (sgn a b c p) (sgn a b c q) s)
        (by rw [hflp, abs_sub_comm]; exact hst))
    rw [pair_F hf hp hq hne hl ht, pair_F hf hp hq hne hl hs, e1] at e2
    simp only [v]
    rw [sub_eq_iff_eq_add] at e2 ⊢
    rw [e2]
    abel)
  refine ⟨v 0, fun u hu => ?_⟩
  have h2 := hc u hu
  simp only [v] at h2 ⊢
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel

/-- The change of `g` along the side `p`, read along its label. -/
noncomputable def volt (a b c : ℕ) (g : ℂ → A) (p : ℕ) : A := g (cor a b c (en a b c p)) - g
  (cor a b c (st a b c p))

theorem volt_pair {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g) {p q : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 * c + 2) (hne : p ≠ q)
    (hl : lab a b c p = lab a b c q) : volt a b c g q = volt a b c g p := by
  obtain ⟨c', h⟩ := side_const hf hg hp hq hne hl
  have h0 := h _ (ofs_mem' (e := sgn a b c p) (t := 0) (.inl rfl))
  have h1 := h _ (ofs_mem' (e := sgn a b c p) (t := 1) (.inr rfl))
  rw [flp_ofs, per_st, per_st] at h0
  rw [flp_ofs, per_en, per_en] at h1
  unfold volt
  rw [h0, h1]
  abel

/-- A side with each label. -/
def rep (a b c k : ℕ) : ℕ :=
  if k < 2 * a then 4 * (k / 2) + k % 2
  else if k < 2 * a + b then 4 * a + 2 * (k - 2 * a)
  else if k < 2 * a + b + 2 * c then
    4 * a + 2 * b + 3 * ((k - (2 * a + b)) / 2) + (k - (2 * a + b)) % 2
  else 4 * a + 2 * b + 3 * c

theorem lab_rep {k : ℕ} (hk : k ≤ 2 * a + b + 2 * c) : lab a b c (rep a b c k) = k := by
  unfold rep
  by_cases h1 : k < 2 * a
  · rw [ite_eq_left h1, lab_h (by omega) (by omega)]
    omega
  rw [ite_eq_right h1]
  by_cases h2 : k < 2 * a + b
  · rw [ite_eq_left h2, ← add_zero (4 * a + 2 * (k - 2 * a)), lab_c (by omega) (by omega)]
    omega
  rw [ite_eq_right h2]
  by_cases h3 : k < 2 * a + b + 2 * c
  · rw [ite_eq_left h3, lab_t (by omega) (by omega)]
    omega
  · rw [ite_eq_right h3, ← add_zero (4 * a + 2 * b + 3 * c), lab_l]
    omega

theorem rep_lt {k : ℕ} (hk : k ≤ 2 * a + b + 2 * c) : rep a b c k < 4 * a + 2 * b + 3 * c + 2 := by
  unfold rep
  split_ifs <;> omega

theorem lab_le {p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) : lab a b c p ≤ 2 * a + b + 2 * c := by
  unfold lab
  split_ifs <;> omega

theorem lab_lt_of_lt {p : ℕ} (hp : p < 4 * a + 2 * b) : lab a b c p < 2 * a + b := by
  unfold lab
  split_ifs <;> omega

/-- The values of the labels. -/
noncomputable def lval (a b c : ℕ) (g : ℂ → A) (k : ℕ) : A := volt a b c g (rep a b c k)

theorem volt_eq {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g) {p : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) : volt a b c g p = lval a b c g (lab a b c p) := by
  have h1 := lab_le hp
  by_cases he : rep a b c (lab a b c p) = p
  · rw [lval, he]
  · exact volt_pair hf hg (rep_lt h1) hp he (lab_rep h1)

theorem cor_succ_eq {g : ℂ → A} (p : ℕ) :
    g (cor a b c (p + 1)) - g (cor a b c p) = if sgn a b c p then volt a b c g p else - volt a b c
      g p := by
  unfold volt en st
  by_cases h : sgn a b c p
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
    abel

/-- The values of a primitive at the corners are sums along the word. -/
theorem g_cor {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g) {j : ℕ}
    (hj : j ≤ 4 * a + 2 * b + 3 * c + 2) : g (cor a b c j) = g (cor a b c 0) + Sm a b c
      (lval a b c g) j := by
  induction j with
  | zero => simp [Sm]
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := cor_succ_eq (a := a) (b := b) (c := c) (g := g) j
    rw [volt_eq hf hg (by omega)] at h2
    rw [sub_eq_iff_eq_add] at h2
    rw [h2, h1, Sm_succ, lv]
    by_cases h : sgn a b c j
    · rw [ite_eq_left h]
      abel
    · rw [ite_eq_right h]
      abel

theorem cor_last (a b c : ℕ) : cor a b c (4 * a + 2 * b + 3 * c + 2) = cor a b c 0 := by
  have h := per_add_self (m := 4 * a + 2 * b + 3 * c + 2) (by omega) 0
  rw [zero_add] at h
  simpa [cor] using h

theorem Sm_prim {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g) :
    Sm a b c (lval a b c g) (4 * a + 2 * b + 3 * c + 2) = 0 := by
  have h1 := g_cor hf hg (j := 4 * a + 2 * b + 3 * c + 2) le_rfl
  rw [cor_last] at h1
  exact (add_eq_left.mp h1.symm)

/-- The ends of a side of a handle or a cross-cap are the same point. -/
theorem loop_cor (hf : Presents (sW (ew a b c)) f) {p : ℕ} (hp : p < 4 * a + 2 * b) :
    pmap f (cor a b c (p + 1)) = pmap f (cor a b c p) := by
  by_cases h4 : p < 4 * a
  · obtain ⟨i, δ, hi, hδ, rfl⟩ : ∃ i δ, i < a ∧ δ < 4 ∧ p = 4 * i + δ
    := ⟨p / 4, p % 4, by omega, by omega, by omega⟩
    have hp0 := pair_cor hf (p := 4 * i + 0) (q := 4 * i + 2) (by omega) (by omega) (by omega)
      (by rw [lab_h hi (by omega), lab_h hi (by omega)])
    have hp1 := pair_cor hf (p := 4 * i + 1) (q := 4 * i + 3) (by omega) (by omega) (by omega)
      (by rw [lab_h hi (by omega), lab_h hi (by omega)])
    have s0 : st a b c (4 * i + 0) = 4 * i + 0 := by
      simp only [st, sgn_h hi (by omega : 0 < 4)]; rfl
    have e0 : en a b c (4 * i + 0) = 4 * i + 1 := by
      simp only [en, sgn_h hi (by omega : 0 < 4)]; rfl
    have s1 : st a b c (4 * i + 1) = 4 * i + 1 := by
      simp only [st, sgn_h hi (by omega : 1 < 4)]; rfl
    have e1 : en a b c (4 * i + 1) = 4 * i + 2 := by
      simp only [en, sgn_h hi (by omega : 1 < 4)]; rfl
    have s2 : st a b c (4 * i + 2) = 4 * i + 3 := by
      simp only [st, sgn_h hi (by omega : 2 < 4)]; rfl
    have e2 : en a b c (4 * i + 2) = 4 * i + 2 := by
      simp only [en, sgn_h hi (by omega : 2 < 4)]; rfl
    have s3 : st a b c (4 * i + 3) = 4 * i + 4 := by
      simp only [st, sgn_h hi (by omega : 3 < 4)]; rfl
    have e3 : en a b c (4 * i + 3) = 4 * i + 3 := by
      simp only [en, sgn_h hi (by omega : 3 < 4)]; rfl
    rw [s0, s2, e0, e2] at hp0
    rw [s1, s3, e1, e3] at hp1
    obtain ⟨h1, h2⟩ := hp0
    obtain ⟨h3, h4'⟩ := hp1
    interval_cases δ
    · exact h2.symm.trans (h4'.symm.trans h1)
    · exact h2
    · exact h4'
    · exact h3.trans (h2.symm.trans h4'.symm)
  · obtain ⟨i, δ, hi, hδ, rfl⟩ : ∃ i δ, i < b ∧ δ < 2 ∧ p = 4 * a + 2 * i + δ :=
      ⟨(p - 4 * a) / 2, (p - 4 * a) % 2, by omega, by omega, by omega⟩
    have hp0 := pair_cor hf (p := 4 * a + 2 * i + 0) (q := 4 * a + 2 * i + 1) (by omega) (by omega)
      (by omega)
      (by rw [lab_c hi (by omega), lab_c hi (by omega)])
    have s0 : ∀ δ, δ < 2 → st a b c (4 * a + 2 * i + δ) = 4 * a + 2 * i + δ := fun δ h => by
      simp only [st, sgn_c hi h, ite_true]
    have e0 : ∀ δ, δ < 2 → en a b c (4 * a + 2 * i + δ) = 4 * a + 2 * i + δ + 1 := fun δ h => by
      simp only [en, sgn_c hi h, ite_true]
    rw [s0 0 (by omega), s0 1 (by omega), e0 0 (by omega), e0 1 (by omega)] at hp0
    interval_cases δ
    · exact hp0.1
    · exact hp0.2

/-- The ends of the free side of a hole are the same point. -/
theorem hole_cor (hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) :
    pmap f (cor a b c (4 * a + 2 * b + 3 * i + 2)) = pmap f (cor a b c (4 * a + 2 * b + 3 * i + 1))
      := by
  have h := (pair_cor hf (p := 4 * a + 2 * b + 3 * i + 0) (q := 4 * a + 2 * b + 3 * i + 2)
    (by omega) (by omega)
    (by omega) (by rw [lab_t hi (by omega), lab_t hi (by omega)])).2
  have e0 : en a b c (4 * a + 2 * b + 3 * i + 0) = 4 * a + 2 * b + 3 * i + 1 := by
    simp only [en, sgn_t hi (by omega : 0 < 3)]
    rfl
  have e2 : en a b c (4 * a + 2 * b + 3 * i + 2) = 4 * a + 2 * b + 3 * i + 2 := by
    simp only [en, sgn_t hi (by omega : 2 < 3)]
    rfl
  rw [e0, e2] at h
  exact h

end GraphMinor.Surface
