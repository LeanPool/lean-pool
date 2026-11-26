/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordSpace
public import LeanPool.GraphMinor.Surface.FanSquare

/-!
# Germs of a family of words

A germ is a point of a side of a word, with a direction along the side. A small polar rectangle in
the disc of the word
starts at a germ. Its left side runs along the radius and its lower side runs along the side of the
word. Two
rectangles at the same point share the left side. The rectangles of two germs that are pasted share
the lower side.
Off these sides and the point the rectangles do not meet (`Germ.rect_same`, `Germ.rect_stp`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

/-- A point of a side and a direction along it. -/
@[ext] structure Germ where
  /-- Index of the word containing the side. -/
  i : ℕ
  /-- Position of the side in that word. -/
  p : ℕ
  /-- Coordinate of the point on the side. -/
  u : ℝ
  /-- Direction along the side. -/
  τ : Bool

/-- The sign of a direction. -/
noncomputable def sg (τ : Bool) : ℝ := if τ then 1 else -1

@[simp] theorem sg_true : sg true = 1 := rfl
@[simp] theorem sg_false : sg false = -1 := rfl

/-- The side of a word that has no other side with its label. -/
def FreeSide (W : ℕ → List Letter) (i p : ℕ) : Prop :=
  ∀ j q k e e', (W i)[p]? = some (k, e) → (W j)[q]? = some (k, e') → (i, p) = (j, q)

theorem per_eq {n : ℕ} (hn : 0 < n) {x y : ℝ} (h : per n x = per n y) : ∃ m : ℤ, x = y + m * n := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (x : ℂ) = y + m * n := by
    have h2 : (2 * Real.pi * x / n : ℝ) * Complex.I = (2 * Real.pi * y / n : ℝ) * Complex.I +
        m * (2 * Real.pi * Complex.I) := hm
    push_cast at h2
    have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [hpi]
    have h3 : (2 * Real.pi * Complex.I : ℂ) * (x / n) = (2 * Real.pi * Complex.I) * (y / n + m)
      := by
      linear_combination h2
    have h4 := mul_left_cancel₀ hc h3
    field_simp at h4
    linear_combination h4
  exact_mod_cast h1

theorem int_eq_zero_of {n : ℕ} (hn : 0 < n) {m : ℤ} (h : |(m : ℝ) * n| < n) : m = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, Nat.abs_cast] at h
  have h1 : |(m : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : |m| < 1 := by exact_mod_cast h1
  exact Int.abs_lt_one_iff.mp h2

theorem sg_cancel {a b : ℝ} {τ τ' : Bool} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 < a ∨ 0 < b)
    (h : sg τ * a = sg τ' * b) : τ = τ' ∧ a = b := by
  cases τ <;> cases τ' <;> simp only [sg_false, sg_true] at h <;>
    first
    | exact ⟨rfl, by linarith⟩
    | (exfalso; rcases hp with h9 | h9 <;> linarith)

theorem abs_sub_le_of_sg {u u' a b h : ℝ} {τ τ' : Bool} (ha : 0 ≤ a) (ha' : a ≤ h) (hb : 0 ≤ b)
  (hb' : b ≤ h)
    (he : u + sg τ * a = u' + sg τ' * b) : |u - u'| ≤ 2 * h := by
  rw [abs_le]
  cases τ <;> cases τ' <;> simp only [sg_false, sg_true] at he <;> constructor <;> linarith

namespace Germ

variable {W : ℕ → List Letter}

/-- A germ in a family of words: the direction goes into the side. -/
def Valid (W : ℕ → List Letter) (g : Germ) : Prop :=
  g.p < (W g.i).length ∧ g.u ∈ Icc (0 : ℝ) 1 ∧ (g.τ = true → g.u < 1) ∧ (g.τ = false → 0 < g.u)

/-- The point of a germ. -/
noncomputable def pt (W : ℕ → List Letter) (g : Germ) : ℕ × ℂ := spt W g.i g.p g.u

/-- The offset on the side of the point `z` of the square. -/
noncomputable def th (h : ℝ) (g : Germ) (z : ℂ) : ℝ := g.u + sg g.τ * (h * z.re)

/-- The polar rectangle of a germ, of size `h`. -/
noncomputable def rect (W : ℕ → List Letter) (h : ℝ) (g : Germ) (z : ℂ) : ℕ × ℂ :=
  (g.i, ((1 - h * z.im : ℝ) : ℂ) * per (W g.i).length (g.p + th h g z))

/-- The germ is far from the ends of the side, on the side that it looks at. -/
def Small (h : ℝ) (g : Germ) : Prop := (g.τ = true → g.u + h < 1) ∧ (g.τ = false → 0 < g.u - h)

theorem Valid.len_pos {g : Germ} (hv : Valid W g) : 0 < (W g.i).length := by
  have := hv.1
  omega

theorem Valid.ne_nil {g : Germ} (hv : Valid W g) : W g.i ≠ [] := List.length_pos_iff.mp hv.len_pos

theorem Valid.exists_label {g : Germ} (hv : Valid W g) : ∃ k e, (W g.i)[g.p]? = some (k, e) :=
  ⟨((W g.i)[g.p]'hv.1).1, ((W g.i)[g.p]'hv.1).2, List.getElem?_eq_getElem hv.1⟩

theorem Valid.pt_mem {g : Germ} (hv : Valid W g) : g.pt W ∈ Dsk W :=
  ⟨hv.ne_nil, (norm_per _ _).le⟩

theorem Valid.norm_pt {g : Germ} (_hv : Valid W g) : ‖(g.pt W).2‖ = 1 := norm_per _ _

theorem eq_of_pt {g g' : Germ} (hv : Valid W g) (hv' : Valid W g') (hτ : g.τ = g'.τ) (he : g.pt W
  = g'.pt W) :
    g = g' := by
  obtain ⟨i, p, u, τ⟩ := g
  obtain ⟨i', p', u', τ'⟩ := g'
  simp only at hτ
  subst hτ
  have hi : i = i' := congrArg Prod.fst he
  subst hi
  obtain ⟨hp, hu, h1, h2⟩ := hv
  obtain ⟨hp', hu', h1', h2'⟩ := hv'
  simp only at hp hu h1 h2 hp' hu' h1' h2'
  have hn : 0 < (W i).length := by omega
  have hpn : (p : ℝ) + 1 ≤ (W i).length := by exact_mod_cast hp
  have hpn' : (p' : ℝ) + 1 ≤ (W i).length := by exact_mod_cast hp'
  have hn0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hn0' : (0 : ℝ) ≤ p' := Nat.cast_nonneg p'
  obtain ⟨m, hm⟩ := per_eq hn (congrArg Prod.snd he)
  have hm0 : m = 0 := by
    apply int_eq_zero_of hn
    have h3 : (m : ℝ) * (W i).length = (p + u) - (p' + u') := by linarith
    rw [h3, abs_lt]
    cases τ
    · have h4 := h2 rfl
      have h4' := h2' rfl
      constructor <;> linarith [hu.2, hu'.2]
    · have h4 := h1 rfl
      have h4' := h1' rfl
      constructor <;> linarith [hu.1, hu'.1]
  rw [hm0] at hm
  simp only [Int.cast_zero, zero_mul, add_zero] at hm
  have hpp : p = p' := by
    rcases lt_trichotomy p p' with h3 | h3 | h3
    · have h5 : (p : ℝ) + 1 ≤ p' := by exact_mod_cast h3
      cases τ
      · have := h2' rfl
        linarith [hu.2]
      · have := h1 rfl
        linarith [hu'.1]
    · exact h3
    · have h5 : (p' : ℝ) + 1 ≤ p := by exact_mod_cast h3
      cases τ
      · have := h2 rfl
        linarith [hu'.2]
      · have := h1' rfl
        linarith [hu.1]
  subst hpp
  have huu : u = u' := by linarith
  rw [huu]

/-- Each germ has a germ at the same point in the other direction. -/
theorem exists_twin {g : Germ} (hv : Valid W g) : ∃ g', Valid W g' ∧ g'.pt W = g.pt W ∧ g'.τ = !g.τ
  := by
  obtain ⟨i, p, u, τ⟩ := g
  obtain ⟨hp, hu, h1, h2⟩ := hv
  simp only at hp hu h1 h2
  have hn : 0 < (W i).length := by omega
  have hper : ∀ x, per (W i).length (x + (W i).length) = per (W i).length x := per_add_self hn.ne'
  cases τ
  · have hu0 := h2 rfl
    rcases lt_or_eq_of_le hu.2 with h3 | h3
    · exact ⟨⟨i, p, u, true⟩, ⟨hp, hu, fun _ => h3, by simp⟩, rfl, rfl⟩
    · subst h3
      by_cases hp1 : p + 1 < (W i).length
      · refine ⟨⟨i, p + 1, 0, true⟩, ⟨hp1, by simp, by simp, by simp⟩, ?_, rfl⟩
        simp [pt, spt]
      · have hpe : p + 1 = (W i).length := by omega
        refine ⟨⟨i, 0, 0, true⟩, ⟨hn, by simp, by simp, by simp⟩, ?_, rfl⟩
        have h4 : (p : ℝ) + 1 = (0 : ℝ) + (W i).length := by
          rw [zero_add]
          exact_mod_cast hpe
        simp only [pt, spt]
        rw [h4, hper]
        simp
  · have hu0 := h1 rfl
    rcases lt_or_eq_of_le hu.1 with h3 | h3
    · exact ⟨⟨i, p, u, false⟩, ⟨hp, hu, by simp, fun _ => h3⟩, rfl, rfl⟩
    · subst h3
      rcases Nat.eq_zero_or_pos p with h4 | h4
      · subst h4
        refine ⟨⟨i, (W i).length - 1, 1, false⟩, ⟨Nat.sub_lt hn one_pos, by simp, by simp,
          by simp⟩, ?_, rfl⟩
        have h5 : (((W i).length - 1 : ℕ) : ℝ) + 1 = (0 : ℝ) + (W i).length := by
          rw [Nat.cast_sub hn]
          simp
        simp only [pt, spt]
        rw [h5, hper]
        simp
      · refine ⟨⟨i, p - 1, 1, false⟩, ⟨by simp only; omega, by simp, by simp, by simp⟩, ?_, rfl⟩
        have h5 : ((p - 1 : ℕ) : ℝ) + 1 = p := by
          rw [Nat.cast_sub h4]
          simp
        simp only [pt, spt]
        rw [h5]
        simp

/-- `g'` is the germ on the other side with the same label as `g`. -/
def Partner (W : ℕ → List Letter) (g g' : Germ) : Prop :=
  ∃ k e e', (W g.i)[g.p]? = some (k, e) ∧ (W g'.i)[g'.p]? = some (k, e') ∧ (g.i, g.p) ≠
    (g'.i, g'.p) ∧
    g'.u = flp e e' g.u ∧ g'.τ = (if e = e' then g.τ else !g.τ)

theorem flp_add (e e' : Bool) (τ : Bool) (u t : ℝ) :
    flp e e' (u + sg τ * t) = flp e e' u + sg (if e = e' then τ else !τ) * t := by
  cases e <;> cases e' <;> cases τ <;> simp [flp] <;> ring

/-- Each side with a label on another side gives a partner. -/
theorem exists_partner {g : Germ} (hv : Valid W g) (hfree : ¬ FreeSide W g.i g.p) :
    ∃ g', Valid W g' ∧ Partner W g g' := by
  unfold FreeSide at hfree
  push Not at hfree
  obtain ⟨j, q, k, e, e', h1, h2, h3⟩ := hfree
  refine ⟨⟨j, q, flp e e' g.u, if e = e' then g.τ else !g.τ⟩, ⟨(List.getElem?_eq_some_iff.mp h2).1,
    flp_mem hv.2.1, ?_, ?_⟩, k, e, e', h1, h2, h3, rfl, rfl⟩
  · simp only
    intro h4
    have hu := hv.2.1
    have h5 := hv.2.2.1
    have h6 := hv.2.2.2
    by_cases h7 : e = e'
    · simp only [h7, ite_true] at h4 ⊢
      simpa [flp] using h5 h4
    · simp only [h7, ite_false] at h4 ⊢
      have h8 : g.τ = false := by simpa using h4
      simpa [flp, h7] using h6 h8
  · simp only
    intro h4
    have hu := hv.2.1
    have h5 := hv.2.2.1
    have h6 := hv.2.2.2
    by_cases h7 : e = e'
    · simp only [h7, ite_true] at h4 ⊢
      simpa [flp] using h6 h4
    · simp only [h7, ite_false] at h4 ⊢
      have h8 : g.τ = true := by simpa using h4
      simpa [flp, h7] using h5 h8

theorem Partner.ne {g g' : Germ} (h : Partner W g g') : g' ≠ g := by
  rintro rfl
  obtain ⟨k, e, e', -, -, h3, -⟩ := h
  exact h3 rfl

theorem Partner.not_free {g g' : Germ} (h : Partner W g g') : ¬ FreeSide W g.i g.p := by
  obtain ⟨k, e, e', h1, h2, h3, -⟩ := h
  exact fun hf => h3 (hf _ _ k e e' h1 h2)

theorem Partner.stp {g g' : Germ} (h : Partner W g g') {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ e e', Stp W (spt W g.i g.p u) (spt W g'.i g'.p (flp e e' u)) ∧ g'.u = flp e e' g.u ∧
      g'.τ = (if e = e' then g.τ else !g.τ) := by
  obtain ⟨k, e, e', h1, h2, h3, h4, h5⟩ := h
  exact ⟨e, e', stp_iff.mpr ⟨_, _, _, _, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩, h4, h5⟩

theorem rect_zero (W : ℕ → List Letter) (h : ℝ) (g : Germ) : rect W h g 0 = g.pt W := by
  simp [rect, pt, spt, th]

theorem rect_im {h : ℝ} (g : Germ) {z : ℂ} (hz : z.im = 0) : rect W h g z = spt W g.i g.p
  (th h g z) := by
  simp [rect, spt, hz]

theorem rect_left (W : ℕ → List Letter) (h : ℝ) (g : Germ) (s : ℝ) :
    rect W h g (s * Complex.I) = (g.i, ((1 - h * s : ℝ) : ℂ) * (g.pt W).2) := by
  simp [rect, pt, spt, th]

section Small

variable {h : ℝ} (h0 : 0 < h) (h1 : h < 1)

include h0 in
theorem th_mem {g : Germ} (hv : Valid W g) (hs : Small h g) {z : ℂ} (hz : z ∈ unitSq) :
    th h g z ∈ Icc (0 : ℝ) 1 ∧ (0 < z.re → th h g z ∈ Ioo (0 : ℝ) 1) := by
  obtain ⟨hz1, -⟩ := hz
  have hu := hv.2.1
  have hb : h * z.re ≤ h := by nlinarith [hz1.2]
  have hb0 : 0 ≤ h * z.re := mul_nonneg h0.le hz1.1
  unfold th
  cases hτ : g.τ
  · have h3 := hs.2 hτ
    simp only [sg_false]
    refine ⟨⟨by linarith, by linarith [hu.2]⟩, fun hp => ?_⟩
    have := mul_pos h0 hp
    exact ⟨by linarith, by linarith [hu.2]⟩
  · have h3 := hs.1 hτ
    simp only [sg_true]
    refine ⟨⟨by linarith [hu.1], by linarith⟩, fun hp => ?_⟩
    have := mul_pos h0 hp
    exact ⟨by linarith [hu.1], by linarith⟩

include h0 h1 in
theorem rect_mem {g : Germ} (hv : Valid W g) {z : ℂ} (hz : z ∈ unitSq) : rect W h g z ∈ Dsk W := by
  obtain ⟨-, hz2⟩ := hz
  refine ⟨hv.ne_nil, ?_⟩
  simp only [rect, norm_mul, norm_per, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb : h * z.im ≤ h := by nlinarith [hz2.2]
  have hb0 : 0 ≤ h * z.im := mul_nonneg h0.le hz2.1
  rw [abs_of_pos (by linarith)]
  linarith

include h0 h1 in
theorem norm_rect {g : Germ} {z : ℂ} (hz : z ∈ unitSq) : ‖(rect W h g z).2‖ = 1 - h * z.im := by
  obtain ⟨-, hz2⟩ := hz
  simp only [rect, norm_mul, norm_per, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb : h * z.im ≤ h := by nlinarith [hz2.2]
  rw [abs_of_pos (by linarith)]

theorem continuous_rect (W : ℕ → List Letter) (h : ℝ) (g : Germ) : Continuous (rect W h g) := by
  unfold rect th
  have := continuous_per (W g.i).length
  fun_prop

/-- The set of germs is separated at the scale `h`. -/
def Sep (h : ℝ) (G : Set Germ) : Prop :=
  ∀ g ∈ G, ∀ g' ∈ G, g.i = g'.i → g.p = g'.p → g.u ≠ g'.u → 2 * h < |g.u - g'.u|

include h0 h1 in
/-- Two equal points of the rectangles of germs. -/
theorem rect_same {G : Set Germ} (hG : ∀ g ∈ G, Valid W g) (hS : ∀ g ∈ G, Small h g)
  (hsep : Sep h G)
    {g g' : Germ} (hg : g ∈ G) (hg' : g' ∈ G) {z z' : ℂ} (hz : z ∈ unitSq) (hz' : z' ∈ unitSq)
    (he : rect W h g z = rect W h g' z') :
    z = z' ∧ (g = g' ∨ (z.re = 0 ∧ g'.τ = !g.τ ∧ g'.pt W = g.pt W)) := by
  have hi : g.i = g'.i := congrArg Prod.fst he
  have hnorm : ‖(rect W h g z).2‖ = ‖(rect W h g' z').2‖ := by rw [he]
  rw [norm_rect h0 h1 hz, norm_rect h0 h1 hz'] at hnorm
  have him : z.im = z'.im := mul_left_cancel₀ h0.ne' (by linarith)
  have hρ : ((1 - h * z.im : ℝ) : ℂ) ≠ 0 := by
    have hb : h * z.im ≤ h := by nlinarith [hz.2.2]
    have : 1 - h * z.im ≠ 0 := by linarith
    exact_mod_cast this
  have hv := hG g hg
  have hv' := hG g' hg'
  have hper : per (W g.i).length (g.p + th h g z) = per (W g.i).length (g'.p + th h g' z') := by
    have h3 : ((1 - h * z.im : ℝ) : ℂ) * per (W g.i).length (g.p + th h g z) =
        ((1 - h * z'.im : ℝ) : ℂ) * per (W g'.i).length (g'.p + th h g' z') := congrArg Prod.snd he
    rw [← him, ← hi] at h3
    exact mul_left_cancel₀ hρ h3
  have hm1 := th_mem h0 hv (hS g hg) hz
  have hm2 := th_mem h0 hv' (hS g' hg') hz'
  have hre0 : 0 ≤ z.re := hz.1.1
  have hre0' : 0 ≤ z'.re := hz'.1.1
  have hre1 : z.re ≤ 1 := hz.1.2
  have hre1' : z'.re ≤ 1 := hz'.1.2
  by_cases hboth : z.re = 0 ∧ z'.re = 0
  · have hzz : z = z' := Complex.ext (by rw [hboth.1, hboth.2]) him
    refine ⟨hzz, ?_⟩
    have hpp : g'.pt W = g.pt W := by
      have h3 := he
      rw [hzz] at h3
      have h4 : rect W h g z' = (g.i, ((1 - h * z'.im : ℝ) : ℂ) * (g.pt W).2) := by
        conv_lhs => rw [show z' = (z'.im : ℝ) * Complex.I from Complex.ext (by simp [hboth.2])
          (by simp)]
        rw [rect_left]
      have h5 : rect W h g' z' = (g'.i, ((1 - h * z'.im : ℝ) : ℂ) * (g'.pt W).2) := by
        conv_lhs => rw [show z' = (z'.im : ℝ) * Complex.I from Complex.ext (by simp [hboth.2])
          (by simp)]
        rw [rect_left]
      rw [h4, h5] at h3
      have h6 := mul_left_cancel₀ (by rw [him] at hρ; exact hρ) (congrArg Prod.snd h3)
      exact Prod.ext hi.symm h6.symm
    by_cases hτ : g'.τ = g.τ
    · exact .inl (eq_of_pt hv hv' hτ.symm hpp.symm)
    · refine .inr ⟨hboth.1, ?_, hpp⟩
      cases h7 : g.τ <;> cases h8 : g'.τ <;> simp_all
  · have hkey : g.p = g'.p ∧ th h g z = th h g' z' := by
      have hlen : (W g.i).length = (W g'.i).length := by rw [hi]
      by_cases h5 : z.re = 0
      · have h6 : 0 < z'.re := lt_of_le_of_ne hre0' fun h7 => hboth ⟨h5, h7.symm⟩
        have h7 := side_unique hv'.1 (hlen ▸ hv.1) (hm2.2 h6) hm1.1 (by rw [← hlen]; exact
          hper.symm)
        exact ⟨h7.1.symm, h7.2.symm⟩
      · have h6 : 0 < z.re := lt_of_le_of_ne hre0 (Ne.symm h5)
        exact side_unique hv.1 (hlen ▸ hv'.1) (hm1.2 h6) hm2.1 hper
    obtain ⟨hp, hth⟩ := hkey
    have hb : h * z.re ≤ h := by nlinarith
    have hb' : h * z'.re ≤ h := by nlinarith
    have hb0 : 0 ≤ h * z.re := mul_nonneg h0.le hre0
    have hb0' : 0 ≤ h * z'.re := mul_nonneg h0.le hre0'
    have huu : g.u = g'.u := by
      by_contra hne
      have h6 := hsep g hg g' hg' hi hp hne
      have h7 : g.u + sg g.τ * (h * z.re) = g'.u + sg g'.τ * (h * z'.re) := hth
      have h8 := abs_sub_le_of_sg hb0 hb hb0' hb' h7
      linarith
    have h7 : sg g.τ * (h * z.re) = sg g'.τ * (h * z'.re) := by
      have h8 : g.u + sg g.τ * (h * z.re) = g'.u + sg g'.τ * (h * z'.re) := hth
      linarith
    have hpos : 0 < z.re ∨ 0 < z'.re := by
      by_contra hc
      push Not at hc
      exact hboth ⟨le_antisymm hc.1 hre0, le_antisymm hc.2 hre0'⟩
    have hpos' : 0 < h * z.re ∨ 0 < h * z'.re := hpos.imp (mul_pos h0) (mul_pos h0)
    have h8 : g.τ = g'.τ ∧ h * z.re = h * z'.re := sg_cancel hb0 hb0' hpos' h7
    have hre : z.re = z'.re := mul_left_cancel₀ h0.ne' h8.2
    exact ⟨Complex.ext hre him, .inl (Germ.ext hi hp huu h8.1)⟩

include h0 in
/-- A step from a rectangle goes to the rectangle of the partner. -/
theorem rect_stp {G : Set Germ} (hP : IsPaired W) (hG : ∀ g ∈ G, Valid W g)
  (hS : ∀ g ∈ G, Small h g) (hsep : Sep h G)
    {g g' g₄ : Germ} (hg : g ∈ G) (hg' : g' ∈ G) (hg₄ : g₄ ∈ G) (hp : Partner W g g₄) {z z' : ℂ}
      (hz : z ∈ unitSq)
    (hz' : z' ∈ unitSq) (hi : z.im = 0) (hi' : z'.im = 0) (hre : 0 < z.re)
    (he : Stp W (rect W h g z) (rect W h g' z')) : z = z' ∧ g' = g₄ := by
  have hv := hG g hg
  have hv' := hG g' hg'
  have hv₄ := hG g₄ hg₄
  have hm1 := th_mem h0 hv (hS g hg) hz
  have hm2 := th_mem h0 hv' (hS g' hg') hz'
  have hm3 := hm1.2 hre
  rw [rect_im g hi, rect_im g' hi'] at he
  obtain ⟨k, e, e', hs1, hs2, hs3, hs4, hs5⟩ := id hp
  obtain ⟨j, q, e₂, h2, h3, h4⟩ := stp_of_side hP hs1 hm3 he
  have h5 : (j, q) = (g.i, g.p) ∨ (j, q) = (g₄.i, g₄.p) := hP.third hs1 hs2 h2 hs3
  have h6 : (j, q) = (g₄.i, g₄.p) := h5.resolve_left fun h7 => h3 h7.symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h6
  rw [hs2] at h2
  obtain ⟨-, h7⟩ := Prod.mk.inj (Option.some.inj h2)
  subst h7
  have hi2 : g'.i = g₄.i := congrArg Prod.fst h4
  have hφ := flp_mem' (e := e) (e' := e') hm3
  have hlen : (W g₄.i).length = (W g'.i).length := by rw [hi2]
  have h8 := side_unique hv₄.1 (hlen ▸ hv'.1) hφ hm2.1 (by
    have h9 : per (W g'.i).length (g'.p + th h g' z') = per (W g₄.i).length (g₄.p + flp e e'
      (th h g z)) :=
      congrArg Prod.snd h4
    rw [← hlen] at h9
    exact h9.symm)
  obtain ⟨hpp, hφe⟩ := h8
  have h9 : g₄.u + sg g₄.τ * (h * z.re) = g'.u + sg g'.τ * (h * z'.re) := by
    have h10 : flp e e' (th h g z) = g₄.u + sg g₄.τ * (h * z.re) := by
      rw [th, flp_add, hs4, hs5]
    rw [← h10, hφe]
    rfl
  have hre0' : 0 ≤ z'.re := hz'.1.1
  have hb : h * z.re ≤ h := by nlinarith [hz.1.2]
  have hb' : h * z'.re ≤ h := by nlinarith [hz'.1.2]
  have hb0 : 0 < h * z.re := mul_pos h0 hre
  have hb0' : 0 ≤ h * z'.re := mul_nonneg h0.le hre0'
  have huu : g₄.u = g'.u := by
    by_contra hne
    have h10 := hsep g₄ hg₄ g' hg' hi2.symm hpp hne
    have h11 := abs_sub_le_of_sg hb0.le hb hb0' hb' h9
    linarith
  have h7 : sg g₄.τ * (h * z.re) = sg g'.τ * (h * z'.re) := by linarith
  have h8 : g₄.τ = g'.τ ∧ h * z.re = h * z'.re := sg_cancel hb0.le hb0' (.inl hb0) h7
  have hre2 : z.re = z'.re := mul_left_cancel₀ h0.ne' h8.2
  exact ⟨Complex.ext hre2 (by rw [hi, hi']), (Germ.ext hi2.symm hpp huu h8.1).symm⟩

end Small

end Germ

end GraphMinor.Surface
