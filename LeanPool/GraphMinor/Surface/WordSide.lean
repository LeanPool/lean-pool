/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Polygon
public import LeanPool.GraphMinor.Surface.WordRules

/-!
# Sides of a family of words

We say that a family of words is paired if each label is on at most two sides. A point of a side
that is not a corner is
related to at most one other point, the point with the same parameter on the other side with this
label
(`PRel.eq_or_stp`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

/-- Each label is on at most two sides. -/
def IsPaired (W : ℕ → List Letter) : Prop :=
  ∀ k, {s : ℕ × ℕ | ∃ e, (W s.1)[s.2]? = some (k, e)}.encard ≤ 2

/-- The point of the side `p` of the word `i` at the distance `u` from the start of the side. -/
noncomputable def spt (W : ℕ → List Letter) (i p : ℕ) (u : ℝ) : ℕ × ℂ := (i, per (W i).length
  (p + u))

/-- The change of the offset between two sides with these signs. -/
noncomputable def flp (e e' : Bool) (u : ℝ) : ℝ := if e = e' then u else 1 - u

theorem flp_mem {e e' : Bool} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : flp e e' u ∈ Icc (0 : ℝ) 1 := by
  unfold flp
  split_ifs
  · exact hu
  · exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

theorem flp_mem' {e e' : Bool} {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : flp e e' u ∈ Ioo (0 : ℝ) 1 := by
  unfold flp
  split_ifs
  · exact hu
  · exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

theorem flp_flp (e e' : Bool) (u : ℝ) : flp e' e (flp e e' u) = u := by
  unfold flp
  by_cases h : e = e'
  · simp [h]
  · have h' : ¬ e' = e := fun he => h he.symm
    simp [h, h']

/-- The offset of the parameter `t` on a side with sign `e`. -/
noncomputable def ofs (e : Bool) (t : ℝ) : ℝ := if e then t else 1 - t

theorem ofs_ofs (e : Bool) (t : ℝ) : ofs e (ofs e t) = t := by
  cases e <;> simp [ofs]

theorem ofs_flp (e e' : Bool) (u : ℝ) : ofs e' (ofs e u) = flp e e' u := by
  cases e <;> cases e' <;> simp [ofs, flp]

theorem ofs_mem {e : Bool} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : ofs e u ∈ Icc (0 : ℝ) 1 := by
  cases e
  · simpa [ofs] using ⟨hu.2, hu.1⟩
  · simpa [ofs] using hu

theorem sdPt_eq (n p : ℕ) (e : Bool) (t : ℝ) : sdPt n p e t = per n (p + ofs e t) := rfl

/-- A step in terms of offsets. -/
theorem stp_iff {W : ℕ → List Letter} {a b : ℕ × ℂ} : Stp W a b ↔
    ∃ (i j p q k : ℕ) (e e' : Bool) (u : ℝ), (W i)[p]? = some (k, e) ∧ (W j)[q]? = some (k, e') ∧
      (i, p) ≠ (j, q) ∧
      u ∈ Icc (0 : ℝ) 1 ∧ a = spt W i p u ∧ b = spt W j q (flp e e' u) := by
  constructor
  · rintro ⟨i, j, p, q, k, e, e', t, h1, h2, h3, ht, rfl, rfl⟩
    refine ⟨i, j, p, q, k, e, e', ofs e t, h1, h2, h3, ofs_mem ht, rfl, ?_⟩
    rw [spt, ← ofs_flp, ofs_ofs]
    rfl
  · rintro ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩
    refine ⟨i, j, p, q, k, e, e', ofs e u, h1, h2, h3, ofs_mem hu, ?_, ?_⟩
    · rw [spt, sdPt_eq, ofs_ofs]
    · rw [spt, sdPt_eq, ofs_flp]

theorem side_unique {n p p' : ℕ} (hp : p < n) (hp' : p' < n) {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (he : per n (p + u) = per n (p' + v)) : p = p' ∧ u = v := by
  have hn : 0 < n := by omega
  have hp1 : (p : ℝ) + 1 ≤ n := by exact_mod_cast hp
  have hp1' : (p' : ℝ) + 1 ≤ n := by exact_mod_cast hp'
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp0' : (0 : ℝ) ≤ p' := Nat.cast_nonneg p'
  have hx : (p : ℝ) + u ∈ Ico (0 : ℝ) n := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hn' : (0 : ℝ) ∈ Ico (0 : ℝ) n := ⟨le_rfl, by exact_mod_cast hn⟩
  rcases eq_or_lt_of_le (show (p' : ℝ) + v ≤ n by linarith [hv.2]) with h1 | h1
  · have h2 : per n (p + u) = per n 0 := by
      rw [he, h1]
      have := per_add_self hn.ne' 0
      simpa using this
    have := per_injOn hn hx hn' h2
    linarith [hu.1]
  · have h2 := per_injOn hn hx ⟨by linarith [hv.1], h1⟩ he
    have hpq : p = p' := by
      rcases lt_trichotomy p p' with h3 | h3 | h3
      · have : (p : ℝ) + 1 ≤ p' := by exact_mod_cast h3
        linarith [hu.2, hv.1]
      · exact h3
      · have : (p' : ℝ) + 1 ≤ p := by exact_mod_cast h3
        linarith [hu.1, hv.2]
    subst hpq
    exact ⟨rfl, by linarith⟩

variable {W : ℕ → List Letter}

theorem lt_length {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some (k, e)) : p < (W i).length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- A third side with a label is one of two given sides. -/
theorem IsPaired.third (hW : IsPaired W) {i j l p q r k : ℕ} {e e' e'' : Bool} (h1 : (W i)[p]?
  = some (k, e))
    (h2 : (W j)[q]? = some (k, e')) (h3 : (W l)[r]? = some (k, e'')) (hne : (i, p) ≠ (j, q)) :
    (l, r) = (i, p) ∨ (l, r) = (j, q) := by
  classical
  by_contra hcon
  push Not at hcon
  have hs : ({(l, r), (i, p), (j, q)} : Set (ℕ × ℕ)) ⊆ {s : ℕ × ℕ | ∃ e, (W s.1)[s.2]? = some
    (k, e)} := by
    rintro x (rfl | rfl | rfl)
    · exact ⟨e'', h3⟩
    · exact ⟨e, h1⟩
    · exact ⟨e', h2⟩
  have h4 := (encard_le_encard hs).trans (hW k)
  rw [encard_insert_of_notMem (by simp [hcon.1, hcon.2]), encard_pair hne] at h4
  norm_num at h4

/-- Steps out of a point of a side that is not a corner go to the other side with the label. -/
theorem stp_of_side (_hW : IsPaired W) {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some (k, e)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) {b : ℕ × ℂ} (hs : Stp W (spt W i p u) b) :
    ∃ j q e', (W j)[q]? = some (k, e') ∧ (i, p) ≠ (j, q) ∧ b = spt W j q (flp e e' u) := by
  obtain ⟨i', j, p', q, k', e₁, e', v, h1, h2, h3, hv, ha, rfl⟩ := stp_iff.mp hs
  have hi : i = i' := congrArg Prod.fst ha
  subst hi
  have hsnd : per (W i).length (p + u) = per (W i).length (p' + v) := congrArg Prod.snd ha
  obtain ⟨rfl, rfl⟩ := side_unique (lt_length h) (lt_length h1) hu hv hsnd
  rw [h] at h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
  exact ⟨j, q, e', h2, h3, rfl⟩

/-- The pasting class of a point of a side that is not a corner has at most two points. -/
theorem PRel.eq_or_stp (hW : IsPaired W) {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some
  (k, e)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) {b : ℕ × ℂ} (hr : PRel W (spt W i p u) b) : b = spt W i p u ∨ Stp W
      (spt W i p u) b := by
  let a := spt W i p u
  let C : Set (ℕ × ℂ) := {x | x = a ∨ Stp W a x}
  have hstep : ∀ x y, Stp W x y → x ∈ C → y ∈ C := by
    rintro x y hxy (rfl | hx)
    · exact .inr hxy
    · obtain ⟨j, q, e', h2, h3, rfl⟩ := stp_of_side hW h hu hx
      obtain ⟨j', q', e'', h4, h5, rfl⟩ := stp_of_side hW h2 (flp_mem' hu) hxy
      have h6 := hW.third h h2 h4 h3
      rcases h6 with h6 | h6
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h6
        rw [h] at h4
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h4)
        rw [flp_flp]
        exact .inl rfl
      · exact absurd h6.symm h5
  have hsym : ∀ x y, Stp W x y → Stp W y x := by
    rintro _ _ ⟨i, j, p, q, k, e, e', t, h1, h2, h3, ht, rfl, rfl⟩
    exact ⟨j, i, q, p, k, e', e, t, h2, h1, h3.symm, ht, rfl, rfl⟩
  have key : ∀ x y, PRel W x y → (x ∈ C ↔ y ∈ C) := by
    intro x y hxy
    induction hxy with
    | rel x y hs => exact ⟨hstep x y hs, hstep y x (hsym x y hs)⟩
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact (key a b hr).mp (.inl rfl)

/-- A point inside a disc is related only to itself. -/
theorem PRel.eq_of_lt {a b : ℕ × ℂ} (hr : PRel W a b) (ha : ‖a.2‖ < 1) : b = a := by
  have hn : ∀ x y, Stp W x y → ‖x.2‖ = 1 ∧ ‖y.2‖ = 1 := by
    rintro _ _ ⟨i, j, p, q, k, e, e', t, -, -, -, -, rfl, rfl⟩
    exact ⟨norm_per _ _, norm_per _ _⟩
  have key : ∀ x y, PRel W x y → (x = a ↔ y = a) := by
    intro x y hxy
    induction hxy with
    | rel x y hs =>
      obtain ⟨h1, h2⟩ := hn x y hs
      constructor
      · rintro rfl
        exact absurd h1 ha.ne
      · rintro rfl
        exact absurd h2 ha.ne
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact (key a b hr).mp rfl

end GraphMinor.Surface
