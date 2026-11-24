/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutComp

/-!
# Words of a surface before cutting

Cutting a surface `Σ(a, b, c)` along an arc is undone by pasting two sides of a word. This file
lists these words for a
connected surface and finds their normal forms. Each word consists of a short front part, and of the
rest `rW` of the
normal word of the surface.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set

universe uu

/-- The first label that the normal word with `c` holes does not use. -/
def frL (a b c : ℕ) : ℕ := 2 * a + b + 2 * c + 1

/-- The state of the procedure for a word with front part `R`. -/
theorem state_of_front {a b c : ℕ} {L : List ℕ} (hL : L.Nodup) {R : List Letter} (hG : Good
  (eW a b c ++ R))
    (hR : ∀ l ∈ eW a b c ++ R, 2 * a + b ≤ l.1 ∧ ∀ m ∈ L, l.1 ≠ 2 * a + b + 2 * m
      ∧ l.1 ≠ 2 * a + b + 2 * m + 1) :
    Inv (eW a b c ++ R) (hW 0 a) (cW (2 * a) b) (hlW (2 * a + b) L) a b L.length ∧
      WEq.{uu} (R ++ rW a b c L) ((eW a b c ++ R) ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L)
        := by
  refine ⟨inv_of_model hL hG hR, ?_⟩
  simpa [List.append_assoc] using weq_front.{uu} a b c L R

/-- The front part for two lifts on two holes. -/
def blkA (a b c i j : ℕ) (σ : Bool) : List Letter :=
  [tL a b j, ((rL a b i).1, σ), (frL a b c + 1, true), linv (tL a b j), tL a b i, rL a b i,
    (frL a b c, true), linv (tL a b i)]

/-- The front part for two lifts on one hole. -/
def blkB (a b c i : ℕ) (σ : Bool) : List Letter :=
  [tL a b i, rL a b i, (frL a b c, true), ((rL a b i).1, σ), (frL a b c + 2, true), linv (tL a b i)]

/-- The front part for one lift that goes twice around a hole. -/
def blkD (a b i : ℕ) : List Letter := [tL a b i, rL a b i, rL a b i, linv (tL a b i)]

/-- The front part for two `O`-arcs. -/
def blkE (a b i j : ℕ) (σ : Bool) : List Letter :=
  [tL a b j, ((rL a b i).1, σ), linv (tL a b j), tL a b i, rL a b i, linv (tL a b i)]

section

variable {a b c i j : ℕ} {L : List ℕ}

theorem nf_blkA (hij : i ≠ j) (hi : i < c) (hj : j < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i
  ∧ m ≠ j) (σ : Bool) :
    (σ = false → ∃ w, IsNF w (a + 1) b (L.length + 1) ∧ WEq.{uu} (blkA a b c i j σ ++ rW a b c L)
      w) ∧
    (σ = true → ∃ w, IsNF w a (b + 2) (L.length + 1) ∧ WEq.{uu} (blkA a b c i j σ ++ rW a b c L) w)
      := by
  obtain ⟨h1, h2⟩ := state_of_front (a := a) (b := b) (c := c) (L := L) (R := blkA a b c i j σ) hL
    (by
    intro k
    cases σ <;> simp only [eW, blkA, List.cons_append, List.nil_append, cnt_cons, cnt_nil, tL, rL,
      frL, linv] <;> split_ifs <;> omega) (by
    intro l hl
    simp only [eW, blkA, List.cons_append, List.nil_append, tL, rL, frL, linv, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · refine ⟨by simp only; omega, fun m hm => ?_⟩
        have := hc m hm
        simp only
        omega)
  constructor
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseA_neg.{uu} (x := (2 * a + b + 2 * c, true)) (t₁ := tL a b j) (p :=
      ((rL a b i).1, false)) (g₁ := (frL a b c + 1, true))
      (t₂ := tL a b i) (g₂ := (frL a b c, true)) h1 (by simp [tL, rL]; omega) (by simp)
    exact ⟨w, h3, h2.trans h4⟩
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseA_pos.{uu} (x := (2 * a + b + 2 * c, true)) (t₁ := tL a b j) (p
      := rL a b i) (g₁ := (frL a b c + 1, true))
      (t₂ := tL a b i) (g₂ := (frL a b c, true)) h1 (by simp [linv])
    exact ⟨w, h3, h2.trans h4⟩

theorem nf_blkB (hi : i < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i) (σ : Bool) :
    (σ = false → ∃ w, IsNF w a b (L.length + 2) ∧ WEq.{uu} (blkB a b c i σ ++ rW a b c L) w) ∧
    (σ = true → ∃ w, IsNF w a (b + 1) (L.length + 1) ∧ WEq.{uu} (blkB a b c i σ ++ rW a b c L) w)
      := by
  obtain ⟨h1, h2⟩ := state_of_front (a := a) (b := b) (c := c) (L := L) (R := blkB a b c i σ) hL (by
    intro k
    cases σ <;> simp only [eW, blkB, List.cons_append, List.nil_append, cnt_cons, cnt_nil, tL, rL,
      frL, linv] <;> split_ifs <;> omega) (by
    intro l hl
    simp only [eW, blkB, List.cons_append, List.nil_append, tL, rL, frL, linv, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · refine ⟨by simp only; omega, fun m hm => ?_⟩
        have := hc m hm
        simp only
        omega)
  constructor
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseB_neg.{uu} (x := (2 * a + b + 2 * c, true)) (t := tL a b i) (p
      := rL a b i) (g₁ := (frL a b c, true))
      (g₂ := (frL a b c + 2, true)) h1 (by
        simp only [cnt_cons, cnt_nil, tL, rL, frL, linv]
        split_ifs <;> omega) (by
        simp only [cnt_cons, cnt_nil, tL, frL, linv]
        split_ifs <;> omega)
    exact ⟨w, h3, h2.trans h4⟩
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseB_pos.{uu} (x := (2 * a + b + 2 * c, true)) (t := tL a b i) (p
      := rL a b i) (g₁ := (frL a b c, true))
      (g₂ := (frL a b c + 2, true)) h1 (by simp [linv])
    exact ⟨w, h3, h2.trans h4⟩

theorem nf_blkD (hi : i < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i) :
    ∃ w, IsNF w a (b + 1) L.length ∧ WEq.{uu} (blkD a b i ++ rW a b c L) w := by
  obtain ⟨h1, h2⟩ := state_of_front (a := a) (b := b) (c := c) (L := L) (R := blkD a b i) hL (by
    intro k
    simp only [eW, blkD, List.cons_append, List.nil_append, cnt_cons, cnt_nil, tL, rL, linv]
    split_ifs <;> omega) (by
    intro l hl
    simp only [eW, blkD, List.cons_append, List.nil_append, tL, rL, linv, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · refine ⟨by simp only; omega, fun m hm => ?_⟩
        have := hc m hm
        simp only
        omega)
  obtain ⟨w, h3, h4⟩ := nf_caseD.{uu} (x := (2 * a + b + 2 * c, true)) (t := tL a b i) (p
    := rL a b i) h1
  exact ⟨w, h3, h2.trans h4⟩

theorem nf_blkE (hij : i ≠ j) (hi : i < c) (hj : j < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i
  ∧ m ≠ j) (σ : Bool) :
    (σ = false → ∃ w, IsNF w (a + 1) b L.length ∧ WEq.{uu} (blkE a b i j σ ++ rW a b c L) w) ∧
    (σ = true → ∃ w, IsNF w a (b + 2) L.length ∧ WEq.{uu} (blkE a b i j σ ++ rW a b c L) w) := by
  obtain ⟨h1, h2⟩ := state_of_front (a := a) (b := b) (c := c) (L := L) (R := blkE a b i j σ) hL (by
    intro k
    cases σ <;> simp only [eW, blkE, List.cons_append, List.nil_append, cnt_cons, cnt_nil, tL, rL,
      linv] <;> split_ifs <;> omega) (by
    intro l hl
    simp only [eW, blkE, List.cons_append, List.nil_append, tL, rL, linv, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · refine ⟨by simp only; omega, fun m hm => ?_⟩
        have := hc m hm
        simp only
        omega)
  constructor
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseE_neg.{uu} (x := (2 * a + b + 2 * c, true)) (t₁ := tL a b j) (p :=
      ((rL a b i).1, false))
      (t₂ := tL a b i) h1 (by simp [tL, rL]; omega)
    exact ⟨w, h3, h2.trans h4⟩
  · rintro rfl
    obtain ⟨w, h3, h4⟩ := nf_caseE_pos.{uu} (x := (2 * a + b + 2 * c, true)) (t₁ := tL a b j) (p
      := rL a b i) (t₂ := tL a b i) h1
    exact ⟨w, h3, h2.trans h4⟩

end

end GraphMinor.Surface
