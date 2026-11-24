/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Sliding finitely many points along an interval

VII (4.6), page 227, says that `H₃` can be chosen to meet the matching
only at vertices of the graph, since each edge of the matching passes
through at least `w` of them. This is a slide of at most `w` points along
each edge. Here we build the slide of an interval: an increasing
homeomorphism, fixed off an open interval, that takes a given finite set
into a given larger finite set.
-/

public section

namespace GraphMinor.GM07

open Set Topology

/-- The increasing piecewise linear map which fixes `a` and `b` and sends `x` to `y`. -/
noncomputable def twoPiece (a b x y r : ℝ) : ℝ :=
  if r ≤ a then r else if r ≤ x then a + (r - a) * (y - a) / (x - a)
    else if r ≤ b then y + (r - x) * (b - y) / (b - x) else r

private theorem twoPiece_inv {a b x y : ℝ} (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (r : ℝ) : twoPiece a b y x (twoPiece a b x y r) = r := by
  have h1 : 0 < x - a := by linarith
  have h2 : 0 < y - a := by linarith
  have h3 : 0 < b - x := by linarith
  have h4 : 0 < b - y := by linarith
  unfold twoPiece
  by_cases hra : r ≤ a
  · simp [hra]
  by_cases hrx : r ≤ x
  · have hr : a < r := not_le.mp hra
    have hv : a + (r - a) * (y - a) / (x - a) = a + (r - a) / (x - a) * (y - a) := by ring
    have hq : 0 < (r - a) / (x - a) := div_pos (by linarith) h1
    have hq1 : (r - a) / (x - a) ≤ 1 := (div_le_one h1).mpr (by linarith)
    have h5 : ¬ a + (r - a) * (y - a) / (x - a) ≤ a := by
      rw [hv]
      have := mul_pos hq h2
      linarith
    have h6 : a + (r - a) * (y - a) / (x - a) ≤ y := by
      rw [hv]
      have := mul_le_of_le_one_left h2.le hq1
      linarith
    simp only [hra, hrx, ite_true, ite_false, h5, h6]
    field_simp
    ring
  by_cases hrb : r ≤ b
  · have hr : x < r := not_le.mp hrx
    have hv : y + (r - x) * (b - y) / (b - x) = y + (r - x) / (b - x) * (b - y) := by ring
    have hq : 0 < (r - x) / (b - x) := div_pos (by linarith) h3
    have hq1 : (r - x) / (b - x) ≤ 1 := (div_le_one h3).mpr (by linarith)
    have h5 : ¬ y + (r - x) * (b - y) / (b - x) ≤ a := by
      rw [hv]
      have := mul_pos hq h4
      linarith
    have h6 : ¬ y + (r - x) * (b - y) / (b - x) ≤ y := by
      rw [hv]
      have := mul_pos hq h4
      linarith
    have h7 : y + (r - x) * (b - y) / (b - x) ≤ b := by
      rw [hv]
      have := mul_le_of_le_one_left h4.le hq1
      linarith
    simp only [hra, hrx, hrb, ite_true, ite_false, h5, h6, h7]
    field_simp
    ring
  · have hr : b < r := not_le.mp hrb
    have h5 : ¬ r ≤ a := hra
    have h6 : ¬ r ≤ y := by linarith
    simp only [hra, hrx, hrb, ite_false, h6]

private theorem continuous_twoPiece {a b x y : ℝ} (hax : a < x) (hxb : x < b) (hay : a < y)
    (hyb : y < b) : Continuous (twoPiece a b x y) := by
  have h1 : (x - a) ≠ 0 := by linarith
  have h3 : (b - x) ≠ 0 := by linarith
  unfold twoPiece
  refine Continuous.if_le continuous_id ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) continuous_id continuous_id continuous_const ?_
      intro r hr
      subst hr
      field_simp
      ring
    · intro r hr
      subst hr
      have hb : r ≤ b := hxb.le
      simp only [hb, ite_true]
      field_simp
      ring
  · intro r hr
    subst hr
    have : r ≤ x := hax.le
    simp only [this, ite_true]
    field_simp
    ring

/-- The two-piece homeomorphism of the line. -/
theorem exists_twoPiece_homeo {a b x y : ℝ} (hax : a < x) (hxb : x < b) (hay : a < y)
    (hyb : y < b) :
    ∃ σ : ℝ ≃ₜ ℝ, StrictMono σ ∧ (∀ r, r ∉ Ioo a b → σ r = r) ∧ σ x = y := by
  have hab : a < b := hax.trans hxb
  let σ : ℝ ≃ₜ ℝ :=
    { toFun := twoPiece a b x y
      invFun := twoPiece a b y x
      left_inv := twoPiece_inv hax hxb hay hyb
      right_inv := twoPiece_inv hay hyb hax hxb
      continuous_toFun := continuous_twoPiece hax hxb hay hyb
      continuous_invFun := continuous_twoPiece hay hyb hax hxb }
  have hfix : ∀ r, r ∉ Ioo a b → σ r = r := by
    intro r hr
    change twoPiece a b x y r = r
    unfold twoPiece
    by_cases hra : r ≤ a
    · simp [hra]
    · have hrb : b ≤ r := by
        by_contra h
        exact hr ⟨not_le.mp hra, not_le.mp h⟩
      have hrx : ¬ r ≤ x := by linarith
      by_cases hrb' : r ≤ b
      · have hreq : r = b := le_antisymm hrb' hrb
        subst hreq
        simp only [hra, hrx, ite_false, ite_true, le_refl]
        have : r - x ≠ 0 := by linarith
        field_simp
        ring
      · simp [hra, hrx, hrb']
  have hxy : σ x = y := by
    change twoPiece a b x y x = y
    unfold twoPiece
    have h1 : ¬ x ≤ a := by linarith
    have h2 : x - a ≠ 0 := by linarith
    simp only [h1, ite_false, le_refl, ite_true]
    field_simp
    ring
  refine ⟨σ, ?_, hfix, hxy⟩
  rcases σ.continuous.strictMono_of_inj σ.injective with h | h
  · exact h
  · have := h hab
    rw [hfix a (fun h => lt_irrefl _ h.1), hfix b (fun h => lt_irrefl _ h.2)] at this
    linarith

/-- A slide between two sorted lists of the same length. -/
theorem exists_slide_lists : ∀ (n : ℕ) (l l' : List ℝ) (a b : ℝ), l.length = n →
    l.length = l'.length → l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (∀ x ∈ l, x ∈ Ioo a b) → (∀ x ∈ l', x ∈ Ioo a b) →
    ∃ σ : ℝ ≃ₜ ℝ, StrictMono σ ∧ (∀ r, r ∉ Ioo a b → σ r = r) ∧ l.map σ = l' := by
  intro n
  induction n with
  | zero =>
    intro l l' a b hn hlen _ _ _ _
    have h1 : l = [] := List.length_eq_zero_iff.mp hn
    have h2 : l' = [] := List.length_eq_zero_iff.mp (hlen ▸ hn)
    subst h1 h2
    exact ⟨Homeomorph.refl ℝ, strictMono_id, fun _ _ => rfl, rfl⟩
  | succ n ih =>
    intro l l' a b hn hlen hl hl' hin hin'
    obtain _ | ⟨x, xs⟩ := l
    · simp at hn
    obtain _ | ⟨y, ys⟩ := l'
    · simp at hlen
    rw [List.pairwise_cons] at hl hl'
    have hx := hin x (by simp)
    have hy := hin' y (by simp)
    obtain ⟨τ, hτm, hτf, hτx⟩ := exists_twoPiece_homeo hx.1 hx.2 hy.1 hy.2
    have hτb : τ b = b := hτf b (fun h => lt_irrefl _ h.2)
    have hpw : (xs.map τ).Pairwise (· < ·) := by
      rw [List.pairwise_map]
      exact hl.2.imp fun h => hτm h
    obtain ⟨ρ, hρm, hρf, hρmap⟩ := ih (xs.map τ) ys y b (by simpa using hn)
      (by simpa using hlen) hpw hl'.2 (by
        intro z hz
        obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
        have h1 := hl.1 z₀ hz₀
        have h2 := (hin z₀ (by simp [hz₀])).2
        exact ⟨hτx ▸ hτm h1, hτb ▸ hτm h2⟩) (by
        intro z hz
        exact ⟨hl'.1 z hz, (hin' z (by simp [hz])).2⟩)
    refine ⟨τ.trans ρ, ?_, ?_, ?_⟩
    · exact hρm.comp hτm
    · intro r hr
      have h1 : τ r = r := hτf r hr
      have h2 : r ∉ Ioo y b := fun h => hr ⟨hy.1.trans h.1, h.2⟩
      change ρ (τ r) = r
      rw [h1, hρf r h2]
    · have h1 : ρ y = y := hρf y (fun h => lt_irrefl _ h.1)
      simp only [List.map_cons, Homeomorph.trans_apply, hτx, h1]
      rw [← hρmap]
      simp [List.map_map, Function.comp_def]

/-- A slide of the line, fixed off `(a, b)`, that takes a finite subset of `(a, b)` into a larger
finite subset. -/
theorem exists_slide_finset {a b : ℝ} {X Y : Finset ℝ} (hX : ↑X ⊆ Ioo a b) (hY : ↑Y ⊆ Ioo a b)
    (hcard : X.card ≤ Y.card) :
    ∃ σ : ℝ ≃ₜ ℝ, StrictMono σ ∧ (∀ r, r ∉ Ioo a b → σ r = r) ∧ ∀ x ∈ X, σ x ∈ Y := by
  obtain ⟨Y', hsub, hc⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨σ, hm, hf, hmap⟩ := exists_slide_lists _ (X.sort (· ≤ ·)) (Y'.sort (· ≤ ·)) a b rfl
    (by simp [hc]) (Finset.sortedLT_sort X).pairwise (Finset.sortedLT_sort Y').pairwise
    (fun x hx => hX (by simpa using hx)) (fun x hx => hY (hsub (by simpa using hx)))
  refine ⟨σ, hm, hf, fun x hx => hsub ?_⟩
  have hmem : σ x ∈ (X.sort (· ≤ ·)).map σ := List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
  rw [hmap] at hmem
  simpa using hmem

/-- The slide of the unit interval. -/
theorem exists_interval_slide {a b : unitInterval} {X Y : Set unitInterval} (hXf : X.Finite)
    (hYf : Y.Finite) (hX : X ⊆ Ioo a b) (hY : Y ⊆ Ioo a b) (hcard : X.ncard ≤ Y.ncard) :
    ∃ σ : unitInterval ≃ₜ unitInterval, (∀ r, r ∉ Ioo a b → σ r = r) ∧ ∀ x ∈ X, σ x ∈ Y := by
  classical
  let X' : Finset ℝ := hXf.toFinset.image Subtype.val
  let Y' : Finset ℝ := hYf.toFinset.image Subtype.val
  have hXc : X'.card = X.ncard := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, ncard_eq_toFinset_card _ hXf]
  have hYc : Y'.card = Y.ncard := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, ncard_eq_toFinset_card _ hYf]
  obtain ⟨σ, hm, hf, hmap⟩ := exists_slide_finset (X := X') (Y := Y') (a := a.1) (b := b.1)
    (by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      exact hX (hXf.mem_toFinset.mp hx))
    (by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      exact hY (hYf.mem_toFinset.mp hx))
    (by omega)
  have h0 : σ 0 = 0 := hf 0 (fun h => not_lt_of_ge a.2.1 h.1)
  have h1 : σ 1 = 1 := hf 1 (fun h => not_lt_of_ge b.2.2 h.2)
  have hiff : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 ↔ σ r ∈ Icc (0 : ℝ) 1 := by
    intro r
    rw [mem_Icc, mem_Icc, ← h0, ← h1, hm.le_iff_le, hm.le_iff_le, h0, h1]
  let τ : unitInterval ≃ₜ unitInterval := σ.subtype hiff
  refine ⟨τ, ?_, ?_⟩
  · intro r hr
    apply Subtype.ext
    exact hf r.1 (fun h => hr ⟨h.1, h.2⟩)
  · intro x hx
    have hmem : (x : ℝ) ∈ X' := Finset.mem_image.mpr ⟨x, hXf.mem_toFinset.mpr hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp (hmap _ hmem)
    have hτ : τ x = y := Subtype.ext hyeq.symm
    rw [hτ]
    exact hYf.mem_toFinset.mp hy

end GraphMinor.GM07
