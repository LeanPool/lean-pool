/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw5
public import LeanPool.GraphMinor.Surface.CrossCut

/-!
# Drawing a graph in a surface of large genus: any permutation

Every permutation is a product of swaps of neighbouring heights. So a row of handles, or a row of
cross-caps, carries a set of disjoint curves from any order of heights on the left to any other
order
on the right. Straight segments in the strips between the circles join these curves to each other
and
to the vertices.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

/-- The curves for a permutation of `m + 1` heights, for `m` positive. -/
theorem wiring {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
      (∀ j, s ≤ j → j < s + L → ∀ i : Fin m,
        Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
      Slab a b c (m + 1) (x s) (x (s + L)) σ := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m ↦
      Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    exact ⟨1, le_rfl, fun a b c _ x s _ h ↦ h s le_rfl (by omega) i⟩
  | one =>
    refine ⟨2, by omega, fun a b c _ x s hx h ↦ ?_⟩
    have h₀ := h s le_rfl (by omega) ⟨0, hm⟩
    have h₁ := h (s + 1) (by omega) (by omega) ⟨0, hm⟩
    have h₂ := h₀.comp h₁ (hx (by omega)) (hx (by omega))
    rw [Equiv.swap_mul_self] at h₂
    exact h₂
  | mul τ τ' _ _ h₁ h₂ =>
    obtain ⟨L₁, hL₁, h₁⟩ := h₁
    obtain ⟨L₂, hL₂, h₂⟩ := h₂
    refine ⟨L₂ + L₁, by omega, fun a b c _ x s hx h ↦ ?_⟩
    have h₃ := h₂ a b c x s hx fun j hj hj' ↦ h j hj (by omega)
    have h₄ := h₁ a b c x (s + L₂) hx fun j hj hj' ↦ h j (by omega) (by omega)
    rw [← add_assoc]
    exact h₃.comp h₄ (hx (by omega)) (hx (by omega))

/-- The curves for a permutation of an even number of heights. -/
theorem wiring_even {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
      (∀ j, s ≤ j → j < s + L → ∀ (m : ℕ) (i : Fin m),
        Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
      Slab a b c n (x s) (x (s + L)) σ := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, le_rfl, fun a b c _ x s _ _ ↦ ?_⟩
    exact ⟨fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0,
      fun p ↦ p.elim0⟩
  · obtain ⟨m, hm⟩ : ∃ m, k + k = m + 1 := ⟨k + k - 1, by omega⟩
    have hm0 : 0 < m := by omega
    revert σ
    rw [hm]
    intro σ
    obtain ⟨L, hL, h⟩ := wiring hm0 σ
    exact ⟨L, hL, fun a b c _ x s hx hs ↦ h a b c x s hx fun j hj hj' i ↦ hs j hj hj' m i⟩

/-- A permutation is carried by a row of handles. -/
theorem wiring_handles {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ a →
      Slab a b c n (3 * ((-1 : ℤ) : ℝ) + 3 / 2) (3 * (((2 * L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, h⟩ := wiring_even hn σ
  refine ⟨L, hL, fun a b c _ hLa ↦ ?_⟩
  have h₁ := h a b c (fun j ↦ 6 * (j : ℝ) - 3 / 2) 0
    (fun i j hij ↦ by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      simp only
      linarith)
    (fun j _ hj m i ↦ by
      have := slab_handle (a := a) (b := b) (c := c) (n := m) (k := j) (by omega) i
      convert this using 1
      push_cast
      ring)
  convert h₁ using 1
  · push_cast
    ring
  · push_cast
    ring

/-- A permutation is carried by a row of cross-caps. -/
theorem wiring_crosscaps {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ b →
      Slab a b c n (3 * (((2 * a : ℕ) : ℤ) - 1 : ℤ) + 3 / 2)
        (3 * (((2 * a + L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, h⟩ := wiring_even hn σ
  refine ⟨L, hL, fun a b c _ hLb ↦ ?_⟩
  have h₁ := h a b c (fun j ↦ 3 * ((2 * a + j : ℕ) : ℝ) - 3 / 2) 0
    (fun i j hij ↦ by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      simp only
      push_cast
      linarith)
    (fun j _ hj m i ↦ by
      have := slab_crosscap (a := a) (b := b) (c := c) (n := m) (k := j) (by omega) i
      convert this using 1
      push_cast
      ring)
  convert h₁ using 1
  · push_cast
    ring
  · push_cast
    ring

/-- The straight segment between two points of the plane. -/
def sg (z z' : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun s : ℝ ↦ ((1 - s) * z.1 + s * z'.1, (1 - s) * z.2 + s * z'.2)) '' Icc 0 1

theorem mem_sg_left (z z' : ℝ × ℝ) : z ∈ sg z z' := ⟨0, by simp, by simp⟩

theorem mem_sg_right (z z' : ℝ × ℝ) : z' ∈ sg z z' := ⟨1, by simp, by simp⟩

theorem sg_fst {z z' w : ℝ × ℝ} (h : w ∈ sg z z') {l r : ℝ} (h₁ : l ≤ z.1) (h₂ : z.1 ≤ r)
    (h₃ : l ≤ z'.1) (h₄ : z'.1 ≤ r) : l ≤ w.1 ∧ w.1 ≤ r := by
  obtain ⟨s, hs, rfl⟩ := h
  have h₅ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₁)
  have h₆ := mul_nonneg hs.1 (sub_nonneg.mpr h₃)
  have h₇ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₂)
  have h₈ := mul_nonneg hs.1 (sub_nonneg.mpr h₄)
  simp only
  constructor <;> nlinarith

/-- A segment in a strip between two circles is a line of the model. -/
theorem isLine_sg [T2Space (SurfaceModel a b c)] (m : ℤ) {z z' : ℝ × ℝ}
    (h₁ : 3 * (m : ℝ) + 5 / 4 ≤ z.1) (h₂ : z.1 ≤ 3 * m + 7 / 4)
    (h₃ : 3 * (m : ℝ) + 5 / 4 ≤ z'.1) (h₄ : z'.1 ≤ 3 * m + 7 / 4) (hne : z ≠ z') :
    IsLineWithEnds (qq a b c '' sg z z') (qq a b c z) (qq a b c z') ∧
      ∀ w ∈ sg z z', Clear a b c w := by
  have hcl : ∀ w ∈ sg z z', Clear a b c w := fun w hw ↦ by
    obtain ⟨h₅, h₆⟩ := sg_fst hw h₁ h₂ h₃ h₄
    exact clear_of_gap m (by linarith) (by linarith)
  refine ⟨?_, hcl⟩
  let pt : ℝ → ℝ × ℝ := fun s ↦ ((1 - s) * z.1 + s * z'.1, (1 - s) * z.2 + s * z'.2)
  have hpt : ∀ t : unitInterval, pt t.1 ∈ sg z z' := fun t ↦ ⟨t.1, ⟨t.2.1, t.2.2⟩, rfl⟩
  have hc : Continuous fun t : unitInterval ↦ pt t.1 := by
    simp only [pt]
    fun_prop
  let g : C(unitInterval, SurfaceModel a b c) :=
    ⟨fun t ↦ qq a b c (pt t.1), continuousOn_qq.comp_continuous hc fun t ↦ (hcl _ (hpt t)).ok⟩
  have hinj : Function.Injective g := by
    intro s t hst
    have h₅ : pt s.1 = pt t.1 := eq_of_qq_eq (hcl _ (hpt s)) (hcl _ (hpt t)).ok hst
    apply Subtype.ext
    obtain ⟨h₆, h₇⟩ := Prod.ext_iff.mp h₅
    simp only [pt] at h₆ h₇
    have h₈ : (s.1 - t.1) * (z'.1 - z.1) = 0 := by linarith
    have h₉ : (s.1 - t.1) * (z'.2 - z.2) = 0 := by linarith
    by_contra hst'
    have h₁₀ : s.1 - t.1 ≠ 0 := sub_ne_zero.mpr hst'
    have h₁₁ := (mul_eq_zero.mp h₈).resolve_left h₁₀
    have h₁₂ := (mul_eq_zero.mp h₉).resolve_left h₁₀
    exact hne (Prod.ext (by linarith) (by linarith))
  have hL := GM11.isLineWithEnds_range g hinj
  have hr : range g = qq a b c '' sg z z' := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, hpt t, rfl⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨⟨s, hs.1, hs.2⟩, rfl⟩
  have h0 : g 0 = qq a b c z := by
    change qq a b c (pt 0) = _
    simp [pt]
  have h1 : g 1 = qq a b c z' := by
    change qq a b c (pt 1) = _
    simp [pt]
  rw [hr, h0, h1] at hL
  exact hL

/-- Two lines with the same ends, meeting only at the ends, form an `O`-arc. -/
theorem isOArc_of_lines {S : Type*} [TopologicalSpace S] [T2Space S] {L L' : Set S} {u v : S}
    (h : IsLineWithEnds L u v) (h' : IsLineWithEnds L' u v) (huv : L ∩ L' ⊆ {u, v}) :
    IsOArc (L ∪ L') := by
  obtain ⟨f, rfl, rfl⟩ := h
  obtain ⟨f', hf₀, hf₁⟩ := h'
  have hinj : ∀ {x y : unitInterval}, (f x).1 = (f y).1 → x = y := fun h ↦
    f.injective (Subtype.ext h)
  have hinj' : ∀ {x y : unitInterval}, (f' x).1 = (f' y).1 → x = y := fun h ↦
    f'.injective (Subtype.ext h)
  have hra : range (fun t ↦ (f t).1) = L := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hw
      exact ⟨f.symm ⟨w, hw⟩, by simp⟩
  have hrb : range (fun t ↦ (f' t).1) = L' := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact (f' t).2
    · intro hw
      exact ⟨f'.symm ⟨w, hw⟩, by simp⟩
  have := GraphMinor.Surface.oArc_of_two_arcs (a := fun t ↦ (f t).1) (b := fun t ↦ (f' t).1)
    ⟨continuous_subtype_val.comp f.continuous, fun _ _ h ↦ hinj h⟩
    ⟨continuous_subtype_val.comp f'.continuous, fun _ _ h ↦ hinj' h⟩ hf₀.symm hf₁.symm
    (fun s t hst ↦ by
      have hm : (f s).1 ∈ L ∩ L' := ⟨(f s).2, hst ▸ (f' t).2⟩
      rcases huv hm with h | h
      · left
        have hs : s = 0 := hinj h
        have ht : t = 0 := hinj' (by rw [hf₀, ← h, ← hst])
        exact ⟨hs, ht⟩
      · right
        have hs : s = 1 := hinj (mem_singleton_iff.mp h)
        have ht : t = 1 := hinj' (by rw [hf₁, ← mem_singleton_iff.mp h, ← hst])
        exact ⟨hs, ht⟩)
  rw [hra, hrb] at this
  exact this

end GraphMinor.GM20.Draw
