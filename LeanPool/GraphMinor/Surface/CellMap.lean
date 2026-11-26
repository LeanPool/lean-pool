/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.EdgeLoop
public import LeanPool.GraphMinor.Surface.WordRules

/-!
# A closed disc as a polygon

A closed disc whose boundary is a cyclic list of arcs is the image of the unit disc, with the sides
of the round
polygon sent to these arcs by their parameters (`exists_cell_map`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem sd_injOn {a : 𝕀 → X} (ha : IsArcMap a) (b : Bool) : InjOn (sd a b) (Icc 0 1) := by
  have h : InjOn (extI a) (Icc 0 1) := extI_injOn ha.2
  intro x hx y hy he
  cases b
  · rw [sd_false, sd_false] at he
    have := h ⟨by linarith [hx.2], by linarith [hx.1]⟩ ⟨by linarith [hy.2], by linarith [hy.1]⟩ he
    linarith
  · rw [sd_true, sd_true] at he
    exact h hx hy he

omit [T2Space X] in
theorem exists_cell_map {Φ : Set X} (hΦ : IsClosedDisc Φ) {m : ℕ} (hm : 0 < m) (a : ℕ → 𝕀 → X)
  (b : ℕ → Bool)
    (ha : ∀ p < m, IsArcMap (a p))
    (hadj : ∀ p, p + 1 < m → sd (a p) (b p) 1 = sd (a (p + 1)) (b (p + 1)) 0)
    (hclose : sd (a (m - 1)) (b (m - 1)) 1 = sd (a 0) (b 0) 0)
    (hdis : ∀ p < m, ∀ q < m, p ≠ q → ∀ u ∈ Ico (0 : ℝ) 1, ∀ v ∈ Ico (0 : ℝ) 1,
      sd (a p) (b p) u ≠ sd (a q) (b q) v)
    (hsub : ∀ p < m, range (a p) ⊆ discBd Φ) (hcov : discBd Φ ⊆ ⋃ p ∈ Iio m, range (a p)) :
    ∃ Ψ : ℂ → X, ContinuousOn Ψ (closedBall 0 1) ∧ InjOn Ψ (closedBall 0 1) ∧ Ψ '' closedBall 0 1
      = Φ ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, Ψ z ∈ discBd Φ ↔ ‖z‖ = 1) ∧
      ∀ p < m, ∀ t ∈ Icc (0 : ℝ) 1, Ψ (sdPt m p (b p) t) = extI (a p) t := by
  classical
  obtain ⟨h, g, c⟩ := hΦ.exists_isChart
  let β : ℝ → X := walkMap m a b
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hβc : ContinuousOn β (Icc 0 m) := continuousOn_walkMap hm (fun p hp => (ha p hp).1) hadj
  have hpos : ∀ x ∈ Icc (0 : ℝ) m, ∃ p < m, x ∈ Icc (p : ℝ) (p + 1) ∧ β x = sd (a p) (b p) (x - p) ∧
      (x < m → x < p + 1) := by
    intro x hx
    refine ⟨min ⌊x⌋₊ (m - 1), by omega, ?_, rfl, fun hxm => ?_⟩
    · have hle : ⌊x⌋₊ ≤ x := Nat.floor_le hx.1
      have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
      by_cases h1 : ⌊x⌋₊ ≤ m - 1
      · rw [min_eq_left h1]
        exact ⟨hle, hlt.le⟩
      · have h2 : ⌊x⌋₊ = m := by
          have : ⌊x⌋₊ ≤ m := Nat.floor_le_of_le hx.2
          omega
        have h3 : ((m - 1 : ℕ) : ℝ) = m - 1 := by
          rw [Nat.cast_sub hm]
          simp
        rw [min_eq_right (by omega), h3]
        rw [h2] at hle
        constructor <;> linarith [hx.2]
    · have h1 : ⌊x⌋₊ ≤ m - 1 := by
        have := Nat.floor_lt hx.1 |>.mpr hxm
        omega
      rw [min_eq_left h1]
      exact Nat.lt_floor_add_one x
  have himg : ∀ x ∈ Icc (0 : ℝ) m, β x ∈ discBd Φ := fun x hx => by
    obtain ⟨p, hp, -, e, -⟩ := hpos x hx
    rw [e]
    exact hsub p hp ⟨_, rfl⟩
  have hsdim : ∀ p < m, ∀ t ∈ Icc (0 : ℝ) 1, sd (a p) (b p) (if b p then t else 1 - t) = extI
    (a p) t := fun p _ t _ => by
    cases b p
    · simp [sd]
    · simp [sd]
  have hβat : ∀ p < m, ∀ t ∈ Icc (0 : ℝ) 1, (p + if b p then t else 1 - t) ∈ Icc (0 : ℝ) m ∧
      β (p + if b p then t else 1 - t) = extI (a p) t := fun p hp t ht => by
    have hp1 : (p : ℝ) + 1 ≤ m := by exact_mod_cast hp
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h01 : (if b p then t else 1 - t) ∈ Icc (0 : ℝ) 1 := by
      cases b p
      · simpa using ⟨ht.2, ht.1⟩
      · simpa using ht
    have hin : (p + if b p then t else 1 - t) ∈ Icc (p : ℝ) (p + 1) := ⟨by linarith [h01.1], by
      linarith [h01.2]⟩
    refine ⟨⟨by linarith [h01.1], by linarith [h01.2]⟩, ?_⟩
    rw [show β (p + if b p then t else 1 - t) = _ from walkMap_eq hm hadj hp hin,
      add_sub_cancel_left]
    exact hsdim p hp t ht
  have hβr : β '' Icc 0 m = discBd Φ := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact himg x hx
    · intro y hy
      obtain ⟨p, hp, t, rfl⟩ : ∃ p < m, ∃ t, y = a p t := by
        have := hcov hy
        simp only [mem_iUnion, exists_prop] at this
        obtain ⟨p, hp, t, ht⟩ := this
        exact ⟨p, hp, t, ht.symm⟩
      obtain ⟨h1, h2⟩ := hβat p hp t t.2
      exact ⟨_, h1, h2.trans (extI_coe _ _)⟩
  have hβi : InjOn β (Ico 0 m) := by
    intro x hx y hy he
    obtain ⟨p, hp, hxp, e1, l1⟩ := hpos x ⟨hx.1, hx.2.le⟩
    obtain ⟨q, hq, hyq, e2, l2⟩ := hpos y ⟨hy.1, hy.2.le⟩
    have hu : x - p ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hxp.1], by linarith [l1 hx.2]⟩
    have hv : y - q ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hyq.1], by linarith [l2 hy.2]⟩
    have he' : sd (a p) (b p) (x - p) = sd (a q) (b q) (y - q) := by rw [← e1, ← e2, he]
    by_cases hpq : p = q
    · subst hpq
      have := sd_injOn (ha p hp) (b p) ⟨hu.1, hu.2.le⟩ ⟨hv.1, hv.2.le⟩ he'
      linarith
    · exact absurd he' (hdis p hp q hq hpq _ hu _ hv)
  have h0m : β 0 = β m := by
    have e1 := walkMap_eq (x := 0) hm hadj hm ⟨by simp, by simp⟩
    have e2 := walkMap_eq (x := m) hm hadj (p := m - 1) (by omega) ⟨by rw [Nat.cast_sub hm]; simp,
      by
      rw [Nat.cast_sub hm]; simp⟩
    have e3 : (m : ℝ) - ((m - 1 : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_sub hm]
      simp
    change walkMap m a b 0 = walkMap m a b m
    rw [e1, e2, e3, hclose]
    simp
  have hcm : ContinuousOn (fun x => h (β x)) (Icc 0 m) :=
    c.hc.comp hβc fun x hx => discBd_subset _ (himg x hx)
  have hii : InjOn (fun x => h (β x)) (Ico 0 m) := fun x hx y hy he => by
    have hx' := himg x ⟨hx.1, hx.2.le⟩
    have hy' := himg y ⟨hy.1, hy.2.le⟩
    refine hβi hx hy ?_
    rw [← c.gh (discBd_subset _ hx'), ← c.gh (discBd_subset _ hy')]
    exact congrArg g he
  have hrr : (fun x => h (β x)) '' Icc 0 m = discBd (closedBall (0 : ℂ) 1) := by
    rw [isClosedDisc_closedBall.2, ← c.bd, ← hβr, image_image]
  obtain ⟨Θ, Θ', hmt, hval⟩ := exists_polygon_map isClosedDisc_closedBall.1 hm hcm hii
    (by simp only [h0m]) hrr
  have hΨv : ∀ x ∈ Icc (0 : ℝ) m, g (Θ (per m x)) = β x := fun x hx => by
    rw [hval x hx]
    exact c.gh (discBd_subset _ (himg x hx))
  have hΨinj : InjOn (fun z => g (Θ z)) (closedBall 0 1) := fun x hx y hy he => by
    have h1 : Θ x = Θ y := by
      rw [← c.hg (hmt.1 hx), ← c.hg (hmt.1 hy)]
      exact congrArg h he
    rw [← hmt.2.2.1 hx, ← hmt.2.2.1 hy, h1]
  refine ⟨fun z => g (Θ z), c.gc.comp hmt.2.2.2.2.1 hmt.1, hΨinj, ?_, ?_, ?_⟩
  · apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact c.gm (hmt.1 hz)
    · intro y hy
      have h1 := c.hm hy
      refine ⟨Θ' (h y), hmt.2.1 h1, ?_⟩
      change g (Θ (Θ' (h y))) = y
      rw [hmt.2.2.2.1 h1]
      exact c.gh hy
  · intro z hz
    constructor
    · intro hb
      obtain ⟨x, hx, e⟩ := hβr.symm ▸ hb
      have hxp : per m x ∈ closedBall (0 : ℂ) 1 := by simpa using (norm_per m x).le
      have h1 : per m x = z := hΨinj hxp hz ((hΨv x hx).trans e)
      rw [← h1]
      exact norm_per m x
    · intro hn
      have h1 : z ∈ sphere (0 : ℂ) 1 := by simpa using hn
      rw [← per_image hm] at h1
      obtain ⟨x, hx, rfl⟩ := h1
      change g (Θ (per m x)) ∈ _
      rw [hΨv x hx]
      exact himg x hx
  · intro p hp t ht
    obtain ⟨h1, h2⟩ := hβat p hp t ht
    change g (Θ (sdPt m p (b p) t)) = _
    rw [sdPt, hΨv _ h1, h2]

end GraphMinor.Surface
