/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.Foundation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Separation in a thin centroid annulus with heavy balls

Formalizes the three geometric facts of the Lean route in
`docs/results/explicit-constant-gain-2026-10-18.md`. All points lie in the
annulus `ρ²(1-x) ≤ |p_i - c|² ≤ ρ²` about their centroid `c`, and every closed
ball of radius `r` about a point holds at least `m` points. If `n < 4m`, no
four points are pairwise farther than `2r`. If moreover
`nρ² < m((4 - 2x)ρ² - 13r²)`, no distance lies in `(2r, 4r]`. If
`9r² < 2ρ²(1-x)`, every point has at least `m` points farther than `2r`.

Two further facts serve Steps A_T and G3 of
`docs/results/refined-constant-gain-2026-10-19.md`. If every ball of radius `τ`
holds at least `m` points, `4τ ≤ θ`, and
`nρ² < m((ρ²(2-x) - τ²/2) + 2(ρ²(2-x) - (θ+τ)²/2))`, no point `z` has points
`a`, `b` with `|za| = |zb| ≤ θ < |ab|` (`no_isosceles_far_base_of_heavy_balls`);
and the number of points in a ball of radius `θ`, times `ρ²(2-x) - θ²/2`, is at
most `nρ²` (`configClosedBall_card_mul_le`).
-/

@[expose] public section

namespace Esgk

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Indices within distance `t` of the point with index `i`, including `i`. -/
noncomputable def ConfigClosedBall (p : Config n) (i : Fin n) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ dist (p i) (p j) ≤ t)

/-- Membership in `ConfigClosedBall` is the distance bound. -/
private lemma mem_configClosedBall {p : Config n} {i j : Fin n} {t : ℝ} :
    j ∈ ConfigClosedBall p i t ↔ dist (p i) (p j) ≤ t := by
  simp [ConfigClosedBall]

/-- Balls of radius `t` about two points farther apart than `2t` are disjoint. -/
private lemma configClosedBall_disjoint {p : Config n} {i j : Fin n} {t : ℝ}
    (h : 2 * t < dist (p i) (p j)) :
    Disjoint (ConfigClosedBall p i t) (ConfigClosedBall p j t) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [mem_configClosedBall] at hki hkj
  have htri := dist_triangle (p i) (p k) (p j)
  rw [dist_comm (p k) (p j)] at htri
  linarith

/-- The centred vectors sum to zero, so their inner products with a fixed one sum
to zero. -/
private lemma sum_inner_sub_center_eq_zero {p : Config n} {c : Point}
    (hsum : ∑ i, (p i - c) = 0) (a : Fin n) :
    ∑ q, ⟪p q - c, p a - c⟫ = 0 := by
  rw [← sum_inner, hsum, inner_zero_left]

/-- The difference of two centred vectors is the difference of the points. -/
private lemma norm_sub_center_sub (p q c : Point) : ‖(p - c) - (q - c)‖ = dist p q := by
  rw [sub_sub_sub_cancel_right, dist_eq_norm]

/-- A squared radius bound gives the radius bound for a centred vector. -/
private lemma norm_sub_center_le {p c : Point} {ρ : ℝ} (hρ : 0 < ρ)
    (h : dist p c ^ 2 ≤ ρ ^ 2) : ‖p - c‖ ≤ ρ := by
  rw [← dist_eq_norm]
  nlinarith [dist_nonneg (x := p) (y := c)]

/-- Cauchy–Schwarz lower bound for the inner product of vectors of norm at most
`r` and `s`. -/
private lemma neg_mul_le_inner {u w : Point} {r s : ℝ} (hu : ‖u‖ ≤ r) (hw : ‖w‖ ≤ s) :
    -(r * s) ≤ ⟪u, w⟫ := by
  have h1 := (abs_le.mp (abs_real_inner_le_norm u w)).1
  have h2 := mul_le_mul hu hw (norm_nonneg w) ((norm_nonneg u).trans hu)
  linarith

/-- Four pairwise far points would give four disjoint heavy balls. -/
theorem no_four_pairwise_far_of_heavy_balls {p : Config n} {r m : ℝ}
    (hball : ∀ i, m ≤ ((ConfigClosedBall p i r).card : ℝ))
    (hm : (n : ℝ) < 4 * m) :
    ∀ a b c d : Fin n,
      2 * r < dist (p a) (p b) → 2 * r < dist (p a) (p c) →
      2 * r < dist (p a) (p d) → 2 * r < dist (p b) (p c) →
      2 * r < dist (p b) (p d) → 2 * r < dist (p c) (p d) → False := by
  intro a b c d hab hac had hbc hbd hcd
  have hd : ∀ i j : Fin n, 2 * r < dist (p i) (p j) →
      Disjoint (ConfigClosedBall p i r) (ConfigClosedBall p j r) :=
    fun i j h ↦ configClosedBall_disjoint h
  have hcard := Finset.card_le_univ (ConfigClosedBall p a r ∪
    ConfigClosedBall p b r ∪ ConfigClosedBall p c r ∪ ConfigClosedBall p d r)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hd a d had, hd b d hbd⟩, hd c d hcd⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd a c hac, hd b c hbc⟩),
    Finset.card_union_of_disjoint (hd a b hab), Fintype.card_fin] at hcard
  have hcardR : ((ConfigClosedBall p a r).card : ℝ) + (ConfigClosedBall p b r).card +
      (ConfigClosedBall p c r).card + (ConfigClosedBall p d r).card ≤ n := by
    exact_mod_cast hcard
  linarith [hball a, hball b, hball c, hball d]

/-- A point within `s` of `q` gives a lower bound for the centred inner product. -/
private lemma inner_sub_center_ge {c u w : Point} {ρ x s : ℝ}
    (hu : ρ ^ 2 * (1 - x) ≤ dist u c ^ 2) (hw : ρ ^ 2 * (1 - x) ≤ dist w c ^ 2)
    (h : dist u w ≤ s) :
    ρ ^ 2 * (1 - x) - s ^ 2 / 2 ≤ ⟪u - c, w - c⟫ := by
  have hsq := norm_sub_sq_real (u - c) (w - c)
  rw [norm_sub_center_sub, ← dist_eq_norm, ← dist_eq_norm] at hsq
  have hs : dist u w ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
  linarith

/-- Distance gap: two disjoint heavy balls near one point of the annulus would
move the centroid away from `c`. -/
theorem annulus_distance_gap_of_heavy_balls {p : Config n} {c : Point} {ρ x r m : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hball : ∀ i, m ≤ ((ConfigClosedBall p i r).card : ℝ))
    (hr : 25 * r ^ 2 ≤ 2 * (2 - x) * ρ ^ 2)
    (hm : (n : ℝ) * ρ ^ 2 < m * ((4 - 2 * x) * ρ ^ 2 - 13 * r ^ 2)) :
    ∀ a b : Fin n, dist (p a) (p b) ≤ 4 * r → dist (p a) (p b) ≤ 2 * r := by
  intro a b hab4
  by_contra hfar
  rw [not_le] at hfar
  have hle : ∀ i, ‖p i - c‖ ≤ ρ := fun i ↦ norm_sub_center_le hρ (hhi i)
  set f : Fin n → ℝ := fun q ↦ ⟪p q - c, p a - c⟫ + ρ ^ 2 with hf
  set Ka : ℝ := ρ ^ 2 * (2 - x) - r ^ 2 / 2 with hKa
  set Kb : ℝ := ρ ^ 2 * (2 - x) - 25 * r ^ 2 / 2 with hKb
  have hf0 : ∀ q, 0 ≤ f q := fun q ↦ by
    have := neg_mul_le_inner (hle q) (hle a)
    simp only [hf]; nlinarith
  have hA : ∀ q ∈ ConfigClosedBall p a r, Ka ≤ f q := by
    intro q hq
    rw [mem_configClosedBall, dist_comm] at hq
    have := inner_sub_center_ge (hlo q) (hlo a) hq
    simp only [hf, hKa]; linarith
  have hB : ∀ q ∈ ConfigClosedBall p b r, Kb ≤ f q := by
    intro q hq
    rw [mem_configClosedBall] at hq
    have hqa : dist (p q) (p a) ≤ 5 * r := by
      have htri := dist_triangle (p q) (p b) (p a)
      rw [dist_comm (p q) (p b), dist_comm (p b) (p a)] at htri
      linarith
    have := inner_sub_center_ge (hlo q) (hlo a) hqa
    simp only [hf, hKb]; linarith
  have hdisj : Disjoint (ConfigClosedBall p a r) (ConfigClosedBall p b r) :=
    configClosedBall_disjoint hfar
  have hsA := Finset.card_nsmul_le_sum _ f Ka hA
  have hsB := Finset.card_nsmul_le_sum _ f Kb hB
  rw [nsmul_eq_mul] at hsA hsB
  have hup := Finset.sum_le_univ_sum_of_nonneg
    (s := ConfigClosedBall p a r ∪ ConfigClosedBall p b r) hf0
  rw [Finset.sum_union hdisj] at hup
  have htot : ∑ q, f q = n * ρ ^ 2 := by
    simp only [hf, Finset.sum_add_distrib, sum_inner_sub_center_eq_zero hsum a,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  have hKb0 : 0 ≤ Kb := by simp only [hKb]; linarith
  have hKa0 : 0 ≤ Ka := by simp only [hKa]; nlinarith [sq_nonneg r]
  have hmA := mul_le_mul_of_nonneg_right (hball a) hKa0
  have hmB := mul_le_mul_of_nonneg_right (hball b) hKb0
  have hK : m * ((4 - 2 * x) * ρ ^ 2 - 13 * r ^ 2) = m * Ka + m * Kb := by
    simp only [hKa, hKb]; ring
  linarith

/-- Every point has a point on the far side of the centroid, and that point's
heavy ball is far from it. -/
theorem far_points_card_ge_of_heavy_balls {p : Config n} {c : Point} {ρ x r m : ℝ}
    (hsum : ∑ i, (p i - c) = 0)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hr : 9 * r ^ 2 < 2 * ρ ^ 2 * (1 - x))
    (hball : ∀ i, m ≤ ((ConfigClosedBall p i r).card : ℝ)) :
    ∀ a : Fin n, m ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ 2 * r < dist (p a) (p q))).card : ℝ) := by
  intro a
  have : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun q ↦ ⟪p q - c, p a - c⟫) (g := fun _ ↦ (0 : ℝ)) Finset.univ_nonempty
    (by rw [sum_inner_sub_center_eq_zero hsum a, Finset.sum_const_zero])
  have hsq := norm_sub_sq_real (p a - c) (p b - c)
  rw [norm_sub_center_sub, real_inner_comm, ← dist_eq_norm, ← dist_eq_norm] at hsq
  have hfar : 3 * r < dist (p a) (p b) := by
    by_contra h
    rw [not_lt] at h
    nlinarith [hlo a, hlo b, dist_nonneg (x := p a) (y := p b)]
  have hsub : ConfigClosedBall p b r ⊆
      (Finset.univ : Finset (Fin n)).filter (fun q ↦ 2 * r < dist (p a) (p q)) := by
    intro q hq
    rw [mem_configClosedBall] at hq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ q, ?_⟩
    have htri := dist_triangle (p a) (p q) (p b)
    rw [dist_comm (p q) (p b)] at htri
    linarith
  calc m ≤ ((ConfigClosedBall p b r).card : ℝ) := hball b
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- Isosceles exclusion: if every ball of radius `τ` about a point holds at least `m`
points, no point `z` has two points `a`, `b` at a common distance at most `θ` from it
with `θ < |ab|`. The three disjoint heavy balls about `z`, `a` and `b` would carry
more than the total centroid weight `nρ²`. -/
theorem no_isosceles_far_base_of_heavy_balls {p : Config n} {c : Point} {ρ x τ θ m : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hball : ∀ i, m ≤ ((ConfigClosedBall p i τ).card : ℝ))
    (hτ : 0 ≤ τ) (hθ : 4 * τ ≤ θ) (hθρ : (θ + τ) ^ 2 ≤ 2 * (2 - x) * ρ ^ 2)
    (hm : (n : ℝ) * ρ ^ 2 <
      m * ((ρ ^ 2 * (2 - x) - τ ^ 2 / 2) + 2 * (ρ ^ 2 * (2 - x) - (θ + τ) ^ 2 / 2))) :
    ∀ z a b : Fin n, dist (p z) (p a) = dist (p z) (p b) → dist (p z) (p a) ≤ θ →
      θ < dist (p a) (p b) → False := by
  intro z a b hzab hza hab
  have hle : ∀ i, ‖p i - c‖ ≤ ρ := fun i ↦ norm_sub_center_le hρ (hhi i)
  have hab2 : dist (p a) (p b) ≤ 2 * dist (p z) (p a) := by
    have htri := dist_triangle (p a) (p z) (p b)
    rw [dist_comm (p a) (p z), ← hzab] at htri
    linarith
  set f : Fin n → ℝ := fun q ↦ ⟪p q - c, p z - c⟫ + ρ ^ 2 with hf
  set K₁ : ℝ := ρ ^ 2 * (2 - x) - τ ^ 2 / 2 with hK₁
  set K₂ : ℝ := ρ ^ 2 * (2 - x) - (θ + τ) ^ 2 / 2 with hK₂
  have hf0 : ∀ q, 0 ≤ f q := fun q ↦ by
    have := neg_mul_le_inner (hle q) (hle z)
    simp only [hf]; nlinarith
  have hZ : ∀ q ∈ ConfigClosedBall p z τ, K₁ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall, dist_comm] at hq
    have := inner_sub_center_ge (hlo q) (hlo z) hq
    simp only [hf, hK₁]; linarith
  have hA : ∀ q ∈ ConfigClosedBall p a τ, K₂ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall] at hq
    have hqz : dist (p q) (p z) ≤ θ + τ := by
      have htri := dist_triangle (p q) (p a) (p z)
      rw [dist_comm (p q) (p a), dist_comm (p a) (p z)] at htri
      linarith
    have := inner_sub_center_ge (hlo q) (hlo z) hqz
    simp only [hf, hK₂]; linarith
  have hB : ∀ q ∈ ConfigClosedBall p b τ, K₂ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall] at hq
    have hqz : dist (p q) (p z) ≤ θ + τ := by
      have htri := dist_triangle (p q) (p b) (p z)
      rw [dist_comm (p q) (p b), dist_comm (p b) (p z), ← hzab] at htri
      linarith
    have := inner_sub_center_ge (hlo q) (hlo z) hqz
    simp only [hf, hK₂]; linarith
  have hza2 : 2 * τ < dist (p z) (p a) := by linarith
  have hzb2 : 2 * τ < dist (p z) (p b) := by rw [← hzab]; exact hza2
  have hab2' : 2 * τ < dist (p a) (p b) := by linarith
  have hdZA := configClosedBall_disjoint hza2
  have hdZB := configClosedBall_disjoint hzb2
  have hdAB := configClosedBall_disjoint hab2'
  have hsZ := Finset.card_nsmul_le_sum _ f K₁ hZ
  have hsA := Finset.card_nsmul_le_sum _ f K₂ hA
  have hsB := Finset.card_nsmul_le_sum _ f K₂ hB
  rw [nsmul_eq_mul] at hsZ hsA hsB
  have hup := Finset.sum_le_univ_sum_of_nonneg
    (s := ConfigClosedBall p z τ ∪ ConfigClosedBall p a τ ∪ ConfigClosedBall p b τ) hf0
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdZB, hdAB⟩),
    Finset.sum_union hdZA] at hup
  have htot : ∑ q, f q = n * ρ ^ 2 := by
    simp only [hf, Finset.sum_add_distrib, sum_inner_sub_center_eq_zero hsum z,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  have hK₂0 : 0 ≤ K₂ := by simp only [hK₂]; linarith
  have hττ : τ ^ 2 ≤ (θ + τ) ^ 2 := pow_le_pow_left₀ hτ (by linarith) 2
  have hK₁0 : 0 ≤ K₁ := by simp only [hK₁]; linarith
  have hmZ := mul_le_mul_of_nonneg_right (hball z) hK₁0
  have hmA := mul_le_mul_of_nonneg_right (hball a) hK₂0
  have hmB := mul_le_mul_of_nonneg_right (hball b) hK₂0
  have hK : m * (K₁ + 2 * K₂) = m * K₁ + m * K₂ + m * K₂ := by ring
  linarith

/-- Ball count: the number of points in the closed ball of radius `θ` about a point
of the annulus, times `ρ²(2-x) - θ²/2`, is at most the total centroid weight `nρ²`. -/
theorem configClosedBall_card_mul_le {p : Config n} {c : Point} {ρ x θ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n) :
    ((ConfigClosedBall p z θ).card : ℝ) * (ρ ^ 2 * (2 - x) - θ ^ 2 / 2) ≤ (n : ℝ) * ρ ^ 2 := by
  have hle : ∀ i, ‖p i - c‖ ≤ ρ := fun i ↦ norm_sub_center_le hρ (hhi i)
  set f : Fin n → ℝ := fun q ↦ ⟪p q - c, p z - c⟫ + ρ ^ 2 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q ↦ by
    have := neg_mul_le_inner (hle q) (hle z)
    simp only [hf]; nlinarith
  have hZ : ∀ q ∈ ConfigClosedBall p z θ, ρ ^ 2 * (2 - x) - θ ^ 2 / 2 ≤ f q := by
    intro q hq
    rw [mem_configClosedBall, dist_comm] at hq
    have := inner_sub_center_ge (hlo q) (hlo z) hq
    simp only [hf]; linarith
  have hsZ := Finset.card_nsmul_le_sum _ f _ hZ
  rw [nsmul_eq_mul] at hsZ
  have hup := Finset.sum_le_univ_sum_of_nonneg (s := ConfigClosedBall p z θ) hf0
  have htot : ∑ q, f q = n * ρ ^ 2 := by
    simp only [hf, Finset.sum_add_distrib, sum_inner_sub_center_eq_zero hsum z,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  linarith

end Esgk
