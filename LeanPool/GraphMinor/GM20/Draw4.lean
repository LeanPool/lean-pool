/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw3

/-!
# Drawing a graph in a surface of large genus: a swap with a handle

The `k`th handle pastes the circles around `(6k, 0)` and `(6k + 3, 0)`. The top point of the first
circle is
pasted to the bottom point of the second. One curve passes below the first circle, up through the
gap
between the circles, and above the second circle. The other curve comes in above, goes into the top
point of the first circle, and leaves from the bottom point of the second circle. So the two curves
swap heights and do not meet.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

theorem ok_of_abs {x y : ℝ} (h : 1 ≤ |y|) : Ok a b c (x, y) := by
  intro i _
  have h₁ : 1 ≤ y ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have h₂ := sq_nonneg (x - 3 * i)
  simp only
  linarith

/-- If a point is outside the open discs but not outside the closed discs, it is on a circle. -/
theorem exists_circle {z : ℝ × ℝ} (h : Ok a b c z) (hc : ¬ Clear a b c z) :
    ∃ j < 2 * a + b + c, (z.1 - 3 * j) ^ 2 + z.2 ^ 2 = 1 := by
  unfold Clear at hc
  simp only [not_forall, not_lt] at hc
  obtain ⟨j, hj, h₁⟩ := hc
  exact ⟨j, hj, le_antisymm h₁ (h j hj)⟩

theorem bound_of_circle {z : ℝ × ℝ} {j : ℕ} (hz : (z.1 - 3 * j) ^ 2 + z.2 ^ 2 = 1) :
    3 * (j : ℝ) - 1 ≤ z.1 ∧ z.1 ≤ 3 * j + 1 := by
  have h₁ := sq_nonneg z.2
  constructor <;> nlinarith

theorem grp_of_lt {j : ℕ} (h : j < 2 * a) : grp a j = j / 2 := ite_eq_left h

theorem grp_of_ge {j : ℕ} (h : 2 * a ≤ j) : grp a j = j := ite_eq_right (by omega)

/-- A point of the model on a handle circle has preimages only near that handle. -/
theorem handle_side {k I : ℕ} (hk : k < a) (hI : I = 2 * k ∨ I = 2 * k + 1) {w z : ℝ × ℝ}
    (hw : (w.1 - 3 * I) ^ 2 + w.2 ^ 2 = 1) (hwok : Ok a b c w) (hz : Ok a b c z)
    (heq : qq a b c z = qq a b c w) :
    6 * (k : ℝ) - 1 ≤ z.1 ∧ z.1 ≤ 6 * k + 4 := by
  have hIc : (I : ℝ) = 2 * k ∨ (I : ℝ) = 2 * k + 1 := by
    rcases hI with rfl | rfl
    · left; push_cast; ring
    · right; push_cast; ring
  have hIlt : I < 2 * a + b + c := by omega
  by_cases hc : Clear a b c z
  · have h₁ := eq_of_qq_eq hc hwok heq
    subst h₁
    obtain ⟨h₂, h₃⟩ := bound_of_circle hw
    rcases hIc with h₄ | h₄ <;> rw [h₄] at h₂ h₃ <;> constructor <;> linarith
  · obtain ⟨j, hj, hzj⟩ := exists_circle hz hc
    have h₁ := congrArg keyM heq
    rw [keyM_circle hj hz hzj, keyM_circle hIlt hwok hw] at h₁
    have h₂ : grp a j = grp a I := by
      have := Sum.inl.inj (Option.some.inj h₁)
      exact (Prod.ext_iff.mp this).1
    rw [grp_of_lt (show I < 2 * a by omega)] at h₂
    have hI2 : I / 2 = k := by omega
    rw [hI2] at h₂
    have hj' : j < 2 * a := by
      by_contra hge
      rw [grp_of_ge (by omega)] at h₂
      omega
    rw [grp_of_lt hj'] at h₂
    have hjc : (j : ℝ) = 2 * k ∨ (j : ℝ) = 2 * k + 1 := by
      have : j = 2 * k ∨ j = 2 * k + 1 := by omega
      rcases this with rfl | rfl
      · left; push_cast; ring
      · right; push_cast; ring
    obtain ⟨h₃, h₄⟩ := bound_of_circle hzj
    rcases hjc with h₅ | h₅ <;> rw [h₅] at h₃ h₄ <;> constructor <;> linarith

/-- The top point of the first circle of a handle has the same image as the bottom point of the
second. -/
theorem qq_handle {k : ℕ} (hk : k < a) :
    qq a b c (6 * (k : ℝ), 1) = qq a b c (6 * (k : ℝ) + 3, -1) := by
  have h₁ : Ok a b c (6 * (k : ℝ), 1) := ok_of_abs (by simp)
  have h₂ : Ok a b c (6 * (k : ℝ) + 3, -1) := ok_of_abs (by simp)
  rw [qq_of_ok h₁, qq_of_ok h₂]
  refine Quot.sound (ModelGlue.handle k hk !₂[0, 1] ?_ _ _ ?_ ?_)
  · have : ‖(!₂[0, 1] : EuclideanPlane)‖ ^ 2 = 1 := by
      rw [norm_sq]
      simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  · refine congrArg (fun x : EuclideanPlane ↦ (x : OnePoint EuclideanPlane)) ?_
    ext j
    fin_cases j
    · simp [pl, modelCentre]
      ring
    · simp [pl, modelCentre]
  · refine congrArg (fun x : EuclideanPlane ↦ (x : OnePoint EuclideanPlane)) ?_
    ext j
    fin_cases j
    · simp [pl, modelCentre, modelMirror]
      ring
    · simp [pl, modelCentre, modelMirror]

/-- The slope of the strand as it goes up across the gap of the handle. -/
noncomputable def mu (k : ℕ) (x : ℝ) : ℝ := max 0 (min 1 (x - (6 * k + 1)))

theorem continuous_mu (k : ℕ) : Continuous (mu k) := by
  unfold mu
  fun_prop

theorem mu_nonneg (k : ℕ) (x : ℝ) : 0 ≤ mu k x := le_max_left _ _

theorem mu_le_one (k : ℕ) (x : ℝ) : mu k x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem mu_zero {k : ℕ} {x : ℝ} (h : x ≤ 6 * k + 1) : mu k x = 0 := by
  unfold mu
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem mu_one {k : ℕ} {x : ℝ} (h : 6 * (k : ℝ) + 2 ≤ x) : mu k x = 1 := by
  unfold mu
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

theorem band_interp {v t A' y : ℝ} (h₀ : 0 ≤ v) (h₁ : v ≤ 1) (hA₁ : t ≤ A') (hA₂ : A' ≤ t + 1)
    (hy₁ : -5 / 4 ≤ y) (hy₂ : y ≤ 5 / 4) :
    (1 - v) * t + v * (-5 / 4) ≤ (1 - v) * A' + v * y ∧
      (1 - v) * A' + v * y ≤ (1 - v) * (t + 1) + v * (5 / 4) := by
  have h₂ := mul_le_mul_of_nonneg_left hA₁ (sub_nonneg.mpr h₁)
  have h₃ := mul_le_mul_of_nonneg_left hA₂ (sub_nonneg.mpr h₁)
  have h₄ := mul_le_mul_of_nonneg_left hy₁ h₀
  have h₅ := mul_le_mul_of_nonneg_left hy₂ h₀
  constructor <;> linarith

theorem mix_bounds {m s t : ℝ} (h₀ : 0 ≤ m) (h₁ : m ≤ 1) (h : s ≤ t) :
    s ≤ (1 - m) * s + m * t ∧ (1 - m) * s + m * t ≤ t := by
  constructor <;> nlinarith

private theorem handle_bands_disjoint {l r t : ℝ} {k : ℕ} :
    let u : ℝ → ℝ := lam l r
    let Q : ℝ → ℝ := fun x ↦ (1 - u x) * ((1 - mu k x) * t + mu k x * (t + 1)) +
      u x * ((1 - mu k x) * (-5 / 4) + mu k x * (5 / 4))
    let A : ℝ → ℝ := fun x ↦ (1 - u x) * (t + 1) + u x * (1 + (6 * k - x) / 6)
    let B : ℝ → ℝ := fun x ↦ (1 - u x) * t + u x * (-1 - (x - 6 * k - 3) / 6)
    (∀ x ∈ Icc l r, Clear a b c (x, Q x)) →
    (∀ x ∈ Icc l (6 * (k : ℝ)), Ok a b c (x, A x)) →
    (∀ x ∈ Icc (6 * (k : ℝ) + 3) r, Ok a b c (x, B x)) →
    Disjoint (qq a b c '' gr Q l r)
      (qq a b c '' (gr A l (6 * (k : ℝ)) ∪ gr B (6 * (k : ℝ) + 3) r)) := by
  intro u Q A B hQclear hAok hBok
  have hu₀ : ∀ x, 0 ≤ u x := lam_nonneg l r
  have hu₁ : ∀ x, u x ≤ 1 := lam_le_one l r
  refine Disjoint.symm (disjoint_of_below ?_ ?_ ?_)
  · rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hAok x hx
    · exact hBok x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact hQclear x hx
  · rw [Set.disjoint_left]
    rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) ⟨x', hx', h⟩
    · obtain ⟨rfl, h₂⟩ := Prod.ext_iff.mp h
      simp only at h₂
      have hm : mu k x' = 0 := mu_zero (by linarith [hx.2])
      have h₃ : Q x' < A x' := by
        have h₄ := interp_lt (A := t) (A' := t + 1) (B := -5 / 4)
          (B' := 1 + (6 * k - x') / 6) (hu₀ x') (hu₁ x') (by linarith)
          (by linarith [hx.2])
        have h₅ : Q x' = (1 - u x') * t + u x' * (-5 / 4) := by
          change (1 - u x') * ((1 - mu k x') * t + mu k x' * (t + 1)) +
            u x' * ((1 - mu k x') * (-5 / 4) + mu k x' * (5 / 4)) = _
          rw [hm]
          ring
        rw [h₅]
        exact h₄
      exact h₃.ne h₂
    · obtain ⟨rfl, h₂⟩ := Prod.ext_iff.mp h
      simp only at h₂
      have hm : mu k x' = 1 := mu_one (by linarith [hx.1])
      have hb₁ : (-1 - (x' - 6 * k - 3) / 6 : ℝ) ≤ -1 := by linarith [hx.1]
      have h₃ : B x' < Q x' := by
        have h₄ := interp_lt (A := t) (A' := t + 1) (B := -1 - (x' - 6 * k - 3) / 6)
          (B' := 5 / 4) (hu₀ x') (hu₁ x') (by linarith) (by linarith)
        have h₅ : Q x' = (1 - u x') * (t + 1) + u x' * (5 / 4) := by
          change (1 - u x') * ((1 - mu k x') * t + mu k x' * (t + 1)) +
            u x' * ((1 - mu k x') * (-5 / 4) + mu k x' * (5 / 4)) = _
          rw [hm]
          ring
        rw [h₅]
        exact h₄
      exact h₃.ne' h₂

private theorem handle_bands_intersection {l r : ℝ} {k : ℕ} (hk : k < a) {A B : ℝ → ℝ}
    (hA6 : A (6 * (k : ℝ)) = 1) (hB6 : B (6 * (k : ℝ) + 3) = -1)
    (hAok : ∀ x ∈ Icc l (6 * (k : ℝ)), Ok a b c (x, A x))
    (hBclear : ∀ x ∈ Icc (6 * (k : ℝ) + 3) r, x ≠ 6 * (k : ℝ) + 3 → Clear a b c (x, B x))
    (hLin : qq a b c (6 * (k : ℝ), 1) ∈ qq a b c '' gr A l (6 * (k : ℝ)))
    (hRin : qq a b c (6 * (k : ℝ), 1) ∈ qq a b c '' gr B (6 * (k : ℝ) + 3) r) :
    (qq a b c '' gr A l (6 * (k : ℝ))) ∩ (qq a b c '' gr B (6 * (k : ℝ) + 3) r) =
      {qq a b c (6 * (k : ℝ), 1)} := by
  ext w
  constructor
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, ⟨_, ⟨x', hx', rfl⟩, heq⟩⟩
    by_cases h₁ : x = 6 * (k : ℝ)
    · subst h₁
      simp [hA6]
    by_cases h₂ : x' = 6 * (k : ℝ) + 3
    · subst h₂
      have heq' : qq a b c (6 * (k : ℝ) + 3, B (6 * (k : ℝ) + 3)) = qq a b c (x, A x) := heq
      rw [hB6] at heq'
      change qq a b c (x, A x) = qq a b c (6 * (k : ℝ), 1)
      rw [← heq', ← qq_handle hk]
    · have := eq_of_qq_eq (hBclear x' hx' h₂) (hAok x hx) heq
      have h₃ := congrArg Prod.fst this
      simp only at h₃
      linarith [hx.2, hx'.1]
  · rintro rfl
    exact ⟨hLin, hRin⟩

/-- The swap of heights `i` and `i + 1` with the `k`th handle. -/
theorem slab_handle [T2Space (SurfaceModel a b c)] {n k : ℕ} (hk : k < a) (i : Fin n) :
    Slab a b c (n + 1) (6 * k - 3 / 2) (6 * k + 9 / 2)
      (Equiv.swap i.castSucc i.succ) := by
  classical
  set l : ℝ := 6 * k - 3 / 2 with hl
  set r : ℝ := 6 * k + 9 / 2 with hr
  set t : ℝ := ((i : ℕ) : ℝ) with ht
  have hlr : l < r := by rw [hl, hr]; linarith
  have hcl := continuous_lam l r
  have hcm := continuous_mu k
  let u : ℝ → ℝ := lam l r
  have hu₀ : ∀ x, 0 ≤ u x := lam_nonneg l r
  have hu₁ : ∀ x, u x ≤ 1 := lam_le_one l r
  have hum : ∀ {x}, 6 * (k : ℝ) - 5 / 4 ≤ x → x ≤ 6 * k + 17 / 4 → u x = 1 := fun h₁ h₂ ↦
    lam_eq_one (by rw [hl]; linarith) (by rw [hr]; linarith)
  have hgap : ∀ x ∈ Icc l r, lam l r x < 1 → ∀ y, Clear a b c (x, y) := by
    intro x hx hlt y
    rw [hl, hr] at hx
    rcases lam_lt_one hlt with h | h
    · refine clear_of_gap (2 * (k : ℤ) - 1) ?_ ?_ <;> push_cast <;> rw [hl] at h <;> linarith [hx.1]
    · refine clear_of_gap (2 * (k : ℤ) + 1) ?_ ?_ <;> push_cast <;> rw [hr] at h <;> linarith [hx.2]
  let Q : ℝ → ℝ := fun x ↦ (1 - u x) * ((1 - mu k x) * t + mu k x * (t + 1)) +
    u x * ((1 - mu k x) * (-5 / 4) + mu k x * (5 / 4))
  let A : ℝ → ℝ := fun x ↦ (1 - u x) * (t + 1) + u x * (1 + (6 * k - x) / 6)
  let B : ℝ → ℝ := fun x ↦ (1 - u x) * t + u x * (-1 - (x - 6 * k - 3) / 6)
  have hu_l : u l = 0 := lam_left hlr.le
  have hu_r : u r = 0 := lam_right hlr.le
  have hQl : Q l = t := by
    have : mu k l = 0 := mu_zero (by rw [hl]; linarith)
    simp [Q, hu_l, this]
  have hQr : Q r = t + 1 := by
    have : mu k r = 1 := mu_one (by rw [hr]; linarith)
    simp [Q, hu_r, this]
  have hAl : A l = t + 1 := by simp [A, hu_l]
  have hBr : B r = t := by simp [B, hu_r]
  have hA6 : A (6 * (k : ℝ)) = 1 := by
    have : u (6 * (k : ℝ)) = 1 := hum (by linarith) (by linarith)
    simp [A, this]
  have hB6 : B (6 * (k : ℝ) + 3) = -1 := by
    have : u (6 * (k : ℝ) + 3) = 1 := hum (by linarith) (by linarith)
    simp [B, this]
  have hQc : ContinuousOn Q (Icc l r) := Continuous.continuousOn (by simp only [Q, u]; fun_prop)
  have hAc : ContinuousOn A (Icc l (6 * (k : ℝ))) :=
    Continuous.continuousOn (by simp only [A, u]; fun_prop)
  have hBc : ContinuousOn B (Icc (6 * (k : ℝ) + 3) r) :=
    Continuous.continuousOn (by simp only [B, u]; fun_prop)
  have hQclear : ∀ x ∈ Icc l r, Clear a b c (x, Q x) := by
    intro x hx
    rcases (hu₁ x).lt_or_eq with h | h
    · exact hgap x hx h _
    · simp only [Q, h]
      by_cases h₁ : x ≤ 6 * k + 1
      · rw [mu_zero h₁]
        exact clear_of_abs (by norm_num)
      by_cases h₂ : 6 * (k : ℝ) + 2 ≤ x
      · rw [mu_one h₂]
        exact clear_of_abs (by norm_num)
      · refine clear_of_gap (2 * (k : ℤ)) ?_ ?_ <;> push_cast <;> linarith
  have hAclear : ∀ x ∈ Icc l (6 * (k : ℝ)), x ≠ 6 * (k : ℝ) → Clear a b c (x, A x) := by
    intro x hx hne
    have hx' : x ∈ Icc l r := ⟨hx.1, hx.2.trans (by rw [hr]; linarith)⟩
    rcases (hu₁ x).lt_or_eq with h | h
    · exact hgap x hx' h _
    · simp only [A, h]
      refine clear_of_abs ?_
      have : x < 6 * k := lt_of_le_of_ne hx.2 hne
      rw [abs_of_pos] <;> linarith
  have hBclear : ∀ x ∈ Icc (6 * (k : ℝ) + 3) r, x ≠ 6 * (k : ℝ) + 3 → Clear a b c (x, B x) := by
    intro x hx hne
    have hx' : x ∈ Icc l r := ⟨by rw [hl]; linarith [hx.1], hx.2⟩
    rcases (hu₁ x).lt_or_eq with h | h
    · exact hgap x hx' h _
    · simp only [B, h]
      refine clear_of_abs ?_
      have : 6 * (k : ℝ) + 3 < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
      rw [abs_of_neg] <;> linarith
  have hAok : ∀ x ∈ Icc l (6 * (k : ℝ)), Ok a b c (x, A x) := fun x hx ↦ by
    by_cases h : x = 6 * (k : ℝ)
    · subst h
      rw [hA6]
      exact ok_of_abs (by simp)
    · exact (hAclear x hx h).ok
  have hBok : ∀ x ∈ Icc (6 * (k : ℝ) + 3) r, Ok a b c (x, B x) := fun x hx ↦ by
    by_cases h : x = 6 * (k : ℝ) + 3
    · subst h
      rw [hB6]
      exact ok_of_abs (by simp)
    · exact (hBclear x hx h).ok
  have hlin₁ := isLine_gr (e := l - 1) hlr hQc (fun x hx ↦ (hQclear x hx).ok)
    (fun x hx _ ↦ hQclear x hx)
  have hlin₂ := isLine_gr (e := 6 * (k : ℝ)) (show l < 6 * (k : ℝ) by rw [hl]; linarith) hAc hAok
    hAclear
  have hlin₃ := isLine_gr (e := 6 * (k : ℝ) + 3) (show 6 * (k : ℝ) + 3 < r by rw [hr]; linarith)
    hBc hBok hBclear
  rw [hQl, hQr] at hlin₁
  rw [hAl, hA6] at hlin₂
  rw [hB6, hBr, ← qq_handle (b := b) (c := c) hk] at hlin₃
  have hport₁ : ((6 * (k : ℝ), 1).1 - 3 * ((2 * k : ℕ) : ℝ)) ^ 2 + (6 * (k : ℝ), (1 : ℝ)).2 ^ 2 = 1
    := by
    simp only; push_cast; ring
  have hport₂ : ((6 * (k : ℝ) + 3, -1).1 - 3 * ((2 * k + 1 : ℕ) : ℝ)) ^ 2 +
      (6 * (k : ℝ) + 3, (-1 : ℝ)).2 ^ 2 = 1 := by
    simp only; push_cast; ring
  have hok₁ : Ok a b c (6 * (k : ℝ), 1) := ok_of_abs (by simp)
  have hok₂ : Ok a b c (6 * (k : ℝ) + 3, -1) := ok_of_abs (by simp)
  have hinter := handle_bands_intersection hk hA6 hB6 hAok hBclear
    (mem_of_line hlin₂).2 (mem_of_line hlin₃).1
  have hSv := GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm hlin₂) hlin₃ hinter
  rw [← image_union] at hSv
  have hcast : (((i : ℕ) + 1 : ℕ) : ℝ) = t + 1 := by rw [ht]; push_cast; ring
  refine slab_of_band i hlr hgap (Su := gr Q l r) (Sv := gr A l (6 * (k : ℝ)) ∪ gr B (6 *
    (k : ℝ) + 3) r)
    (by rw [hcast]; exact hlin₁) (by rw [hcast]; exact hSv) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨(hQclear x hx).ok, hx.1, hx.2⟩
    · exact ⟨hAok x hx, hx.1, hx.2.trans (by rw [hr]; linarith)⟩
    · exact ⟨hBok x hx, by rw [hl]; linarith [hx.1], hx.2⟩
  · rw [hcast]
    rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> simp only
    · obtain ⟨h₂, h₃⟩ := mix_bounds (mu_nonneg k x) (mu_le_one k x) (show t ≤ t + 1 by linarith)
      obtain ⟨h₄, h₅⟩ := mix_bounds (mu_nonneg k x) (mu_le_one k x)
        (show (-5 / 4 : ℝ) ≤ 5 / 4 by norm_num)
      exact band_interp (hu₀ x) (hu₁ x) h₂ h₃ h₄ h₅
    · have h₂ : (-5 / 4 : ℝ) ≤ 1 + (6 * k - x) / 6 := by linarith [hx.2]
      have h₃ : 1 + (6 * (k : ℝ) - x) / 6 ≤ 5 / 4 := by rw [hl] at hx; linarith [hx.1]
      exact band_interp (hu₀ x) (hu₁ x) (by linarith) le_rfl h₂ h₃
    · have h₂ : -1 - (x - 6 * k - 3) / 6 ≤ (5 / 4 : ℝ) := by linarith [hx.1]
      have h₃ : (-5 / 4 : ℝ) ≤ -1 - (x - 6 * k - 3) / 6 := by rw [hr] at hx; linarith [hx.2]
      exact band_interp (hu₀ x) (hu₁ x) le_rfl (by linarith) h₃ h₂
  · exact handle_bands_disjoint hQclear hAok hBok
  · rintro z hz hzl ⟨_, ⟨x, hx, rfl⟩, heq⟩
    have h₁ := eq_of_qq_eq (hQclear x hx) hz heq
    subst h₁
    have h₂ : x = l := le_antisymm hzl hx.1
    subst h₂
    rw [hQl]
  · rintro z hz hzr ⟨_, ⟨x, hx, rfl⟩, heq⟩
    have h₁ := eq_of_qq_eq (hQclear x hx) hz heq
    subst h₁
    have h₂ : x = r := le_antisymm hx.2 hzr
    subst h₂
    rw [hQr, hcast]
  · rintro z hz hzl ⟨_, (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩), heq⟩
    · by_cases h₁ : x = 6 * (k : ℝ)
      · subst h₁
        replace heq : qq a b c (6 * (k : ℝ), A (6 * (k : ℝ))) = qq a b c z := heq
        rw [hA6] at heq
        have := (handle_side hk (Or.inl rfl) hport₁ hok₁ hz heq.symm).1
        rw [hl] at hzl
        linarith
      · have h₃ := eq_of_qq_eq (hAclear x hx h₁) hz heq
        subst h₃
        have h₂ : x = l := le_antisymm hzl hx.1
        subst h₂
        rw [hAl, hcast]
    · by_cases h₁ : x = 6 * (k : ℝ) + 3
      · subst h₁
        replace heq : qq a b c (6 * (k : ℝ) + 3, B (6 * (k : ℝ) + 3)) = qq a b c z := heq
        rw [hB6] at heq
        have := (handle_side hk (Or.inr rfl) hport₂ hok₂ hz heq.symm).1
        rw [hl] at hzl
        linarith
      · have h₃ := eq_of_qq_eq (hBclear x hx h₁) hz heq
        subst h₃
        rw [hl] at hzl
        have := hx.1
        simp only at hzl
        linarith
  · rintro z hz hzr ⟨_, (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩), heq⟩
    · by_cases h₁ : x = 6 * (k : ℝ)
      · subst h₁
        replace heq : qq a b c (6 * (k : ℝ), A (6 * (k : ℝ))) = qq a b c z := heq
        rw [hA6] at heq
        have := (handle_side hk (Or.inl rfl) hport₁ hok₁ hz heq.symm).2
        rw [hr] at hzr
        linarith
      · have h₃ := eq_of_qq_eq (hAclear x hx h₁) hz heq
        subst h₃
        rw [hr] at hzr
        have := hx.2
        simp only at hzr
        linarith
    · by_cases h₁ : x = 6 * (k : ℝ) + 3
      · subst h₁
        replace heq : qq a b c (6 * (k : ℝ) + 3, B (6 * (k : ℝ) + 3)) = qq a b c z := heq
        rw [hB6] at heq
        have := (handle_side hk (Or.inr rfl) hport₂ hok₂ hz heq.symm).2
        rw [hr] at hzr
        linarith
      · have h₃ := eq_of_qq_eq (hBclear x hx h₁) hz heq
        subst h₃
        have h₂ : x = r := le_antisymm hx.2 hzr
        subst h₂
        rw [hBr]

end GraphMinor.GM20.Draw
