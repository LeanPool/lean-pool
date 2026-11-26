/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw4

/-!
# Drawing a graph in a surface of large genus: a swap with a cross-cap

Two curves that cross at the centre of a cross-cap do not meet in the surface: each one goes into
the
circle at a point and comes back at the antipodal point. So two straight lines through the centre,
of
slopes `4/3` and `-4/3`, swap two heights.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

/-- A curve in two parts, whose inner ends have the same image. -/
theorem two_part [T2Space (SurfaceModel a b c)] {f₁ f₂ : ℝ → ℝ} {l e₁ e₂ r : ℝ} (hl : l < e₁)
    (h₁₂ : e₁ < e₂) (hr : e₂ < r) (hc₁ : ContinuousOn f₁ (Icc l e₁))
    (hc₂ : ContinuousOn f₂ (Icc e₂ r)) (ok₁ : ∀ x ∈ Icc l e₁, Ok a b c (x, f₁ x))
    (ok₂ : ∀ x ∈ Icc e₂ r, Ok a b c (x, f₂ x))
    (cl₁ : ∀ x ∈ Icc l e₁, x ≠ e₁ → Clear a b c (x, f₁ x))
    (cl₂ : ∀ x ∈ Icc e₂ r, x ≠ e₂ → Clear a b c (x, f₂ x))
    (hj : qq a b c (e₁, f₁ e₁) = qq a b c (e₂, f₂ e₂))
    (hs : ∀ z, Ok a b c z → qq a b c z = qq a b c (e₁, f₁ e₁) → l < z.1 ∧ z.1 < r) :
    IsLineWithEnds (qq a b c '' (gr f₁ l e₁ ∪ gr f₂ e₂ r)) (qq a b c (l, f₁ l))
        (qq a b c (r, f₂ r)) ∧
      (∀ z, Ok a b c z → z.1 ≤ l → qq a b c z ∈ qq a b c '' (gr f₁ l e₁ ∪ gr f₂ e₂ r) →
        qq a b c z = qq a b c (l, f₁ l)) ∧
      (∀ z, Ok a b c z → r ≤ z.1 → qq a b c z ∈ qq a b c '' (gr f₁ l e₁ ∪ gr f₂ e₂ r) →
        qq a b c z = qq a b c (r, f₂ r)) := by
  have hL₁ := isLine_gr hl hc₁ ok₁ cl₁
  have hL₂ := isLine_gr hr hc₂ ok₂ cl₂
  have hinter : (qq a b c '' gr f₁ l e₁) ∩ (qq a b c '' gr f₂ e₂ r) =
      {qq a b c (e₁, f₁ e₁)} := by
    ext w
    constructor
    · rintro ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, ⟨_, ⟨x', hx', rfl⟩, heq⟩⟩
      replace heq : qq a b c (x', f₂ x') = qq a b c (x, f₁ x) := heq
      by_cases h₁ : x = e₁
      · subst h₁
        rfl
      by_cases h₂ : x' = e₂
      · subst h₂
        change qq a b c (x, f₁ x) = _
        rw [← heq, hj]
      · have h₃ := congrArg Prod.fst (eq_of_qq_eq (cl₂ x' hx' h₂) (ok₁ x hx) heq)
        simp only at h₃
        linarith [hx.2, hx'.1]
    · rintro rfl
      exact ⟨(mem_of_line hL₁).2, hj ▸ (mem_of_line hL₂).1⟩
  have hL₂' : IsLineWithEnds (qq a b c '' gr f₂ e₂ r) (qq a b c (e₁, f₁ e₁))
      (qq a b c (r, f₂ r)) := hj ▸ hL₂
  have hline := GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm hL₁) hL₂' hinter
  rw [← image_union] at hline
  refine ⟨hline, ?_, ?_⟩
  · rintro z hz hzl ⟨_, (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩), heq⟩
    · replace heq : qq a b c (x, f₁ x) = qq a b c z := heq
      by_cases h₁ : x = e₁
      · subst h₁
        have := (hs z hz heq.symm).1
        linarith
      · have h₃ := eq_of_qq_eq (cl₁ x hx h₁) hz heq
        subst h₃
        have h₂ : x = l := le_antisymm hzl hx.1
        subst h₂
        rfl
    · replace heq : qq a b c (x, f₂ x) = qq a b c z := heq
      by_cases h₁ : x = e₂
      · subst h₁
        have := (hs z hz (heq.symm.trans hj.symm)).1
        linarith
      · have h₃ := eq_of_qq_eq (cl₂ x hx h₁) hz heq
        subst h₃
        have := hx.1
        simp only at hzl
        linarith
  · rintro z hz hzr ⟨_, (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩), heq⟩
    · replace heq : qq a b c (x, f₁ x) = qq a b c z := heq
      by_cases h₁ : x = e₁
      · subst h₁
        have := (hs z hz heq.symm).2
        linarith
      · have h₃ := eq_of_qq_eq (cl₁ x hx h₁) hz heq
        subst h₃
        have := hx.2
        simp only at hzr
        linarith
    · replace heq : qq a b c (x, f₂ x) = qq a b c z := heq
      by_cases h₁ : x = e₂
      · subst h₁
        have := (hs z hz (heq.symm.trans hj.symm)).2
        linarith
      · have h₃ := eq_of_qq_eq (cl₂ x hx h₁) hz heq
        subst h₃
        have h₂ : x = r := le_antisymm hx.2 hzr
        subst h₂
        rfl

/-- A point of the model on a cross-cap circle has preimages only on that circle. -/
theorem crosscap_side {k : ℕ} (hk : k < b) {w z : ℝ × ℝ}
    (hw : (w.1 - 3 * ((2 * a + k : ℕ) : ℝ)) ^ 2 + w.2 ^ 2 = 1) (hwok : Ok a b c w)
    (hz : Ok a b c z) (heq : qq a b c z = qq a b c w) :
    3 * ((2 * a + k : ℕ) : ℝ) - 1 ≤ z.1 ∧ z.1 ≤ 3 * ((2 * a + k : ℕ) : ℝ) + 1 := by
  have hI : 2 * a + k < 2 * a + b + c := by omega
  by_cases hc : Clear a b c z
  · have h₁ := eq_of_qq_eq hc hwok heq
    subst h₁
    exact bound_of_circle hw
  · obtain ⟨j, hj, hzj⟩ := exists_circle hz hc
    have h₁ := congrArg keyM heq
    rw [keyM_circle hj hz hzj, keyM_circle hI hwok hw] at h₁
    have h₂ : grp a j = grp a (2 * a + k) := by
      have := Sum.inl.inj (Option.some.inj h₁)
      exact (Prod.ext_iff.mp this).1
    have h₃ : grp a (2 * a + k) = 2 * a + k := grp_of_ge (by omega)
    rw [h₃] at h₂
    have hj' : 2 * a ≤ j := by
      by_contra hlt
      have h₄ : grp a j = j / 2 := grp_of_lt (by omega)
      rw [h₄] at h₂
      omega
    have h₄ : grp a j = j := grp_of_ge hj'
    rw [h₄] at h₂
    subst h₂
    exact bound_of_circle hzj

/-- A point of the circle around the `k`th centre is outside every open disc. -/
theorem dist_sq_ge {k i : ℕ} {x y : ℝ} (hu : x ^ 2 + y ^ 2 = 1) :
    1 ≤ (3 * (k : ℝ) + x - 3 * i) ^ 2 + y ^ 2 := by
  rcases eq_or_ne k i with rfl | hne
  · have : 3 * (k : ℝ) + x - 3 * k = x := by ring
    rw [this, hu]
  · have h₁ : (1 : ℝ) ≤ ((k : ℝ) - i) ^ 2 := by
      have h₂ : (k : ℤ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
      have h₃ : (1 : ℤ) ≤ ((k : ℤ) - i) ^ 2 := by
        have := sq_pos_of_ne_zero h₂
        omega
      exact_mod_cast h₃
    have h₂ : x ^ 2 ≤ 1 := by linarith only [hu, sq_nonneg y]
    have h₃ : |x| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]
      exact h₂
    obtain ⟨h₄, h₅⟩ := abs_le.mp h₃
    have h₆ : 3 ≤ |3 * ((k : ℝ) - i)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have : 1 ≤ |(k : ℝ) - i| := by
        rw [← one_le_sq_iff_one_le_abs]
        exact h₁
      linarith
    have h₇ : 2 ≤ |3 * (k : ℝ) + x - 3 * i| := by
      have : |3 * ((k : ℝ) - i)| ≤ |3 * (k : ℝ) + x - 3 * i| + |x| := by
        have h₈ : 3 * ((k : ℝ) - i) = (3 * (k : ℝ) + x - 3 * i) - x := by ring
        rw [h₈]
        exact abs_sub _ _
      linarith
    have hsq : 1 ≤ (3 * (k : ℝ) + x - 3 * i) ^ 2 :=
      (one_le_sq_iff_one_le_abs _).mpr (le_trans (by norm_num) h₇)
    exact hsq.trans (le_add_of_nonneg_right (sq_nonneg y))

/-- Antipodal points of a cross-cap circle have the same image. -/
theorem qq_crosscap {k : ℕ} (hk : k < b) {u₁ u₂ : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1) :
    qq a b c (3 * ((2 * a + k : ℕ) : ℝ) + u₁, u₂) =
      qq a b c (3 * ((2 * a + k : ℕ) : ℝ) - u₁, -u₂) := by
  have h₁ : Ok a b c (3 * ((2 * a + k : ℕ) : ℝ) + u₁, u₂) := by
    intro i hi
    have hne := dist_sq_ge (k := 2 * a + k) (i := i) (x := u₁) (y := u₂) hu
    exact hne
  have h₂ : Ok a b c (3 * ((2 * a + k : ℕ) : ℝ) - u₁, -u₂) := by
    intro i hi
    have hne := dist_sq_ge (k := 2 * a + k) (i := i) (x := -u₁) (y := -u₂)
      (by simpa only [neg_sq] using hu)
    simpa [sub_eq_add_neg] using hne
  rw [qq_of_ok h₁, qq_of_ok h₂]
  refine Quot.sound (ModelGlue.crosscap k hk !₂[u₁, u₂] ?_ _ _ ?_ ?_)
  · have : ‖(!₂[u₁, u₂] : EuclideanPlane)‖ ^ 2 = 1 := by
      rw [norm_sq]
      simpa using hu
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  · refine congrArg (fun x : EuclideanPlane ↦ (x : OnePoint EuclideanPlane)) ?_
    ext j
    fin_cases j <;> simp [pl, modelCentre]
  · refine congrArg (fun x : EuclideanPlane ↦ (x : OnePoint EuclideanPlane)) ?_
    ext j
    fin_cases j <;> simp [pl, modelCentre, sub_eq_add_neg]

/-- Saturation at `±5/4`. -/
noncomputable def sat (v : ℝ) : ℝ := max (-5 / 4) (min (5 / 4) v)

theorem continuous_sat : Continuous sat := by
  unfold sat
  fun_prop

theorem sat_le (v : ℝ) : sat v ≤ 5 / 4 := max_le (by norm_num) (min_le_left _ _)

theorem le_sat (v : ℝ) : -5 / 4 ≤ sat v := le_max_left _ _

/-- A point on the line of slope `4/3` or `-4/3`, outside the circle around `C = 3I`, and at most
`5/4`
to the side of `C`, is clear. -/
theorem clear_slope {I : ℕ} {x y : ℝ}
    (h₁ : 9 / 25 < (x - 3 * I) ^ 2) (h₂ : (x - 3 * I) ^ 2 ≤ 25 / 16)
    (h₃ : y ^ 2 = 16 / 9 * (x - 3 * I) ^ 2 ∨ y ^ 2 = 25 / 16) : Clear a b c (x, y) := by
  intro i _
  simp only
  rcases eq_or_ne i I with rfl | hne
  · rcases h₃ with h₃ | h₃
    · linarith only [h₁, h₃]
    · linarith only [h₃, sq_nonneg (x - 3 * (i : ℝ))]
  · have h₄ : (1 : ℝ) ≤ ((I : ℝ) - i) ^ 2 := by
      have h₂' : (I : ℤ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
      have h₃' : (1 : ℤ) ≤ ((I : ℤ) - i) ^ 2 := by
        have := sq_pos_of_ne_zero h₂'
        omega
      exact_mod_cast h₃'
    have h₅ : |x - 3 * I| ≤ 5 / 4 := by
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4), ← sq_le_sq]
      linarith
    obtain ⟨h₆, h₇⟩ := abs_le.mp h₅
    have h₈ : 1 ≤ |(I : ℝ) - i| := by
      rw [← one_le_sq_iff_one_le_abs]
      exact h₄
    have h₉ := sq_nonneg y
    rcases le_abs'.mp h₈ with h₁₀ | h₁₀
    · have hdist : 1 < 3 * (i : ℝ) - x := by linarith only [h₇, h₁₀]
      have hsq' : (1 : ℝ) ^ 2 < (3 * (i : ℝ) - x) ^ 2 :=
        (sq_lt_sq₀ zero_le_one (zero_le_one.trans hdist.le)).mpr hdist
      rw [← neg_sub, neg_sq]
      linarith only [hsq', h₉]
    · have hdist : 1 < x - 3 * i := by linarith only [h₆, h₁₀]
      have hsq' : (1 : ℝ) ^ 2 < (x - 3 * i) ^ 2 :=
        (sq_lt_sq₀ zero_le_one (zero_le_one.trans hdist.le)).mpr hdist
      linarith only [hsq', h₉]

theorem sat_sq (v : ℝ) : sat v ^ 2 = v ^ 2 ∨ sat v ^ 2 = 25 / 16 := by
  unfold sat
  rcases le_total (5 / 4) v with h | h
  · rw [min_eq_left h, max_eq_right (by norm_num)]
    right
    norm_num
  · rw [min_eq_right h]
    rcases le_total (-5 / 4) v with h' | h'
    · rw [max_eq_right h']
      exact Or.inl rfl
    · rw [max_eq_left h']
      right
      norm_num

theorem sat_eq {v : ℝ} (h₁ : -5 / 4 ≤ v) (h₂ : v ≤ 5 / 4) : sat v = v := by
  unfold sat
  rw [min_eq_right h₂, max_eq_right h₁]

theorem sat_neg {v : ℝ} (h : v ≤ 0) : sat v ≤ 0 :=
  max_le (by norm_num) ((min_le_right _ _).trans h)

theorem sat_lt_zero {v : ℝ} (h : v < 0) : sat v < 0 :=
  max_lt (by norm_num) ((min_le_right _ _).trans_lt h)

theorem sat_pos {v : ℝ} (h : 0 < v) : 0 < sat v :=
  lt_max_of_lt_right (lt_min (by norm_num) h)

theorem ok_circle {k : ℕ} {x y : ℝ} (hu : x ^ 2 + y ^ 2 = 1) :
    Ok a b c (3 * (k : ℝ) + x, y) := fun _ _ ↦ dist_sq_ge hu

private theorem crosscap_bands_disjoint {k : ℕ} (hk : k < b) {l r t : ℝ} :
    let I : ℕ := 2 * a + k
    let C : ℝ := 3 * (I : ℝ)
    let u : ℝ → ℝ := lam l r
    let v : ℝ → ℝ := fun x ↦ sat (4 / 3 * (x - C))
    let F : ℝ → ℝ → ℝ → ℝ := fun P s x ↦ (1 - u x) * P + u x * (s * v x)
    (∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc l r, 9 / 25 < (x - C) ^ 2 →
      Clear a b c (x, F P s x)) →
    (Icc l (C - 3 / 5) ⊆ Icc l r) →
    (Icc (C + 3 / 5) r ⊆ Icc l r) →
    (∀ x ∈ Icc l (C - 3 / 5), x ≠ C - 3 / 5 → 9 / 25 < (x - C) ^ 2) →
    (∀ x ∈ Icc (C + 3 / 5) r, x ≠ C + 3 / 5 → 9 / 25 < (x - C) ^ 2) →
    (∀ P s, F P s (C - 3 / 5) = s * (-4 / 5)) →
    (∀ P s, F P s (C + 3 / 5) = s * (4 / 5)) →
    (∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc l (C - 3 / 5), Ok a b c (x, F P s x)) →
    (∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc (C + 3 / 5) r, Ok a b c (x, F P s x)) →
    Disjoint (qq a b c '' (gr (F t 1) l (C - 3 / 5) ∪ gr (F (t + 1) 1) (C + 3 / 5) r))
      (qq a b c '' (gr (F (t + 1) (-1)) l (C - 3 / 5) ∪ gr (F t (-1)) (C + 3 / 5) r)) := by
  intro I C u v F hclear hIcl hIcr hsql hsqr hFm hFp hOkL hOkR
  have hIdef : I = 2 * a + k := rfl
  have hIlt : I < 2 * a + b + c := by omega
  have hC : C = 3 * (I : ℝ) := rfl
  have hu₀ : ∀ x, 0 ≤ u x := lam_nonneg l r
  have hu₁ : ∀ x, u x ≤ 1 := lam_le_one l r
  have hport : ∀ {u₁ u₂ : ℝ}, u₁ ^ 2 + u₂ ^ 2 = 1 → Ok a b c (C + u₁, u₂) := fun h ↦ ok_circle h
  have hglue : ∀ {u₁ u₂ : ℝ}, u₁ ^ 2 + u₂ ^ 2 = 1 →
      qq a b c (C + u₁, u₂) = qq a b c (C - u₁, -u₂) := fun h ↦ qq_crosscap hk h
  have hsqs : ∀ s : ℝ, (s = 1 ∨ s = -1) → (-3 / 5 : ℝ) ^ 2 + (s * (-4 / 5)) ^ 2 = 1 := by
    rintro s (rfl | rfl) <;> norm_num
  have ep₁ : ∀ s : ℝ, (C - 3 / 5, s * (-4 / 5)) = (C + (-3 / 5), s * (-4 / 5)) := fun s ↦
    Prod.ext (by simp only; ring) rfl
  have ep₂ : ∀ s : ℝ, (C + 3 / 5, s * (4 / 5)) = (C - (-3 / 5), -(s * (-4 / 5))) := fun s ↦
    Prod.ext (by simp only; ring) (by simp only; ring)
  have hcu : ∀ P s, (s = 1 ∨ s = -1) → ∀ z ∈ gr (F P s) l (C - 3 / 5),
      Clear a b c z ∨ z = (C - 3 / 5, s * (-4 / 5)) := by
    rintro P s hs _ ⟨x, hx, rfl⟩
    by_cases h : x = C - 3 / 5
    · subst h
      right
      simp only [hFm]
    · exact Or.inl (hclear P s hs x (hIcl hx) (hsql x hx h))
  have hcv : ∀ P s, (s = 1 ∨ s = -1) → ∀ z ∈ gr (F P s) (C + 3 / 5) r,
      Clear a b c z ∨ z = (C + 3 / 5, s * (4 / 5)) := by
    rintro P s hs _ ⟨x, hx, rfl⟩
    by_cases h : x = C + 3 / 5
    · subst h
      right
      simp only [hFp]
    · exact Or.inl (hclear P s hs x (hIcr hx) (hsqr x hx h))
  have htw : ∀ z : ℝ × ℝ, tw a b I (pl z - modelCentre I) = (z.1 - 3 * I) * z.2 := by
    intro z
    simp only [tw]
    rw [ite_eq_left (by omega)]
    simp [pl, modelCentre]
  have hP₁ : Ok a b c (C - 3 / 5, (1 : ℝ) * (-4 / 5)) := by
    rw [ep₁]
    exact hport (hsqs 1 (Or.inl rfl))
  have hP₃ : Ok a b c (C - 3 / 5, (-1 : ℝ) * (-4 / 5)) := by
    rw [ep₁]
    exact hport (hsqs (-1) (Or.inr rfl))
  have hkey : qq a b c (C - 3 / 5, (1 : ℝ) * (-4 / 5)) ≠
      qq a b c (C - 3 / 5, (-1 : ℝ) * (-4 / 5)) := by
    intro heq
    have h₁ := congrArg keyM heq
    rw [keyM_circle hIlt hP₁ (by simp only [hC]; ring), keyM_circle hIlt hP₃
      (by simp only [hC]; ring), htw, htw] at h₁
    have h₂ := (Prod.ext_iff.mp (Sum.inl.inj (Option.some.inj h₁))).2
    simp only [hC] at h₂
    have h₃ : ((3 * (I : ℝ) - 3 / 5 - 3 * I) * (1 * (-4 / 5)) : ℝ) = 12 / 25 := by ring
    have h₄ : ((3 * (I : ℝ) - 3 / 5 - 3 * I) * (-1 * (-4 / 5)) : ℝ) = -12 / 25 := by ring
    rw [h₃, h₄] at h₂
    norm_num at h₂
  have hg₁ : qq a b c (C + 3 / 5, (1 : ℝ) * (4 / 5)) =
      qq a b c (C - 3 / 5, (1 : ℝ) * (-4 / 5)) := by
    rw [ep₁ 1, ep₂ 1]
    exact (hglue (hsqs 1 (Or.inl rfl))).symm
  have hg₂ : qq a b c (C + 3 / 5, (-1 : ℝ) * (4 / 5)) =
      qq a b c (C - 3 / 5, (-1 : ℝ) * (-4 / 5)) := by
    rw [ep₁ (-1), ep₂ (-1)]
    exact (hglue (hsqs (-1) (Or.inr rfl))).symm
  have hclass₁ : ∀ z ∈ gr (F t 1) l (C - 3 / 5) ∪ gr (F (t + 1) 1) (C + 3 / 5) r,
      Clear a b c z ∨ qq a b c z = qq a b c (C - 3 / 5, (1 : ℝ) * (-4 / 5)) := by
    rintro z (hz | hz)
    · rcases hcu _ _ (Or.inl rfl) z hz with h | rfl
      · exact Or.inl h
      · exact Or.inr rfl
    · rcases hcv _ _ (Or.inl rfl) z hz with h | rfl
      · exact Or.inl h
      · exact Or.inr hg₁
  have hclass₂ : ∀ z ∈ gr (F (t + 1) (-1)) l (C - 3 / 5) ∪ gr (F t (-1)) (C + 3 / 5) r,
      Clear a b c z ∨ qq a b c z = qq a b c (C - 3 / 5, (-1 : ℝ) * (-4 / 5)) := by
    rintro z (hz | hz)
    · rcases hcu _ _ (Or.inr rfl) z hz with h | rfl
      · exact Or.inl h
      · exact Or.inr rfl
    · rcases hcv _ _ (Or.inr rfl) z hz with h | rfl
      · exact Or.inl h
      · exact Or.inr hg₂
  have hvneg : ∀ x, x ≤ C - 3 / 5 → v x < 0 := fun x hx ↦
    sat_lt_zero (by linarith)
  have hvpos : ∀ x, C + 3 / 5 ≤ x → 0 < v x := fun x hx ↦ sat_pos (by linarith)
  have hsep : ∀ z ∈ gr (F t 1) l (C - 3 / 5) ∪ gr (F (t + 1) 1) (C + 3 / 5) r,
      ∀ z' ∈ gr (F (t + 1) (-1)) l (C - 3 / 5) ∪ gr (F t (-1)) (C + 3 / 5) r, z ≠ z' := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) _ (⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩) h
    · obtain ⟨rfl, h₂⟩ := Prod.ext_iff.mp h
      simp only at h₂
      have h₃ := hvneg x hx.2
      have := interp_lt (A := t) (A' := t + 1) (B := 1 * v x) (B' := -1 * v x) (hu₀ x)
        (hu₁ x) (by linarith) (by linarith)
      exact this.ne h₂
    · have := congrArg Prod.fst h
      simp only at this
      linarith [hx.2, hx'.1]
    · have := congrArg Prod.fst h
      simp only at this
      linarith [hx.1, hx'.2]
    · obtain ⟨rfl, h₂⟩ := Prod.ext_iff.mp h
      simp only at h₂
      have h₃ := hvpos x hx.1
      have := interp_lt (A := t) (A' := t + 1) (B := -1 * v x) (B' := 1 * v x) (hu₀ x)
        (hu₁ x) (by linarith) (by linarith)
      exact this.ne h₂.symm
  have hOkU : ∀ z ∈ gr (F t 1) l (C - 3 / 5) ∪ gr (F (t + 1) 1) (C + 3 / 5) r, Ok a b c z := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hOkL _ _ (Or.inl rfl) x hx
    · exact hOkR _ _ (Or.inl rfl) x hx
  have hOkV : ∀ z ∈ gr (F (t + 1) (-1)) l (C - 3 / 5) ∪ gr (F t (-1)) (C + 3 / 5) r,
      Ok a b c z := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hOkL _ _ (Or.inr rfl) x hx
    · exact hOkR _ _ (Or.inr rfl) x hx
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', heq⟩
  rcases hclass₁ z hz with h₁ | h₁
  · exact hsep z hz z' hz' (eq_of_qq_eq h₁ (hOkV z' hz') heq.symm)
  rcases hclass₂ z' hz' with h₂ | h₂
  · exact hsep z hz z' hz' (eq_of_qq_eq h₂ (hOkU z hz) heq).symm
  · exact hkey (h₁.symm.trans (heq.symm.trans h₂))

/-- The swap of heights `i` and `i + 1` with the `k`th cross-cap. -/
theorem slab_crosscap [T2Space (SurfaceModel a b c)] {n k : ℕ} (hk : k < b) (i : Fin n) :
    Slab a b c (n + 1) (3 * ((2 * a + k : ℕ) : ℝ) - 3 / 2) (3 * ((2 * a + k : ℕ) : ℝ) + 3 / 2)
      (Equiv.swap i.castSucc i.succ) := by
  classical
  set I : ℕ := 2 * a + k with hIdef
  have hIlt : I < 2 * a + b + c := by omega
  set C : ℝ := 3 * (I : ℝ) with hC
  set l : ℝ := C - 3 / 2 with hl
  set r : ℝ := C + 3 / 2 with hr
  set t : ℝ := ((i : ℕ) : ℝ) with ht
  have hlr : l < r := by rw [hl, hr]; linarith
  have hcl := continuous_lam l r
  have hcs := continuous_sat
  let u : ℝ → ℝ := lam l r
  have hu₀ : ∀ x, 0 ≤ u x := lam_nonneg l r
  have hu₁ : ∀ x, u x ≤ 1 := lam_le_one l r
  have hum : ∀ {x}, C - 5 / 4 ≤ x → x ≤ C + 5 / 4 → u x = 1 := fun h₁ h₂ ↦
    lam_eq_one (by rw [hl]; linarith) (by rw [hr]; linarith)
  have hgap : ∀ x ∈ Icc l r, lam l r x < 1 → ∀ y, Clear a b c (x, y) := by
    intro x hx hlt y
    have hx₁ := hx.1
    have hx₂ := hx.2
    rcases lam_lt_one hlt with h | h
    · refine clear_of_gap ((I : ℤ) - 1) ?_ ?_ <;> push_cast <;> linarith
    · refine clear_of_gap ((I : ℤ)) ?_ ?_ <;> push_cast <;> linarith
  let v : ℝ → ℝ := fun x ↦ sat (4 / 3 * (x - C))
  have hvc : Continuous v := by simp only [v]; fun_prop
  let F : ℝ → ℝ → ℝ → ℝ := fun P s x ↦ (1 - u x) * P + u x * (s * v x)
  have hFc : ∀ P s, Continuous (F P s) := fun P s ↦ by
    simp only [F, u]
    fun_prop
  have hout : ∀ x ∈ Icc l r, ¬ (C - 5 / 4 ≤ x ∧ x ≤ C + 5 / 4) → ∀ y, Clear a b c (x, y) := by
    intro x hx hn y
    have hx₁ := hx.1
    have hx₂ := hx.2
    rw [not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · refine clear_of_gap ((I : ℤ) - 1) ?_ ?_ <;> push_cast <;> linarith
    · refine clear_of_gap ((I : ℤ)) ?_ ?_ <;> push_cast <;> linarith
  have hclear : ∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc l r, 9 / 25 < (x - C) ^ 2 →
      Clear a b c (x, F P s x) := by
    intro P s hs x hx hsq
    rcases (hu₁ x).lt_or_eq with h | h
    · exact hgap x hx h _
    by_cases hmid : C - 5 / 4 ≤ x ∧ x ≤ C + 5 / 4
    · have hFx : F P s x = s * v x := by simp only [F, h]; ring
      rw [hFx]
      have hle : (x - C) ^ 2 ≤ 25 / 16 := by nlinarith [hmid.1, hmid.2]
      have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      refine clear_slope (I := I) hsq hle ?_
      rcases sat_sq (4 / 3 * (x - C)) with h₁ | h₁
      · left
        simp only [v, mul_pow, hs2, h₁]
        ring
      · right
        simp only [v, mul_pow, hs2, h₁]
        ring
    · exact hout x hx hmid _
  have hu_l : u l = 0 := lam_left hlr.le
  have hu_r : u r = 0 := lam_right hlr.le
  have hFl : ∀ P s, F P s l = P := fun P s ↦ by simp [F, hu_l]
  have hFr : ∀ P s, F P s r = P := fun P s ↦ by simp [F, hu_r]
  have hvm : v (C - 3 / 5) = -4 / 5 := by
    simp only [v]
    rw [show (4 / 3 * (C - 3 / 5 - C) : ℝ) = -4 / 5 by ring]
    exact sat_eq (by norm_num) (by norm_num)
  have hvp : v (C + 3 / 5) = 4 / 5 := by
    simp only [v]
    rw [show (4 / 3 * (C + 3 / 5 - C) : ℝ) = 4 / 5 by ring]
    exact sat_eq (by norm_num) (by norm_num)
  have hum' : u (C - 3 / 5) = 1 := hum (by linarith) (by linarith)
  have hup' : u (C + 3 / 5) = 1 := hum (by linarith) (by linarith)
  have hFm : ∀ P s, F P s (C - 3 / 5) = s * (-4 / 5) := fun P s ↦ by
    simp only [F, hum', hvm]; ring
  have hFp : ∀ P s, F P s (C + 3 / 5) = s * (4 / 5) := fun P s ↦ by
    simp only [F, hup', hvp]; ring
  have hIcl : Icc l (C - 3 / 5) ⊆ Icc l r := fun x hx ↦ ⟨hx.1, hx.2.trans (by rw [hr]; linarith)⟩
  have hIcr : Icc (C + 3 / 5) r ⊆ Icc l r := fun x hx ↦ ⟨by rw [hl]; linarith [hx.1], hx.2⟩
  have hsql : ∀ x ∈ Icc l (C - 3 / 5), x ≠ C - 3 / 5 → 9 / 25 < (x - C) ^ 2 := by
    intro x hx hne
    have : x < C - 3 / 5 := lt_of_le_of_ne hx.2 hne
    nlinarith
  have hsqr : ∀ x ∈ Icc (C + 3 / 5) r, x ≠ C + 3 / 5 → 9 / 25 < (x - C) ^ 2 := by
    intro x hx hne
    have : C + 3 / 5 < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
    nlinarith
  have hport : ∀ {u₁ u₂ : ℝ}, u₁ ^ 2 + u₂ ^ 2 = 1 → Ok a b c (C + u₁, u₂) := fun h ↦ ok_circle h
  have hglue : ∀ {u₁ u₂ : ℝ}, u₁ ^ 2 + u₂ ^ 2 = 1 →
      qq a b c (C + u₁, u₂) = qq a b c (C - u₁, -u₂) := fun h ↦ qq_crosscap hk h
  have hside : ∀ {u₁ u₂ : ℝ}, u₁ ^ 2 + u₂ ^ 2 = 1 → ∀ z, Ok a b c z →
      qq a b c z = qq a b c (C + u₁, u₂) → l < z.1 ∧ z.1 < r := by
    intro u₁ u₂ h z hz heq
    obtain ⟨h₁, h₂⟩ := crosscap_side hk (w := (C + u₁, u₂)) (by simp only [hC]; nlinarith)
      (hport h) hz heq
    rw [hl, hr]
    constructor <;> linarith
  have hsqs : ∀ s : ℝ, (s = 1 ∨ s = -1) → (-3 / 5 : ℝ) ^ 2 + (s * (-4 / 5)) ^ 2 = 1 := by
    rintro s (rfl | rfl) <;> norm_num
  have hsqs' : ∀ s : ℝ, (s = 1 ∨ s = -1) → (3 / 5 : ℝ) ^ 2 + (s * (4 / 5)) ^ 2 = 1 := by
    rintro s (rfl | rfl) <;> norm_num
  have ep₁ : ∀ s : ℝ, (C - 3 / 5, s * (-4 / 5)) = (C + (-3 / 5), s * (-4 / 5)) := fun s ↦
    Prod.ext (by simp only; ring) rfl
  have ep₂ : ∀ s : ℝ, (C + 3 / 5, s * (4 / 5)) = (C - (-3 / 5), -(s * (-4 / 5))) := fun s ↦
    Prod.ext (by simp only; ring) (by simp only; ring)
  have hOkL : ∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc l (C - 3 / 5), Ok a b c (x, F P s x) := by
    intro P s hs x hx
    by_cases h : x = C - 3 / 5
    · subst h
      rw [hFm, ep₁]
      exact hport (hsqs s hs)
    · exact (hclear P s hs x (hIcl hx) (hsql x hx h)).ok
  have hOkR : ∀ P s, (s = 1 ∨ s = -1) → ∀ x ∈ Icc (C + 3 / 5) r, Ok a b c (x, F P s x) := by
    intro P s hs x hx
    by_cases h : x = C + 3 / 5
    · subst h
      rw [hFp]
      exact hport (hsqs' s hs)
    · exact (hclear P s hs x (hIcr hx) (hsqr x hx h)).ok
  have hpart : ∀ P P' s, (s = 1 ∨ s = -1) →
      IsLineWithEnds (qq a b c '' (gr (F P s) l (C - 3 / 5) ∪ gr (F P' s) (C + 3 / 5) r))
          (qq a b c (l, P)) (qq a b c (r, P')) ∧
        (∀ z, Ok a b c z → z.1 ≤ l →
          qq a b c z ∈ qq a b c '' (gr (F P s) l (C - 3 / 5) ∪ gr (F P' s) (C + 3 / 5) r) →
          qq a b c z = qq a b c (l, P)) ∧
        (∀ z, Ok a b c z → r ≤ z.1 →
          qq a b c z ∈ qq a b c '' (gr (F P s) l (C - 3 / 5) ∪ gr (F P' s) (C + 3 / 5) r) →
          qq a b c z = qq a b c (r, P')) := by
    intro P P' s hs
    have hsq' := hsqs s hs
    have := two_part (a := a) (b := b) (c := c) (f₁ := F P s) (f₂ := F P' s) (l := l)
      (e₁ := C - 3 / 5) (e₂ := C + 3 / 5) (r := r) (by rw [hl]; linarith) (by linarith)
      (by rw [hr]; linarith) (hFc _ _).continuousOn (hFc _ _).continuousOn (hOkL P s hs)
        (hOkR P' s hs)
      (fun x hx h ↦ hclear P s hs x (hIcl hx) (hsql x hx h))
      (fun x hx h ↦ hclear P' s hs x (hIcr hx) (hsqr x hx h))
      (by rw [hFm, hFp, ep₁, ep₂]; exact hglue hsq')
      (fun z hz heq ↦ by
        rw [hFm, ep₁] at heq
        exact hside hsq' z hz heq)
    rw [hFl, hFr] at this
    exact this
  have hcast : (((i : ℕ) + 1 : ℕ) : ℝ) = t + 1 := by rw [ht]; push_cast; ring
  obtain ⟨hA, hAl, hAr⟩ := hpart t (t + 1) 1 (Or.inl rfl)
  obtain ⟨hB, hBl, hBr⟩ := hpart (t + 1) t (-1) (Or.inr rfl)
  refine slab_of_band i hlr hgap
    (Su := gr (F t 1) l (C - 3 / 5) ∪ gr (F (t + 1) 1) (C + 3 / 5) r)
    (Sv := gr (F (t + 1) (-1)) l (C - 3 / 5) ∪ gr (F t (-1)) (C + 3 / 5) r)
    (by rw [hcast]; exact hA) (by rw [hcast]; exact hB) ?_ ?_ ?_ hAl (by rw [hcast]; exact hAr)
    (by rw [hcast]; exact hBl) hBr
  · rintro z ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩))
    · exact ⟨hOkL _ _ (Or.inl rfl) x hx, (hIcl hx).1, (hIcl hx).2⟩
    · exact ⟨hOkR _ _ (Or.inl rfl) x hx, (hIcr hx).1, (hIcr hx).2⟩
    · exact ⟨hOkL _ _ (Or.inr rfl) x hx, (hIcl hx).1, (hIcl hx).2⟩
    · exact ⟨hOkR _ _ (Or.inr rfl) x hx, (hIcr hx).1, (hIcr hx).2⟩
  · rw [hcast]
    have hv₁ : ∀ x, -5 / 4 ≤ v x := fun x ↦ le_sat _
    have hv₂ : ∀ x, v x ≤ 5 / 4 := fun x ↦ sat_le _
    rintro z ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩))
    · exact band_interp (hu₀ x) (hu₁ x) le_rfl (by linarith) (by linarith [hv₁ x])
        (by linarith [hv₂ x])
    · exact band_interp (hu₀ x) (hu₁ x) (by linarith) le_rfl (by linarith [hv₁ x])
        (by linarith [hv₂ x])
    · exact band_interp (hu₀ x) (hu₁ x) (by linarith) le_rfl (by linarith [hv₂ x])
        (by linarith [hv₁ x])
    · exact band_interp (hu₀ x) (hu₁ x) le_rfl (by linarith) (by linarith [hv₂ x])
        (by linarith [hv₁ x])
  · exact crosscap_bands_disjoint hk hclear hIcl hIcr hsql hsqr hFm hFp hOkL hOkR

end GraphMinor.GM20.Draw
