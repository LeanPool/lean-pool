/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw2

/-!
# Drawing a graph in a surface of large genus: slabs for a swap

A slab that swaps the neighbouring heights `t` and `t + 1`. All curves but two run from left to
right
and keep their height order. They are pushed up or down, in the first and last quarter unit of the
strip, so that they stay away from the axis in the middle. The two other curves stay in a band
around
the axis. `slab_of_band` reduces the slab to these two curves. The band is the region between the
curves
with `g = -5/4` from height `t` and `g = 5/4` from height `t + 1`.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

/-- The ramp: `0` at `l` and `r`, and `1` from `l + 1/4` to `r - 1/4`. -/
noncomputable def lam (l r x : ℝ) : ℝ := max 0 (min 1 (min (4 * (x - l)) (4 * (r - x))))

theorem continuous_lam (l r : ℝ) : Continuous (lam l r) := by
  unfold lam
  fun_prop

theorem lam_nonneg (l r x : ℝ) : 0 ≤ lam l r x := le_max_left _ _

theorem lam_le_one (l r x : ℝ) : lam l r x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem lam_left {l r : ℝ} (_h : l ≤ r) : lam l r l = 0 := by
  unfold lam
  rw [max_eq_left]
  exact (min_le_right _ _).trans ((min_le_left _ _).trans (by simp))

theorem lam_right {l r : ℝ} (_h : l ≤ r) : lam l r r = 0 := by
  unfold lam
  rw [max_eq_left]
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (by simp))

theorem lam_eq_one {l r x : ℝ} (h₁ : l + 1 / 4 ≤ x) (h₂ : x ≤ r - 1 / 4) : lam l r x = 1 := by
  unfold lam
  rw [min_eq_left (le_min (by linarith) (by linarith))]
  exact max_eq_right zero_le_one

theorem lam_lt_one {l r x : ℝ} (h : lam l r x < 1) : x < l + 1 / 4 ∨ r - 1 / 4 < x := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact absurd (lam_eq_one hc.1 hc.2) h.ne

/-- The height in the middle of the strip of the curve starting at height `p`. -/
noncomputable def gg (t p : ℕ) : ℝ :=
  if p < t then 3 * ((p : ℝ) - t) - 5 / 4
  else if p = t then -5 / 4
  else if p = t + 1 then 5 / 4
  else 3 * ((p : ℝ) - t - 1) + 5 / 4

theorem gg_lt {t p : ℕ} (h : p < t) : gg t p ≤ -17 / 4 := by
  have h₁ : (p : ℝ) + 1 ≤ t := by exact_mod_cast h
  simp only [gg, ite_eq_left h]
  linarith

theorem gg_gt {t p : ℕ} (h : t + 1 < p) : 17 / 4 ≤ gg t p := by
  have h₁ : (t : ℝ) + 2 ≤ p := by exact_mod_cast h
  simp only [gg]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  linarith

theorem gg_strictMono (t : ℕ) : StrictMono (gg t) := by
  refine strictMono_nat_of_lt_succ fun p ↦ ?_
  have hcast : ((p + 1 : ℕ) : ℝ) = p + 1 := by push_cast; ring
  rcases lt_trichotomy (p + 1) t with h | h | h
  · simp only [gg, ite_eq_left h, ite_eq_left (show p < t by omega)]
    rw [hcast]
    linarith
  · have h₁ : (p : ℝ) + 1 = t := by exact_mod_cast h
    simp only [gg]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    linarith
  · by_cases h₂ : p = t
    · subst h₂
      have h₃ : gg p p = -5 / 4 := by simp [gg]
      have h₄ : gg p (p + 1) = 5 / 4 := by simp [gg]
      rw [h₃, h₄]
      norm_num
    · by_cases h₃ : p = t + 1
      · subst h₃
        have h₄ : gg t (t + 1) = 5 / 4 := by simp [gg]
        have h₅ : gg t (t + 1 + 1) = 3 * (((t + 1 + 1 : ℕ) : ℝ) - t - 1) + 5 / 4 := by
          simp only [gg]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [h₄, h₅]
        push_cast
        linarith
      · simp only [gg]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right
          (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), hcast]
        linarith

/-- The height over `x` of the curve from height `p`. -/
noncomputable def yy (l r : ℝ) (t p : ℕ) (x : ℝ) : ℝ :=
  (1 - lam l r x) * p + lam l r x * gg t p

theorem interp_lt {u A B A' B' : ℝ} (h₀ : 0 ≤ u) (h₁ : u ≤ 1) (hA : A < A') (hB : B < B') :
    (1 - u) * A + u * B < (1 - u) * A' + u * B' := by
  rcases h₀.eq_or_lt with rfl | h₀
  · simpa using hA
  · nlinarith [mul_lt_mul_of_pos_left hB h₀, mul_le_mul_of_nonneg_left hA.le (sub_nonneg.mpr h₁)]

/-- A slab for the swap of `t` and `t + 1`, from two curves that stay in the band. -/
theorem slab_of_band [T2Space (SurfaceModel a b c)] {n : ℕ} (i : Fin n) {l r : ℝ} (hlr : l < r)
    (hgap : ∀ x ∈ Icc l r, lam l r x < 1 → ∀ y, Clear a b c (x, y))
    {Su Sv : Set (ℝ × ℝ)}
    (hu : IsLineWithEnds (qq a b c '' Su) (qq a b c (l, (i : ℕ)))
      (qq a b c (r, ((i : ℕ) + 1 : ℕ))))
    (hv : IsLineWithEnds (qq a b c '' Sv) (qq a b c (l, ((i : ℕ) + 1 : ℕ)))
      (qq a b c (r, (i : ℕ))))
    (hok : ∀ z ∈ Su ∪ Sv, Ok a b c z ∧ l ≤ z.1 ∧ z.1 ≤ r)
    (hband : ∀ z ∈ Su ∪ Sv, (1 - lam l r z.1) * ((i : ℕ) : ℝ) + lam l r z.1 * (-5 / 4) ≤ z.2 ∧
      z.2 ≤ (1 - lam l r z.1) * (((i : ℕ) + 1 : ℕ) : ℝ) + lam l r z.1 * (5 / 4))
    (hd : Disjoint (qq a b c '' Su) (qq a b c '' Sv))
    (hul : ∀ z, Ok a b c z → z.1 ≤ l → qq a b c z ∈ qq a b c '' Su →
      qq a b c z = qq a b c (l, (i : ℕ)))
    (hur : ∀ z, Ok a b c z → r ≤ z.1 → qq a b c z ∈ qq a b c '' Su →
      qq a b c z = qq a b c (r, ((i : ℕ) + 1 : ℕ)))
    (hvl : ∀ z, Ok a b c z → z.1 ≤ l → qq a b c z ∈ qq a b c '' Sv →
      qq a b c z = qq a b c (l, ((i : ℕ) + 1 : ℕ)))
    (hvr : ∀ z, Ok a b c z → r ≤ z.1 → qq a b c z ∈ qq a b c '' Sv →
      qq a b c z = qq a b c (r, (i : ℕ))) :
    Slab a b c (n + 1) l r (Equiv.swap i.castSucc i.succ) := by
  classical
  set t : ℕ := (i : ℕ) with ht
  have hcont : ∀ p : ℕ, ContinuousOn (yy l r t p) (Icc l r) := fun p ↦ by
    unfold yy
    have := continuous_lam l r
    exact Continuous.continuousOn (by fun_prop)
  have hgen : ∀ p : ℕ, p ≠ t → p ≠ t + 1 → ∀ x ∈ Icc l r, Clear a b c (x, yy l r t p x) := by
    intro p h₁ h₂ x hx
    rcases (lam_le_one l r x).lt_or_eq with h | h
    · exact hgap x hx h _
    · refine clear_of_abs ?_
      simp only [yy, h]
      rcases lt_or_gt_of_ne h₁ with h₃ | h₃
      · have := gg_lt h₃
        rw [abs_of_neg (by linarith)]
        linarith
      · have := gg_gt (show t + 1 < p by omega)
        rw [abs_of_pos (by linarith)]
        linarith
  have hyl : ∀ p : ℕ, yy l r t p l = p := fun p ↦ by simp [yy, lam_left hlr.le]
  have hyr : ∀ p : ℕ, yy l r t p r = p := fun p ↦ by simp [yy, lam_right hlr.le]
  let G : ℕ → Set (ℝ × ℝ) := fun p ↦ gr (yy l r t p) l r
  have hGline : ∀ p : ℕ, p ≠ t → p ≠ t + 1 →
      IsLineWithEnds (qq a b c '' G p) (qq a b c (l, p)) (qq a b c (r, p)) := by
    intro p h₁ h₂
    have := isLine_gr (a := a) (b := b) (c := c) (e := l - 1) hlr (hcont p)
      (fun x hx ↦ (hgen p h₁ h₂ x hx).ok) (fun x hx _ ↦ hgen p h₁ h₂ x hx)
    rwa [hyl, hyr] at this
  have hGclear : ∀ p : ℕ, p ≠ t → p ≠ t + 1 → ∀ z ∈ G p, Clear a b c z := by
    rintro p h₁ h₂ _ ⟨x, hx, rfl⟩
    exact hgen p h₁ h₂ x hx
  have hGend : ∀ p : ℕ, p ≠ t → p ≠ t + 1 → ∀ z, Ok a b c z → (z.1 ≤ l ∨ r ≤ z.1) →
      qq a b c z ∈ qq a b c '' G p → qq a b c z = qq a b c (z.1, p) ∧ (z.1 = l ∨ z.1 = r) := by
    rintro p h₁ h₂ z hz hside ⟨_, ⟨x, hx, rfl⟩, heq⟩
    have h₃ := eq_of_qq_eq (hgen p h₁ h₂ x hx) hz heq
    subst h₃
    rcases hside with h₄ | h₄
    · have h₅ : x = l := le_antisymm h₄ hx.1
      subst h₅
      exact ⟨by simp [hyl], Or.inl rfl⟩
    · have h₅ : x = r := le_antisymm hx.2 h₄
      subst h₅
      exact ⟨by simp [hyr], Or.inr rfl⟩
  have hGG : ∀ p p' : ℕ, p < p' → Disjoint (G p) (G p') := by
    intro p p' hpp
    rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ ⟨x', -, h⟩
    obtain ⟨rfl, h₂⟩ := Prod.ext_iff.mp h
    have h₃ : yy l r t p x' < yy l r t p' x' :=
      interp_lt (lam_nonneg _ _ _) (lam_le_one _ _ _) (by exact_mod_cast hpp) (gg_strictMono t hpp)
    simp only at h₂
    exact h₃.ne h₂.symm
  have hband' : ∀ p : ℕ, p ≠ t → p ≠ t + 1 → Disjoint (Su ∪ Sv) (G p) := by
    intro p h₁ h₂
    rw [Set.disjoint_left]
    rintro z hz ⟨x, -, rfl⟩
    obtain ⟨h₃, h₄⟩ := hband _ hz
    simp only at h₃ h₄
    have hu₀ := lam_nonneg l r x
    have hu₁ := lam_le_one l r x
    rcases lt_or_gt_of_ne h₁ with h₅ | h₅
    · have := interp_lt (A := p) (A' := t) (B := gg t p) (B' := -5 / 4) hu₀ hu₁
        (by exact_mod_cast h₅) (by have := gg_lt h₅; linarith)
      simp only [yy] at *
      linarith
    · have := interp_lt (A := ((t + 1 : ℕ) : ℝ)) (A' := p) (B := 5 / 4) (B' := gg t p) hu₀ hu₁
        (by exact_mod_cast (show t + 1 < p by omega))
        (by have := gg_gt (show t + 1 < p by omega); linarith)
      simp only [yy] at *
      linarith
  have hGdisj : ∀ (S : Set (ℝ × ℝ)), S ⊆ Su ∪ Sv → ∀ p : ℕ, p ≠ t → p ≠ t + 1 →
      Disjoint (qq a b c '' S) (qq a b c '' G p) := fun S hS p h₁ h₂ ↦
    disjoint_of_below (fun z hz ↦ (hok z (hS hz)).1) (hGclear p h₁ h₂)
      ((hband' p h₁ h₂).mono_left hS)
  have hGzone : ∀ p : ℕ, p ≠ t → p ≠ t + 1 → qq a b c '' G p ⊆ Zone a b c l r := by
    rintro p h₁ h₂ _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨(hgen p h₁ h₂ x hx).ok, hx.1, hx.2⟩, rfl⟩
  have hSzone : ∀ S : Set (ℝ × ℝ), S ⊆ Su ∪ Sv → qq a b c '' S ⊆ Zone a b c l r := by
    rintro S hS _ ⟨z, hz, rfl⟩
    exact ⟨z, hok z (hS hz), rfl⟩
  have hival : (i.castSucc : ℕ) = t := rfl
  have hsval : (i.succ : ℕ) = t + 1 := rfl
  have hne : i.castSucc ≠ i.succ := fun h ↦ by
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hnet : ∀ {p : Fin (n + 1)}, p ≠ i.castSucc → (p : ℕ) ≠ t := fun h h' ↦ h (Fin.ext h')
  have hnes : ∀ {p : Fin (n + 1)}, p ≠ i.succ → (p : ℕ) ≠ t + 1 := fun h h' ↦ h (Fin.ext h')
  let P : Fin (n + 1) → Set (SurfaceModel a b c) := fun p ↦
    if p = i.castSucc then qq a b c '' Su else if p = i.succ then qq a b c '' Sv
    else qq a b c '' G p
  have hP₁ : P i.castSucc = qq a b c '' Su := ite_eq_left rfl
  have hP₂ : P i.succ = qq a b c '' Sv := by
    simp [P, hne.symm]
  have hP₃ : ∀ {p}, p ≠ i.castSucc → p ≠ i.succ → P p = qq a b c '' G p := fun h₁ h₂ ↦ by
    simp only [P]
    rw [ite_eq_right h₁, ite_eq_right h₂]
  refine ⟨P, fun p ↦ ?_, ?_, fun p ↦ ?_, fun p z hz hzl hm ↦ ?_, fun p z hz hzr hm ↦ ?_⟩
  · by_cases h₁ : p = i.castSucc
    · subst h₁
      rw [hP₁, Equiv.swap_apply_left]
      exact hu
    by_cases h₂ : p = i.succ
    · subst h₂
      rw [hP₂, Equiv.swap_apply_right]
      exact hv
    · rw [hP₃ h₁ h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
      exact hGline p (hnet h₁) (hnes h₂)
  · have key : ∀ p p' : Fin (n + 1), (p : ℕ) < p' → Disjoint (P p) (P p') := by
      intro p p' hpp
      by_cases h₁ : p = i.castSucc
      · subst h₁
        by_cases h₂ : p' = i.succ
        · subst h₂
          rw [hP₁, hP₂]
          exact hd
        · have h₃ : p' ≠ i.castSucc := fun h ↦ by subst h; omega
          rw [hP₁, hP₃ h₃ h₂]
          exact hGdisj _ subset_union_left p' (hnet h₃) (hnes h₂)
      by_cases h₂ : p = i.succ
      · subst h₂
        have h₃ : p' ≠ i.castSucc := fun h ↦ by
          subst h
          simp only [Fin.val_castSucc, Fin.val_succ] at hpp
          omega
        have h₄ : p' ≠ i.succ := fun h ↦ by subst h; omega
        rw [hP₂, hP₃ h₃ h₄]
        exact hGdisj _ subset_union_right p' (hnet h₃) (hnes h₄)
      rw [hP₃ h₁ h₂]
      by_cases h₃ : p' = i.castSucc
      · subst h₃
        rw [hP₁]
        exact (hGdisj _ subset_union_left p (hnet h₁) (hnes h₂)).symm
      by_cases h₄ : p' = i.succ
      · subst h₄
        rw [hP₂]
        exact (hGdisj _ subset_union_right p (hnet h₁) (hnes h₂)).symm
      rw [hP₃ h₃ h₄]
      exact disjoint_of_below (fun z hz ↦ (hGclear p (hnet h₁) (hnes h₂) z hz).ok)
        (hGclear p' (hnet h₃) (hnes h₄)) (hGG _ _ hpp)
    intro p p' hne'
    rcases lt_or_gt_of_ne (fun h ↦ hne' (Fin.ext h) : (p : ℕ) ≠ p') with h | h
    · exact key p p' h
    · exact (key p' p h).symm
  · by_cases h₁ : p = i.castSucc
    · subst h₁
      rw [hP₁]
      exact hSzone _ subset_union_left
    by_cases h₂ : p = i.succ
    · subst h₂
      rw [hP₂]
      exact hSzone _ subset_union_right
    · rw [hP₃ h₁ h₂]
      exact hGzone p (hnet h₁) (hnes h₂)
  · by_cases h₁ : p = i.castSucc
    · subst h₁
      rw [hP₁] at hm
      exact hul z hz hzl hm
    by_cases h₂ : p = i.succ
    · subst h₂
      rw [hP₂] at hm
      exact hvl z hz hzl hm
    · rw [hP₃ h₁ h₂] at hm
      obtain ⟨h₃, h₄⟩ := hGend p (hnet h₁) (hnes h₂) z hz (Or.inl hzl) hm
      rcases h₄ with h₄ | h₄
      · rwa [h₄] at h₃
      · exfalso
        linarith
  · by_cases h₁ : p = i.castSucc
    · subst h₁
      rw [hP₁] at hm
      rw [Equiv.swap_apply_left]
      exact hur z hz hzr hm
    by_cases h₂ : p = i.succ
    · subst h₂
      rw [hP₂] at hm
      rw [Equiv.swap_apply_right]
      exact hvr z hz hzr hm
    · rw [hP₃ h₁ h₂] at hm
      rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
      obtain ⟨h₃, h₄⟩ := hGend p (hnet h₁) (hnes h₂) z hz (Or.inr hzr) hm
      rcases h₄ with h₄ | h₄
      · exfalso
        linarith
      · rwa [h₄] at h₃

end GraphMinor.GM20.Draw
