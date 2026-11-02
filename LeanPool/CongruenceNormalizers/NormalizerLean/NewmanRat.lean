/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.T1General

/-!
# Newman's theorem, step 1: normalizing elements are rational up to a scalar ([Nw §2])

If g = [[x, y], [z, w]] normalizes Γ₀(N), the conjugates of T, U, TU are integral, so
x², xz, z², Nyw, Ny², Nw², Nxw, Nxy, Nzw, Nyz are integers.  With t = x (or t = z if x = 0),
N t x, N t y, N t z, N t w are integers, and g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (dividing by the gcd of the entries).
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

/-- `r` is an integer. -/
def IsIntR (r : ℝ) : Prop := ∃ m : ℤ, r = m

theorem IsIntR.add {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r + s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m + n, by push_cast; ring⟩
theorem IsIntR.sub {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r - s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m - n, by push_cast; ring⟩
theorem IsIntR.mul {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r * s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m * n, by push_cast; ring⟩
theorem IsIntR.neg {r : ℝ} (hr : IsIntR r) : IsIntR (-r) := by
  obtain ⟨m, rfl⟩ := hr; exact ⟨-m, by push_cast; ring⟩
theorem IsIntR.int (m : ℤ) : IsIntR m := ⟨m, rfl⟩
theorem IsIntR.nat (m : ℕ) : IsIntR m := ⟨m, by simp⟩
theorem IsIntR.one : IsIntR 1 := ⟨1, by simp⟩

theorem isIntR_entries_of_mem {N : ℕ} {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N) (i j : Fin 2) :
    IsIntR ((γ : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain ⟨a, b, c, d, -, -, hm⟩ := exists_entries_of_mem_Gamma0R hγ
  rw [hm]
  fin_cases i <;> fin_cases j <;> simp [IsIntR.int]

/-- The unit upper-unipotent matrix. -/
def matT : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩
/-- The lower-unipotent matrix with lower-left entry N. -/
def matU (N : ℕ) : SL(2, ℝ) := ⟨!![1, 0; (N : ℝ), 1], by simp [det_fin_two_of]⟩

theorem matT_mem (N : ℕ) : matT ∈ Gamma0R N :=
  mem_Gamma0R_of_entries 1 1 0 1 (by simp [matT]) (dvd_zero _)

theorem matU_mem (N : ℕ) : matU N ∈ Gamma0R N :=
  mem_Gamma0R_of_entries 1 0 N 1 (by simp [matU]) (dvd_refl _)

theorem coe_conj (g Y : SL(2, ℝ)) :
    ((g * Y * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) * (Y : Matrix (Fin 2) (Fin 2) ℝ) *
        (g : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]

/-- The products of entries that are integers. -/
theorem integral_products_of_normalizer {N : ℕ} {Γ : Subgroup SL(2, ℝ)}
    (subgroup_le : Γ ≤ Gamma0R N) (translation_mem : matT ∈ Γ)
    (lower_translation_mem : matU N ∈ Γ) {g : SL(2, ℝ)}
    (hg : g ∈ NormG Γ) {x y z w : ℝ}
    (hx : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = x) (hy : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = y)
    (hz : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = z) (hw : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = w) :
    IsIntR (x * x) ∧ IsIntR (x * z) ∧ IsIntR (z * z) ∧ IsIntR (N * (y * y)) ∧
      IsIntR (N * (w * w)) ∧ IsIntR (N * (y * w)) ∧ IsIntR (N * (x * w)) ∧
      IsIntR (N * (x * y)) ∧ IsIntR (N * (z * w)) ∧ IsIntR (N * (y * z)) := by
  have hconj : ∀ Y ∈ Γ, g * Y * g⁻¹ ∈ Γ := fun Y hY =>
    (Subgroup.mem_normalizer_iff.1 hg Y).1 hY
  have hT := isIntR_entries_of_mem (subgroup_le (hconj _ translation_mem))
  have hU := isIntR_entries_of_mem (subgroup_le (hconj _ lower_translation_mem))
  have hTU := isIntR_entries_of_mem
    (subgroup_le (hconj _ (mul_mem translation_mem lower_translation_mem)))
  have hdet : x * w - y * z = 1 := by
    have := g.2
    rw [det_fin_two, hx, hy, hz, hw] at this
    exact this
  -- explicit conjugates
  have eT : ∀ i j, ((g * matT * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      !![1 - x * z, x * x; -(z * z), 1 + x * z] i j := by
    intro i j
    rw [coe_conj, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp only [matT, Fin.isValue, hw, hy, hz, hx, Fin.zero_eta, Matrix.mul_apply, of_apply,
        cons_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, mul_one,
        mul_zero, add_zero, mul_neg, Fin.mk_one] <;>
      first | ring1 | (linear_combination hdet)
  have eU : ∀ i j, ((g * matU N * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      !![1 + N * (y * w), -(N * (y * y)); N * (w * w), 1 - N * (y * w)] i j := by
    intro i j
    rw [coe_conj, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp only [matU, Fin.isValue, hw, hy, hz, hx, Fin.zero_eta, Matrix.mul_apply, of_apply,
        cons_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, mul_one,
        mul_zero, zero_add, mul_neg, Fin.mk_one] <;>
      first | ring1 | (linear_combination hdet)
  have eTU : ∀ i j, ((g * (matT * matU N) * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      !![1 - x * z + N * (y * w) + N * (x * w), x * x - N * (y * y) - N * (x * y);
        -(z * z) + N * (w * w) + N * (z * w), 1 + x * z - N * (y * w) - N * (y * z)] i j := by
    intro i j
    rw [coe_conj, Matrix.SpecialLinearGroup.coe_mul, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp only [matT, matU, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
        one_smul, tail_cons, empty_vecMul, add_zero, add_cons, zero_add, empty_add_empty,
        zero_smul, empty_mul, Equiv.symm_apply_apply, Fin.isValue, hw, hy, hz, hx, Fin.zero_eta,
        Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_zero,
        cons_val_one, mul_one, mul_neg, Fin.mk_one] <;>
      first | ring1 | (linear_combination hdet)
  have t01 := hT 0 1; rw [eT] at t01; simp only [Fin.isValue, of_apply, cons_val', cons_val_one,
    cons_val_fin_one, cons_val_zero] at t01
  have t00 := hT 0 0; rw [eT] at t00; simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one] at t00
  have t10 := hT 1 0; rw [eT] at t10; simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one] at t10
  have u01 := hU 0 1; rw [eU] at u01; simp only [Fin.isValue, of_apply, cons_val', cons_val_one,
    cons_val_fin_one, cons_val_zero] at u01
  have u10 := hU 1 0; rw [eU] at u10; simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one] at u10
  have u00 := hU 0 0; rw [eU] at u00; simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one] at u00
  have v00 := hTU 0 0; rw [eTU] at v00; simp only [Fin.isValue, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one] at v00
  have v01 := hTU 0 1; rw [eTU] at v01; simp only [Fin.isValue, of_apply, cons_val', cons_val_one,
    cons_val_fin_one, cons_val_zero] at v01
  have v10 := hTU 1 0; rw [eTU] at v10; simp only [Fin.isValue, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val_one] at v10
  have v11 := hTU 1 1; rw [eTU] at v11; simp only [Fin.isValue, of_apply, cons_val', cons_val_one,
    cons_val_fin_one] at v11
  have hxz : IsIntR (x * z) := by
    have := (IsIntR.one.sub t00)
    simpa using this
  have hzz : IsIntR (z * z) := by simpa using t10.neg
  have hyy : IsIntR (N * (y * y)) := by simpa using u01.neg
  have hyw : IsIntR (N * (y * w)) := by
    have := u00.sub IsIntR.one
    simpa using this
  refine ⟨t01, hxz, hzz, hyy, u10, hyw, ?_, ?_, ?_, ?_⟩
  · have := ((v00.sub IsIntR.one).add hxz).sub hyw
    convert this using 1; ring
  · have := ((t01.sub hyy).sub v01)
    convert this using 1; ring
  · have := ((v10.add hzz).sub u10)
    convert this using 1; ring
  · have := (((IsIntR.one.add hxz).sub hyw).sub v11)
    convert this using 1; ring

/-- Integral entry products for the full congruence subgroup. -/
theorem products_int {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) {x y z w : ℝ}
    (hx : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = x) (hy : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = y)
    (hz : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = z) (hw : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = w) :
    IsIntR (x * x) ∧ IsIntR (x * z) ∧ IsIntR (z * z) ∧ IsIntR (N * (y * y)) ∧
      IsIntR (N * (w * w)) ∧ IsIntR (N * (y * w)) ∧ IsIntR (N * (x * w)) ∧
      IsIntR (N * (x * y)) ∧ IsIntR (N * (z * w)) ∧ IsIntR (N * (y * z))  := by
  exact integral_products_of_normalizer le_rfl (matT_mem N) (matU_mem N) hg hx hy hz hw

/-- **Step 1** ([Nw §2]): g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ without a common prime
factor. -/
theorem primitive_form_of_normalizer {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℝ)}
    (subgroup_le : Γ ≤ Gamma0R N) (translation_mem : matT ∈ Γ)
    (lower_translation_mem : matU N ∈ Γ) (scale : ℕ) (scale_pos : 0 < scale)
    {g : SL(2, ℝ)} (hg : g ∈ NormG Γ) :
    ∃ (κ : ℝ) (α β γ δ : ℤ), κ ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ)) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        κ • !![(α : ℝ), (β : ℝ) / scale; (scale : ℝ) * γ, (δ : ℝ)] := by
  set x := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with hx
  set y := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hy
  set z := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hz
  set w := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hw
  obtain ⟨hxx, hxz, hzz, hyy, hww, hyw, hxw, hxy, hzw, hyz⟩ :=
    integral_products_of_normalizer subgroup_le translation_mem lower_translation_mem hg
      hx.symm hy.symm hz.symm hw.symm
  have hdet : x * w - y * z = 1 := by
    have := g.2
    rwa [det_fin_two] at this
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hh : (scale : ℝ) ≠ 0 := Nat.cast_ne_zero.2 scale_pos.ne'
  -- a nonzero t with N t x, N t y, N t z, N t w integral
  obtain ⟨t, ht, htx, hty, htz, htw⟩ : ∃ t : ℝ, t ≠ 0 ∧ IsIntR (N * t * x) ∧ IsIntR (N * t * y) ∧
      IsIntR (N * t * z) ∧ IsIntR (N * t * w) := by
    by_cases hx0 : x = 0
    · have hz0 : z ≠ 0 := by
        intro hz0
        rw [hx0, hz0] at hdet
        simp at hdet
      refine ⟨z, hz0, ?_, ?_, ?_, ?_⟩
      · convert (IsIntR.nat N).mul hxz using 1; ring
      · convert hyz using 1; ring
      · convert (IsIntR.nat N).mul hzz using 1; ring
      · convert hzw using 1; ring
    · refine ⟨x, hx0, ?_, ?_, ?_, ?_⟩
      · convert (IsIntR.nat N).mul hxx using 1; ring
      · convert hxy using 1; ring
      · convert (IsIntR.nat N).mul hxz using 1; ring
      · convert hxw using 1; ring
  obtain ⟨Ix, hIx⟩ := htx
  obtain ⟨Iy, hIy⟩ := hty
  obtain ⟨Iz, hIz⟩ := htz
  obtain ⟨Iw, hIw⟩ := htw
  set h := scale
  set M0 : ℤ := h * Ix
  set M1 : ℤ := h ^ 2 * Iy
  set M2 : ℤ := Iz
  set M3 : ℤ := h * Iw
  set G : ℕ := Int.gcd (Int.gcd M0 M1) (Int.gcd M2 M3) with hG
  have hNt : (N : ℝ) * t ≠ 0 := mul_ne_zero hN ht
  have hG0 : G ≠ 0 := by
    intro hG0
    simp only [hG, Int.gcd_eq_zero_iff, Nat.cast_eq_zero] at hG0
    obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hG0
    have hx0 : x = 0 := by
      have : (N : ℝ) * t * x = 0 := by
        rw [hIx]
        have : Ix = 0 := by
          simp only [M0] at h0
          rcases mul_eq_zero.1 h0 with h' | h'
          · exact absurd (by exact_mod_cast h') scale_pos.ne'
          · exact h'
        simp [this]
      exact (mul_eq_zero.1 this).resolve_left hNt
    have hy0 : y = 0 := by
      have : (N : ℝ) * t * y = 0 := by
        rw [hIy]
        have : Iy = 0 := by
          simp only [M1] at h1
          rcases mul_eq_zero.1 h1 with h' | h'
          · have h'' : (h : ℤ) = 0 := (pow_eq_zero_iff two_ne_zero).1 h'
            exact absurd (by exact_mod_cast h'' : h = 0) scale_pos.ne'
          · exact h'
        simp [this]
      exact (mul_eq_zero.1 this).resolve_left hNt
    rw [hx0, hy0] at hdet
    simp at hdet
  have hGdvd : ∀ m : ℤ, m = M0 ∨ m = M1 ∨ m = M2 ∨ m = M3 → (G : ℤ) ∣ m := by
    rintro m (rfl | rfl | rfl | rfl)
    · exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    · exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
  obtain ⟨α, hα⟩ := hGdvd M0 (Or.inl rfl)
  obtain ⟨β, hβ⟩ := hGdvd M1 (Or.inr (Or.inl rfl))
  obtain ⟨γ, hγ⟩ := hGdvd M2 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨δ, hδ⟩ := hGdvd M3 (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨G / ((h : ℝ) * N * t), α, β, γ, δ, ?_, ?_, ?_⟩
  · exact div_ne_zero (Nat.cast_ne_zero.2 hG0) (mul_ne_zero (mul_ne_zero hh hN) ht)
  · rintro p hp ⟨hpα, hpβ, hpγ, hpδ⟩
    obtain ⟨α', hα'⟩ := hpα
    obtain ⟨β', hβ'⟩ := hpβ
    obtain ⟨γ', hγ'⟩ := hpγ
    obtain ⟨δ', hδ'⟩ := hpδ
    have hpG : ((p * G : ℕ) : ℤ) ∣ (G : ℤ) := by
      have h0 : ((p * G : ℕ) : ℤ) ∣ M0 := ⟨α', by rw [hα, hα']; push_cast; ring⟩
      have h1 : ((p * G : ℕ) : ℤ) ∣ M1 := ⟨β', by rw [hβ, hβ']; push_cast; ring⟩
      have h2 : ((p * G : ℕ) : ℤ) ∣ M2 := ⟨γ', by rw [hγ, hγ']; push_cast; ring⟩
      have h3 : ((p * G : ℕ) : ℤ) ∣ M3 := ⟨δ', by rw [hδ, hδ']; push_cast; ring⟩
      rw [hG]
      exact Int.dvd_coe_gcd (Int.dvd_coe_gcd h0 h1) (Int.dvd_coe_gcd h2 h3)
    have : p * G ∣ G := by exact_mod_cast hpG
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hG0) this
    have := hp.two_le
    nlinarith [Nat.pos_of_ne_zero hG0]
  · have hGr : (G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hG0
    have eα : (G : ℝ) * α = h * (N * t * x) := by rw [hIx]; exact_mod_cast hα.symm
    have eβ : (G : ℝ) * β = h ^ 2 * (N * t * y) := by rw [hIy]; exact_mod_cast hβ.symm
    have eγ : (G : ℝ) * γ = N * t * z := by rw [hIz]; exact_mod_cast hγ.symm
    have eδ : (G : ℝ) * δ = h * (N * t * w) := by rw [hIw]; exact_mod_cast hδ.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hx, ← hy, ← hz, ← hw]
    · field_simp
      linear_combination -eα
    · field_simp
      linear_combination -eβ
    · field_simp
      linear_combination -eγ
    · field_simp
      linear_combination -eδ

/-- Primitive rational representatives for the full congruence subgroup. -/
theorem exists_prim_form {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) :
    ∃ (κ : ℝ) (α β γ δ : ℤ), κ ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ)) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        κ • !![(α : ℝ), (β : ℝ) / hPart N; (hPart N : ℝ) * γ, (δ : ℝ)]  := by
  exact primitive_form_of_normalizer le_rfl (matT_mem N) (matU_mem N)
    (hPart N) (hPart_pos N) hg

end

end CongruenceNormalizers
