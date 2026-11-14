/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.Basic

/-!
# T1 for Atkin–Lehner elements and translations

* `S_mem_normalizer'`: S_k normalizes Γ₀(N) for k ∣ h(N);
* `isAtkinLehner_mem_normalizer'`: every AL element w_Q (Q ∣ N) normalizes Γ₀(N);
* `exists_isAtkinLehner'`: AL elements exist for Q ∥ N;
* `isAtkinLehner_mul_inv_mem'`: two AL elements for Q differ by Γ₀(N).

The AL computations are the identities W γ adj(W) = Q·M₁, adj(W) γ W = Q·M₂, W adj(W') = Q·M₃
with explicit integer matrices Mᵢ (checked symbolically in sympy before being given to `ring`).
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

/-! ### Scalar bookkeeping -/

theorem inv_mul_inv_mul_eq_one {Q s : ℝ} (hs : s * s = Q) (hQ : Q ≠ 0) : s⁻¹ * s⁻¹ * Q = 1 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hQ (by simpa using hs.symm)
  rw [← hs]
  field_simp

theorem smul_mul_mul_smul_eq {Q s : ℝ} (hs : s * s = Q) (hQ : Q ≠ 0)
    {W γ A X : Matrix (Fin 2) (Fin 2) ℝ} (h : W * γ * A = Q • X) :
    (s⁻¹ • W) * γ * (s⁻¹ • A) = X := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul,
    inv_mul_inv_mul_eq_one hs hQ, one_smul]

theorem smul_mul_smul_eq {Q s : ℝ} (hs : s * s = Q) (hQ : Q ≠ 0)
    {W A X : Matrix (Fin 2) (Fin 2) ℝ} (h : W * A = Q • X) :
    (s⁻¹ • W) * (s⁻¹ • A) = X := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul,
    inv_mul_inv_mul_eq_one hs hQ, one_smul]

theorem coe_inv_of_coe_eq_smul {g : SL(2, ℝ)} {s a b c d : ℝ}
    (h : (g : Matrix (Fin 2) (Fin 2) ℝ) = s • !![a, b; c, d]) :
    ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = s • !![d, -b; -c, a] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, h, adjugate_smul, adjugate_fin_two_of]
  simp

/-! ### Translations -/

theorem S_conj_mem {N k : ℕ} (hN : N ≠ 0) (hk : k ∣ hPart N) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Gamma0R N) :
    S k * γ * (S k)⁻¹ ∈ Gamma0R N ∧ (S k)⁻¹ * γ * S k ∈ Gamma0R N := by
  have hk24 : k ∣ 24 := dvd_trans hk (hPart_dvd_24 N)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (hPart_pos N).ne' (Nat.eq_zero_of_zero_dvd hk)
  have hksq : k ^ 2 ∣ N := dvd_trans (pow_dvd_pow_of_dvd hk 2) (hPart_sq_dvd hN)
  obtain ⟨a, b, c, d, hdet, hc, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hkc : ((k : ℤ) ^ 2) ∣ c := dvd_trans (by exact_mod_cast hksq) hc
  -- a ≡ d (mod k)
  have had : a * d ≡ 1 [ZMOD k] := by
    have hkc1 : (k : ℤ) ∣ c := dvd_trans (dvd_pow_self _ two_ne_zero) hkc
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, show a * d - 1 = b * c by linarith]
    exact dvd_mul_of_dvd_right hkc1 b
  obtain ⟨e, he⟩ := (Int.ModEq.dvd (modEq_of_mul_modEq_one hk24 had))
  obtain ⟨c', rfl⟩ := hkc
  have hd : d = a + k * e := by linarith
  subst hd
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  constructor
  · refine mem_Gamma0R_of_entries (a + k * c') (b + e - c') (k ^ 2 * c') (a + k * e - k * c')
      ?_ hc
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hγm, coe_S,
      coe_S_inv, mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · refine mem_Gamma0R_of_entries (a - k * c') (b - e - c') (k ^ 2 * c') (a + k * e + k * c')
      ?_ hc
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hγm, coe_S,
      coe_S_inv, mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **T1** for translations. -/
theorem S_mem_normalizer' {N k : ℕ} [NeZero N] (hk : k ∣ hPart N) : S k ∈ Norm0 N :=
  mem_Norm0_of (fun _ hγ => (S_conj_mem (NeZero.ne N) hk hγ).1)
    (fun _ hγ => (S_conj_mem (NeZero.ne N) hk hγ).2)

/-! ### Atkin–Lehner elements -/

theorem isAtkinLehner_conj_mem {N Q : ℕ} (hQ : Q ∣ N) (hQ0 : Q ≠ 0) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N) :
    g * γ * g⁻¹ ∈ Gamma0R N ∧ g⁻¹ * γ * g ∈ Gamma0R N := by
  obtain ⟨x, y, z, w, -, hgm⟩ := hg
  obtain ⟨K, rfl⟩ := hQ
  obtain ⟨a, b, c', d, -, ⟨c, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hs : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hQr : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hQ0
  have hginv := coe_inv_of_coe_eq_smul hgm
  constructor
  · refine mem_Gamma0R_of_entries
      ((Q : ℤ) * w * (x * a + y * (K : ℤ) * c) - (K : ℤ) * z * ((Q : ℤ) * x * b + y * d))
      (-y * (x * a + y * (K : ℤ) * c) + x * ((Q : ℤ) * x * b + y * d))
      (((Q * K : ℕ) : ℤ) * (w * (z * a + (Q : ℤ) * w * c) - z * ((K : ℤ) * z * b + w * d)))
      (-(K : ℤ) * y * (z * a + (Q : ℤ) * w * c) + (Q : ℤ) * x * ((K : ℤ) * z * b + w * d)) ?_
        (dvd_mul_right _ _)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgm, hγm, hginv]
    apply smul_mul_mul_smul_eq hs hQr
    rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · refine mem_Gamma0R_of_entries
      ((Q : ℤ) * x * (w * a - y * (K : ℤ) * c) + (K : ℤ) * z * ((Q : ℤ) * w * b - y * d))
      (y * (w * a - y * (K : ℤ) * c) + w * ((Q : ℤ) * w * b - y * d))
      (((Q * K : ℕ) : ℤ) * (x * (-z * a + (Q : ℤ) * x * c) + z * (x * d - (K : ℤ) * z * b)))
      ((K : ℤ) * y * (-z * a + (Q : ℤ) * x * c) + (Q : ℤ) * w * (x * d - (K : ℤ) * z * b)) ?_
        (dvd_mul_right _ _)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgm, hγm, hginv]
    apply smul_mul_mul_smul_eq hs hQr
    rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **T1** for Atkin–Lehner elements. -/
theorem isAtkinLehner_mem_normalizer' {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : g ∈ Norm0 N := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  exact mem_Norm0_of (fun _ hγ => (isAtkinLehner_conj_mem hQ hQ0 hg hγ).1)
    (fun _ hγ => (isAtkinLehner_conj_mem hQ hQ0 hg hγ).2)

/-- The AL element with explicit integer data. -/
def alElt (N Q : ℕ) (x y z w : ℤ) (h : (Q : ℤ) ^ 2 * x * w - N * y * z = Q) (hQ : Q ≠ 0) :
    SL(2, ℝ) :=
  ⟨(Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w], by
    have hr : (Q : ℝ) ^ 2 * x * w - N * y * z = Q := by exact_mod_cast h
    have hQr : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hQ
    rw [det_smul, Fintype.card_fin, det_fin_two_of, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [show (Q : ℝ) * x * (Q * w) - y * (N * z) = Q by linear_combination hr]
    exact inv_mul_cancel₀ hQr⟩

theorem alElt_isAtkinLehner {N Q : ℕ} {x y z w : ℤ} (h) (hQ) :
    IsAtkinLehner N Q (alElt N Q x y z w h hQ) := ⟨x, y, z, w, h, rfl⟩

/-- Atkin–Lehner elements exist for Q ∥ N. -/
theorem exists_isAtkinLehner' {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hcop : Nat.Coprime Q (N / Q)) :
    ∃ g, IsAtkinLehner N Q g := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  obtain ⟨K, rfl⟩ := hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)] at hcop
  have hb := Int.gcd_eq_gcd_ab Q K
  rw [Int.gcd_natCast_natCast, hcop] at hb
  refine ⟨alElt (Q * K) Q (Int.gcdA Q K) (-Int.gcdB Q K) 1 1 ?_ hQ0, alElt_isAtkinLehner _ _⟩
  push_cast
  linear_combination (Q : ℤ) * hb.symm

theorem isAtkinLehner_mul_inv_mem' {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g g' : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) (hg' : IsAtkinLehner N Q g') : g * g'⁻¹ ∈ Gamma0R N := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  obtain ⟨x, y, z, w, -, hgm⟩ := hg
  obtain ⟨x2, y2, z2, w2, -, hgm'⟩ := hg'
  obtain ⟨K, rfl⟩ := hQ
  have hs : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hQr : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hQ0
  have hginv := coe_inv_of_coe_eq_smul hgm'
  refine mem_Gamma0R_of_entries ((Q : ℤ) * x * w2 - (K : ℤ) * y * z2) (x2 * y - x * y2)
    (((Q * K : ℕ) : ℤ) * (z * w2 - w * z2)) ((Q : ℤ) * w * x2 - (K : ℤ) * z * y2) ?_
      (dvd_mul_right _ _)
  rw [Matrix.SpecialLinearGroup.coe_mul, hgm, hginv]
  apply smul_mul_smul_eq hs hQr
  rw [mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end

end CongruenceNormalizers
