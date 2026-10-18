/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.AtkinLehner

/-!
# T1 in general: matrices of Newman's form (8′) normalize Γ₀(N) ([Nw §1])

With N = e·m·h² (h = h(N), n = N/h² = e·m), g = (ε/√e)·G, G = [[ae, b/h], [Nc/h, de]], and
γ = [[x, y], [Nz, x + hf]] ∈ Γ₀(N) (t ≡ x mod h because units mod h ∣ 24 square to 1),
G γ adj(G) = e·M with M the explicit integer matrix below (checked in sympy first).
Also `conjGamma0n_le_normalizer`: D⁻¹Γ₀(n)D consists of (8′)-matrices with e = 1.
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

theorem smul_mul_mul_smul_eq_of {s Q : ℝ} (hs : s * s * Q = 1)
    {W γ A X : Matrix (Fin 2) (Fin 2) ℝ} (h : W * γ * A = Q • X) :
    (s • W) * γ * (s • A) = X := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul, hs, one_smul]

theorem hPart_sq_mul_nPart (N : ℕ) (hN : N ≠ 0) : nPart N * hPart N ^ 2 = N :=
  Nat.div_mul_cancel (hPart_sq_dvd hN)

theorem isNewmanForm_inv {N : ℕ} {g : SL(2, ℝ)} (hg : IsNewmanForm N g) : IsNewmanForm N g⁻¹ := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := hg
  refine ⟨d, -b, -c, a, e, he0, he, by linear_combination hdet, ε, hε, ?_⟩
  rw [coe_inv_of_coe_eq_smul hgm]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem isNewmanForm_conj_mem {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : IsNewmanForm N g)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N) : g * γ * g⁻¹ ∈ Gamma0R N := by
  have hN0 := NeZero.ne N
  obtain ⟨a, b, c, d, e, he0, ⟨m, hm⟩, hdet, ε, hε, hgm⟩ := hg
  change nPart N = e * m at hm
  obtain ⟨x, y, c', t, hγdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hNnh := hPart_sq_mul_nPart N hN0
  set h := hPart N with hh
  have hh0 : h ≠ 0 := (hPart_pos N).ne'
  -- t ≡ x (mod h)
  have hxt : x * t ≡ 1 [ZMOD h] := by
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    refine ⟨y * z * nPart N * h, ?_⟩
    have : (N : ℤ) = nPart N * h ^ 2 := by exact_mod_cast hNnh.symm
    rw [this] at hγdet
    linear_combination hγdet
  obtain ⟨f, hf⟩ := Int.ModEq.dvd (modEq_of_mul_modEq_one (hPart_dvd_24 N) hxt)
  have ht : t = x + h * f := by linarith
  subst ht
  have hNr : (N : ℝ) = e * m * h ^ 2 := by
    rw [← hNnh, hm]
    push_cast
    ring
  have her : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he0.ne'
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh0
  have hε2 : ε / Real.sqrt e * (ε / Real.sqrt e) * e = 1 := by
    have hs : Real.sqrt e * Real.sqrt e = e := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hε1 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hs0 : Real.sqrt e ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hs; exact her hs.symm
    rw [div_mul_div_comm, hε1, hs, one_div_mul_cancel her]
  refine mem_Gamma0R_of_entries
    (-a * c * e * h * m * y + a * d * e * x - b * c * f * h * m - b * c * m * x +
      b * d * e * h * m * z)
    (a ^ 2 * e * y + a * b * f - b ^ 2 * m * z)
    (N * (-c ^ 2 * m * y - c * d * f + d ^ 2 * e * z))
    (a * c * e * h * m * y + a * d * e * f * h + a * d * e * x - b * c * m * x -
      b * d * e * h * m * z) ?_ (dvd_mul_right _ _)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgm, hγm,
    coe_inv_of_coe_eq_smul hgm]
  apply smul_mul_mul_smul_eq_of hε2
  rw [mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> ring

/-- **T1** in general. -/
theorem newmanForm_mem_normalizer' {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : IsNewmanForm N g) :
    g ∈ Norm0 N := by
  refine mem_Norm0_of (fun γ hγ => isNewmanForm_conj_mem hg hγ) (fun γ hγ => ?_)
  have := isNewmanForm_conj_mem (isNewmanForm_inv hg) hγ
  simpa using this

/-! ### D⁻¹Γ₀(n)D -/

theorem coe_projSL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) :
    ((projSL A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt A.det)⁻¹ • A := by
  have : projSL A = ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩ :=
    dite_eq_left hA
  rw [this]

theorem coe_Dsl (N : ℕ) :
    ((Dsl N : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt (hPart N))⁻¹ • !![(hPart N : ℝ), 0; 0, 1] := by
  have hpos : (0 : ℝ) < (!![(hPart N : ℝ), 0; 0, 1]).det := by
    have : (0 : ℝ) < hPart N := Nat.cast_pos.2 (hPart_pos N)
    simpa [det_fin_two_of] using this
  rw [Dsl, coe_projSL _ hpos]
  simp [det_fin_two_of]

theorem conjGamma0n_isNewmanForm {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ conjGamma0n N) :
    IsNewmanForm N g := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨a, b, c', d, hdet, ⟨c, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hh0 : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  dsimp only [nPart] at hdet
  refine ⟨a, b, c, d, 1, one_pos, one_dvd _, by linear_combination hdet, 1, Or.inl rfl, ?_⟩
  have hD := coe_Dsl N
  have hDinv := coe_inv_of_coe_eq_smul hD
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDinv, hγm, hD]
  have hs : Real.sqrt (hPart N) * Real.sqrt (hPart N) = hPart N :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hsq : (Real.sqrt (hPart N))⁻¹ * (Real.sqrt (hPart N))⁻¹ * (hPart N : ℝ) = 1 := by
    rw [← mul_inv, hs, inv_mul_cancel₀ hh0]
  have hNr : (N : ℝ) = nPart N * (hPart N) ^ 2 := by exact_mod_cast hNnh.symm
  rw [smul_mul_mul_smul_eq_of hsq (X := !![(a : ℝ), b / hPart N; nPart N * c * hPart N, d])]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hNr] ; field_simp
  · rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem conjGamma0n_le_normalizer' (N : ℕ) [NeZero N] : conjGamma0n N ≤ Norm0 N :=
  fun _ hg => newmanForm_mem_normalizer' (conjGamma0n_isNewmanForm hg)

end

end CongruenceNormalizers
