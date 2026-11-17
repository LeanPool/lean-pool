/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.Defs

/-!
# Basic API for Γ₀(N) ≤ SL₂(ℝ), its normalizer, B(N), S_k and h(N)
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

/-! ### Membership in Γ₀(N) -/

/-- The real matrix of an integer matrix. -/
abbrev castM (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ := M.map (Int.cast)

theorem mem_Gamma0R_iff {N : ℕ} {g : SL(2, ℝ)} :
    g ∈ Gamma0R N ↔ ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      (N : ℤ) ∣ M 1 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) = castM M := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ?_, ?_⟩
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA)
    · ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  · rintro ⟨M, hM, hg⟩
    have hdet : M.det = 1 := by
      have h1 := g.2
      rw [hg, det_fin_two] at h1
      rw [det_fin_two]
      simp only [castM, map_apply] at h1
      exact_mod_cast h1
    let A : SL(2, ℤ) := ⟨M, hdet⟩
    refine ⟨A, CongruenceSubgroup.Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hM), ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ (fun i j => ?_)
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg]
    rfl

/-- Membership in Γ₀(N) from explicit integer entries. -/
theorem mem_Gamma0R_of_entries {N : ℕ} {g : SL(2, ℝ)} (a b c d : ℤ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d]) (hc : (N : ℤ) ∣ c) :
    g ∈ Gamma0R N := by
  refine mem_Gamma0R_iff.2 ⟨!![a, b; c, d], by simpa using hc, ?_⟩
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Elements of Γ₀(N) have integer entries, lower-left divisible by N, determinant 1. -/
theorem exists_entries_of_mem_Gamma0R {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Gamma0R N) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (N : ℤ) ∣ c ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d] := by
  obtain ⟨M, hM, hgM⟩ := mem_Gamma0R_iff.1 hg
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, ?_, hM, ?_⟩
  · have h1 := g.2
    rw [hgM, det_fin_two] at h1
    simp only [castM, map_apply] at h1
    exact_mod_cast h1
  · rw [hgM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ### The normalizer -/

/-- Normalizer criterion: g Γ g⁻¹ ⊆ Γ and g⁻¹ Γ g ⊆ Γ. -/
theorem mem_Norm0_of {N : ℕ} {g : SL(2, ℝ)}
    (h₁ : ∀ γ ∈ Gamma0R N, g * γ * g⁻¹ ∈ Gamma0R N)
    (h₂ : ∀ γ ∈ Gamma0R N, g⁻¹ * γ * g ∈ Gamma0R N) : g ∈ Norm0 N := by
  rw [Subgroup.mem_normalizer_iff]
  intro γ
  refine ⟨h₁ γ, fun h => ?_⟩
  have := h₂ _ h
  simpa [mul_assoc] using this

theorem Gamma0R_le_Norm0 (N : ℕ) : Gamma0R N ≤ Norm0 N :=
  Subgroup.le_normalizer

/-! ### B(N) -/

theorem B.isClassOf_mk {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) :
    B.IsClassOf (QuotientGroup.mk ⟨g, hg⟩ : B N) g := ⟨hg, rfl⟩

theorem B.mk_eq_mk_iff {N : ℕ} {g g' : SL(2, ℝ)} (hg : g ∈ Norm0 N) (hg' : g' ∈ Norm0 N) :
    (QuotientGroup.mk ⟨g, hg⟩ : B N) = QuotientGroup.mk ⟨g', hg'⟩ ↔ g⁻¹ * g' ∈ Gamma0R N := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem B.mk_eq_one_iff {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) :
    (QuotientGroup.mk ⟨g, hg⟩ : B N) = 1 ↔ g ∈ Gamma0R N := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

/-- In the normalizer, `a * b⁻¹ ∈ Γ ↔ a⁻¹ * b ∈ Γ`. -/
theorem mul_inv_mem_iff_inv_mul_mem {N : ℕ} {a b : SL(2, ℝ)} (ha : a ∈ Norm0 N) :
    a * b⁻¹ ∈ Gamma0R N ↔ a⁻¹ * b ∈ Gamma0R N := by
  have key : ∀ x, x ∈ Gamma0R N ↔ a⁻¹ * x * a ∈ Gamma0R N := by
    intro x
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem ha)) x
    simpa using this
  rw [key (a * b⁻¹), ← inv_mem_iff (x := a⁻¹ * b)]
  simp

/-! ### Translations S_k -/

theorem coe_S (k : ℕ) : ((S k : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (k : ℝ)⁻¹; 0, 1] :=
  rfl

theorem coe_S_pow (k m : ℕ) :
    ((S k ^ m : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (m : ℝ) * (k : ℝ)⁻¹; 0, 1] := by
  induction m with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ m ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_S, mul_fin_two]
    congr 1
    simp only [mul_one, mul_zero, add_zero, one_mul, Nat.cast_succ]
    ring_nf

theorem coe_S_inv (k : ℕ) :
    (((S k)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -(k : ℝ)⁻¹; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_S, adjugate_fin_two_of]
  simp

theorem S_one_mem (N : ℕ) : S 1 ∈ Gamma0R N :=
  mem_Gamma0R_of_entries 1 1 0 1 (by rw [coe_S]; simp) (dvd_zero _)

/-! ### h(N) -/

theorem hPart_pos (N : ℕ) : 0 < hPart N := by
  unfold hPart
  positivity

theorem hPart_dvd_24 (N : ℕ) : hPart N ∣ 24 := by
  unfold hPart
  have h2 : 2 ^ min 3 (N.factorization 2 / 2) ∣ 2 ^ 3 := pow_dvd_pow _ (min_le_left _ _)
  have h3 : 3 ^ min 1 (N.factorization 3 / 2) ∣ 3 ^ 1 := pow_dvd_pow _ (min_le_left _ _)
  have := mul_dvd_mul h2 h3
  simpa using this

/-- Key divisibility: if (2^α 3^β)² ∣ N with α ≤ 3, β ≤ 1, then 2^α 3^β ∣ h(N). -/
theorem dvd_hPart_of_sq_dvd {N : ℕ} (hN : N ≠ 0) {α β : ℕ} (hα : α ≤ 3) (hβ : β ≤ 1)
    (h : (2 ^ α * 3 ^ β) ^ 2 ∣ N) : 2 ^ α * 3 ^ β ∣ hPart N := by
  unfold hPart
  have hsplit : (2 ^ α * 3 ^ β) ^ 2 = 2 ^ (2 * α) * 3 ^ (2 * β) := by ring
  rw [hsplit] at h
  have h2 : 2 ^ (2 * α) ∣ N := dvd_trans (dvd_mul_right _ _) h
  have h3 : 3 ^ (2 * β) ∣ N := dvd_trans (dvd_mul_left _ _) h
  rw [Nat.prime_two.pow_dvd_iff_le_factorization hN] at h2
  rw [Nat.prime_three.pow_dvd_iff_le_factorization hN] at h3
  refine mul_dvd_mul (pow_dvd_pow _ ?_) (pow_dvd_pow _ ?_)
  · exact le_min hα (by omega)
  · exact le_min hβ (by omega)

theorem hPart_sq_dvd {N : ℕ} (hN : N ≠ 0) : hPart N ^ 2 ∣ N := by
  unfold hPart
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hc : Nat.Coprime (2 ^ (min 3 (N.factorization 2 / 2) * 2))
      (3 ^ (min 1 (N.factorization 3 / 2) * 2)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  refine hc.mul_dvd_of_dvd_of_dvd ?_ ?_
  · rw [Nat.prime_two.pow_dvd_iff_le_factorization hN]
    have := Nat.div_mul_le_self (N.factorization 2) 2
    have := min_le_right 3 (N.factorization 2 / 2)
    nlinarith
  · rw [Nat.prime_three.pow_dvd_iff_le_factorization hN]
    have := Nat.div_mul_le_self (N.factorization 3) 2
    have := min_le_right 1 (N.factorization 3 / 2)
    nlinarith

theorem dvd_hPart_iff {N : ℕ} (hN : N ≠ 0) {d : ℕ} (hd : d ∣ 24) (hsq : d ^ 2 ∣ N) :
    d ∣ hPart N := by
  have hd24 : d ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  · exact one_dvd _
  · exact (dvd_hPart_of_sq_dvd hN (α := 1) (β := 0) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 0) (β := 1) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 2) (β := 0) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 1) (β := 1) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 3) (β := 0) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 2) (β := 1) (by norm_num) (by norm_num) (by simpa using
      hsq))
  · exact (dvd_hPart_of_sq_dvd hN (α := 3) (β := 1) (by norm_num) (by norm_num) (by simpa using
      hsq))

theorem hPart_isGreatest' (N : ℕ) [NeZero N] :
    IsGreatest {d : ℕ | d ∣ 24 ∧ d ^ 2 ∣ N} (hPart N) := by
  refine ⟨⟨hPart_dvd_24 N, hPart_sq_dvd (NeZero.ne N)⟩, ?_⟩
  rintro d ⟨hd, hsq⟩
  exact Nat.le_of_dvd (hPart_pos N) (dvd_hPart_iff (NeZero.ne N) hd hsq)

/-! ### Units modulo divisors of 24 square to 1 -/

theorem modEq_of_mul_modEq_one {k : ℕ} (hk : k ∣ 24) {a d : ℤ} (h : a * d ≡ 1 [ZMOD k]) :
    a ≡ d [ZMOD k] := by
  have hk24 : k ≤ 24 := Nat.le_of_dvd (by norm_num) hk
  rw [← ZMod.intCast_eq_intCast_iff] at h ⊢
  push_cast at h
  generalize (a : ZMod k) = x at h ⊢
  generalize (d : ZMod k) = y at h ⊢
  revert x y
  interval_cases k <;> norm_num at hk <;> decide

end

end CongruenceNormalizers
