/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanRat

/-!
# Newman's theorem, step 2: the integrality conditions ([Nw §3])

With g = κ·S, S = [[α, β/h], [hγ, δ]] and e = αδ − βγ (so κ²e = 1), conjugation by g is
Φ(M) = S M adj(S) / e.  `InL N M` says that M is an integer matrix with N ∣ M₁₀ and ε ∣ M₁₁ − M₀₀
(ε = gcd(N, 24)); it holds on Γ₀(N) (units mod divisors of 24 square to 1) and is closed under
integer combinations.  Applying Φ to E₁₂ = T − 1, NE₂₁ = U − 1, NE₂₂ = N − (TU − T − U + 1) and
(t − x)E₂₂ = γ − x − yE₁₂ − NE₂₁ (γ = [[x, y], [N, t]] ∈ Γ₀(N)) gives integer divisibilities.
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

/-- ε = gcd(N, 24). -/
def epsPart (N : ℕ) : ℕ := Nat.gcd N 24

/-- An integer matrix with N ∣ M₁₀ and ε ∣ M₁₁ − M₀₀. -/
def InL (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a b c d : ℤ, M = !![(a : ℝ), b; c, d] ∧ (N : ℤ) ∣ c ∧ (epsPart N : ℤ) ∣ d - a

theorem InL.add {N : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) (h' : InL N M') :
    InL N (M + M') := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  obtain ⟨a', b', c', d', rfl, hc', hd'⟩ := h'
  refine ⟨a + a', b + b', c + c', d + d', ?_, dvd_add hc hc', ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [show d + d' - (a + a') = (d - a) + (d' - a') by ring]; exact dvd_add hd hd'

theorem InL.zsmul {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) (m : ℤ) :
    InL N ((m : ℝ) • M) := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  refine ⟨m * a, m * b, m * c, m * d, ?_, dvd_mul_of_dvd_right hc _, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [show m * d - m * a = m * (d - a) by ring]; exact dvd_mul_of_dvd_right hd _

theorem InL.sub {N : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) (h' : InL N M') :
    InL N (M - M') := by
  have := h.add (h'.zsmul (-1))
  convert this using 1
  simp [sub_eq_add_neg]

theorem InL.one (N : ℕ) : InL N 1 :=
  ⟨1, 0, 0, 1, by ext i j; fin_cases i <;> fin_cases j <;> simp, dvd_zero _, by simp⟩

theorem epsPart_dvd_24 (N : ℕ) : epsPart N ∣ 24 := Nat.gcd_dvd_right _ _

theorem epsPart_dvd (N : ℕ) : epsPart N ∣ N := Nat.gcd_dvd_left _ _

theorem InL.of_mem {N : ℕ} {Y : SL(2, ℝ)} (hY : Y ∈ Gamma0R N) :
    InL N (Y : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨a, b, c, d, hdet, hc, hm⟩ := exists_entries_of_mem_Gamma0R hY
  refine ⟨a, b, c, d, hm, hc, ?_⟩
  have hεc : (epsPart N : ℤ) ∣ c := dvd_trans (Int.natCast_dvd_natCast.2 (epsPart_dvd N)) hc
  have had : a * d ≡ 1 [ZMOD epsPart N] := by
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, show a * d - 1 = b * c by linarith]
    exact dvd_mul_of_dvd_right hεc _
  exact Int.ModEq.dvd (modEq_of_mul_modEq_one (epsPart_dvd_24 N) had)

/-! ### Conjugation as a linear map -/

/-- S = [[α, β/h], [hγ, δ]]. -/
def Smat (h : ℕ) (α β γ δ : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]

/-- Φ(M) = S M adj(S) / e. -/
def Phi (h : ℕ) (α β γ δ : ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((α * δ - β * γ : ℤ) : ℝ)⁻¹ • (Smat h α β γ δ * M * (Smat h α β γ δ).adjugate)

theorem Phi_add (h : ℕ) (α β γ δ : ℤ) (M M' : Matrix (Fin 2) (Fin 2) ℝ) :
    Phi h α β γ δ (M + M') = Phi h α β γ δ M + Phi h α β γ δ M' := by
  simp [Phi, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Phi_smul (h : ℕ) (α β γ δ : ℤ) (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Phi h α β γ δ (r • M) = r • Phi h α β γ δ M := by
  simp [Phi, smul_smul, mul_comm]

theorem Phi_sub (h : ℕ) (α β γ δ : ℤ) (M M' : Matrix (Fin 2) (Fin 2) ℝ) :
    Phi h α β γ δ (M - M') = Phi h α β γ δ M - Phi h α β γ δ M' := by
  have := Phi_add h α β γ δ M ((-1 : ℝ) • M')
  rw [Phi_smul] at this
  simpa [sub_eq_add_neg] using this

theorem det_Smat {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    (Smat h α β γ δ).det = ((α * δ - β * γ : ℤ) : ℝ) := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  rw [Smat, det_fin_two_of]
  push_cast
  field_simp

theorem Phi_one {h : ℕ} (hh : h ≠ 0) {α β γ δ : ℤ} (he : α * δ - β * γ ≠ 0) :
    Phi h α β γ δ 1 = 1 := by
  have her : ((α * δ - β * γ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast he
  rw [Phi, Matrix.mul_one, Matrix.mul_adjugate, det_Smat hh, smul_smul, inv_mul_cancel₀ her,
    one_smul]

/-- Conjugation by g = κ S is Φ. -/
theorem coe_conj_eq_Phi {g : SL(2, ℝ)} {κ : ℝ} {h : ℕ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat h α β γ δ) (hh : h ≠ 0) (Y : SL(2, ℝ)) :
    ((g * Y * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Phi h α β γ δ (Y : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := g.2
    rw [hg, det_smul, Fintype.card_fin, Smat, det_fin_two_of] at this
    have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
    push_cast
    field_simp at this
    linear_combination this
  have hE : ((α * δ - β * γ : ℤ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
  have hinv : κ ^ 2 = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ := by
    field_simp
    linear_combination hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hg, adjugate_smul, Fintype.card_fin]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Phi]
  congr 1

/-- The explicit images of E₁₂, E₂₁, E₂₂ under M ↦ S M adj(S). -/
theorem Phi_E12 (h : ℕ) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 1; 0, 0] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![-(α * h * γ : ℝ), (α : ℝ) ^ 2; -((h : ℝ) ^ 2 * γ ^ 2), α * h * γ] := by
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem Phi_E21 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 1, 0] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![(β : ℝ) * δ / h, -((β : ℝ) ^ 2 / (h : ℝ) ^ 2); (δ : ℝ) ^ 2, -((β : ℝ) * δ / h)] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem Phi_E22 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 0, 1] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![-((β : ℝ) * γ), (α : ℝ) * β / h; -((h : ℝ) * γ * δ), (α : ℝ) * δ] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

end

end CongruenceNormalizers
