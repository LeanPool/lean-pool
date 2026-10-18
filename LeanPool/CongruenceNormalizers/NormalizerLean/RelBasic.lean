/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.AtkinLehner

/-!
# Infrastructure for the relations: Fricke elements, transfer between representatives, (14)
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

/-! ### h at prime powers -/

theorem factorization_prime_pow {p q a : ℕ} (hp : p.Prime) :
    (p ^ a).factorization q = if p = q then a else 0 := by
  rw [hp.factorization_pow, Finsupp.single_apply]

theorem hPart_two_pow (a : ℕ) : hPart (2 ^ a) = 2 ^ min 3 (a / 2) := by
  unfold hPart
  rw [factorization_prime_pow Nat.prime_two, factorization_prime_pow Nat.prime_two]
  simp

theorem hPart_three_pow (b : ℕ) : hPart (3 ^ b) = 3 ^ min 1 (b / 2) := by
  unfold hPart
  rw [factorization_prime_pow Nat.prime_three, factorization_prime_pow Nat.prime_three]
  simp

theorem hPart_prime_pow {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (a : ℕ) :
    hPart (p ^ a) = 1 := by
  unfold hPart
  rw [factorization_prime_pow hp, factorization_prime_pow hp]
  simp [h2, h3]

/-! ### The Fricke element -/

/-- (1/√m)·[[0, −1], [m, 0]]. -/
def fricke (m : ℕ) (hm : m ≠ 0) : SL(2, ℝ) :=
  alElt m m 0 (-1) 1 0 (by ring) hm

theorem coe_fricke (m : ℕ) (hm : m ≠ 0) :
    ((fricke m hm : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt m)⁻¹ • !![0, -1; (m : ℝ), 0] := by
  simp [fricke, alElt]

theorem fricke_isAtkinLehner (m : ℕ) (hm : m ≠ 0) : IsAtkinLehner m m (fricke m hm) :=
  alElt_isAtkinLehner _ _

/-- For m = t², the Fricke element is rational. -/
theorem coe_fricke_of_sq (m t : ℕ) (hm : m ≠ 0) (hmt : m = t ^ 2) :
    ((fricke m hm : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -(t : ℝ)⁻¹; (t : ℝ), 0] := by
  subst hmt
  rw [coe_fricke]
  have ht : t ≠ 0 := by rintro rfl; simp at hm
  have htr : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ht
  have hs : Real.sqrt ((t ^ 2 : ℕ) : ℝ) = t := by
    rw [Nat.cast_pow]
    exact Real.sqrt_sq (Nat.cast_nonneg _)
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp ; field_simp

/-! ### Transfer between representatives -/

theorem coe_mem_Gamma0R_iff {N : ℕ} (y : Norm0 N) :
    (y : SL(2, ℝ)) ∈ Gamma0R N ↔ (QuotientGroup.mk y : B N) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem coe_lift_subtype {N : ℕ} {α : Type*} (f : α → SL(2, ℝ)) (hf : ∀ a, f a ∈ Norm0 N)
    (ρ : FreeGroup α) :
    ((FreeGroup.lift (fun a => (⟨f a, hf a⟩ : Norm0 N)) ρ : Norm0 N) : SL(2, ℝ)) =
      FreeGroup.lift f ρ := by
  have : (Norm0 N).subtype.comp (FreeGroup.lift (fun a => (⟨f a, hf a⟩ : Norm0 N))) =
      FreeGroup.lift f := FreeGroup.ext_hom _ _ (fun a => by simp)
  exact DFunLike.congr_fun this ρ

/-- Whether a word evaluates into Γ₀(N) depends only on the classes of the generators in B(N). -/
theorem lift_mem_iff_of_cosets {N : ℕ} {α : Type*} (f₀ f₁ : α → SL(2, ℝ))
    (h₀ : ∀ a, f₀ a ∈ Norm0 N) (h₁ : ∀ a, f₁ a ∈ Norm0 N)
    (h : ∀ a, (f₀ a)⁻¹ * f₁ a ∈ Gamma0R N) (ρ : FreeGroup α) :
    FreeGroup.lift f₀ ρ ∈ Gamma0R N ↔ FreeGroup.lift f₁ ρ ∈ Gamma0R N := by
  rw [← coe_lift_subtype f₀ h₀, ← coe_lift_subtype f₁ h₁, coe_mem_Gamma0R_iff,
    coe_mem_Gamma0R_iff]
  have hq : (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N))).comp
        (FreeGroup.lift (fun a => (⟨f₀ a, h₀ a⟩ : Norm0 N))) =
      (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N))).comp
        (FreeGroup.lift (fun a => (⟨f₁ a, h₁ a⟩ : Norm0 N))) := by
    refine FreeGroup.ext_hom _ _ (fun a => ?_)
    simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of,
      QuotientGroup.mk'_apply]
    exact (B.mk_eq_mk_iff (h₀ a) (h₁ a)).2 (h a)
  have := DFunLike.congr_fun hq ρ
  simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply] at this
  rw [this]

/-! ### The local generator assignment and the image of r -/

/-- w ↦ wg, s ↦ S_k. -/
def locF (wg : SL(2, ℝ)) (k : ℕ) : LGen → SL(2, ℝ)
  | .w => wg
  | .s => S k

/-- An irreducible copy of the word r = w s⁻¹ w, so that `simp` does not unfold it. -/
irreducible_def rr : FreeGroup LGen := Words.r

/-- The image of r under w ↦ Fricke, s ↦ S_k: −[[1, 0], [m/k, 1]]. -/
theorem coe_lift_rr (m k : ℕ) (hm : m ≠ 0) (hk : k ≠ 0) :
    ((FreeGroup.lift (locF (fricke m hm) k) rr : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1, 0; -((m : ℝ) / k), -1] := by
  rw [rr_def]
  simp only [Words.r, map_mul, map_inv, FreeGroup.lift_apply_of, locF]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_fricke, coe_S_inv]
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  apply smul_mul_mul_smul_eq hs hmr
  rw [mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp ; field_simp

/-! ### (14): [r, s] for m = n h² -/

/-- (14) of [BA]: with r ↦ −[[1, 0], [m/h, 1]], s ↦ S_h and m = n h², the commutator
[r, s] = r⁻¹s⁻¹rs is [[1 − n, −n/h], [n²h, 1 + n + n²]]; it lies in Γ₀(m) when h ∣ n. -/
theorem bracket_rr_mem (m h t : ℕ) (hm : m ≠ 0) (hh : h ≠ 0) (hmht : m = h * t * h ^ 2) :
    FreeGroup.lift (locF (fricke m hm) h) (bracket rr Words.s) ∈ Gamma0R m := by
  have hR := coe_lift_rr m h hm hh
  simp only [bracket, map_mul, map_inv, FreeGroup.lift_apply_of, locF]
  set R := FreeGroup.lift (locF (fricke m hm) h) rr
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  -- n = h t
  refine mem_Gamma0R_of_entries (1 - h * t) (-t) (m * t) (1 + h * t + (h * t) ^ 2) ?_
    (dvd_mul_right _ _)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, hR, coe_S, adjugate_fin_two_of, adjugate_fin_two_of,
    mul_fin_two, mul_fin_two, mul_fin_two]
  subst hmht
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end

end CongruenceNormalizers
