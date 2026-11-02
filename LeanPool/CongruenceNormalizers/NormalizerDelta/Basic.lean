/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerDelta.NewmanGen

/-!
# Γ_Δ(N), ε_Δ, h_Δ: basic facts

* membership in Γ_Δ(N) and its image in SL₂(ℝ); T, U ∈ Γ_Δ(N);
* ε_Δ ∣ N and ε_Δ ∣ d² − 1 for d ∈ Δ (`dvd_epsDelta_iff`), hence every element of Γ_Δ(N) lies in the
  lattice L_{ε_Δ} (`inLe_of_mem_GammaDeltaR`);
* v_p(h_Δ) = min(v_p(ε_Δ), ⌊v_p(N)/2⌋) (`factorization_hDelta`);
* the element γ_p ∈ Γ_Δ(N) (`exists_gamma_delta`): if v_p(ε_Δ) < v_p(N), some d ∈ Δ has
  v_p(d² − 1) = v_p(ε_Δ), and [[x, y], [N, d]] has v_p(d − x) = v_p(ε_Δ).
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

theorem mem_toR {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℝ)} : g ∈ toR Γ ↔ ∃ γ ∈ Γ, ofZ γ = g :=
  Subgroup.mem_map

theorem ofZ_mem_toR {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} (h : γ ∈ Γ) : ofZ γ ∈ toR Γ :=
  Subgroup.mem_map_of_mem _ h

theorem coe_ofZ (γ : SL(2, ℤ)) :
    (ofZ γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem GammaDelta_le_Gamma0 : GammaDelta N Δ ≤ CongruenceSubgroup.Gamma0 N := fun _ h => h.1

theorem GammaDeltaR_le_Gamma0R : GammaDeltaR N Δ ≤ Gamma0R N :=
  Subgroup.map_mono GammaDelta_le_Gamma0

/-- An integer matrix of determinant 1. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) := ⟨!![a, b; c, d], by
  rw [det_fin_two_of]; exact h⟩

theorem mkSL_mem_GammaDelta {a b c d : ℤ} (h : a * d - b * c = 1) (hc : (N : ℤ) ∣ c)
    {u : (ZMod N)ˣ} (hu : u ∈ Δ) (hud : (u : ZMod N) = (d : ZMod N)) :
    mkSL a b c d h ∈ GammaDelta N Δ := by
  refine ⟨?_, u, hu, by simpa [mkSL] using hud⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simpa [mkSL] using (ZMod.intCast_zmod_eq_zero_iff_dvd c N).2 hc

theorem coe_ofZ_mkSL {a b c d : ℤ} (h : a * d - b * c = 1) :
    (ofZ (mkSL a b c d h) : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d] := by
  rw [coe_ofZ]; rfl

theorem matT_mem_GammaDeltaR : matT ∈ GammaDeltaR N Δ := by
  have h : (1 : ℤ) * 1 - 1 * 0 = 1 := by norm_num
  refine mem_toR.2 ⟨mkSL 1 1 0 1 h, mkSL_mem_GammaDelta h (dvd_zero _) (Subgroup.one_mem _)
    (by simp), ?_⟩
  apply Subtype.ext
  rw [coe_ofZ_mkSL]
  simp [matT]

theorem matU_mem_GammaDeltaR : matU N ∈ GammaDeltaR N Δ := by
  have h : (1 : ℤ) * 1 - 0 * N = 1 := by norm_num
  refine mem_toR.2 ⟨mkSL 1 0 N 1 h, mkSL_mem_GammaDelta h (dvd_refl _) (Subgroup.one_mem _)
    (by simp), ?_⟩
  apply Subtype.ext
  rw [coe_ofZ_mkSL]
  simp [matU]

/-! ### ε_Δ -/

theorem dvd_epsDelta_iff [NeZero N] {m : ℕ} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical
  unfold epsDelta
  rw [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem epsDelta_dvd [NeZero N] : epsDelta N Δ ∣ N := (dvd_epsDelta_iff.1 dvd_rfl).1

theorem epsDelta_dvd_val [NeZero N] {u : (ZMod N)ˣ} (hu : u ∈ Δ) :
    epsDelta N Δ ∣ (u : ZMod N).val ^ 2 - 1 := (dvd_epsDelta_iff.1 dvd_rfl).2 u hu

theorem epsDelta_pos [NeZero N] : 0 < epsDelta N Δ :=
  Nat.pos_of_dvd_of_pos epsDelta_dvd (Nat.pos_of_ne_zero (NeZero.ne N))

/-- For N ≥ 2 a unit has a positive representative. -/
theorem one_le_val_unit (hN : 2 ≤ N) (u : (ZMod N)ˣ) : 1 ≤ (u : ZMod N).val := by
  have : NeZero N := ⟨by omega⟩
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  by_contra h
  have h0 : (u : ZMod N).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  exact u.ne_zero h0

/-- The integer form of ε_Δ ∣ val(u)² − 1. -/
theorem epsDelta_dvd_val_int [NeZero N] {u : (ZMod N)ˣ} (hu : u ∈ Δ) :
    (epsDelta N Δ : ℤ) ∣ ((u : ZMod N).val : ℤ) ^ 2 - 1 := by
  by_cases hN : N = 1
  · have : epsDelta N Δ = 1 := Nat.dvd_one.1 (hN ▸ epsDelta_dvd)
    rw [this]; exact one_dvd _
  have h1 := one_le_val_unit (by have := NeZero.ne N; omega) u
  have := Int.natCast_dvd_natCast.2 (epsDelta_dvd_val hu)
  rwa [Nat.cast_sub (Nat.one_le_pow _ _ h1), Nat.cast_pow, Nat.cast_one] at this

/-- Every element of Γ_Δ(N) lies in the lattice L_{ε_Δ}. -/
theorem inLe_of_mem_GammaDeltaR [NeZero N] {Y : SL(2, ℝ)} (hY : Y ∈ GammaDeltaR N Δ) :
    InLe N (epsDelta N Δ) (Y : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨γ, ⟨h0, u, hu, hγ⟩, rfl⟩ := mem_toR.1 hY
  refine ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, coe_ofZ γ, ?_, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 h0)
  · have hc : (N : ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 h0)
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rwa [det_fin_two] at this
    set v : ℤ := ((u : ZMod N).val : ℤ)
    have hv : (N : ℤ) ∣ γ 1 1 - v := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hγ
    have hεN : (epsDelta N Δ : ℤ) ∣ N := Int.natCast_dvd_natCast.2 epsDelta_dvd
    obtain ⟨k1, hk1⟩ := hεN.trans hv
    obtain ⟨k2, hk2⟩ := epsDelta_dvd_val_int hu
    obtain ⟨k3, hk3⟩ := hεN.trans hc
    refine ⟨-(γ 1 1 * (γ 0 1 * k3)) + γ 0 0 * ((γ 1 1 + v) * k1 + k2), ?_⟩
    linear_combination -(γ 1 1) * hdet - (γ 1 1) * (γ 0 1) * hk3 + (γ 0 0) * (γ 1 1 + v) * hk1 +
      (γ 0 0) * hk2

/-! ### h_Δ -/

theorem factorization_hDelta [NeZero N] (p : ℕ) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  unfold hDelta
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finset.sum_apply']
  rw [Finset.sum_congr rfl (fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hp
  · rfl
  · have : N.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    simp [this]

end

end CongruenceNormalizers
