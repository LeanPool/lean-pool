/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerDelta.Basic

/-!
# The generalized Newman bound (`newman_delta'`)

Γ_Δ(N) satisfies the hypotheses `NewmanData N (Γ_Δ(N)) ε_Δ h_Δ` of the generic Newman argument
(`NewmanGen.lean`); the only new ingredient is the element γ_p (`exists_gamma_delta`):
if j = v_p(ε_Δ) < ν = v_p(N), then p^{j+1} ∣ N, so p^{j+1} ∤ d² − 1 for some d ∈ Δ (otherwise
p^{j+1} ∣ ε_Δ), while p^j ∣ ε_Δ ∣ d² − 1.  With t = d and x t − y N = 1, the matrix
[[x, y], [N, t]] lies in Γ_Δ(N), and t(t − x) ≡ t² − 1 (mod N) gives v_p(t − x) = j (`gamma_val`).
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

/-- The element γ_p of Γ_Δ(N). -/
theorem exists_gamma_delta [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hj : (epsDelta N Δ).factorization p < N.factorization p) :
    ∃ x y t : ℤ, x * t - y * N = 1 ∧
      (∃ γ ∈ GammaDeltaR N Δ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(x : ℝ), y; N, t]) ∧
      t - x ≠ 0 ∧ vz p (t - x) = (epsDelta N Δ).factorization p := by
  have hN := NeZero.ne N
  have hN2 : 2 ≤ N := le_trans hp.two_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpN)
  set j := (epsDelta N Δ).factorization p with hjdef
  set ν := N.factorization p with hν
  have hε0 : epsDelta N Δ ≠ 0 := epsDelta_pos.ne'
  -- some u ∈ Δ with p^{j+1} ∤ val(u)² − 1
  obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ (j + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization hN).2 (by omega)
    have h2 : p ^ (j + 1) ∣ epsDelta N Δ := dvd_epsDelta_iff.2 ⟨h1, hcon⟩
    have := (hp.pow_dvd_iff_le_factorization hε0).1 h2
    omega
  have hpj : p ^ j ∣ (u : ZMod N).val ^ 2 - 1 :=
    (Nat.ordProj_dvd (epsDelta N Δ) p).trans (epsDelta_dvd_val hu)
  set v := (u : ZMod N).val with hvdef
  have hv1 : 1 ≤ v := one_le_val_unit hN2 u
  have hcopN : Nat.Coprime v N := ZMod.val_coe_unit_coprime u
  -- Bézout: x v − y N = 1
  have hb := Int.gcd_eq_gcd_ab v N
  rw [Int.gcd_natCast_natCast, hcopN] at hb
  set x := Int.gcdA v N
  set y := -Int.gcdB v N
  have hdet : x * v - y * N = 1 := by
    push_cast at hb
    simp only [y]
    linear_combination -hb
  refine ⟨x, y, v, hdet, ?_, ?_⟩
  · have hdet' : x * v - y * N = 1 := hdet
    refine ⟨ofZ (mkSL x y N v hdet'), ofZ_mem_toR (mkSL_mem_GammaDelta hdet' (dvd_refl _) hu ?_),
      coe_ofZ_mkSL hdet'⟩
    simp [v]
  · -- the valuation, by `gamma_val` with the roles of x and t exchanged
    have hdet2 : (v : ℤ) * x - y * N = 1 := by linear_combination hdet
    have hpν : (p : ℤ) ^ ν ∣ (N : ℤ) := by exact_mod_cast Nat.ordProj_dvd N p
    have hpv : IsCoprime (p : ℤ) (v : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Coprime.coprime_dvd_right hpN hcopN).symm
    have hcast : (((v ^ 2 - 1 : ℕ)) : ℤ) = (v : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hv1)]; push_cast; ring
    have hρ1 : (p : ℤ) ^ j ∣ 1 - (v : ℤ) ^ 2 := by
      have := Int.natCast_dvd_natCast.2 hpj
      rw [hcast] at this
      push_cast at this
      have := this.neg_right
      convert this using 1; ring
    have hρ2 : ¬ (p : ℤ) ^ (j + 1) ∣ 1 - (v : ℤ) ^ 2 := by
      intro hd
      apply hnd
      have hd' : (p : ℤ) ^ (j + 1) ∣ (((v ^ 2 - 1 : ℕ)) : ℤ) := by
        rw [hcast]; have := hd.neg_right; convert this using 1; ring
      exact_mod_cast hd'
    rcases gamma_val hp hdet2 hpν (by simp) hpv hρ1 hρ2 with h | ⟨-, hne, hval⟩
    · omega
    · refine ⟨fun h0 => hne (by linear_combination -h0), ?_⟩
      rw [show (v : ℤ) - x = -(x - v) by ring, vz_neg]
      exact hval

/-- Γ_Δ(N) satisfies the hypotheses of the generic Newman argument. -/
theorem newmanData_delta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NewmanData N (GammaDeltaR N Δ) (epsDelta N Δ) (hDelta N Δ) where
  le := GammaDeltaR_le_Gamma0R
  T_mem := matT_mem_GammaDeltaR
  U_mem := matU_mem_GammaDeltaR
  inL := fun _ hY => inLe_of_mem_GammaDeltaR hY
  eps_dvd := epsDelta_dvd
  h_pos := by unfold hDelta; exact Finset.prod_pos (fun q hq => pow_pos
    (Nat.pos_of_mem_primeFactors hq) _)
  h_sq_dvd := by
    have hN := NeZero.ne N
    have hh : hDelta N Δ ≠ 0 := by
      unfold hDelta
      exact Finset.prod_ne_zero_iff.2 (fun q hq => pow_ne_zero _ (Nat.pos_of_mem_primeFactors
        hq).ne')
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hh) hN]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_hDelta]
    omega
  h_fact := factorization_hDelta
  gamma := fun _ hp hpN hj => exists_gamma_delta hp hpN hj

/-- **The generalized Newman bound.** -/
theorem newman_delta' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {g : SL(2, ℝ)}
    (hg : g ∈ NormG (GammaDeltaR N Δ)) : IsNewmanFormH N (hDelta N Δ) g :=
  newmanG (newmanData_delta N Δ) hg

end

end CongruenceNormalizers
