/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Duality
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.FunProp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

/-!
# A maximiser of `E(v) − v·ρ`

Assume nonnegative occupations with a fixed particle number (`Σ_i n_i(c) = N` for all `c`) and a
density `ρ = Σ_c λ_c n(c)` that is a strictly positive mixture of configuration densities, with
rigid occupations.
* `Egs_shift`: `E(v + k) = E(v) + kN`;
* `Egs_lipschitz`, `continuous_Egs`: `E` is Lipschitz;
* `coercive`: `E(v) − v·ρ ≤ K − δ‖v‖` on potentials with `Σ_i v_i = 0`;
* `exists_maximiser`: `v ↦ E(v) − v·ρ` attains its maximum.
-/

@[expose] public section

namespace DFT

open Matrix Filter Topology

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V] [Nonempty C]

section
variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ}
  (hN : ∀ c, ∑ i, n i c = Nr)
include hH0 hn0 hN

omit [DecidableEq C] [DecidableEq V] [Nonempty C] hH0 hn0 in
lemma sum_dens (φ : C → ℝ) : ∑ i, dens n φ i = Nr * (φ ⬝ᵥ φ) := by
  simp only [dens, dotProduct]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  rw [← Finset.sum_mul, hN c]; ring

omit [DecidableEq V] [Nonempty C] hH0 hn0 in
lemma qf_hamN_shift (v : V → ℝ) (k : ℝ) (φ : C → ℝ) :
    qf (hamN H0 n (v + fun _ => k)) φ = qf (hamN H0 n v) φ + k * Nr * (φ ⬝ᵥ φ) := by
  rw [qf_hamN, qf_hamN]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, sum_dens hN]
  ring

omit [DecidableEq V] hn0 in
lemma Egs_shift (v : V → ℝ) (k : ℝ) : Egs H0 n (v + fun _ => k) = Egs H0 n v + k * Nr := by
  obtain ⟨ψ, hψ, hn⟩ := exists_groundState (hamN_isSymm hH0 n v)
  obtain ⟨ψ', hψ', hn'⟩ := exists_groundState (hamN_isSymm hH0 n (v + fun _ => k))
  apply le_antisymm
  · have := gsEnergy_le (hamN_isSymm hH0 n (v + fun _ => k)) hn
    rw [qf_hamN_shift hN, qf_groundState_eq (hamN_isSymm hH0 n v) hψ hn, hn] at this
    unfold Egs; linarith
  · have := gsEnergy_le (hamN_isSymm hH0 n v) hn'
    have h2 := qf_groundState_eq (hamN_isSymm hH0 n (v + fun _ => k)) hψ' hn'
    rw [qf_hamN_shift hN, hn'] at h2
    unfold Egs; linarith

omit [Fintype C] [DecidableEq C] [DecidableEq V] hH0 in
lemma Nr_nonneg : 0 ≤ Nr := by
  obtain ⟨c⟩ := (inferInstance : Nonempty C)
  rw [← hN c]; exact Finset.sum_nonneg fun i _ => hn0 i c

omit [DecidableEq V] [Nonempty C] hH0 in
lemma qf_hamN_diff_le (v v' : V → ℝ) {φ : C → ℝ} (hφ : φ ⬝ᵥ φ = 1) :
    qf (hamN H0 n v) φ ≤ qf (hamN H0 n v') φ + Nr * ‖v - v'‖ := by
  rw [qf_hamN, qf_hamN]
  have hd : ∀ i, 0 ≤ dens n φ i :=
      fun i => Finset.sum_nonneg fun c _ => mul_nonneg (hn0 i c) (sq_nonneg _)
  have : ∑ i, v i * dens n φ i ≤ ∑ i, v' i * dens n φ i + ‖v - v'‖ * ∑ i, dens n φ i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have h1 : v i - v' i ≤ ‖v - v'‖ := (le_abs_self _).trans (by
      have := norm_le_pi_norm (v - v') i; simpa [Real.norm_eq_abs] using this)
    nlinarith [hd i]
  rw [sum_dens hN, hφ, mul_one] at this
  linarith

omit [DecidableEq V] in
lemma Egs_lipschitz (v v' : V → ℝ) : Egs H0 n v ≤ Egs H0 n v' + Nr * ‖v - v'‖ := by
  obtain ⟨ψ', hψ', hn'⟩ := exists_groundState (hamN_isSymm hH0 n v')
  have h1 := gsEnergy_le (hamN_isSymm hH0 n v) hn'
  have h2 := qf_hamN_diff_le (H0 := H0) hn0 hN v v' hn'
  rw [qf_groundState_eq (hamN_isSymm hH0 n v') hψ' hn'] at h2
  unfold Egs; linarith

omit [DecidableEq V] in
theorem continuous_Egs : Continuous (Egs H0 n) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (Nr + 1), div_pos hε (by linarith [Nr_nonneg hn0 hN]), fun a ha => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hNr := Nr_nonneg hn0 hN
  have h1 := Egs_lipschitz hH0 hn0 hN a b
  have h2 := Egs_lipschitz hH0 hn0 hN b a
  rw [dist_eq_norm] at ha
  have hab : ‖b - a‖ = ‖a - b‖ := norm_sub_rev _ _
  have hlt : Nr * ‖a - b‖ < ε := by
    calc Nr * ‖a - b‖ ≤ (Nr + 1) * ‖a - b‖ := by nlinarith [norm_nonneg (a - b)]
      _ < (Nr + 1) * (ε / (Nr + 1)) := by
          apply mul_lt_mul_of_pos_left ha; linarith
      _ = ε := by field_simp
  rw [hab] at h2
  constructor <;> linarith

end

section
variable {n : V → C → ℝ} (ρ : V → ℝ)

/-- `a_c(v) = v·n(c) − v·ρ`. -/
def aval (v : V → ℝ) (c : C) : ℝ := ∑ i, v i * n i c - v ⬝ᵥ ρ

/-- `m(v) = min_c a_c(v)`. -/
noncomputable def mval (v : V → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty (aval (n := n) ρ v)

variable {ρ}

omit [DecidableEq C] [DecidableEq V] in
lemma mval_le (v : V → ℝ) (c : C) : mval (n := n) ρ v ≤ aval (n := n) ρ v c :=
    Finset.inf'_le _ (Finset.mem_univ c)

omit [DecidableEq C] [DecidableEq V] in
lemma continuous_mval : Continuous (mval (n := n) ρ) := by
  apply Continuous.finset_inf'_apply
  intro c _
  unfold aval dotProduct
  fun_prop

omit [DecidableEq C] [DecidableEq V] in
lemma mval_smul {t : ℝ} (ht : 0 ≤ t) (v : V → ℝ) : mval (n := n) ρ (t • v) =
    t * mval (n := n) ρ v := by
  have ha : ∀ c, aval (n := n) ρ (t • v) c = t * aval (n := n) ρ v c := by
    intro c; simp only [aval, Pi.smul_apply, smul_eq_mul, dotProduct]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  apply le_antisymm
  · obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (aval (n := n) ρ v)
    calc mval (n := n) ρ (t • v) ≤ aval (n := n) ρ (t • v) c := mval_le _ c
      _ = t * mval (n := n) ρ v := by rw [ha, mval, hc]
  · apply Finset.le_inf'; intro c _
    rw [ha]; exact mul_le_mul_of_nonneg_left (mval_le v c) ht

variable {lam : C → ℝ} (hlam : ∀ c, 0 < lam c) (hsum : ∑ c, lam c = 1)
  (hρ : ρ = fun i => ∑ c, lam c * n i c)
include hlam hsum hρ

omit [DecidableEq C] [DecidableEq V] [Nonempty C] hlam in
lemma weighted_aval (v : V → ℝ) : ∑ c, lam c * aval (n := n) ρ v c = 0 := by
  simp only [aval, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [sub_eq_zero, hρ]
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro c _; ring

omit [DecidableEq C] [DecidableEq V] in
lemma mval_nonpos (v : V → ℝ) : mval (n := n) ρ v ≤ 0 := by
  have h := weighted_aval hsum hρ v
  have : ∑ c, lam c * mval (n := n) ρ v ≤ ∑ c, lam c * aval ρ v c :=
    Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (mval_le v c) (hlam c).le
  rw [← Finset.sum_mul, hsum, one_mul, h] at this
  exact this

omit [DecidableEq C] [DecidableEq V] in
lemma const_of_mval_eq_zero (hR : Rigid n) {v : V → ℝ} (h0 : mval (n := n) ρ v = 0) :
    ∃ k, ∀ i, v i = k := by
  have hge : ∀ c, 0 ≤ aval (n := n) ρ v c := fun c => h0 ▸ mval_le v c
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hlam c).le (hge c))).mp
    (weighted_aval hsum hρ v)
  apply hR v (v ⬝ᵥ ρ)
  intro c
  have := hzero c (Finset.mem_univ c)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (hlam c).ne'
  · unfold aval at h; linarith

omit [DecidableEq C] [DecidableEq V] in
/-- **Coercivity of `m` on potentials with zero sum.** -/
theorem coercive (hR : Rigid n) : ∃ δ > 0, ∀ v : V → ℝ, ∑ i, v i = 0 →
    mval (n := n) ρ v ≤ -δ * ‖v‖ := by
  set S1 : Set (V → ℝ) := {v | ∑ i, v i = 0 ∧ ‖v‖ = 1}
  have hzero_of : ∀ v : V → ℝ, ∑ i, v i = 0 → (∃ k, ∀ i, v i = k) → v = 0 := by
    intro v hs ⟨k, hk⟩
    by_cases hV : (Finset.univ : Finset V).card = 0
    · funext i; exact absurd (Finset.mem_univ i) (by rw [Finset.card_eq_zero.mp hV]; simp)
    · have : (Finset.univ : Finset V).card * k = 0 := by
        rw [← hs]; simp [hk, Finset.sum_const]
      have hk0 : k = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by exact_mod_cast h) hV
        · exact h
      funext i; simp [hk i, hk0]
  have mval_zero : mval (n := n) ρ 0 = 0 := by
    have h := mval_smul (n := n) (ρ := ρ) (t := 0) le_rfl 0
    simpa using h
  have normalize_mem {v : V → ℝ} (hs : ∑ i, v i = 0) (hv : v ≠ 0) :
      ‖v‖⁻¹ • v ∈ S1 := by
    refine ⟨?_, ?_⟩
    · simp [Pi.smul_apply, ← Finset.mul_sum, hs]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  rcases S1.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · subst hv0; simp [mval_zero]
    · exact (hS ▸ normalize_mem hv hv0).elim
  · have hcomp : IsCompact S1 := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact (isClosed_eq (by fun_prop) continuous_const).inter
          (isClosed_eq continuous_norm continuous_const)
      · exact (Metric.isBounded_closedBall (x := (0 : V → ℝ)) (r := 1)).subset fun v hv => by
          simp [hv.2]
    obtain ⟨v1, hv1, hmax⟩ :=
        hcomp.exists_isMaxOn hS (continuous_mval (n := n) (ρ := ρ)).continuousOn
    have hneg : mval (n := n) ρ v1 < 0 := by
      rcases (mval_nonpos hlam hsum hρ v1).lt_or_eq with h | h
      · exact h
      · exfalso
        have := hzero_of v1 hv1.1 (const_of_mval_eq_zero hlam hsum hρ hR h)
        have h1 := hv1.2; rw [this, norm_zero] at h1; exact zero_ne_one h1
    refine ⟨-mval (n := n) ρ v1, by linarith, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · subst hv0; simp [mval_zero]
    · have h1 : mval (n := n) ρ (‖v‖⁻¹ • v) ≤ mval (n := n) ρ v1 :=
        hmax (normalize_mem hv hv0)
      have hv_eq : v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
      calc
        mval (n := n) ρ v = ‖v‖ * mval (n := n) ρ (‖v‖⁻¹ • v) := by
          conv_lhs => rw [hv_eq]
          exact mval_smul (norm_nonneg _) _
        _ ≤ -(-mval (n := n) ρ v1) * ‖v‖ := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left h1 (norm_nonneg v)

end

section
variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ}
  (hN : ∀ c, ∑ i, n i c = Nr) {ρ : V → ℝ} {lam : C → ℝ} (hlam : ∀ c, 0 < lam c)
  (hsum : ∑ c, lam c = 1) (hρ : ρ = fun i => ∑ c, lam c * n i c) (hR : Rigid n)
include hH0 hn0 hN hlam hsum hρ hR

omit [DecidableEq C] [DecidableEq V] [Nonempty C] hH0 hn0 hlam hR in
lemma sum_rho : ∑ i, ρ i = Nr := by
  rw [hρ]; simp only
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hN, ← Finset.sum_mul, hsum, one_mul]

omit [DecidableEq V] in
/-- **Existence of a maximiser of `E(v) − v·ρ`.** -/
theorem exists_maximiser : ∃ vs : V → ℝ, ∀ v, Egs H0 n v - v ⬝ᵥ ρ ≤ Egs H0 n vs - vs ⬝ᵥ ρ := by
  set G : (V → ℝ) → ℝ := fun v => Egs H0 n v - v ⬝ᵥ ρ
  have hG : Continuous G := (continuous_Egs hH0 hn0 hN).sub (by unfold dotProduct; fun_prop)
  have hshift : ∀ v k, G (v + fun _ => k) = G v := by
    intro v k
    simp only [G, Egs_shift hH0 hN, add_dotProduct]
    have : (fun _ : V => k) ⬝ᵥ ρ = k * Nr := by
      simp [dotProduct, ← Finset.mul_sum, sum_rho hN hsum hρ]
    rw [this]; ring
  obtain ⟨δ, hδ, hcoer⟩ := coercive hlam hsum hρ hR
  set Kh := Finset.univ.sup' Finset.univ_nonempty fun c => H0 c c
  have hGle : ∀ v, G v ≤ Kh + mval (n := n) ρ v := by
    intro v
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (aval (n := n) ρ v)
    have h1 := Egs_le_config hH0 n v c
    have h2 : H0 c c ≤ Kh := Finset.le_sup' (fun c => H0 c c) (Finset.mem_univ c)
    simp only [G, mval, hc, aval]
    linarith
  set R := max 0 ((Kh - G 0) / δ) + 1
  set B : Set (V → ℝ) := {v | ∑ i, v i = 0 ∧ ‖v‖ ≤ R}
  have hB : IsCompact B := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : V → ℝ)) (r := R)).subset fun v hv => by
        simpa using hv.2
  have h0B : (0 : V → ℝ) ∈ B := ⟨by simp, by simp only [norm_zero]; positivity⟩
  obtain ⟨vs, hvsB, hmax⟩ := hB.exists_isMaxOn ⟨0, h0B⟩ hG.continuousOn
  refine ⟨vs, fun v => ?_⟩
  set m := (∑ i, v i) / (Finset.univ : Finset V).card
  set v0 : V → ℝ := v + fun _ => -m
  have hv0 : ∑ i, v0 i = 0 := by
    simp only [v0, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, m]
    by_cases hV : ((Finset.univ : Finset V).card : ℝ) = 0
    · have : (Finset.univ : Finset V) = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hV)
      simp [this]
    · field_simp; ring
  have hGv : G v = G v0 := (hshift v (-m)).symm
  change G v ≤ G vs
  rw [hGv]
  by_cases hin : ‖v0‖ ≤ R
  · exact hmax ⟨hv0, hin⟩
  · push Not at hin
    have h1 := hGle v0
    have h2 := hcoer v0 hv0
    have h3 : G 0 ≤ G vs := hmax h0B
    have hR1 : (Kh - G 0) / δ + 1 ≤ R := by simp [R]
    have hR2 : Kh - G 0 + δ ≤ δ * R := by
      have := mul_le_mul_of_nonneg_left hR1 hδ.le
      rw [mul_add, mul_div_cancel₀ _ hδ.ne', mul_one] at this; linarith
    nlinarith

end

end DFT
