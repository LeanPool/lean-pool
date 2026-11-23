/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.HK.Gap
public import LeanPool.DFT.Lattice.Basic.Spectral
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.FunProp
meta import Mathlib.Tactic.GCongr
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.LinearCombination
meta import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

/-!
# Spectral gaps of non-degenerate ground states and Lipschitz densities

* `HasGap H ψ g`: the variational gap condition `⟨χ, H χ⟩ ≥ (⟨ψ, H ψ⟩ + g) ‖χ‖²` for `χ ⊥ ψ`.
* `exists_gap_of_unique`: a non-degenerate normalised ground state has a positive gap.
* `dens_eq_of_gap`: all normalised ground states of a gapped Hamiltonian share their density.
* `dens_lipschitz_of_gap`: near a potential with a gapped ground state, the density of any
  normalised ground state is a Lipschitz function of the potential (first-order perturbation
  theory by Rayleigh quotients, Davis–Kahan style).
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {C V : Type*} [Fintype C] [Fintype V]

lemma HasGap.mono {H : Matrix C C ℝ} {ψ : C → ℝ} {g g' : ℝ} (h : HasGap H ψ g) (hg : g' ≤ g) :
    HasGap H ψ g' := fun χ hχ => by
  have := h χ hχ
  nlinarith [dot_self_nonneg χ]

lemma qf_smul (H : Matrix C C ℝ) (r : ℝ) (χ : C → ℝ) : qf H (r • χ) = r ^ 2 * qf H χ := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma sq_le_dot_self (χ : C → ℝ) (c : C) : χ c ^ 2 ≤ χ ⬝ᵥ χ := by
  rw [sq]
  exact Finset.single_le_sum (f := fun j => χ j * χ j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ c)

/-- **Non-degenerate ground states are gapped.** If every ground state of `H` is a multiple of the
normalised ground state `ψ`, then `ψ` has a positive variational gap. -/
theorem exists_gap_of_unique {H : Matrix C C ℝ} {ψ : C → ℝ} (hψ : IsGroundState H ψ)
    (hn : ψ ⬝ᵥ ψ = 1) (hu : ∀ φ, IsGroundState H φ → ∃ a : ℝ, φ = a • ψ) :
    ∃ g, 0 < g ∧ HasGap H ψ g := by
  set S : Set (C → ℝ) := {χ | ψ ⬝ᵥ χ = 0 ∧ χ ⬝ᵥ χ = 1}
  -- reduction to unit vectors
  have hred : ∀ g, (∀ u ∈ S, qf H ψ + g ≤ qf H u) → HasGap H ψ g := by
    intro g hS χ hχ
    by_cases h0 : χ ⬝ᵥ χ = 0
    · have : χ = 0 := dotProduct_self_eq_zero.mp h0
      subst this; simp [qf]
    have hpos : 0 < χ ⬝ᵥ χ := lt_of_le_of_ne (dot_self_nonneg χ) (Ne.symm h0)
    set r := Real.sqrt (χ ⬝ᵥ χ)
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r ^ 2 = χ ⬝ᵥ χ := Real.sq_sqrt hpos.le
    have hu : r⁻¹ • χ ∈ S := by
      refine ⟨by rw [dotProduct_smul, hχ, smul_zero], ?_⟩
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hrr]
      field_simp
    have h1 := hS _ hu
    rw [qf_smul] at h1
    have h2 : qf H χ = r ^ 2 * (r⁻¹ ^ 2 * qf H χ) := by field_simp
    rw [h2, ← hrr]
    exact mul_comm (qf H ψ + g) (r ^ 2) ▸ mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exact ⟨1, one_pos, hred 1 (by simp [hSe])⟩
  have hcomp : IsCompact S := by
    exact isCompact_sphere1.of_isClosed_subset
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const)) (fun _ h => h.2)
  obtain ⟨u0, hu0, hmin⟩ := hcomp.exists_isMinOn hSne (continuous_qf H).continuousOn
  refine ⟨qf H u0 - qf H ψ, ?_, hred _ (fun u hu => by
    have := hmin hu; change qf H u0 ≤ qf H u at this; linarith)⟩
  by_contra hle
  push Not at hle
  have hge := hψ.2 u0
  rw [hn, hu0.2, mul_one, mul_one] at hge
  have hgs : IsGroundState H u0 := by
    refine ⟨fun h => by have := hu0.2; rw [h] at this; simp at this, fun φ => ?_⟩
    have := hψ.2 φ
    rw [hn, mul_one] at this
    rw [hu0.2, mul_one]
    have heq : qf H u0 = qf H ψ := by linarith
    rw [heq]; exact this
  obtain ⟨a, ha⟩ := hu u0 hgs
  have h1 := hu0.1
  rw [ha, dotProduct_smul, hn, smul_eq_mul, mul_one] at h1
  have h2 := hu0.2
  rw [ha, h1, zero_smul] at h2
  simp at h2

omit [Fintype V] in
/-- All normalised ground states of a Hamiltonian with a gapped ground state have the same density.
-/
theorem dens_eq_of_gap {H : Matrix C C ℝ} (hS : H.IsSymm) (n : V → C → ℝ) {ψ φ : C → ℝ}
    (hψ : IsGroundState H ψ) (hn : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g) (hgap : HasGap H ψ g)
    (hφ : IsGroundState H φ) (hφn : φ ⬝ᵥ φ = 1) : dens n φ = dens n ψ := by
  have h := unique_of_gap hS hψ hn hg hgap hφ
  set a := ψ ⬝ᵥ φ
  have ha : a ^ 2 = 1 := by
    rw [h, smul_dotProduct, dotProduct_smul, hn, smul_eq_mul, smul_eq_mul] at hφn
    linear_combination hφn
  funext i
  simp only [dens]
  apply Finset.sum_congr rfl; intro c _
  rw [h, Pi.smul_apply, smul_eq_mul, mul_pow, ha, one_mul]

/-- crude bound on the potential coupling of a configuration -/
lemma abs_sum_mul_le (n : V → C → ℝ) (k : V → ℝ) (c : C) :
    |∑ i, k i * n i c| ≤ (∑ i, ∑ c', |n i c'|) * ‖k‖ := by
  calc |∑ i, k i * n i c| ≤ ∑ i, |k i * n i c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖k‖ * ∑ c', |n i c'| := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        apply mul_le_mul (by simpa using norm_le_pi_norm k i)
          (Finset.single_le_sum (f := fun c' => |n i c'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ c)) (abs_nonneg _) (norm_nonneg _)
    _ = (∑ i, ∑ c', |n i c'|) * ‖k‖ := by rw [← Finset.mul_sum, mul_comm]

/-- **Lipschitz dependence of the density near a gapped ground state.** If `ψ` is a normalised
ground state of `H(x)` with gap `g > 0`, then for `z` close to `x` every normalised ground state
`φ` of `H(z)` satisfies `‖ρ_φ - ρ_ψ‖ ≤ K ‖z - x‖`. -/
theorem dens_lipschitz_of_gap [DecidableEq C] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)
    {x : V → ℝ} {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n x) ψ) (hn : ψ ⬝ᵥ ψ = 1) {g : ℝ}
    (hg : 0 < g) (hgap : HasGap (hamN H0 n x) ψ g) :
    ∃ K δ : ℝ, 0 < δ ∧ ∀ (z : V → ℝ) (φ : C → ℝ), IsGroundState (hamN H0 n z) φ →
      φ ⬝ᵥ φ = 1 → dist z x < δ → dist (dens n φ) (dens n ψ) ≤ K * dist z x := by
  classical
  set Λ := ∑ i, ∑ c', |n i c'| with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  refine ⟨8 * Λ ^ 2 / g, g / (4 * (Λ + 1)), by positivity, fun z φ hφ hφn hz => ?_⟩
  set Hx := hamN H0 n x
  set Hz := hamN H0 n z
  set η := Λ * dist z x with hη
  have hη0 : 0 ≤ η := mul_nonneg hΛ0 dist_nonneg
  have hηg : η ≤ g / 4 := by
    have h1 : η ≤ Λ * (g / (4 * (Λ + 1))) := mul_le_mul_of_nonneg_left hz.le hΛ0
    have h2 : Λ * (g / (4 * (Λ + 1))) ≤ g / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hg]
    exact h1.trans h2
  set d : C → ℝ := fun c => ∑ i, (z i - x i) * n i c
  have hd : ∀ c, |d c| ≤ η := by
    intro c
    have := abs_sum_mul_le n (z - x) c
    simpa [d, hη, dist_eq_norm] using this
  have hd2 : ∀ c, d c ^ 2 ≤ η ^ 2 := fun c => sq_le_sq' (abs_le.mp (hd c)).1 (abs_le.mp (hd c)).2
  -- eigen-equations
  have hSx := hamN_isSymm hH0 n x
  have hSz := hamN_isSymm hH0 n z
  set E := qf Hx ψ
  set E' := qf Hz φ
  have hEx : Hx *ᵥ ψ = E • ψ := by have := isGroundState_eigen hSx hψ; rwa [hn, div_one] at this
  have hEz : Hz *ᵥ φ = E' • φ := by have := isGroundState_eigen hSz hφ; rwa [hφn, div_one] at this
  have hHzx : ∀ c, (Hz *ᵥ φ) c = (Hx *ᵥ φ) c + d c * φ c := by
    intro c
    simp only [Hz, Hx, hamN_mulVec_apply, d]
    have : ∑ i, z i * n i c = ∑ i, x i * n i c + ∑ i, (z i - x i) * n i c := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this]; ring
  -- (i) upper bound on E'
  have hE'le : E' ≤ E + η := by
    have h1 := hφ.2 ψ
    rw [hn, hφn, mul_one, mul_one] at h1
    have h2 : qf Hz ψ = E + ∑ c, d c * ψ c ^ 2 := by
      have shift : x + (1 : ℝ) • (z - x) = z := by
        simp only [one_smul]
        abel
      have increment := qf_hamN_add H0 n x (z - x) 1 ψ
      rw [shift, one_mul, dotProduct, dens_weighted] at increment
      exact increment
    have h3 : ∑ c, d c * ψ c ^ 2 ≤ η := by
      calc ∑ c, d c * ψ c ^ 2 ≤ ∑ c, η * (ψ c * ψ c) := by
            apply Finset.sum_le_sum; intro c _
            rw [sq]; exact mul_le_mul_of_nonneg_right (abs_le.mp (hd c)).2 (mul_self_nonneg _)
        _ = η := by rw [← Finset.mul_sum]; change η * (ψ ⬝ᵥ ψ) = η; rw [hn, mul_one]
    linarith
  -- (ii) decomposition φ = a ψ + χ
  obtain ⟨h0, hnorm, -⟩ := decomp hSx hn hEx φ
  set a := ψ ⬝ᵥ φ
  set χ := φ - a • ψ with hχ
  have hχc : ∀ c, φ c = a * ψ c + χ c := fun c => by simp [hχ]
  -- (iii) ⟨χ, (Hx - E') χ⟩ = -Σ χ d φ
  have hkey : qf Hx χ = E' * (χ ⬝ᵥ χ) - ∑ c, χ c * (d c * φ c) := by
    have hHχ : Hx *ᵥ χ = E' • φ - (fun c => d c * φ c) - (a * E) • ψ := by
      rw [hχ, mulVec_sub, mulVec_smul, hEx, smul_smul]
      congr 1
      funext c
      have := hHzx c
      rw [hEz] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
      linarith
    have hχψ : χ ⬝ᵥ ψ = 0 := by rw [dotProduct_comm]; exact h0
    have hφeq : φ = a • ψ + χ := funext fun c => by simp [hχc c]
    have hχφ : χ ⬝ᵥ φ = χ ⬝ᵥ χ := by
      calc χ ⬝ᵥ φ = χ ⬝ᵥ (a • ψ + χ) := by rw [← hφeq]
        _ = χ ⬝ᵥ χ := by rw [dotProduct_add, dotProduct_smul, hχψ, smul_zero, zero_add]
    unfold qf
    rw [hHχ, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, hχφ, hχψ,
      smul_eq_mul, smul_eq_mul, mul_zero, sub_zero]
    rfl
  -- (iv) gap and AM-GM
  have hgx := hgap χ h0
  have hamgm : -∑ c, χ c * (d c * φ c) ≤ g / 4 * (χ ⬝ᵥ χ) + η ^ 2 / g := by
    have : ∀ c, -(χ c * (d c * φ c)) ≤ g / 4 * (χ c * χ c) + η ^ 2 / g * (φ c * φ c) := by
      intro c
      have h1 : 0 ≤ (g / 2 * χ c + d c * φ c) ^ 2 / g := by positivity
      have h2 : d c ^ 2 * φ c ^ 2 / g ≤ η ^ 2 * φ c ^ 2 / g :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hd2 c) (sq_nonneg _)) hg.le
      have h3 : (g / 2 * χ c + d c * φ c) ^ 2 / g =
          g / 4 * (χ c * χ c) + d c ^ 2 * φ c ^ 2 / g + χ c * (d c * φ c) := by
        field_simp; ring
      have h4 : η ^ 2 / g * (φ c * φ c) = η ^ 2 * φ c ^ 2 / g := by ring
      linarith only [h1, h2, h3, h4]
    calc -∑ c, χ c * (d c * φ c) = ∑ c, -(χ c * (d c * φ c)) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ c, (g / 4 * (χ c * χ c) + η ^ 2 / g * (φ c * φ c)) :=
          Finset.sum_le_sum fun c _ => this c
      _ = g / 4 * (χ ⬝ᵥ χ) + η ^ 2 / g * (φ ⬝ᵥ φ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
      _ = g / 4 * (χ ⬝ᵥ χ) + η ^ 2 / g := by rw [hφn, mul_one]
  have hχ0 := dot_self_nonneg χ
  have hχbound : χ ⬝ᵥ χ ≤ (2 * η / g) ^ 2 := by
    have h1 : (g / 2) * (χ ⬝ᵥ χ) ≤ η ^ 2 / g := by
      have energy := mul_le_mul_of_nonneg_right hE'le hχ0
      have perturbation := mul_le_mul_of_nonneg_right hηg hχ0
      nlinarith only [hgx, hkey, hamgm, energy, perturbation]
    have h2 : (2 * η / g) ^ 2 = 4 * (η ^ 2 / g) / g := by field_simp; ring
    rw [h2, le_div_iff₀ hg]
    linarith only [h1, div_nonneg (sq_nonneg η) hg.le]
  -- (v) density estimate
  set s := Real.sqrt (χ ⬝ᵥ χ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ≤ 2 * η / g := (Real.sqrt_le_left (by positivity)).mpr hχbound
  have ha2 : a ^ 2 + χ ⬝ᵥ χ = 1 := by rw [← hnorm, hφn]
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by linarith [sq_nonneg a])
  have hss : s ^ 2 = χ ⬝ᵥ χ := Real.sq_sqrt hχ0
  have hχcs : ∀ c, |χ c| ≤ s := fun c => Real.abs_le_sqrt (sq_le_dot_self χ c)
  have hψc : ∀ c, |ψ c| ≤ 1 := fun c => by
    rw [abs_le_one_iff_mul_self_le_one, ← sq, ← hn]; exact sq_le_dot_self ψ c
  have ha1 : |a| ≤ 1 := by
    rw [abs_le_one_iff_mul_self_le_one, ← sq]; linarith
  have hpt : ∀ c, |φ c ^ 2 - ψ c ^ 2| ≤ 4 * s := by
    intro c
    have hid : φ c ^ 2 - ψ c ^ 2 = -(s ^ 2) * ψ c ^ 2 + 2 * a * ψ c * χ c + χ c ^ 2 := by
      rw [hχc c, hss]; linear_combination (ψ c ^ 2) * ha2
    rw [hid]
    have e1 : |-(s ^ 2) * ψ c ^ 2| ≤ s ^ 2 := by
      rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg s), abs_of_nonneg (sq_nonneg _)]
      have : ψ c ^ 2 ≤ 1 := by rw [← hn]; exact sq_le_dot_self ψ c
      nlinarith [sq_nonneg s]
    have e2 : |2 * a * ψ c * χ c| ≤ 2 * s := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have haψ : |a| * |ψ c| ≤ 1 := by
        calc
          |a| * |ψ c| ≤ 1 * 1 := mul_le_mul ha1 (hψc c) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul _
      have := mul_le_mul haψ (hχcs c) (abs_nonneg _)
        zero_le_one
      nlinarith [abs_nonneg a, abs_nonneg (ψ c), abs_nonneg (χ c)]
    have e3 : |χ c ^ 2| ≤ s ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), hss]; exact sq_le_dot_self χ c
    calc |-(s ^ 2) * ψ c ^ 2 + 2 * a * ψ c * χ c + χ c ^ 2|
        ≤ |-(s ^ 2) * ψ c ^ 2| + |2 * a * ψ c * χ c| + |χ c ^ 2| := abs_add_three _ _ _
      _ ≤ s ^ 2 + 2 * s + s ^ 2 := by linarith
      _ ≤ 4 * s := by nlinarith
  have hfin : dist (dens n φ) (dens n ψ) ≤ 4 * s * Λ := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [Pi.sub_apply, dens, Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    calc |∑ c, (n i c * φ c ^ 2 - n i c * ψ c ^ 2)| ≤ ∑ c, |n i c * φ c ^ 2 - n i c * ψ c ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, |n i c| * (4 * s) := by
          apply Finset.sum_le_sum; intro c _
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hpt c) (abs_nonneg _)
      _ = 4 * s * ∑ c, |n i c| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ 4 * s * Λ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.single_le_sum (f := fun i => ∑ c', |n i c'|)
            (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  calc dist (dens n φ) (dens n ψ) ≤ 4 * s * Λ := hfin
    _ ≤ 4 * (2 * η / g) * Λ := by gcongr
    _ = 8 * Λ ^ 2 / g * dist z x := by rw [hη]; field_simp; ring

end

end DFT
