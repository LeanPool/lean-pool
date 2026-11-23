/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Basic.GroundState

/-!
# Hohenberg–Kohn theorems on a finite configuration space

Many-body Hamiltonian `hamN H0 n v = H0 + diag(Σ_i v_i n_i)` on configurations `C`, density
`dens n ψ`.
* `weak_hk`: equal ground-state densities ⇒ each ground state is a ground state of both
  Hamiltonians.
* `strong_hk`: if no non-constant `w` makes `Σ_i w_i n_i` constant on the support of the ground
  state, the potential is determined up to a constant.
* `nonunique_of_minimiser`: ground states living on the minimum set of `W = Σ_i w_i n_i` are shared
  by the whole half-line `v + ε w`, `ε ≥ 0` (spin-DFT non-uniqueness mechanism).
-/

@[expose] public section

namespace DFT

section

open Matrix Finset

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- many-body Hamiltonian H(v) = H0 + diag(Σ_i v_i n_i) -/
noncomputable def hamN (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Matrix C C ℝ :=
  H0 + Matrix.diagonal (fun c => ∑ i, v i * n i c)

/-- (unnormalised) density ρ_ψ(i) = Σ_c n_i(c) ψ(c)² -/
def dens (n : V → C → ℝ) (ψ : C → ℝ) : V → ℝ := fun i => ∑ c, n i c * ψ c ^ 2

lemma qf_hamN (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (φ : C → ℝ) :
    qf (hamN H0 n v) φ = qf H0 φ + ∑ i, v i * dens n φ i := by
  simp only [qf, hamN, Matrix.add_mulVec, dotProduct_add, dens]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro i _; ring

/-- PvL Theorem 7 (weak HK): a shared ground-state density makes each ground state a ground state of
the other Hamiltonian. -/
theorem weak_hk {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v v' : V → ℝ} {ψ ψ' : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hψ' : IsGroundState (hamN H0 n v') ψ')
    (hN : ψ ⬝ᵥ ψ = 1) (hN' : ψ' ⬝ᵥ ψ' = 1) (hd : dens n ψ = dens n ψ') :
    IsGroundState (hamN H0 n v') ψ ∧ IsGroundState (hamN H0 n v) ψ' := by
  have a := hψ.2 ψ'
  have b := hψ'.2 ψ
  rw [hN, hN', mul_one, mul_one] at a b
  rw [qf_hamN, qf_hamN, hd] at a b
  -- a : qf H0 ψ + Σ v ρ' ≤ qf H0 ψ' + Σ v ρ'   and   b : qf H0 ψ' + Σ v' ρ' ≤ qf H0 ψ + Σ v' ρ'
  have hE : qf H0 ψ = qf H0 ψ' := by linarith
  have e1 : qf (hamN H0 n v') ψ = qf (hamN H0 n v') ψ' := by rw [qf_hamN, qf_hamN, hd, hE]
  have e2 : qf (hamN H0 n v) ψ' = qf (hamN H0 n v) ψ := by rw [qf_hamN, qf_hamN, hd, hE]
  refine ⟨⟨hψ.1, fun φ => ?_⟩, ⟨hψ'.1, fun φ => ?_⟩⟩
  · rw [e1, hN]; have := hψ'.2 φ; rwa [hN'] at this
  · rw [e2, hN']; have := hψ.2 φ; rwa [hN] at this

lemma hamN_mulVec_apply (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : C → ℝ) (c : C) :
    (hamN H0 n v *ᵥ ψ) c = (H0 *ᵥ ψ) c + (∑ i, v i * n i c) * ψ c := by
  simp [hamN, Matrix.add_mulVec, Matrix.mulVec_diagonal]

omit [Fintype C] in
lemma hamN_isSymm {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) :
    (hamN H0 n v).IsSymm :=
  hH0.add (Matrix.isSymm_diagonal _)

/-- Strong HK under a lattice unique-continuation hypothesis on the support of ψ. -/
theorem strong_hk {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v v' : V → ℝ}
    {ψ ψ' : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hψ' : IsGroundState (hamN H0 n v') ψ')
    (hN : ψ ⬝ᵥ ψ = 1) (hN' : ψ' ⬝ᵥ ψ' = 1) (hd : dens n ψ = dens n ψ')
    (hsupp : ∀ (w : V → ℝ) (κ : ℝ), (∀ c, ψ c ≠ 0 → ∑ i, w i * n i c = κ) → ∃ k, ∀ i, w i = k) :
    ∃ k, ∀ i, v i - v' i = k := by
  have hψv' := (weak_hk hψ hψ' hN hN' hd).1
  have e1 := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  have e2 := isGroundState_eigen (hamN_isSymm hH0 n v') hψv'
  set E := qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ)
  set E' := qf (hamN H0 n v') ψ / (ψ ⬝ᵥ ψ)
  apply hsupp (fun i => v i - v' i) (E - E')
  intro c hc
  have h1 := congrFun e1 c; have h2 := congrFun e2 c
  rw [hamN_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hkey : (∑ i, (v i - v' i) * n i c) * ψ c = (E - E') * ψ c := by
    have : ∑ i, (v i - v' i) * n i c = ∑ i, v i * n i c - ∑ i, v' i * n i c := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this]; linear_combination h1 - h2
  exact mul_right_cancel₀ hc hkey


/-! ### Global (symmetry) mechanism of non-uniqueness — spin-DFT corollary
If the ground state ψ of H(v) lives only on configurations where W(c) = Σ_i w_i n_i(c) attains its
minimum κ, then ψ minimises both ⟨H(v)⟩ and ⟨W⟩, hence remains a ground state of H(v + ε w) for
every ε ≥ 0: a whole half-line of potentials shares ψ (and its density). No commutation and no
spectral gap are needed. Spin-DFT reading (Capelle–Vignale / Eschrig–Pickett): sites = (site, spin),
w = Zeeman coupling (+1 on ↓, −1 on ↑); a fully polarised ground state minimises W, so increasing
the field B never changes it — B is not unique. -/

omit [DecidableEq C] in
lemma dens_weighted (n : V → C → ℝ) (w : V → ℝ) (φ : C → ℝ) :
    ∑ i, w i * dens n φ i = ∑ c, (∑ i, w i * n i c) * φ c ^ 2 := by
  simp only [dens, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro i _; ring

theorem nonunique_of_minimiser {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v w : V → ℝ} {ψ : C → ℝ} {κ : ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ)
    (hmin : ∀ c, κ ≤ ∑ i, w i * n i c)
    (hsupp : ∀ c, ψ c ≠ 0 → ∑ i, w i * n i c = κ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsGroundState (hamN H0 n (v + ε • w)) ψ := by
  -- the potential term of v + ε w splits
  have hsplit : ∀ φ : C → ℝ, qf (hamN H0 n (v + ε • w)) φ =
      qf (hamN H0 n v) φ + ε * ∑ i, w i * dens n φ i := by
    intro φ
    rw [qf_hamN, qf_hamN]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    ring_nf
  -- ⟨W⟩ ≥ κ |φ|², with equality for ψ
  have hW : ∀ φ : C → ℝ, κ * (φ ⬝ᵥ φ) ≤ ∑ i, w i * dens n φ i := by
    intro φ
    rw [dens_weighted]
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum; intro c _
    have := hmin c
    nlinarith [sq_nonneg (φ c)]
  have hWψ : ∑ i, w i * dens n ψ i = κ * (ψ ⬝ᵥ ψ) := by
    rw [dens_weighted]
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    by_cases hc : ψ c = 0
    · simp [hc]
    · rw [hsupp c hc]; ring
  refine ⟨hψ.1, fun φ => ?_⟩
  rw [hsplit, hsplit, hWψ]
  have h1 := hψ.2 φ
  have h2 := hW φ
  have hψψ : 0 ≤ ψ ⬝ᵥ ψ := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hε hψψ)]

end

end DFT
