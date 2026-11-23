/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Basic.GroundState
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.LinearCombination
meta import Mathlib.Tactic.Ring

/-!
# Hohenberg–Kohn theorems on a finite configuration space

Many-body Hamiltonian `hamN H0 n v = H0 + diag(Σ_i v_i n_i)` on configurations `C`, density
`dens n ψ`.
* `weak_hk` (real pure states): equal ground-state densities make each state a ground state of both
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

omit [DecidableEq C] in
/-- Pairing a potential with the occupation average transfers the sum to configuration weights. -/
lemma occupation_pairing (n : V → C → ℝ) (v : V → ℝ) (weights : C → ℝ) :
    v ⬝ᵥ (fun i => ∑ c, weights c * n i c) = ∑ c, weights c * ∑ i, v i * n i c := by
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => by ring))

omit [DecidableEq C] in
lemma dens_weighted (n : V → C → ℝ) (w : V → ℝ) (φ : C → ℝ) :
    ∑ i, w i * dens n φ i = ∑ c, (∑ i, w i * n i c) * φ c ^ 2 := by
  simpa only [dens, dotProduct, mul_comm] using occupation_pairing n w (fun c => φ c ^ 2)

lemma qf_hamN (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (φ : C → ℝ) :
    qf (hamN H0 n v) φ = qf H0 φ + ∑ i, v i * dens n φ i := by
  rw [dens_weighted]
  simp only [qf, hamN, Matrix.add_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, sq]
  exact Finset.sum_congr rfl (fun c _ => by ring)

/-- The Rayleigh numerator is affine in the external potential. -/
lemma qf_hamN_add (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v w : V → ℝ) (t : ℝ) (ψ : C → ℝ) :
    qf (hamN H0 n (v + t • w)) ψ = qf (hamN H0 n v) ψ + t * (w ⬝ᵥ dens n ψ) := by
  rw [qf_hamN, qf_hamN]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, dotProduct,
    Finset.mul_sum]
  ring_nf

/-- Real pure-state version of Penz and van Leeuwen, Theorem 7 (weak HK). A shared ground-state
density makes each state a ground state of the other Hamiltonian. -/
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
  exact ⟨hψ'.of_qf_eq hN' hN e1, hψ.of_qf_eq hN hN' e2⟩

lemma hamN_mulVec_apply (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : C → ℝ) (c : C) :
    (hamN H0 n v *ᵥ ψ) c = (H0 *ᵥ ψ) c + (∑ i, v i * n i c) * ψ c := by
  simp [hamN, Matrix.add_mulVec, Matrix.mulVec_diagonal]

omit [Fintype C] in
lemma hamN_isSymm {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) :
    (hamN H0 n v).IsSymm :=
  hH0.add (Matrix.isSymm_diagonal _)

/-- Rigidity modulo a set `Tr` of trivial potential shifts: a density-coupled potential that is
constant on every configuration lies in `Tr`. `Rigid` is the case of the constant potentials. -/
def RigidMod (Tr : Set (V → ℝ)) (n : V → C → ℝ) : Prop :=
  ∀ (w : V → ℝ) (κ : ℝ), (∀ c, ∑ i, w i * n i c = κ) → w ∈ Tr

/-- Non-unique v-representability modulo trivial shifts `Tr`: some ground state of `H(v)` is also
a ground state of `H(v')` with `v - v' ∉ Tr`. `NonUV` is the case of the constant potentials. -/
def NonUVMod (Tr : Set (V → ℝ)) (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Prop :=
  ∃ (ψ : C → ℝ) (v' : V → ℝ), IsGroundState (hamN H0 n v) ψ ∧ IsGroundState (hamN H0 n v') ψ ∧
    (fun i => v i - v' i) ∉ Tr

/-- The constant potentials. -/
def constPot : Set (V → ℝ) := {w | ∃ k, ∀ i, w i = k}

/-- Rigidity modulo constant potential shifts. -/
def Rigid (n : V → C → ℝ) : Prop := RigidMod constPot n

/-- Non-unique v-representability modulo constant potential shifts. -/
def NonUV (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Prop :=
  NonUVMod constPot H0 n v

omit [Fintype C] [DecidableEq C] in
lemma rigid_iff_rigidMod (n : V → C → ℝ) : Rigid n ↔ RigidMod constPot n := Iff.rfl

lemma nonUV_iff_nonUVMod (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    NonUV H0 n v ↔ NonUVMod constPot H0 n v := Iff.rfl

/-- The difference of two potentials is constant on the support of a common eigenvector. -/
lemma potential_sub_eq_on_support {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v v' : V → ℝ}
    {ψ : C → ℝ} {E E' : ℝ} (h : hamN H0 n v *ᵥ ψ = E • ψ)
    (h' : hamN H0 n v' *ᵥ ψ = E' • ψ) {c : C} (hc : ψ c ≠ 0) :
    ∑ i, (v - v') i * n i c = E - E' := by
  have left := congrFun h c
  have right := congrFun h' c
  rw [hamN_mulVec_apply, Pi.smul_apply, smul_eq_mul] at left right
  apply mul_right_cancel₀ hc
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  linear_combination left - right

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
  refine hsupp (v - v') _ fun c hc => potential_sub_eq_on_support e1 e2 hc


/-! ### Global (symmetry) mechanism of non-uniqueness — spin-DFT corollary
If the ground state ψ of H(v) lives only on configurations where W(c) = Σ_i w_i n_i(c) attains its
minimum κ, then ψ minimises both ⟨H(v)⟩ and ⟨W⟩, hence remains a ground state of H(v + ε w) for
every ε ≥ 0: a whole half-line of potentials shares ψ (and its density). No commutation and no
spectral gap are needed. Spin-DFT reading (Capelle–Vignale / Eschrig–Pickett): sites = (site, spin),
w = Zeeman coupling (+1 on ↓, −1 on ↑); a fully polarised ground state minimises W, so increasing
the field B never changes it — B is not unique. -/

theorem nonunique_of_minimiser {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v w : V → ℝ} {ψ : C → ℝ} {κ : ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ)
    (hmin : ∀ c, κ ≤ ∑ i, w i * n i c)
    (hsupp : ∀ c, ψ c ≠ 0 → ∑ i, w i * n i c = κ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsGroundState (hamN H0 n (v + ε • w)) ψ := by
  have hsplit (φ : C → ℝ) : qf (hamN H0 n (v + ε • w)) φ =
      qf (hamN H0 n v) φ + ε * ∑ i, w i * dens n φ i :=
    qf_hamN_add H0 n v w ε φ
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
