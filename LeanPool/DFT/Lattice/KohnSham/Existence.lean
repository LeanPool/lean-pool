/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Representability
public import LeanPool.DFT.Lattice.Fermions.SecondQuantization

/-!
# Existence of Kohn–Sham potentials for lattice fermions

`v_representable_lattice_fermions`: for `N` spinless fermions (`0 < N < M`) with hopping `t` on any
graph and any configuration-diagonal interaction `Vint`, every density that is a strictly positive
mixture of configuration densities is the density of a ground-state ensemble of `H(v)` for some
potential `v`. With `Vint = 0` this is the existence of a Kohn–Sham potential
(`ks_potential_exists`).
-/

@[expose] public section

namespace DFT

variable {M N : ℕ}

/-- **Ensemble v-representability for lattice fermions.** -/
theorem v_representable_lattice_fermions [Nonempty (Conf M N)] (G : SimpleGraph (Fin M))
    [DecidableRel G.Adj] (t : ℝ) (Vint : Conf M N → ℝ) (hN0 : 0 < N) (hNM : N < M)
    {ρ : Fin M → ℝ} {lam : Conf M N → ℝ} (hlam : ∀ s, 0 < lam s) (hsum : ∑ s, lam s = 1)
    (hρ : ρ = fun i => ∑ s, lam s * occF i s) :
    ∃ v : Fin M → ℝ, ∃ Γ ∈ Ens (H0F G t Vint) occF v, ensDens occF Γ = ρ :=
  ensemble_v_representable (H0F_isSymm G t Vint) (fun i s => by unfold occF; split_ifs <;> norm_num)
    sum_occF hlam hsum hρ (rigid_occF hN0 hNM)

/-- **Existence of a Kohn–Sham potential.** Every strictly positive mixture of configuration
densities is the ground-state (ensemble) density of a non-interacting system. -/
theorem ks_potential_exists [Nonempty (Conf M N)] (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t : ℝ)
    (hN0 : 0 < N) (hNM : N < M) {ρ : Fin M → ℝ} {lam : Conf M N → ℝ} (hlam : ∀ s, 0 < lam s)
    (hsum : ∑ s, lam s = 1) (hρ : ρ = fun i => ∑ s, lam s * occF i s) :
    ∃ vs : Fin M → ℝ, ∃ Γ ∈ Ens (H0F G t (0 : Conf M N → ℝ)) occF vs, ensDens occF Γ = ρ :=
  v_representable_lattice_fermions G t 0 hN0 hNM hlam hsum hρ

end DFT
