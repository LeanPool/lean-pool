/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.FermionOperators
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Definitions

This file defines the graph, configurations, and matrices used in
`HubbardMoments.Spec`. The proofs live in the other files.

* `arcs G`: the directed edges of a graph `G`.
* `hops G S`: the hops out of a configuration `S`, from an occupied site to an empty
  neighbouring site.
* `Config V σ`, `occ`, `basis V n`, `move`: configurations without double occupancy, their
  occupied sites, the `N_d = 0` basis of a spin composition `n`, and one hop.
* `IsProjectedHopping G t H`: the properties of the projected hopping operator `H∞`.
* `secondMoment B H`: the second spectral moment of `H` on the basis `B`.
* `pairHopping G t A`, `doublonSecondOrder`: two electrons of opposite spin with Peierls
  phases `A`, and the second-order effective Hamiltonian of a doublon.
* `FockState V σ`, `siteOcc`, `IsHop`, `IsHoppingOperator G H`, `virtualOp Q H`: Fock basis
  states (double occupancy allowed), site occupations, one hop, hopping operators, and the
  operator `V = T₁† T₁` of the Schrieffer–Wolff expansion.
-/

@[expose] public section

namespace HubbardMoments

open Finset SimpleGraph

section Hops

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The directed edges of `G`: ordered pairs of adjacent vertices. -/
def arcs : Finset (V × V) := G.interedges univ univ

@[simp]
theorem mem_arcs {p : V × V} : p ∈ arcs G ↔ G.Adj p.1 p.2 := by
  simp [arcs, G.mem_interedges_iff]

/-- Reversing the orientation of every arc leaves the sum unchanged. -/
theorem sum_arcs_swap {R : Type*} [AddCommMonoid R] (weight : V × V → R) :
    ∑ p ∈ arcs G, weight p.swap = ∑ p ∈ arcs G, weight p :=
  sum_equiv (Equiv.prodComm V V) (fun p ↦ by simp [G.adj_comm]) fun _ _ ↦ rfl

/-- The hops out of a configuration `S` (the set of occupied sites): directed edges from
an occupied site to an empty one. Their number is the `M(S)` of the paper, and the
diagonal element of `H∞²` at `S` is `λ² M(S)`. -/
def hops [DecidableEq V] (S : Finset V) : Finset (V × V) :=
  G.interedges S Sᶜ

theorem mem_hops [DecidableEq V] {S : Finset V} {p : V × V} :
    p ∈ hops G S ↔ G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S := by
  simp [hops, G.mem_interedges_iff, and_comm, and_assoc]

theorem hops_eq_filter [DecidableEq V] (S : Finset V) :
    hops G S = (arcs G).filter (fun p => p.1 ∈ S ∧ p.2 ∉ S) := by
  ext p
  simp [mem_hops]

end Hops

section Configurations

/-- A configuration with no doubly occupied site: each site is empty (`none`) or holds one
particle with spin label `s : σ`. Take `σ = Unit` for spinless fermions and a two-element
type for spin ½. -/
abbrev Config (V σ : Type*) := V → Option σ

variable {V σ : Type*} [Fintype V] [DecidableEq V]

/-- The occupied sites of a configuration. -/
def occ (c : Config V σ) : Finset V := univ.filter (fun v => c v ≠ none)

variable (V) in
/-- The no-double-occupancy basis (the `N_d = 0` sector) with `n s` particles of spin `s`
for every spin label `s`. -/
def basis [Fintype σ] [DecidableEq σ] (n : σ → ℕ) : Finset (Config V σ) :=
  univ.filter (fun c => ∀ s, (univ.filter (fun v => c v = some s)).card = n s)

/-- The configuration obtained from `c` by moving the particle at site `i` to site `j`,
keeping its spin. -/
def move (c : Config V σ) (i j : V) : Config V σ :=
  Function.update (Function.update c i none) j (c i)

/-- A legal projected hop sends an occupied site to a vacant neighbor and moves its spin. -/
def IsProjectedHop (G : SimpleGraph V) (c b : Config V σ) : Prop :=
  ∃ i j, G.Adj i j ∧ c i ≠ none ∧ c j = none ∧ b = move c i j

/-- **Projected hopping operators.** `H`, a matrix on the configurations, is a projected
hopping operator on the graph `G` with bond moduli `w` if

* it is Hermitian;
* its matrix element from `c` to `move c i j` has modulus `w i j` whenever `i` and `j` are
  adjacent, `i` is occupied and `j` is empty (one particle hops to an empty neighbour);
* its matrix element from `c` to `b` vanishes when `b` is not obtained from `c` by such a hop.

The operator `H∞ = P₀ H_t P₀` of the Hubbard model at `U → ∞`, written in the
configuration basis, has these properties when every bond has `|t_ij| = λ = t`, whatever
the fermionic signs and the Peierls phases: a hop onto an occupied site either violates
the Pauli principle or creates a doubly occupied site, which `P₀` removes. The theorems
about this structure therefore apply to `H∞`; `projectedHubbard_isProjectedHopping` proves
it for `H∞` built from fermion operators (`projectedHubbard`), with any ordering of the
orbitals. -/
structure IsGraphProjectedHopping (G : SimpleGraph V) (w : V → V → ℝ)
    (H : Matrix (Config V σ) (Config V σ) ℂ) : Prop where
  isHermitian : H.IsHermitian
  norm_apply_move : ∀ c i j, G.Adj i j → c i ≠ none → c j = none → ‖H (move c i j) c‖ = w i j
  apply_eq_zero : ∀ c b, ¬ IsProjectedHop G c b → H b c = 0

/-- A graph hopping operator with constant modulus `t` on every edge. -/
abbrev IsProjectedHopping (G : SimpleGraph V) (t : ℝ)
    (H : Matrix (Config V σ) (Config V σ) ℂ) : Prop :=
  IsGraphProjectedHopping G (fun _ _ => t) H

/-- A hopping operator with modulus `w i j` on each ordered pair of distinct sites. -/
abbrev IsWeightedProjectedHopping (w : V → V → ℝ) (H : Matrix (Config V σ) (Config V σ) ℂ) :
    Prop :=
  IsGraphProjectedHopping ⊤ w H

/-- The second spectral moment of `H` on a finite basis `B`:
`μ₂ = Tr(H_B²)/|B| - (Tr H_B/|B|)²`, where `H_B` is the block of `H` on `B`. For Hermitian
`H_B` this is the variance of its eigenvalue distribution. -/
noncomputable def secondMoment {ι : Type*} (B : Finset ι) (H : Matrix ι ι ℂ) : ℂ :=
  (∑ c ∈ B, ∑ b ∈ B, H c b * H b c) / B.card - ((∑ c ∈ B, H c c) / B.card) ^ 2

end Configurations

section PairHopping

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The second-order doublon Hamiltonian.** The `O(t²/U)` term of the effective
Hamiltonian on the doublon states, from second-order degenerate perturbation theory
(Schrieffer–Wolff): `⟨D_{R'}| H_eff^{(2)} |D_R⟩ = (1/U) ∑_m ⟨D_{R'}|H|m⟩ ⟨m|H|D_R⟩`, summed
over the two-electron states `m = (i, j)`, `i ≠ j`, without double occupancy. These have
interaction energy `0` and the doublons `U`, so the energy denominator is exactly `U`. -/
noncomputable def doublonSecondOrder (H : Matrix (V × V) (V × V) ℂ) (U : ℝ) (R' R : V) : ℂ :=
  (∑ m ∈ univ.filter (fun m : V × V => m.1 ≠ m.2), H (R', R') m * H m (R, R)) / U

end PairHopping

section Fock

/-- A Fock basis state of fermions with spin labels `σ` on the sites `V`, given by its set of
occupied orbitals `(site, spin)`. Unlike `Config`, it allows doubly occupied sites. -/
abbrev FockState (V σ : Type*) := Finset (V × σ)

variable {V σ : Type*} [DecidableEq V] [DecidableEq σ]

/-- The number of particles on site `v`. The no-double-occupancy states (`P₀`) are those with
`siteOcc c v ≤ 1` at every site. -/
def siteOcc (c : FockState V σ) (v : V) : ℕ := (c.filter (fun p => p.1 = v)).card

/-- `b` is obtained from `a` by one hop: a particle of spin `s` moves from a site `i` to an
adjacent site `j` holding no particle of spin `s` (Pauli principle). -/
def IsHop (G : SimpleGraph V) (a b : FockState V σ) : Prop :=
  ∃ i j s, G.Adj i j ∧ (i, s) ∈ a ∧ (j, s) ∉ a ∧ b = insert (j, s) (a.erase (i, s))

/-- **Hopping operators** on Fock states: the matrix element from `a` to `b` vanishes unless
`b` is obtained from `a` by one hop. The Hubbard hopping term
`H_t = -∑_{i ~ j, s} t_{ij} c†_{j s} c_{i s}` is one, for any amplitudes `t_{ij}`, Peierls
phases and fermionic signs: `c†_{j s} c_{i s}` maps a Fock basis state to `±` the state with
that one particle moved, or to zero (`hubbardHopping_isHoppingOperator` for the hopping term
built from fermion operators). -/
structure IsHoppingOperator (G : SimpleGraph V) (H : Matrix (FockState V σ) (FockState V σ) ℂ) :
    Prop where
  apply_eq_zero : ∀ a b, ¬ IsHop G a b → H b a = 0

/-- **The operator `V = T₁† T₁`** of the Schrieffer–Wolff expansion
`H_eff = T₀ - V/U + O(1/U²)`, where `T₀ = P₀ H P₀`, `T₁ = Q H P₀`, and `Q` is the set of
intermediate states (for the paper, the states with exactly one doubly occupied site):
`V_{ba} = ∑_{m ∈ Q} conj(H_{mb}) H_{ma}`. -/
noncomputable def virtualOp (Q : Finset (FockState V σ))
    (H : Matrix (FockState V σ) (FockState V σ) ℂ) :
    Matrix (FockState V σ) (FockState V σ) ℂ :=
  fun b a => ∑ m ∈ Q, star (H m b) * H m a

end Fock

section HubbardOperators

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

/-- The fermionic hopping operator with coefficient `amplitude i j` for a move from `i`
to `j`. The graph specifies which moves are allowed. -/
noncomputable def fermionHopping (G : SimpleGraph V) [DecidableRel G.Adj]
    (amplitude : V → V → ℂ) (ord : V × σ ↪ ℕ) :
    Matrix (FockState V σ) (FockState V σ) ℂ :=
  ∑ p ∈ arcs G, ∑ s, amplitude p.1 p.2 •
    (create ord (p.2, s) * annihilate ord (p.1, s))

/-- The Fock state of a configuration without double occupancy: its occupied orbitals. -/
def configState (c : Config V σ) : FockState V σ := univ.filter fun o => c o.1 = some o.2

/-- The block of the fermionic hopping operator on states without double occupancy, written
in the configuration basis. -/
noncomputable def projectedFermionHopping (G : SimpleGraph V) [DecidableRel G.Adj]
    (amplitude : V → V → ℂ) (ord : V × σ ↪ ℕ) : Matrix (Config V σ) (Config V σ) ℂ :=
  fun c b => fermionHopping G amplitude ord (configState c) (configState b)

/-- **The hopping term with arbitrary amplitudes**, `H_t = -∑_{i ≠ j} ∑_s t_{ij} c†_{i s} c_{j s}`
(a particle hops from `j` to `i` with amplitude `-t_{ij}`). It is Hermitian when
`t_{ji} = conj(t_{ij})`. The sum runs over the ordered pairs of distinct sites, the arcs of
the complete graph. -/
noncomputable def hubbardHoppingWeighted (tt : V → V → ℂ) (ord : V × σ ↪ ℕ) :
    Matrix (FockState V σ) (FockState V σ) ℂ :=
  fermionHopping ⊤ (fun i j => -tt j i) ord

/-- `H∞ = P₀ H_t P₀` for arbitrary amplitudes, in the configuration basis. -/
noncomputable def projectedHubbardWeighted (tt : V → V → ℂ) (ord : V × σ ↪ ℕ) :
    Matrix (Config V σ) (Config V σ) ℂ :=
  projectedFermionHopping ⊤ (fun i j => -tt j i) ord

end HubbardOperators

end HubbardMoments
