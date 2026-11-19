/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Definitions

This file defines the graph, configurations, and matrices used in
`HubbardMoments.Spec`. The proofs live in the other files.

* `sector V a b k`: basis states of `a` up and `b` down electrons on the sites `V` with
  exactly `k` doubly occupied sites.
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

section Sector

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The basis states with `a` up electrons, `b` down electrons and exactly `k` doubly
occupied sites, as pairs (up-occupied sites, down-occupied sites). A pair `(u, d)` of
subsets of the sites labels exactly one Fock basis state, so these pairs count the
states. -/
def sector (a b k : ℕ) : Finset (Finset V × Finset V) :=
  (powersetCard a univ ×ˢ powersetCard b univ).filter (fun p => (p.1 ∩ p.2).card = k)

end Sector

section Hops

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The directed edges of `G`: ordered pairs of adjacent vertices. -/
def arcs : Finset (V × V) := univ.filter (fun p => G.Adj p.1 p.2)

/-- The hops out of a configuration `S` (the set of occupied sites): directed edges from
an occupied site to an empty one. Their number is the `M(S)` of the paper, and the
diagonal element of `H∞²` at `S` is `λ² M(S)`. -/
def hops [DecidableEq V] (S : Finset V) : Finset (V × V) :=
  (arcs G).filter (fun p => p.1 ∈ S ∧ p.2 ∉ S)

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

section FermionOperators

variable {O : Type*} [DecidableEq O]

/-- The number of occupied orbitals of `S` that come before `o` in the order `ord`. -/
def countBelow (ord : O ↪ ℕ) (S : Finset O) (o : O) : ℕ := (S.filter fun x => ord x < ord o).card

/-- **Fermion annihilation operator** `c_o` on the Fock space of the orbitals `O`. The basis
state of an occupied set `S` is `|S⟩ = c†_{o₁} ⋯ c†_{o_k} |0⟩`, with `o₁, …, o_k` the orbitals
of `S` in the order `ord`. Then `c_o |S⟩ = (-1)^m |S \ {o}⟩` if `o ∈ S`, `m` the number of
orbitals of `S` before `o`, and `c_o |S⟩ = 0` otherwise. -/
def annihilate (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∈ S ∧ S' = S.erase o then (-1) ^ countBelow ord S o else 0

/-- **Fermion creation operator** `c†_o`: `c†_o |S⟩ = (-1)^m |S ∪ {o}⟩` if `o ∉ S`, `m` the
number of orbitals of `S` before `o`, and `0` otherwise. It is the adjoint of `annihilate`. -/
def create (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∉ S ∧ S' = insert o S then (-1) ^ countBelow ord S o else 0

end FermionOperators

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

section FinitePopulation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Moments of sampling without replacement.** The `ℓ`-th moment of the sum of `k` values
drawn without replacement from the population `ε`: the average of `(∑_{i ∈ K} ε_i)^ℓ` over
the `k`-subsets `K` of `V`. For `k` non-interacting fermions of one spin species with
single-particle energies `ε`, the many-body energies are exactly these sums (one Slater
determinant per `K`), so this is the `μ_ℓ` of the paper at `U = 0`. -/
noncomputable def sampleMoment (ε : V → ℝ) (k ℓ : ℕ) : ℝ :=
  (∑ K ∈ powersetCard k univ, (∑ i ∈ K, ε i) ^ ℓ) / (Fintype.card V).choose k

/-- `p_m = k(k-1)⋯(k-m+1) / (N(N-1)⋯(N-m+1))`: the probability that `m` given distinct labels
are all among `k` labels drawn without replacement from `N`. It is `0` for `m > k`. -/
noncomputable def inclusionProb (N k m : ℕ) : ℝ := (k.descFactorial m : ℝ) / N.descFactorial m

end FinitePopulation

/-- **One hop of labelled hard-core particles.** `pos p` is the site of particle `p`. One
particle `p` moves to a site `w` adjacent to its own that no particle occupies. A closed walk
of `h` hops is a sequence `walk 0, …, walk h` of positions, consecutive ones related by
`IsParticleHop`, whose final sites are a permutation `σ` of the initial ones:
`walk h p = walk 0 (σ p)`. -/
def IsParticleHop {P V : Type*} [DecidableEq P] (G : SimpleGraph V) (pos pos' : P → V) : Prop :=
  ∃ p w, G.Adj (pos p) w ∧ w ∉ Set.range pos ∧ pos' = Function.update pos p w

end HubbardMoments
